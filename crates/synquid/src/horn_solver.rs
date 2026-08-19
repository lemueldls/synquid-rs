//! Second-order constraint solver (mirror of `Synquid.HornSolver`).
//!
//! The Haskell reference is a `ReaderT HornSolverParams s` over a `MonadSMT`
//! state (`Z3State`); the plan's decision (M1) is to thread state explicitly,
//! so `FixPointSolver` below borrows the `Z3Runtime` (the `MonadSMT` state)
//! and the `HornSolverParams` (the reader environment) directly.

use std::collections::BTreeSet;

use crate::{
    cli::HornSolverParams,
    logic::{
        BinOp, Candidate, ExtractAssumptions, Formula, QMap, QSpace, Solution, Valuation, and,
        and_clean, apply_solution, conjunction, conjuncts_of, disjunction, ffalse, fnot, ftrue,
        iff, implies, left_hand_side, lookup_max_count, lookup_quals, lookup_quals_subst, merge,
        neg_unknowns, pos_unknowns, right_hand_side, substitute, u_dnf, unknown_name, unknowns_of,
        valuation,
    },
    program::Environment,
    smt::Z3Runtime,
    util::{bounded_subsets, restrict_domain, set_concat_map},
};

/// The fix point solver environment: Z3 state + solver parameters
/// (mirror of `FixPointSolver s = ReaderT HornSolverParams s`).
pub struct FixPointSolver {
    z3: Z3Runtime,
    params: HornSolverParams,
}

impl FixPointSolver {
    /// Cumulative time spent inside Z3 calls, in microseconds.
    #[must_use]
    pub fn z3_us(&self) -> u128 {
        self.z3.total_us()
    }

    /// Number of `is_sat` calls.
    #[must_use]
    pub fn sat_calls(&self) -> u64 {
        self.z3.sat_calls()
    }

    /// Number of `get_all_mus` calls.
    #[must_use]
    pub fn mus_calls(&self) -> u64 {
        self.z3.mus_calls()
    }

    /// `initHornSolver`: initialize the underlying SMT
    /// state. The initial candidate is `crate::logic::initial_candidate`.
    #[must_use]
    pub fn init_horn_solver(env: &Environment, params: &HornSolverParams) -> FixPointSolver {
        FixPointSolver {
            z3: Z3Runtime::new(env),
            params: params.clone(),
        }
    }

    /// `preprocessConstraint`: `preprocess` below.
    #[must_use]
    pub fn preprocess_constraint(&self, fml: &Formula) -> Vec<Formula> {
        Self::preprocess(fml, self.params.is_least_fixpoint)
    }

    /// `checkCandidates`: `check` below.
    #[must_use]
    pub fn check_candidates(
        &mut self,
        consistency: bool,
        fmls: &[Formula],
        extract_assumptions: &ExtractAssumptions,
        cands: &[Candidate],
    ) -> Vec<Candidate> {
        Self::check(&mut self.z3, consistency, fmls, extract_assumptions, cands)
    }

    /// `refineCandidates`: `refine` below.
    #[must_use]
    pub fn refine_candidates(
        &mut self,
        constraints: &[Formula],
        quals: &QMap,
        extract_assumptions: &ExtractAssumptions,
        cands: &[Candidate],
    ) -> Vec<Candidate> {
        Self::refine(
            &mut self.z3,
            &self.params,
            constraints,
            quals,
            extract_assumptions,
            cands,
        )
    }

    /// `pruneQualifiers`: remove redundant qualifiers
    /// from `quals` when `pruneQuals` is set, otherwise return them as is.
    #[must_use]
    pub fn prune_qualifiers(&mut self, quals: QSpace) -> QSpace {
        if self.params.prune_quals {
            Self::prune_q_space(&mut self.z3, &quals)
        } else {
            quals
        }
    }

    /// `isValid`: is `fml` valid (free variables
    /// implicitly universally quantified)?
    #[must_use]
    pub fn is_valid_fml(z3: &mut Z3Runtime, fml: &Formula) -> bool {
        !z3.is_sat(&fnot(fml.clone()))
    }

    /// `isSat`: is `fml` satisfiable (free variables
    /// implicitly existentially quantified)?
    #[must_use]
    pub fn is_sat_fml(z3: &mut Z3Runtime, fml: &Formula) -> bool {
        z3.is_sat(fml)
    }

    /// `hornApplySolution`: apply the solution to both
    /// sides of the clause and conjoin the extracted axioms with the
    /// (simplified) antecedent.
    #[must_use]
    pub fn horn_apply_solution(
        extract_assumptions: &ExtractAssumptions,
        sol: &Solution,
        fml: &Formula,
    ) -> Formula {
        let (lhs, rhs) = match fml {
            Formula::Binary(BinOp::Implies, lhs, rhs) => (&**lhs, &**rhs),
            _ => panic!("hornApplySolution: not an implication"),
        };
        let lhs1 = apply_solution(sol, lhs);
        let rhs1 = apply_solution(sol, rhs);
        let assumptions = extract_assumptions(&lhs1)
            .union(&extract_assumptions(&rhs1))
            .cloned()
            .collect::<BTreeSet<_>>();
        Formula::Binary(
            BinOp::Implies,
            Box::new(and_clean(lhs1, conjunction(&assumptions))),
            Box::new(rhs1),
        )
    }

    /// `preprocess`: convert a Horn clause to the
    /// format the fix point solver expects.
    fn preprocess(fml: &Formula, lfp: bool) -> Vec<Formula> {
        match fml {
            Formula::Binary(BinOp::Implies, lhs, rhs) => {
                if lfp {
                    let r_disjuncts: BTreeSet<Formula> = u_dnf(rhs).into_iter().collect();
                    let (no_unknowns, with_unknowns): (BTreeSet<Formula>, BTreeSet<Formula>) =
                        r_disjuncts
                            .into_iter()
                            .partition(|d| unknowns_of(d).is_empty());
                    assert!(
                        with_unknowns.len() <= 1,
                        "Least fixpoint solver got a disjunctive right-hand-side: {rhs:?}"
                    );
                    let mut lhs_extra: BTreeSet<Formula> =
                        no_unknowns.iter().map(|d| fnot(d.clone())).collect();
                    lhs_extra.insert((**lhs).clone());
                    let lhs1 = conjunction(&lhs_extra);
                    let r_conjuncts = conjuncts_of(&disjunction(&with_unknowns));
                    let (conj_no_unknowns, conj_with_unknowns): (
                        BTreeSet<Formula>,
                        BTreeSet<Formula>,
                    ) = r_conjuncts
                        .into_iter()
                        .partition(|c| unknowns_of(c).is_empty());
                    let mut rhss = Vec::new();
                    if !conj_no_unknowns.is_empty() {
                        rhss.push(conjunction(&conj_no_unknowns));
                    }
                    rhss.extend(conj_with_unknowns);
                    rhss.into_iter().map(|r| implies(lhs1.clone(), r)).collect()
                } else {
                    u_dnf(lhs)
                        .into_iter()
                        .map(|l| implies(l, (**rhs).clone()))
                        .collect()
                }
            }
            _ => panic!("preprocess: encountered ill-formed constraint {fml:?}"),
        }
    }

    /// `refine`: solve `constraints` using `quals`
    /// starting from candidates `cands`.
    fn refine(
        z3: &mut Z3Runtime,
        params: &HornSolverParams,
        constraints: &[Formula],
        quals: &QMap,
        extract_assumptions: &ExtractAssumptions,
        cands: &[Candidate],
    ) -> Vec<Candidate> {
        let constraints1 = constraints
            .iter()
            .filter(|c| Self::is_new(c, &cands[0]))
            .cloned()
            .collect::<Vec<_>>();
        let cands1 = cands
            .iter()
            .map(|c| {
                Self::add_constraints(z3, params, quals, extract_assumptions, &constraints1, c)
            })
            .collect::<Vec<_>>();
        if let Some(idx) = cands1.iter().position(|c| c.invalid_constraints.is_empty()) {
            let mut result = cands1;
            let c = result.remove(idx);
            result.insert(0, c);
            result
        } else if params.is_least_fixpoint {
            Self::least_fixpoint(z3, params, extract_assumptions, cands1)
        } else {
            Self::greatest_fixpoint(z3, params, quals, extract_assumptions, cands1)
        }
    }

    /// `check`: keep candidates under which all `fmls`
    /// are valid or satisfiable, depending on `consistency`.
    fn check(
        z3: &mut Z3Runtime,
        consistency: bool,
        fmls: &[Formula],
        extract_assumptions: &ExtractAssumptions,
        cands: &[Candidate],
    ) -> Vec<Candidate> {
        cands
            .iter()
            .filter(|c| check_cand(z3, consistency, fmls, extract_assumptions, c))
            .cloned()
            .collect()
    }

    /// `greatestFixPoint`: weakest solution for a
    /// system of second-order constraints.
    fn greatest_fixpoint(
        z3: &mut Z3Runtime,
        params: &HornSolverParams,
        quals: &QMap,
        extract_assumptions: &ExtractAssumptions,
        candidates: Vec<Candidate>,
    ) -> Vec<Candidate> {
        if candidates.is_empty() {
            return candidates;
        }
        let (cand, rest) = Self::pick_candidate(&candidates, params.candidate_pick_strategy);
        let fml = Self::pick_constraint_gfp(&cand, quals, params.constraint_pick_strategy);
        let modified_constraint = Self::instantiate_rhs(&cand.solution, &fml);
        let diffs = Self::strengthen(
            z3,
            params,
            quals,
            extract_assumptions,
            &modified_constraint,
            &cand.solution,
        );
        let (mut new_candidates, rest1) = if diffs.len() == 1 {
            let unknowns: BTreeSet<String> = unknowns_of(&fml)
                .iter()
                .map(unknown_name)
                .cloned()
                .collect();
            let (equivs, nequivs): (Vec<Candidate>, Vec<Candidate>) =
                rest.into_iter().partition(|c| {
                    restrict_domain(&unknowns, &c.solution)
                        == restrict_domain(&unknowns, &cand.solution)
                        && c.invalid_constraints.contains(&fml)
                });
            let mut cands = vec![cand];
            cands.extend(equivs);
            let nc: Vec<Candidate> = cands
                .into_iter()
                .map(|c| {
                    Self::update_candidate(z3, extract_assumptions, &fml, c, &diffs, &diffs[0])
                })
                .collect();
            (nc, nequivs)
        } else {
            let nc = diffs
                .iter()
                .map(|diff| {
                    Self::update_candidate(
                        z3,
                        extract_assumptions,
                        &fml,
                        cand.clone(),
                        &diffs,
                        diff,
                    )
                })
                .collect();
            (nc, rest)
        };
        if let Some(idx) = new_candidates
            .iter()
            .position(|c| c.invalid_constraints.is_empty())
        {
            let cand1 = new_candidates.remove(idx);
            let mut result = vec![cand1];
            result.extend(new_candidates);
            result.extend(rest1);
            result
        } else {
            let mut candidates = new_candidates;
            candidates.extend(rest1);
            Self::greatest_fixpoint(z3, params, quals, extract_assumptions, candidates)
        }
    }

    /// `strengthen`: all minimal strengthenings of
    /// `sol` using qualifiers from `qmap` that make `fml` valid.
    fn strengthen(
        z3: &mut Z3Runtime,
        params: &HornSolverParams,
        qmap: &QMap,
        extract_assumptions: &ExtractAssumptions,
        fml: &Formula,
        sol: &Solution,
    ) -> Vec<Solution> {
        let (lhs, rhs) = match fml {
            Formula::Binary(BinOp::Implies, lhs, rhs) => (&**lhs, &**rhs),
            _ => panic!("strengthen: not an implication"),
        };
        let unknowns = unknowns_of(lhs);
        let known_conjuncts = conjuncts_of(lhs)
            .difference(&unknowns)
            .cloned()
            .collect::<BTreeSet<_>>();
        let unknowns_list = unknowns.iter().cloned().collect::<Vec<_>>();
        let lhs_quals = set_concat_map(
            |u| lookup_quals_subst(qmap, u).into_iter().collect(),
            &unknowns,
        );
        let used_lhs_quals = set_concat_map(|u| valuation(sol, u), &unknowns)
            .union(&known_conjuncts)
            .cloned()
            .collect::<BTreeSet<_>>();
        let assumptions = set_concat_map(extract_assumptions, &lhs_quals)
            .union(&set_concat_map(extract_assumptions, &known_conjuncts))
            .cloned()
            .chain(extract_assumptions(rhs))
            .collect::<BTreeSet<_>>();
        let all_assumptions = used_lhs_quals.union(&assumptions).cloned().collect();
        let n = Self::max_val_size(qmap, sol, &unknowns);
        let available: BTreeSet<Formula> = lhs_quals.difference(&used_lhs_quals).cloned().collect();
        let lhs_valuations =
            Self::optimal_valuations(z3, params, &available, &all_assumptions, rhs, n);
        let split_vals = |vals: Vec<Valuation>| {
            let mut res: Vec<Solution> = Vec::new();
            for val in vals {
                for s in Self::split_lhs_valuation(qmap, sol, &unknowns_list, &val) {
                    if !res.contains(&s) {
                        res.push(s);
                    }
                }
            }
            res
        };
        if params.semantic_prune {
            if params.aggressive_prune {
                let prune_assumptions: BTreeSet<Formula> = if *rhs == ffalse() {
                    BTreeSet::new()
                } else {
                    all_assumptions
                };
                let valuations1 =
                    Self::prune_valuations(z3, &conjunction(&prune_assumptions), lhs_valuations);
                split_vals(valuations1)
            } else {
                Self::prune_solutions(z3, &unknowns_list, split_vals(lhs_valuations))
            }
        } else {
            split_vals(lhs_valuations)
        }
    }

    /// `weaken`: a minimal weakening of `sol` that
    /// makes `fml` valid.
    fn weaken(z3: &mut Z3Runtime, fml: &Formula, sol: &Solution) -> Option<Solution> {
        match fml {
            Formula::Binary(BinOp::Implies, lhs, rhs) => {
                match &**rhs {
                    Formula::Unknown(subst, u) => {
                        let quals1 = sol
                            .get(u)
                            .expect("weaken: no value for unknown")
                            .iter()
                            .filter(|q| {
                                Self::is_valid_fml(
                                    z3,
                                    &Formula::Binary(
                                        BinOp::Implies,
                                        lhs.clone(),
                                        Box::new(substitute(subst, (*q).clone())),
                                    ),
                                )
                            })
                            .cloned()
                            .collect::<BTreeSet<_>>();
                        let mut sol1 = sol.clone();
                        sol1.insert(u.clone(), quals1);
                        Some(sol1)
                    }
                    _ => None,
                }
            }
            _ => panic!("weaken: not an implication"),
        }
    }

    /// `optimalValuations`: all smallest subsets of
    /// `quals` for which the check returns a solution.
    fn optimal_valuations(
        z3: &mut Z3Runtime,
        params: &HornSolverParams,
        quals: &BTreeSet<Formula>,
        lhs: &BTreeSet<Formula>,
        rhs: &Formula,
        max_size: usize,
    ) -> Vec<Valuation> {
        match params.optimal_valuations_strategy {
            crate::cli::OptimalValuationsStrategy::BfsValuations => {
                optimal_valuations_bfs(z3, max_size, quals, lhs, rhs)
            }
            crate::cli::OptimalValuationsStrategy::MarcoValuations => {
                optimal_valuations_marco(z3, quals, lhs, rhs)
            }
        }
    }

    /// `leastFixPoint`: strongest solution for a system
    /// of second-order constraints.
    fn least_fixpoint(
        z3: &mut Z3Runtime,
        params: &HornSolverParams,
        extract_assumptions: &ExtractAssumptions,
        candidates: Vec<Candidate>,
    ) -> Vec<Candidate> {
        if candidates.is_empty() {
            return candidates;
        }
        let mut rest = candidates;
        let cand = rest.remove(0);
        let fml = Self::pick_constraint_lfp(&cand, params.constraint_pick_strategy);
        let (lhs, rhs) = match &fml {
            Formula::Binary(BinOp::Implies, lhs, rhs) => (&**lhs, &**rhs),
            _ => panic!("leastFixPoint: not an implication"),
        };
        let lhs1 = apply_solution(&cand.solution, lhs);
        let assumptions = extract_assumptions(&lhs1)
            .union(&extract_assumptions(&apply_solution(&cand.solution, rhs)))
            .cloned()
            .collect::<BTreeSet<_>>();
        let mut modified_lhs: BTreeSet<Formula> = assumptions;
        modified_lhs.insert(lhs1);
        let modified_constraint = Formula::Binary(
            BinOp::Implies,
            Box::new(conjunction(&modified_lhs)),
            Box::new(rhs.clone()),
        );
        match Self::weaken(z3, &modified_constraint, &cand.solution) {
            None => Self::least_fixpoint(z3, params, extract_assumptions, rest),
            Some(sol1) => {
                let cand1 = Self::update_candidate_lfp(z3, extract_assumptions, &fml, cand, &sol1);
                if cand1.invalid_constraints.is_empty() {
                    let mut result = vec![cand1];
                    result.extend(rest);
                    result
                } else {
                    let mut candidates = vec![cand1];
                    candidates.extend(rest);
                    Self::least_fixpoint(z3, params, extract_assumptions, candidates)
                }
            }
        }
    }

    /// `pruneSolutions`: eliminate solutions that are
    /// semantically stronger on all unknowns than another solution.
    fn prune_solutions(
        z3: &mut Z3Runtime,
        unknowns: &[Formula],
        solutions: Vec<Solution>,
    ) -> Vec<Solution> {
        let is_subsumed = |sol: &Solution, xs: &[Solution]| {
            xs.iter().any(|s| {
                unknowns.iter().all(|u| {
                    Self::is_valid_fml(
                        z3,
                        &implies(
                            conjunction(&valuation(sol, u)),
                            conjunction(&valuation(s, u)),
                        ),
                    )
                })
            })
        };
        prune(is_subsumed, solutions)
    }

    /// `pruneValuations`: eliminate valuations that
    /// are semantically stronger than another valuation.
    fn prune_valuations(
        z3: &mut Z3Runtime,
        assumption: &Formula,
        vals: Vec<Valuation>,
    ) -> Vec<Valuation> {
        let is_subsumed = |val: &Valuation, xs: &[Valuation]| {
            xs.iter().any(|v| strictly_implies(z3, assumption, val, v))
        };
        prune(is_subsumed, vals)
    }

    /// `pruneQSpace`: eliminate logical duplicates
    /// from the qualifier space.
    fn prune_q_space(z3: &mut Z3Runtime, q_space: &QSpace) -> QSpace {
        let quals1 = q_space
            .qualifiers
            .iter()
            .filter(|q| !Self::is_valid_fml(z3, q) && !Self::is_valid_fml(z3, &fnot((*q).clone())))
            .cloned()
            .collect::<Vec<_>>();
        let quals = prune(
            |qual: &Formula, xs: &[Formula]| {
                xs.iter()
                    .any(|q| Self::is_valid_fml(z3, &iff(qual.clone(), q.clone())))
            },
            quals1,
        );
        QSpace {
            qualifiers: quals,
            max_count: q_space.max_count,
        }
    }

    /// A constraint that the head candidate has neither already solved nor
    /// failed.
    fn is_new(c: &Formula, cand: &Candidate) -> bool {
        !cand.valid_constraints.contains(c) && !cand.invalid_constraints.contains(c)
    }

    /// `addConstraints` (in `refine`).
    fn add_constraints(
        z3: &mut Z3Runtime,
        params: &HornSolverParams,
        quals: &QMap,
        extract_assumptions: &ExtractAssumptions,
        constraints: &[Formula],
        cand: &Candidate,
    ) -> Candidate {
        let init_sol = if params.is_least_fixpoint {
            crate::logic::bot_solution(quals)
        } else {
            crate::logic::top_solution(quals)
        };
        let sol1 = merge(&cand.solution, &init_sol);
        let (valids, invalids): (Vec<Formula>, Vec<Formula>) =
            constraints.iter().cloned().partition(|c| {
                Self::is_valid_fml(
                    z3,
                    &Self::horn_apply_solution(extract_assumptions, &sol1, c),
                )
            });
        Candidate {
            solution: sol1,
            valid_constraints: cand
                .valid_constraints
                .union(&valids.into_iter().collect())
                .cloned()
                .collect(),
            invalid_constraints: cand
                .invalid_constraints
                .union(&invalids.into_iter().collect())
                .cloned()
                .collect(),
            label: cand.label.clone(),
        }
    }

    /// `instantiateRhs` (in `greatestFixPoint`).
    fn instantiate_rhs(sol: &Solution, fml: &Formula) -> Formula {
        match fml {
            Formula::Binary(BinOp::Implies, lhs, rhs) => {
                Formula::Binary(
                    BinOp::Implies,
                    lhs.clone(),
                    Box::new(apply_solution(sol, rhs)),
                )
            }
            _ => panic!("instantiateRhs: not an implication"),
        }
    }

    /// `updateCandidate` (in `greatestFixPoint`).
    fn update_candidate(
        z3: &mut Z3Runtime,
        extract_assumptions: &ExtractAssumptions,
        fml: &Formula,
        cand: Candidate,
        diffs: &[Solution],
        diff: &Solution,
    ) -> Candidate {
        let sol1 = merge(&cand.solution, diff);
        let modified_unknowns: BTreeSet<String> = diff
            .iter()
            .filter(|(_, v)| !v.is_empty())
            .map(|(k, _)| k.clone())
            .collect();
        let valids_with_fml: BTreeSet<Formula> = cand
            .valid_constraints
            .iter()
            .cloned()
            .chain(std::iter::once(fml.clone()))
            .collect();
        let (unaffected_valids, affected_valids): (BTreeSet<Formula>, BTreeSet<Formula>) =
            valids_with_fml
                .into_iter()
                .partition(|f| pos_unknowns(f).is_disjoint(&modified_unknowns));
        let invalids_without_fml: BTreeSet<Formula> = cand
            .invalid_constraints
            .iter()
            .filter(|f| **f != *fml)
            .cloned()
            .collect();
        let (unaffected_invalids, affected_invalids): (BTreeSet<Formula>, BTreeSet<Formula>) =
            invalids_without_fml
                .into_iter()
                .partition(|f| neg_unknowns(f).is_disjoint(&modified_unknowns));
        let (new_valids, new_invalids): (BTreeSet<Formula>, BTreeSet<Formula>) = affected_valids
            .union(&affected_invalids)
            .cloned()
            .partition(|f| {
                Self::is_valid_fml(
                    z3,
                    &Self::horn_apply_solution(extract_assumptions, &sol1, f),
                )
            });
        let new_label = if diffs.len() == 1 {
            cand.label
        } else {
            let idx = diffs
                .iter()
                .position(|d| d == diff)
                .expect("updateCandidate: diff not in diffs");
            format!("{}.{idx}", cand.label)
        };
        Candidate {
            solution: sol1,
            valid_constraints: unaffected_valids.union(&new_valids).cloned().collect(),
            invalid_constraints: unaffected_invalids.union(&new_invalids).cloned().collect(),
            label: new_label,
        }
    }

    /// `updateCandidate` (in `leastFixPoint`).
    fn update_candidate_lfp(
        z3: &mut Z3Runtime,
        extract_assumptions: &ExtractAssumptions,
        fml: &Formula,
        cand: Candidate,
        sol1: &Solution,
    ) -> Candidate {
        let modified_unknowns = pos_unknowns(&right_hand_side(fml));
        let valids_with_fml: BTreeSet<Formula> = cand
            .valid_constraints
            .iter()
            .cloned()
            .chain(std::iter::once(fml.clone()))
            .collect();
        let (unaffected_valids, affected_valids): (BTreeSet<Formula>, BTreeSet<Formula>) =
            valids_with_fml
                .into_iter()
                .partition(|f| neg_unknowns(f).is_disjoint(&modified_unknowns));
        let invalids_without_fml: BTreeSet<Formula> = cand
            .invalid_constraints
            .iter()
            .filter(|f| **f != *fml)
            .cloned()
            .collect();
        let (unaffected_invalids, affected_invalids): (BTreeSet<Formula>, BTreeSet<Formula>) =
            invalids_without_fml
                .into_iter()
                .partition(|f| pos_unknowns(f).is_disjoint(&modified_unknowns));
        let (new_valids, new_invalids): (BTreeSet<Formula>, BTreeSet<Formula>) = affected_valids
            .union(&affected_invalids)
            .cloned()
            .partition(|f| {
                Self::is_valid_fml(z3, &Self::horn_apply_solution(extract_assumptions, sol1, f))
            });
        Candidate {
            solution: sol1.clone(),
            valid_constraints: unaffected_valids.union(&new_valids).cloned().collect(),
            invalid_constraints: unaffected_invalids.union(&new_invalids).cloned().collect(),
            label: cand.label,
        }
    }

    /// `pickCandidate` (in `greatestFixPoint`).
    fn pick_candidate(
        cands: &[Candidate],
        strategy: crate::cli::CandidatePickStrategy,
    ) -> (Candidate, Vec<Candidate>) {
        match strategy {
            crate::cli::CandidatePickStrategy::FirstCandidate => {
                let mut rest = cands.to_vec();
                let cand = rest.remove(0);
                (cand, rest)
            }
            crate::cli::CandidatePickStrategy::ValidWeakCandidate => {
                let best = cands
                    .iter()
                    .max_by(|a, b| {
                        let fa = (
                            a.invalid_constraints.len(),
                            total_q_count(&a.solution),
                            nontriv_count(&a.solution),
                        );
                        let fb = (
                            b.invalid_constraints.len(),
                            total_q_count(&b.solution),
                            nontriv_count(&b.solution),
                        );
                        fb.cmp(&fa)
                    })
                    .expect("pickCandidate: empty list");
                let idx = cands
                    .iter()
                    .position(|c| std::ptr::eq(c, best))
                    .expect("pickCandidate: best not found");
                let mut rest = cands.to_vec();
                (rest.remove(idx), rest)
            }
            crate::cli::CandidatePickStrategy::InitializedWeakCandidate => {
                let best = cands
                    .iter()
                    .max_by(|a, b| {
                        let fa = (nontriv_count(&a.solution), total_q_count(&a.solution));
                        let fb = (nontriv_count(&b.solution), total_q_count(&b.solution));
                        fb.cmp(&fa)
                    })
                    .expect("pickCandidate: empty list");
                let idx = cands
                    .iter()
                    .position(|c| std::ptr::eq(c, best))
                    .expect("pickCandidate: best not found");
                let mut rest = cands.to_vec();
                (rest.remove(idx), rest)
            }
        }
    }

    /// `pickConstraint` in `greatestFixPoint`.
    fn pick_constraint_gfp(
        cand: &Candidate,
        quals: &QMap,
        strategy: crate::cli::ConstraintPickStrategy,
    ) -> Formula {
        match strategy {
            crate::cli::ConstraintPickStrategy::FirstConstraint => {
                cand.invalid_constraints
                    .iter()
                    .next()
                    .cloned()
                    .expect("pickConstraint: no invalid constraints")
            }
            crate::cli::ConstraintPickStrategy::SmallSpaceConstraint => {
                cand.invalid_constraints
                    .iter()
                    .min_by(|x, y| {
                        let sx = Self::max_val_size(
                            quals,
                            &cand.solution,
                            &unknowns_of(&left_hand_side(x)),
                        );
                        let sy = Self::max_val_size(
                            quals,
                            &cand.solution,
                            &unknowns_of(&left_hand_side(y)),
                        );
                        sx.cmp(&sy)
                    })
                    .cloned()
                    .expect("pickConstraint: no invalid constraints")
            }
        }
    }

    /// `pickConstraint` in `leastFixPoint`.
    fn pick_constraint_lfp(
        cand: &Candidate,
        strategy: crate::cli::ConstraintPickStrategy,
    ) -> Formula {
        match strategy {
            crate::cli::ConstraintPickStrategy::FirstConstraint => {
                cand.invalid_constraints
                    .iter()
                    .next()
                    .cloned()
                    .expect("pickConstraint: no invalid constraints")
            }
            crate::cli::ConstraintPickStrategy::SmallSpaceConstraint => {
                cand.invalid_constraints
                    .iter()
                    .min_by(|x, y| {
                        let sx = unknowns_of(&right_hand_side(x)).len();
                        let sy = unknowns_of(&right_hand_side(y)).len();
                        sx.cmp(&sy)
                    })
                    .cloned()
                    .expect("pickConstraint: no invalid constraints")
            }
        }
    }

    /// `maxValSize`: upper bound on the size of
    /// valuations of a conjunction of unknowns when strengthening `sol`.
    fn max_val_size(qmap: &QMap, sol: &Solution, unknowns: &BTreeSet<Formula>) -> usize {
        let used_quals = set_concat_map(|u| valuation(sol, u), unknowns);
        let total: usize = unknowns.iter().map(|u| lookup_max_count(qmap, u)).sum();
        total - used_quals.len()
    }

    /// `splitLhsValuation` (in `strengthen`): all valid
    /// partitions of `lhs_val` into solutions for multiple unknowns.
    fn split_lhs_valuation(
        qmap: &QMap,
        sol: &Solution,
        unknowns_list: &[Formula],
        lhs_val: &Valuation,
    ) -> Vec<Solution> {
        fn go(
            qmap: &QMap,
            unknowns_list: &[Formula],
            lhs_val: &Valuation,
            options: &[Vec<BTreeSet<Formula>>],
            acc: &mut Vec<Solution>,
            chosen: &mut Vec<BTreeSet<Formula>>,
            total: &BTreeSet<Formula>,
            size: usize,
        ) {
            match options.split_first() {
                None => {
                    if *total == *lhs_val && size == lhs_val.len() {
                        let mut sol = Solution::new();
                        for (u, val) in unknowns_list.iter().zip(chosen.iter()) {
                            for (name, valuation) in FixPointSolver::unsubst(qmap, u, val) {
                                sol.entry(name).or_default().extend(valuation);
                            }
                        }
                        acc.push(sol);
                    }
                }
                Some((head, tail)) => {
                    for option in head {
                        chosen.push(option.clone());
                        let mut new_total = total.clone();
                        new_total.extend(option.iter().cloned());
                        go(
                            qmap,
                            unknowns_list,
                            lhs_val,
                            tail,
                            acc,
                            chosen,
                            &new_total,
                            size + option.len(),
                        );
                        chosen.pop();
                    }
                }
            }
        }
        let options: Vec<Vec<BTreeSet<Formula>>> = unknowns_list
            .iter()
            .map(|u| Self::single_unknown_candidates(qmap, sol, u, lhs_val))
            .collect();
        let mut acc = Vec::new();
        go(
            qmap,
            unknowns_list,
            lhs_val,
            &options,
            &mut acc,
            &mut Vec::new(),
            &BTreeSet::new(),
            0,
        );
        acc
    }

    /// `singleUnknownCandidates` (in `strengthen`).
    fn single_unknown_candidates(
        qmap: &QMap,
        sol: &Solution,
        u: &Formula,
        lhs_val: &Valuation,
    ) -> Vec<BTreeSet<Formula>> {
        let qs = lookup_quals_subst(qmap, u);
        let max = lookup_max_count(qmap, u);
        let used = valuation(sol, u);
        let n = used.len();
        let pool: BTreeSet<Formula> = qs
            .into_iter()
            .filter(|q| !used.contains(q))
            .filter(|q| lhs_val.contains(q))
            .collect();
        bounded_subsets(max - n, &pool).into_iter().collect()
    }

    /// `unsubst` (in `strengthen`).
    fn unsubst(
        qmap: &QMap,
        u: &Formula,
        val: &BTreeSet<Formula>,
    ) -> Vec<(String, BTreeSet<Formula>)> {
        let ((), name) = match u {
            Formula::Unknown(_, name) => ((), name),
            _ => panic!("unsubst: not an unknown"),
        };
        let mut acc: Vec<BTreeSet<Formula>> = vec![BTreeSet::new()];
        for qual in val {
            let options = Self::unsubst_qual(qmap, u, qual);
            let mut new_acc = Vec::new();
            for option in options {
                for chosen in &acc {
                    let mut c = chosen.clone();
                    c.insert(option.clone());
                    new_acc.push(c);
                }
            }
            acc = new_acc;
        }
        acc.into_iter().map(|s| (name.clone(), s)).collect()
    }

    /// `unsubstQual` (in `strengthen`).
    fn unsubst_qual(qmap: &QMap, u: &Formula, qual: &Formula) -> Vec<Formula> {
        match u {
            Formula::Unknown(subst, _) => {
                lookup_quals(qmap, u)
                    .iter()
                    .filter(|q| substitute(subst, (*q).clone()) == *qual)
                    .cloned()
                    .collect()
            }
            _ => panic!("unsubstQual: not an unknown"),
        }
    }
}

/// `strictlyImplies` (in `pruneValuations`).
fn strictly_implies(
    z3: &mut Z3Runtime,
    assumption: &Formula,
    ls: &Valuation,
    rs: &Valuation,
) -> bool {
    let l = conjunction(ls);
    let r = conjunction(rs);
    let res1 = FixPointSolver::is_valid_fml(
        z3,
        &implies(and_clean(assumption.clone(), l.clone()), r.clone()),
    );
    let res2 = FixPointSolver::is_valid_fml(z3, &implies(and_clean(assumption.clone(), r), l));
    res1 && (!res2 || ls.len() > rs.len())
}

/// `prune`: prune elements subsumed by another element
/// (note: the reference returns the survivors in reverse order).
fn prune<A: Clone>(mut is_subsumed: impl FnMut(&A, &[A]) -> bool, xs: Vec<A>) -> Vec<A> {
    fn go<A: Clone>(
        is_subsumed: &mut impl FnMut(&A, &[A]) -> bool,
        lefts: Vec<A>,
        x: A,
        mut rights: Vec<A>,
    ) -> Vec<A> {
        if rights.is_empty() {
            if is_subsumed(&x, &lefts) {
                lefts
            } else {
                let mut res = vec![x];
                res.extend(lefts);
                res
            }
        } else {
            let mut lefts_rights: Vec<A> = lefts.clone();
            lefts_rights.extend(rights.iter().cloned());
            let y = rights.remove(0);
            if is_subsumed(&x, &lefts_rights) {
                go(is_subsumed, lefts, y, rights)
            } else {
                let mut lefts1 = lefts;
                lefts1.push(x);
                go(is_subsumed, lefts1, y, rights)
            }
        }
    }
    if xs.is_empty() {
        Vec::new()
    } else {
        let mut xs = xs;
        let x = xs.remove(0);
        go(&mut is_subsumed, Vec::new(), x, xs)
    }
}

/// `filterSubsets`: all minimal subsets of indexes
/// from `[0..n)` that satisfy `check` (monotone), via breadth-first search.
fn filter_subsets(
    mut check: impl FnMut(&BTreeSet<usize>) -> bool,
    n: usize,
) -> Vec<BTreeSet<usize>> {
    fn go(
        check: &mut impl FnMut(&BTreeSet<usize>) -> bool,
        n: usize,
        mut solutions: Vec<BTreeSet<usize>>,
        candidates: Vec<BTreeSet<usize>>,
    ) -> Vec<BTreeSet<usize>> {
        if candidates.is_empty() {
            return solutions;
        }
        let new: Vec<BTreeSet<usize>> = candidates
            .into_iter()
            .filter(|c| !solutions.iter().any(|s| s.is_subset(c)))
            .collect();
        let results: Vec<(BTreeSet<usize>, bool)> =
            new.iter().map(|c| (c.clone(), check(c))).collect();
        let valids: Vec<BTreeSet<usize>> = results
            .iter()
            .filter(|(_, ok)| *ok)
            .map(|(c, _)| c.clone())
            .collect();
        let invalids: Vec<BTreeSet<usize>> = results
            .iter()
            .filter(|(_, ok)| !*ok)
            .map(|(c, _)| c.clone())
            .collect();
        let children: Vec<BTreeSet<usize>> =
            invalids.iter().flat_map(|idxs| children(idxs, n)).collect();
        solutions.extend(valids);
        go(check, n, solutions, children)
    }
    go(&mut check, n, Vec::new(), vec![BTreeSet::new()])
}

/// `children` (in `filterSubsets`).
fn children(idxs: &BTreeSet<usize>, n: usize) -> Vec<BTreeSet<usize>> {
    let lower = if idxs.is_empty() {
        0
    } else {
        *idxs.iter().next_back().expect("children: empty") + 1
    };
    (lower..n)
        .map(|i| {
            let mut c = idxs.clone();
            c.insert(i);
            c
        })
        .collect()
}

/// `optimalValuationsBFS`: all smallest subsets of
/// `quals` for which the check returns a solution.
fn optimal_valuations_bfs(
    z3: &mut Z3Runtime,
    max_size: usize,
    quals: &BTreeSet<Formula>,
    lhs: &BTreeSet<Formula>,
    rhs: &Formula,
) -> Vec<Valuation> {
    let quals_list: Vec<Formula> = quals.iter().cloned().collect();
    let quals_at = |idxs: &BTreeSet<usize>| {
        idxs.iter()
            .map(|&i| quals_list[i].clone())
            .collect::<BTreeSet<_>>()
    };
    let mut check = |idxs: &BTreeSet<usize>| {
        let val = quals_at(idxs);
        let n = val.len();
        if n >= 1 && n <= max_size {
            let lhs1 = and_clean(conjunction(lhs), conjunction(&val));
            FixPointSolver::is_valid_fml(z3, &implies(lhs1, rhs.clone()))
        } else {
            false
        }
    };
    filter_subsets(&mut check, quals_list.len())
        .into_iter()
        .map(|idxs| quals_at(&idxs))
        .collect()
}

/// `optimalValuationsMarco`: all smallest subsets of
/// `quals` for which the check returns a solution, via MARCO.
fn optimal_valuations_marco(
    z3: &mut Z3Runtime,
    quals: &BTreeSet<Formula>,
    lhs: &BTreeSet<Formula>,
    rhs: &Formula,
) -> Vec<Valuation> {
    let quals_list: Vec<Formula> = quals
        .iter()
        .filter(|q| !lhs.contains(q) && !lhs.contains(&fnot((*q).clone())))
        .cloned()
        .collect();
    let fixed_lhs = conjunction(lhs);
    let fixed_rhs = fnot(rhs.clone());
    let (assumption, must_have) = if *rhs == ffalse() {
        (ftrue(), fixed_lhs)
    } else {
        (fixed_lhs, fixed_rhs)
    };
    z3.get_all_mus(&assumption, &must_have, &quals_list)
        .into_iter()
        .map(|core| core.into_iter().collect())
        .collect()
}

/// `checkCand` (in `check`).
fn check_cand(
    z3: &mut Z3Runtime,
    consistency: bool,
    fmls: &[Formula],
    extract_assumptions: &ExtractAssumptions,
    cand: &Candidate,
) -> bool {
    let apply = |sol: &Solution, fml: &Formula| {
        let applied = apply_solution(sol, fml);
        let with_assumptions = conjunction(&extract_assumptions(&applied));
        and(applied, with_assumptions)
    };

    if consistency {
        fmls.iter()
            .all(|f| FixPointSolver::is_sat_fml(z3, &apply(&cand.solution, f)))
    } else {
        fmls.iter().all(|f| {
            FixPointSolver::is_valid_fml(
                z3,
                &FixPointSolver::horn_apply_solution(extract_assumptions, &cand.solution, f),
            )
        })
    }
}

/// `nontrivCount` (in `greatestFixPoint`): number of
/// unknowns with a non-top valuation.
fn nontriv_count(sol: &Solution) -> usize {
    sol.values().filter(|v| !v.is_empty()).count()
}

/// `totalQCount` (in `greatestFixPoint`): total number
/// of qualifiers in a solution.
fn total_q_count(sol: &Solution) -> usize {
    sol.values().map(|v| v.len()).sum()
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use super::{
        FixPointSolver, filter_subsets, optimal_valuations_bfs, optimal_valuations_marco, prune,
        strictly_implies,
    };
    use crate::{
        cli::{OptimalValuationsStrategy, default_horn_solver_params},
        logic::{
            Formula, QMap, QSpace, Solution, Sort, UnOp, and, conjunction, eq, ffalse, fnot, ftrue,
            ge, implies, initial_candidate, int_lit, int_var, le, left_hand_side, lt, neq, or,
        },
        program::empty_env,
    };

    fn p_x() -> Formula {
        Formula::Unknown(BTreeMap::new(), "P".to_string())
    }

    fn no_assumptions() -> crate::logic::ExtractAssumptions {
        Box::new(|_: &Formula| BTreeSet::new())
    }

    fn qmap_single(qs: &[Formula], max_count: usize) -> QMap {
        QMap::from([("P".to_string(), QSpace {
            qualifiers: qs.to_vec(),
            max_count,
        })])
    }

    #[test]
    fn preprocess_gfp_disjunctive_antecedent() {
        let solver = FixPointSolver::init_horn_solver(&empty_env(), &default_horn_solver_params());
        let c = ge(int_var("x"), int_lit(0));
        let fml = implies(or(c.clone(), ge(int_var("x"), int_lit(1))), p_x());
        let out = solver.preprocess_constraint(&fml);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], fml);
        let fml2 = implies(or(and(p_x(), c.clone()), ge(int_var("x"), int_lit(1))), c);
        let out2 = solver.preprocess_constraint(&fml2);
        assert_eq!(out2.len(), 2);
        let antecedents: BTreeSet<Formula> = out2.iter().map(left_hand_side).collect();
        assert_eq!(
            antecedents,
            BTreeSet::from([
                and(p_x(), ge(int_var("x"), int_lit(0))),
                ge(int_var("x"), int_lit(1))
            ])
        );
    }

    #[test]
    fn preprocess_lfp_single_unknown_rhs() {
        let mut params = default_horn_solver_params();
        params.is_least_fixpoint = true;
        let solver = FixPointSolver::init_horn_solver(&empty_env(), &params);
        let fml = implies(ge(int_var("x"), int_lit(0)), p_x());
        let out = solver.preprocess_constraint(&fml);
        assert_eq!(out, vec![implies(ge(int_var("x"), int_lit(0)), p_x())]);
    }

    #[test]
    fn horn_apply_solution_instantiates_unknowns() {
        let mut solver =
            FixPointSolver::init_horn_solver(&empty_env(), &default_horn_solver_params());
        let mut sol = Solution::new();
        sol.insert(
            "P".to_string(),
            BTreeSet::from([ge(int_var("x"), int_lit(0))]),
        );
        let fml = implies(ge(int_var("x"), int_lit(0)), p_x());
        let applied = FixPointSolver::horn_apply_solution(&no_assumptions(), &sol, &fml);
        assert_eq!(
            applied,
            implies(ge(int_var("x"), int_lit(0)), ge(int_var("x"), int_lit(0)))
        );
        let fml2 = implies(p_x(), ge(int_var("x"), int_lit(0)));
        let applied2 = FixPointSolver::horn_apply_solution(&no_assumptions(), &sol, &fml2);
        assert_eq!(
            applied2,
            implies(ge(int_var("x"), int_lit(0)), ge(int_var("x"), int_lit(0)))
        );
        assert!(FixPointSolver::is_valid_fml(&mut solver.z3, &applied2));
    }

    #[test]
    fn greatest_fixpoint_small_system() {
        let params = default_horn_solver_params();
        let mut solver = FixPointSolver::init_horn_solver(&empty_env(), &params);
        let qmap = qmap_single(&[ge(int_var("x"), int_lit(0))], 1);
        let c1 = implies(eq(int_var("x"), int_lit(0)), p_x());
        let c2 = implies(p_x(), ge(int_var("x"), int_lit(0)));
        let cands = solver.refine_candidates(&[c1, c2.clone()], &qmap, &no_assumptions(), &[
            initial_candidate(),
        ]);
        assert_eq!(cands.len(), 1);
        let cand = &cands[0];
        assert_eq!(
            cand.solution.get("P"),
            Some(&BTreeSet::from([ge(int_var("x"), int_lit(0))]))
        );
        assert!(cand.invalid_constraints.is_empty());
        assert!(cand.valid_constraints.contains(&c2));
    }

    #[test]
    fn least_fixpoint_small_system() {
        let mut params = default_horn_solver_params();
        params.is_least_fixpoint = true;
        let mut solver = FixPointSolver::init_horn_solver(&empty_env(), &params);
        let qmap = qmap_single(
            &[ge(int_var("x"), int_lit(0)), ge(int_var("x"), int_lit(1))],
            2,
        );
        let c1 = implies(ge(int_var("x"), int_lit(1)), p_x());
        let c2 = implies(ge(int_var("x"), int_lit(0)), p_x());
        let cands =
            solver.refine_candidates(&[c1, c2], &qmap, &no_assumptions(), &[initial_candidate()]);
        assert_eq!(cands.len(), 1);
        let cand = &cands[0];
        assert_eq!(
            cand.solution.get("P"),
            Some(&BTreeSet::from([ge(int_var("x"), int_lit(0))]))
        );
        assert!(cand.invalid_constraints.is_empty());
    }

    #[test]
    fn optimal_valuations_bfs_minimal_subsets() {
        let mut solver =
            FixPointSolver::init_horn_solver(&empty_env(), &default_horn_solver_params());
        let quals = BTreeSet::from([ge(int_var("x"), int_lit(1)), le(int_var("x"), int_lit(-1))]);
        let vals = optimal_valuations_bfs(
            &mut solver.z3,
            2,
            &quals,
            &BTreeSet::new(),
            &ge(int_var("x"), int_lit(0)),
        );
        assert_eq!(vals, vec![BTreeSet::from([ge(int_var("x"), int_lit(1))])]);
    }

    #[test]
    fn optimal_valuations_marco_minimal_subsets() {
        let mut solver =
            FixPointSolver::init_horn_solver(&empty_env(), &default_horn_solver_params());
        let quals = BTreeSet::from([ge(int_var("x"), int_lit(1)), le(int_var("x"), int_lit(-1))]);
        let vals = optimal_valuations_marco(
            &mut solver.z3,
            &quals,
            &BTreeSet::new(),
            &ge(int_var("x"), int_lit(0)),
        );
        assert_eq!(vals, vec![BTreeSet::from([ge(int_var("x"), int_lit(1))])]);
    }

    #[test]
    fn marco_replicate_nil_condition() {
        let mut solver =
            FixPointSolver::init_horn_solver(&empty_env(), &default_horn_solver_params());
        let n = int_var("n");
        let v = int_var("_v");
        let len = |name: String| {
            Formula::Pred(Box::new(Sort::IntS), "len".to_string(), vec![Formula::Var(
                Box::new(Sort::DataS("List".to_string(), vec![Sort::VarS(
                    "a".to_string(),
                )])),
                name,
            )])
        };
        let rhs = eq(len("_v".to_string()), n.clone());
        let lhs: BTreeSet<Formula> = [
            eq(len("_v".to_string()), int_lit(0)),
            ge(n.clone(), int_lit(0)),
        ]
        .into_iter()
        .collect();
        let quals: BTreeSet<Formula> = [
            neq(int_lit(0), n.clone()),
            le(n.clone(), int_lit(0)),
            le(int_lit(0), n.clone()),
        ]
        .into_iter()
        .collect();
        let vals = optimal_valuations_marco(&mut solver.z3, &quals, &lhs, &rhs);
        assert_eq!(vals, vec![BTreeSet::from([le(n, int_lit(0))])]);
    }

    #[test]
    fn marco_recursive_arg_zero() {
        let mut solver =
            FixPointSolver::init_horn_solver(&empty_env(), &default_horn_solver_params());
        let n = int_var("n");
        let v = int_var("_v");
        let c1 = Formula::Unary(UnOp::Not, Box::new(le(n.clone(), int_lit(0))));
        let rhs = and(ge(v.clone(), int_lit(0)), lt(v.clone(), n.clone()));
        let lhs: BTreeSet<Formula> = [c1, eq(v.clone(), int_lit(0)), ge(n.clone(), int_lit(0))]
            .into_iter()
            .collect();
        let quals: BTreeSet<Formula> = [
            neq(int_lit(0), n.clone()),
            le(n.clone(), int_lit(0)),
            le(int_lit(0), n.clone()),
        ]
        .into_iter()
        .collect();
        let vals = optimal_valuations_marco(&mut solver.z3, &quals, &lhs, &rhs);
        assert_eq!(vals, vec![BTreeSet::new()]);
    }

    #[test]
    fn filter_subsets_minimal_satisfying() {
        let out = filter_subsets(&|idxs: &BTreeSet<usize>| idxs.iter().any(|&i| i == 0), 2);
        assert_eq!(out, vec![BTreeSet::from([0])]);
    }

    #[test]
    fn prune_drops_subsumed_reversed_order() {
        let out = prune(
            |x: &BTreeSet<usize>, xs: &[BTreeSet<usize>]| {
                xs.iter().any(|s| s.is_superset(x) && s != x)
            },
            vec![
                BTreeSet::from([1]),
                BTreeSet::from([1, 2]),
                BTreeSet::from([0]),
            ],
        );
        assert_eq!(out, vec![BTreeSet::from([0]), BTreeSet::from([1, 2])]);
    }

    #[test]
    fn strictly_implies_semantics() {
        let mut solver =
            FixPointSolver::init_horn_solver(&empty_env(), &default_horn_solver_params());
        let assumption = ftrue();
        let stronger = BTreeSet::from([ge(int_var("x"), int_lit(1))]);
        let weaker = BTreeSet::from([ge(int_var("x"), int_lit(0))]);
        assert!(strictly_implies(
            &mut solver.z3,
            &assumption,
            &stronger,
            &weaker
        ));
        assert!(!strictly_implies(
            &mut solver.z3,
            &assumption,
            &weaker,
            &stronger
        ));
        assert!(!strictly_implies(
            &mut solver.z3,
            &assumption,
            &weaker,
            &weaker
        ));
    }

    #[test]
    fn refine_matches_marco_and_bfs() {
        let mk = |strategy: OptimalValuationsStrategy| {
            let mut params = default_horn_solver_params();
            params.optimal_valuations_strategy = strategy;
            let mut solver = FixPointSolver::init_horn_solver(&empty_env(), &params);
            let qmap = qmap_single(&[ge(int_var("x"), int_lit(0))], 1);
            let c1 = implies(eq(int_var("x"), int_lit(0)), p_x());
            let c2 = implies(p_x(), ge(int_var("x"), int_lit(0)));
            solver.refine_candidates(&[c1, c2], &qmap, &no_assumptions(), &[initial_candidate()])
        };
        let by_bfs = mk(OptimalValuationsStrategy::BfsValuations);
        let by_marco = mk(OptimalValuationsStrategy::MarcoValuations);
        assert_eq!(by_bfs.len(), 1);
        assert_eq!(by_marco.len(), 1);
        assert_eq!(by_bfs[0].solution, by_marco[0].solution);
    }
}

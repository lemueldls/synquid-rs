use std::{
    collections::{BTreeMap, BTreeSet},
    iter,
};

use hashbrown::{HashMap, HashSet};
use itertools::Itertools;

use crate::{
    logic::{BinOp, Candidate, ExtractAssumptions, Formula, QMap, QSpace, Solution, Valuation},
    program::Environment,
    smt::{init_solver, Z3State},
    solver::fixpoint::{greatest_fix_point, least_fix_point},
    util::{self, Id},
};

/// Strategies for picking the next candidate solution to strengthen
#[derive(Debug, Clone)]
pub enum CandidatePickStrategy {
    FirstCandidate,
    ValidWeakCandidate,
    InitializedWeakCandidate,
}

/// Strategies for picking the next constraint to solve
#[derive(Debug, Clone)]
pub enum ConstraintPickStrategy {
    FirstConstraint,
    SmallSpaceConstraint,
}

/// MUS search strategies
#[derive(Debug, Clone)]
pub enum OptimalValuationsStrategy {
    BFSValuations,
    MarcoValuations,
}

// Parameters of the fix point algorithm
#[derive(Debug)]
pub struct HornSolverParams {
    /// Should redundant qualifiers be removed before solving constraints?
    pub prune_quals: bool,
    /// Should the solver look for the least fixpoint (as opposed to greatest)?
    pub is_least_fixpoint: bool,
    /// How should we find optimal left-hand side valuations?
    pub optimal_valuations_strategy: OptimalValuationsStrategy,
    /// After solving each constraints, remove semantically non-optimal solutions
    pub semantic_prune: bool,
    /// Perform pruning on the LHS-pValuation of as opposed to per-variable valuations
    pub agressive_prune: bool,
    /// How should the next candidate solution to strengthen be picked?
    pub candidate_pick_strategy: CandidatePickStrategy,
    /// How should the next constraint to solve be picked?
    pub constraint_pick_strategy: ConstraintPickStrategy,
    /// How verbose logging is
    pub solver_log_level: usize,
}

// #[repr(transparent)]
// #[derive(Debug)]
// pub struct FixPointSolver(HornSolverParams);
pub type FixPointSolver = HornSolverParams;

// instance MonadSMT s => MonadHorn (FixPointSolver s) where
//   initHornSolver env = do
//     lift (initSolver env)
//     return initialCandidate

//   preprocessConstraint = preprocess

//   checkCandidates = check

//   refineCandidates = refine

//   pruneQualifiers quals = ifM (asks pruneQuals) (pruneQSpace quals) (return quals)

pub fn init_horn_solver(env: Environment, state: &mut Z3State) -> Candidate {
    init_solver(env, state);

    Candidate::default()
}

pub fn preprocess_constraint(fml: Formula, params: &FixPointSolver) -> Vec<Formula> {
    preprocess(fml, params)
}

pub fn check_candidates(
    consistency: bool,
    fmls: Vec<Formula>,
    extract_assumptions: &ExtractAssumptions,
    cands: Vec<Candidate>,
    state: &mut Z3State,
) -> Vec<Candidate> {
    check(consistency, fmls, extract_assumptions, cands, state)
}

pub fn refine_candidates(
    constraints: Vec<Formula>,
    qmap: &QMap,
    extract_assumptions: &ExtractAssumptions,
    cands: Vec<Candidate>,
    state: &mut Z3State,
    params: &FixPointSolver,
) -> Vec<Candidate> {
    refine(constraints, qmap, extract_assumptions, cands, state, params)
}

pub fn prune_qualifiers(quals: QSpace, params: &FixPointSolver, state: &mut Z3State) -> QSpace {
    if params.prune_quals {
        prune_q_space(quals, state)
    } else {
        quals.clone()
    }
}

// initialSolution :: MonadSMT s => QMap -> FixPointSolver s Solution
// initialSolution qmap = ifM (asks isLeastFixpoint) (return $ botSolution qmap) (return $ topSolution qmap)

pub fn initial_solution(qmap: &QMap, params: &FixPointSolver) -> Solution {
    if params.is_least_fixpoint {
        qmap.bot_solution()
    } else {
        qmap.top_solution()
    }
}

// preprocess (Binary Implies lhs rhs) = ifM (asks isLeastFixpoint) (return preprocessLFP) (return preprocessGFP)
//   where
//     preprocessLFP =
//       -- ToDo: split conjuncts
//       let
//         rDisjuncts = Set.fromList $ uDNF rhs
//         (noUnknowns, withUnknowns) = Set.partition (Set.null . unknownsOf) rDisjuncts
//       in if Set.size withUnknowns > 1
//         then error $ unwords ["Least fixpoint solver got a disjunctive right-hand-side:", show rhs]
//         else -- Only one disjuncts with unknowns: split into all conjuncts with unknowns into separate constraints
//           let
//             lhs' = conjunction $ Set.insert lhs (Set.map fnot noUnknowns)
//             rConjuncts = conjunctsOf (disjunction withUnknowns)
//             (conjNoUnknowns, conjWithUnknowns) = Set.partition (Set.null . unknownsOf) rConjuncts
//             rhss = (if Set.null conjNoUnknowns then [] else [conjunction conjNoUnknowns]) ++ Set.toList conjWithUnknowns
//           in map (lhs' |=>|) rhss

//     preprocessGFP = map (|=>| rhs) (uDNF lhs) -- Remove disjunctions of unknowns on the left

// preprocess fml = error $ unwords ["preprocess: encountered ill-formed constraint", show fml]

pub fn preprocess(fml: Formula, params: &FixPointSolver) -> Vec<Formula> {
    match fml {
        Formula::Binary(BinOp::Implies, lhs, rhs) => {
            if params.is_least_fixpoint {
                preprocess_lfp(lhs, rhs)
            } else {
                preprocess_gfp(lhs, rhs)
            }
        }
        _ => panic!("encountered ill-formed constraint: {fml}"),
    }
}

fn preprocess_lfp(lhs: Box<Formula>, rhs: Box<Formula>) -> Vec<Formula> {
    let r_disjuncts = rhs.clone().u_dnf();
    let (no_unknowns, with_unknowns): (BTreeSet<Formula>, BTreeSet<Formula>) = r_disjuncts
        .into_iter()
        .partition(|f| f.unknowns().is_empty());

    if with_unknowns.len() > 1 {
        panic!("Least fixpoint solver got a disjunctive right-hand-side: {rhs}");
    }

    let lhs_prime = Formula::conjunction(
        no_unknowns
            .into_iter()
            .map(|f| !f)
            .chain(iter::once(*lhs.clone()))
            .collect(),
    );

    let r_conjuncts = Formula::disjunction(with_unknowns).conjuncts();
    let (conj_no_unknowns, conj_with_unknowns): (BTreeSet<Formula>, BTreeSet<Formula>) =
        r_conjuncts
            .into_iter()
            .partition(|f| f.unknowns().is_empty());

    let rhss = conj_no_unknowns
        .iter()
        .map(|f| f.clone())
        .chain(conj_with_unknowns.iter().map(|f| f.clone()));

    rhss.map(|rhs| lhs_prime.clone().implies(rhs.clone()))
        .collect()
}

fn preprocess_gfp(lhs: Box<Formula>, rhs: Box<Formula>) -> Vec<Formula> {
    lhs.u_dnf()
        .into_iter()
        .map(|f| f.implies(*rhs.clone()))
        .collect()
}

// -- | 'refine' @constraints quals extractAssumptions cands@ : solve @constraints@ using @quals@ starting from initial candidates @cands@;
// -- use @extractAssumptions@ to extract axiom instantiations from formulas;
// -- if there is no solution, produce an empty list of candidates; otherwise the first candidate in the list is a complete solution
// refine :: MonadSMT s => [Formula] -> QMap -> ExtractAssumptions -> [Candidate] -> FixPointSolver s [Candidate]
// refine constraints quals extractAssumptions cands = do
//     writeLog 3 (vsep [nest 2 $ text "Constraints" $+$ vsep (map pretty constraints), nest 2 $ text "QMap" $+$ pretty quals])
//     let constraints' = filter isNew constraints
//     cands' <- mapM (addConstraints constraints') cands
//     case find (Set.null . invalidConstraints) cands' of
//       Just c -> return $ c : delete c cands'
//       Nothing -> ifM (asks isLeastFixpoint)
//                     (leastFixPoint extractAssumptions cands')
//                     (greatestFixPoint quals extractAssumptions cands')
//   where
//     isNew c = not (c `Set.member` validConstraints (head cands)) && not (c `Set.member` invalidConstraints (head cands))

//     addConstraints constraints (Candidate sol valids invalids label) = do
//       initSol <- initialSolution quals
//       let sol' = Map.union sol initSol -- Add new unknowns (since map-union is left-biased, old solutions are preserved for old unknowns)
//       (valids', invalids') <- partitionM (isValidFml . hornApplySolution extractAssumptions sol') constraints -- Evaluate new constraints
//       return $ Candidate sol' (valids `Set.union` Set.fromList valids') (invalids `Set.union` Set.fromList invalids') label

/// Solve `constraints` using `quals` starting from initial candidates `cands`
/// If there is no solution, produce an empty list of candidates; otherwise the first candidate in the list is a complete solution
pub fn refine(
    constraints: Vec<Formula>,
    qmap: &QMap,
    extract_assumptions: &ExtractAssumptions,
    cands: Vec<Candidate>,
    state: &mut Z3State,
    params: &FixPointSolver,
) -> Vec<Candidate> {
    log::debug!("Constraints: {constraints:?}\nQMap: {qmap:?}");

    let constraints_prime = constraints
        .into_iter()
        .filter(|c| is_new(c, &cands))
        .collect::<Vec<_>>();
    let cands_prime = cands
        .into_iter()
        .map(|c| {
            add_constraints(
                constraints_prime.clone(),
                c,
                qmap,
                extract_assumptions,
                state,
                params,
            )
        })
        .collect::<Vec<_>>();

    match cands_prime
        .iter()
        .find(|c| c.invalid_constraints.is_empty())
        .cloned()
    {
        Some(c) => cands_prime
            .into_iter()
            .filter(|c_prime| *c_prime != c)
            .chain(iter::once(c.clone()))
            .collect(),
        None => {
            if params.is_least_fixpoint {
                least_fix_point(extract_assumptions, cands_prime, params, state)
            } else {
                greatest_fix_point(qmap, extract_assumptions, cands_prime, params, state)
            }
        }
    }
}

fn is_new(c: &Formula, cands: &[Candidate]) -> bool {
    !cands[0].valid_constraints.contains(c) && !cands[0].invalid_constraints.contains(c)
}

fn add_constraints(
    constraints: Vec<Formula>,
    candidate: Candidate,
    qmap: &QMap,
    extract_assumptions: &ExtractAssumptions,
    state: &mut Z3State,
    params: &FixPointSolver,
) -> Candidate {
    let init_sol = initial_solution(qmap, params);
    let sol = Solution::new(
        candidate
            .solution
            .into_iter()
            .chain(init_sol.into_iter())
            .collect(),
    );

    let (valids, invalids): (Vec<Formula>, Vec<Formula>) = constraints.into_iter().partition(|f| {
        is_valid_fml(
            horn_apply_solution(extract_assumptions, &sol, f.clone()),
            state,
        )
    });

    Candidate {
        solution: sol,
        valid_constraints: candidate
            .valid_constraints
            .into_iter()
            .chain(valids.into_iter())
            .collect(),
        invalid_constraints: candidate
            .invalid_constraints
            .into_iter()
            .chain(invalids.into_iter())
            .collect(),
        label: candidate.label.clone(),
    }
}

// -- | 'check' @consistency fmls extractAssumptions cands@ : return those candidates from @cands@ under which all @fmls@ are either valid or satisfiable, depending on @consistency@;
// -- use @extractAssumptions@ to extract axiom instantiations from formulas
// check :: MonadSMT s => Bool -> [Formula] ->  ExtractAssumptions -> [Candidate] -> FixPointSolver s [Candidate]
// check consistency fmls extractAssumptions cands = do
//     writeLog 3 (vsep [
//       nest 2 $ (if consistency then text "Checking consistency" else text "Checking validity") $+$ vsep (map pretty fmls),
//       nest 2 $ text "Candidates" <+> parens (pretty $ length cands) $+$ (vsep $ map pretty cands)])
//     cands' <- filterM checkCand cands
//     writeLog 3 (nest 2 $ text "Remaining Candidates" <+> parens (pretty $ length cands') $+$ (vsep $ map pretty cands'))
//     return cands'
//   where
//     apply sol fml = let fml' = applySolution sol fml in fml' |&| conjunction (extractAssumptions fml')
//     checkCand (Candidate sol valids invalids label) = if consistency
//       then allM isSatFml (map (apply sol) fmls)
//       else allM isValidFml (map (hornApplySolution extractAssumptions sol) fmls)

/// Return those candidates from `cands` under which all `fmls` are either valid or satisfiable, depending on `consistency`
pub fn check(
    consistency: bool,
    fmls: Vec<Formula>,
    extract_assumptions: &ExtractAssumptions,
    cands: Vec<Candidate>,
    state: &mut Z3State,
) -> Vec<Candidate> {
    // log::debug!(
    //     "{if consistency { 'Checking consistency' } else { 'Checking validity' }} {fmls}"
    // );

    let cands_prime = cands
        .into_iter()
        .filter(|c| {
            check_cand(
                extract_assumptions,
                consistency,
                &c.solution,
                fmls.clone(),
                state,
            )
        })
        .collect::<Vec<_>>();

    log::debug!(
        "Remaining Candidates: {} {cands_prime:?}",
        cands_prime.len()
    );

    cands_prime
}

fn apply(extract_assumptions: &ExtractAssumptions, sol: &Solution, fml: Formula) -> Formula {
    let fml_prime = fml.apply_solution(sol);

    fml_prime
        .clone()
        .and(Formula::conjunction(extract_assumptions.as_ref()(
            fml_prime,
        )))
}

fn check_cand(
    extract_assumptions: &ExtractAssumptions,
    consistency: bool,
    sol: &Solution,
    fmls: Vec<Formula>,
    state: &mut Z3State,
) -> bool {
    if consistency {
        fmls.into_iter()
            .all(|f| is_sat_fml(apply(extract_assumptions, sol, f.clone()), state))
    } else {
        fmls.into_iter().all(|f| {
            is_valid_fml(
                horn_apply_solution(extract_assumptions, sol, f.clone()),
                state,
            )
        })
    }
}

// hornApplySolution extractAssumptions sol (Binary Implies lhs rhs) =
//     let
//      lhs' = applySolution sol lhs
//      rhs' = applySolution sol rhs
//      assumptions = extractAssumptions lhs' `Set.union` extractAssumptions rhs'
//     in Binary Implies (lhs' `andClean` conjunction assumptions) rhs'

pub fn horn_apply_solution(
    extract_assumptions: &ExtractAssumptions,
    sol: &Solution,
    fml: Formula,
) -> Formula {
    match fml {
        Formula::Binary(BinOp::Implies, lhs, rhs) => {
            let lhs = lhs.apply_solution(sol);
            let rhs = rhs.apply_solution(sol);

            let mut assumptions = extract_assumptions.as_ref()(lhs.clone());
            assumptions.extend(extract_assumptions.as_ref()(rhs.clone()));

            Formula::Binary(
                BinOp::Implies,
                Box::new(Formula::and_clean(lhs, Formula::conjunction(assumptions))),
                Box::new(rhs),
            )
        }
        _ => panic!("expected implication"),
    }
}

// -- | 'strengthen' @qmap fml sol@: all minimal strengthenings of @sol@ using qualifiers from @qmap@ that make @fml@ valid;
// -- | @fml@ must have the form "/\ u_i ==> const".
// strengthen :: MonadSMT s => QMap -> ExtractAssumptions -> Formula -> Solution -> FixPointSolver s [Solution]
// strengthen qmap extractAssumptions fml@(Binary Implies lhs rhs) sol = do
//     let n = maxValSize qmap sol unknowns
//     writeLog 3 (text "Instantiated axioms:" $+$ commaSep (map pretty $ Set.toList assumptions))
//     let allAssumptions = usedLhsQuals `Set.union` assumptions
//     lhsValuations <- optimalValuations n (lhsQuals Set.\\ usedLhsQuals) allAssumptions rhs -- all minimal valid valuations of the whole antecedent
//     writeLog 3 (text "Optimal valuations:" $+$ vsep (map pretty lhsValuations))
//     let splitVals vals = nub $ concatMap splitLhsValuation vals
//     pruned <- ifM (asks semanticPrune)
//       (ifM (asks agressivePrune)
//         (do
//           let pruneAssumptions = if rhs == ffalse then Set.empty else allAssumptions -- TODO: is this dangerous??? the result might not cover the pruned alternatives in a different context!
//           valuations' <- pruneValuations (conjunction pruneAssumptions) lhsValuations
//           writeLog 3 (text "Pruned valuations:" $+$ vsep (map pretty valuations'))
//           return $ splitVals valuations')   -- Prune LHS valuations and then return the splits of only optimal valuations
//         (pruneSolutions unknownsList (splitVals lhsValuations)))           -- Prune per-variable
//       (return $ splitVals lhsValuations)
//     writeLog 3 (text "Diffs:" <+> parens (pretty $ length pruned) $+$ vsep (map pretty pruned))
//     return pruned
//   where
//     unknowns = unknownsOf lhs
//     knownConjuncts = conjunctsOf lhs Set.\\ unknowns
//     unknownsList = Set.toList unknowns
//     lhsQuals = setConcatMap (Set.fromList . lookupQualsSubst qmap) unknowns   -- available qualifiers for the whole antecedent
//     usedLhsQuals = setConcatMap (valuation sol) unknowns `Set.union` knownConjuncts      -- already used qualifiers for the whole antecedent
//     rhsVars = Set.map varName $ varsOf rhs
//     assumptions = setConcatMap extractAssumptions lhsQuals `Set.union`
//                   setConcatMap extractAssumptions knownConjuncts `Set.union`
//                   extractAssumptions rhs

//       -- | All possible additional valuations of @u@ that are subsets of $lhsVal@.
//     singleUnknownCandidates lhsVal u = let
//           qs = lookupQualsSubst qmap u
//           max = lookupQuals qmap maxCount u
//           used = valuation sol u
//           n = Set.size used
//       in Set.toList $ boundedSubsets (max - n) $ (Set.fromList qs Set.\\ used) `Set.intersection` lhsVal

//       -- | All valid partitions of @lhsVal@ into solutions for multiple unknowns.
//     splitLhsValuation :: Valuation -> [Solution]
//     splitLhsValuation lhsVal = do
//       unknownsVal <- mapM (singleUnknownCandidates lhsVal) unknownsList
//       let isValidsplit ss s = Set.unions ss == s && sum (map Set.size ss) == Set.size s
//       guard $ isValidsplit unknownsVal lhsVal
//       Map.fromListWith Set.union <$> zipWithM unsubst unknownsList unknownsVal

//     -- | Given an unknown @[subst]u@ and its valuation @val@, get all possible valuations of @u@
//     unsubst :: Formula -> Set Formula -> [(Id, Set Formula)]
//     unsubst u@(Unknown s name) val = do
//       option <- mapM (unsubstQual u) (Set.toList val)
//       return (name, Set.fromList option)

//     unsubstQual :: Formula -> Formula -> [Formula]
//     unsubstQual u@(Unknown s name) qual = [q | q <- lookupQuals qmap qualifiers u, substitute s q == qual]

/// All minimal strengthenings of `sol` using qualifiers from `qmap` that make `fml` valid
/// `fml` must have the form "/\ u_i ==> const"
pub fn strengthen(
    qmap: &QMap,
    extract_assumptions: &ExtractAssumptions,
    fml: Formula,
    sol: &Solution,
    state: &mut Z3State,
    params: &FixPointSolver,
) -> Vec<Solution> {
    match fml {
        Formula::Binary(BinOp::Implies, lhs, rhs) => {
            let unknowns = lhs.unknowns();
            let known_conjuncts = lhs
                .clone()
                .conjuncts()
                .into_iter()
                .filter(|f| !unknowns.contains(f))
                .collect::<BTreeSet<_>>();
            let unknowns_set = unknowns
                .iter()
                .map(|fml| (*fml).clone())
                .collect::<BTreeSet<_>>();
            let lhs_quals = unknowns
                .iter()
                .flat_map(|u| qmap.lookup_quals_subst(u))
                .collect::<HashSet<_>>();
            let used_lhs_quals = unknowns
                .iter()
                .flat_map(|u| sol.valuation(u))
                .chain(known_conjuncts.iter().cloned())
                .collect::<HashSet<_>>();
            // let rhs_vars = rhs
            //     .vars()
            //     .iter()
            //     .map(|v| v.var_name().clone())
            //     .collect::<HashSet<_>>();
            let assumptions = unknowns
                .iter()
                .flat_map(|u| extract_assumptions.as_ref()((*u).clone()))
                .chain(
                    known_conjuncts
                        .iter()
                        .flat_map(|f| extract_assumptions.as_ref()(f.clone())),
                )
                .chain(extract_assumptions.as_ref()(*rhs.clone()))
                .collect::<HashSet<_>>();

            let n = max_val_size(qmap, sol, &unknowns);
            log::info!("Instantiated axioms: {assumptions:?}");

            let all_assumptions = used_lhs_quals
                .union(&assumptions)
                .cloned()
                .collect::<BTreeSet<_>>();
            let lhs_valuations = optimal_valuations(
                n,
                lhs_quals
                    .difference(&used_lhs_quals)
                    .cloned()
                    .collect::<HashSet<_>>(),
                &all_assumptions,
                *rhs.clone(),
                state,
                params,
            );
            log::info!("Optimal valuations: {lhs_valuations:?}");

            let split_vals = |vals: Vec<Valuation>| -> Vec<Solution> {
                vals.into_iter()
                    .flat_map(|val| split_lhs_valuation(qmap, sol, &unknowns_set, &val))
                    .collect()
            };

            let pruned = if params.semantic_prune {
                if params.agressive_prune {
                    let prune_assumptions = if *rhs == Formula::FALSE {
                        BTreeSet::new()
                    } else {
                        all_assumptions
                    };

                    let valuations_prime = prune_valuations(
                        Formula::conjunction(prune_assumptions),
                        lhs_valuations,
                        state,
                    );
                    log::info!("Pruned valuations: {valuations_prime:?}");
                    split_vals(valuations_prime)
                } else {
                    prune_solutions(unknowns_set.clone(), split_vals(lhs_valuations), state)
                }
            } else {
                split_vals(lhs_valuations)
            };

            log::info!("Diffs: {pruned:?}");

            pruned
        }
        _ => panic!("expected implication"),
    }
}

/// All possible additional valuations of `u` that are subsets of `lhs_val`
pub fn single_unknown_candidates(
    qmap: &QMap,
    sol: &Solution,
    lhs_val: &Valuation,
    u: &Formula,
) -> HashSet<BTreeSet<Formula>> {
    let qs = qmap.lookup_quals_subst(u);
    let max = qmap.lookup_quals(|q_space| q_space.max_count, u);
    let used = sol.valuation(u);
    let n = used.as_ref().len();

    util::bounded_subsets(
        max - n,
        &qs.into_iter()
            .filter(|q| !used.as_ref().contains(q) && lhs_val.as_ref().contains(q))
            .collect(),
    )
}

/// All valid partitions of `lhs_val` into solutions for multiple unknowns
fn split_lhs_valuation(
    qmap: &QMap,
    sol: &Solution,
    unknowns_list: &BTreeSet<Formula>,
    lhs_val: &Valuation,
) -> Vec<Solution> {
    let unknowns_val = unknowns_list
        .iter()
        .map(|u| single_unknown_candidates(qmap, sol, lhs_val, u))
        .collect::<Vec<_>>();
    let is_valid_split = |ss: &HashSet<BTreeSet<Formula>>, s: &Valuation| {
        ss.iter()
            .all(|ss| ss.iter().all(|q| s.as_ref().contains(q)))
            && ss.iter().map(|ss| ss.len()).sum::<usize>() == s.as_ref().len()
    };

    unknowns_val
        .iter()
        .filter(|ss| is_valid_split(ss, lhs_val))
        .map(|ss| {
            Solution::new(
                unknowns_list
                    .iter()
                    .zip(ss.iter())
                    .flat_map(|(u, q)| unsubst(qmap, u, q))
                    .collect(),
            )
        })
        .collect()
}

/// Given an unknown `u` and its valuation `val`, get all possible valuations of `u`
fn unsubst(qmap: &QMap, u: &Formula, val: &BTreeSet<Formula>) -> Vec<(Id, Valuation)> {
    match u {
        Formula::Unknown(s, name) => {
            let option = val
                .iter()
                .map(|q| unsubst_qual(qmap, u, q))
                .collect::<Vec<_>>();

            option.into_iter().map(|q| (name.clone(), q)).collect()
        }
        _ => panic!("expected unknown"),
    }
}

fn unsubst_qual(qmap: &QMap, u: &Formula, qual: &Formula) -> Valuation {
    match u {
        Formula::Unknown(s, name) => Valuation::new(
            qmap.lookup_quals(|q_space| q_space.qualifiers.clone(), u)
                .into_iter()
                .filter(|q| q.clone().substitute(&s) == *qual)
                .collect(),
        ),
        _ => panic!("expected unknown"),
    }
}

// -- | 'maxValSize' @qmap sol unknowns@: Upper bound on the size of valuations of a conjunction of @unknowns@ when strengthening @sol@
// maxValSize :: QMap -> Solution -> Set Formula -> Int
// maxValSize qmap sol unknowns = let
//     usedQuals = setConcatMap (valuation sol) unknowns
//   in Set.foldl (\n u -> n + lookupQuals qmap maxCount u) 0 unknowns - Set.size usedQuals

/// Upper bound on the size of valuations of a conjunction of `unknowns` when strengthening `sol`
pub fn max_val_size(qmap: &QMap, sol: &Solution, unknowns: &HashSet<&Formula>) -> usize {
    let used_quals = unknowns
        .iter()
        .flat_map(|u| sol.valuation(u))
        .collect::<HashSet<Formula>>();

    unknowns
        .iter()
        .map(|u| qmap.lookup_quals(|q_space| q_space.max_count, u))
        .sum::<usize>()
        - used_quals.len()
}

// optimalValuations :: MonadSMT s => Int -> Set Formula -> Set Formula -> Formula -> FixPointSolver s [Valuation]
// optimalValuations maxSize quals lhs rhs = do
//   strategy <- asks optimalValuationsStrategy
//   case strategy of
//     BFSValuations -> optimalValuationsBFS maxSize quals lhs rhs
//     MarcoValuations -> optimalValuationsMarco quals lhs rhs

pub fn optimal_valuations(
    max_size: usize,
    quals: HashSet<Formula>,
    lhs: &BTreeSet<Formula>,
    rhs: Formula,
    state: &mut Z3State,
    params: &FixPointSolver,
) -> Vec<Valuation> {
    match params.optimal_valuations_strategy {
        OptimalValuationsStrategy::BFSValuations => {
            optimal_valuations_bfs(max_size, quals, lhs, rhs, state)
        }
        OptimalValuationsStrategy::MarcoValuations => {
            optimal_valuations_macro(quals, lhs.clone(), rhs, state)
        }
    }
}

// -- | 'optimalValuations' @quals check@: all smallest subsets of @quals@ for which @check@ returns a solution.
// optimalValuationsBFS :: MonadSMT s => Int -> Set Formula -> Set Formula -> Formula -> FixPointSolver s [Valuation]
// optimalValuationsBFS maxSize quals lhs rhs = map qualsAt <$> filterSubsets (check . qualsAt) (length qualsList)
//   where
//     qualsList = Set.toList quals
//     qualsAt = Set.map (qualsList !!)
//     check val = let
//                   n = Set.size val
//                   lhs' = conjunction lhs `andClean` conjunction val
//       in if 1 <= n && n <= maxSize
//           then isValidFml $ lhs' |=>| rhs
//           else return False

/// All smallest subsets of `quals` for which `check` returns a solution
pub fn optimal_valuations_bfs(
    max_size: usize,
    quals: HashSet<Formula>,
    lhs: &BTreeSet<Formula>,
    rhs: Formula,
    state: &mut Z3State,
) -> Vec<Valuation> {
    let quals_list = quals.into_iter().collect::<Vec<_>>();
    let quals_at = |val: BTreeSet<usize>| {
        val.into_iter()
            .map(|i| quals_list[i].clone())
            .collect::<BTreeSet<_>>()
    };

    let mut check = |val: BTreeSet<Formula>| {
        let n = val.len();
        let lhs_prime =
            Formula::and_clean(Formula::conjunction(lhs.clone()), Formula::conjunction(val));

        if 1 <= n && n <= max_size {
            is_valid_fml(lhs_prime.implies(rhs.clone()), state)
        } else {
            false
        }
    };

    filter_subsets(|val| check(quals_at(val)), quals_list.len())
        .into_iter()
        .map(|val| Valuation::new(quals_at(val)))
        .collect()
}

// optimalValuationsMarco :: MonadSMT s => Set Formula -> Set Formula -> Formula -> FixPointSolver s [Valuation]
// optimalValuationsMarco quals lhs rhs = map Set.fromList <$> lift (allUnsatCores assumption mustHave qualsList)
//   where
//     qualsList = Set.toList $ Set.filter (\q -> not $ q `Set.member` lhs || fnot q `Set.member` lhs) quals
//     fixedLhs = conjunction lhs
//     fixedRhs = fnot rhs
//     (assumption, mustHave) = if rhs == ffalse then (ftrue, fixedLhs) else (fixedLhs, fixedRhs) -- When RHS is literally false, then inconsistent LHSs are acceptable

pub fn optimal_valuations_macro(
    quals: HashSet<Formula>,
    lhs: BTreeSet<Formula>,
    rhs: Formula,
    state: &mut Z3State,
) -> Vec<Valuation> {
    let quals_list = quals
        .into_iter()
        .filter(|q| !lhs.contains(q) && !lhs.contains(&!(*q).clone()))
        .collect::<BTreeSet<_>>();

    let fixed_lhs = Formula::conjunction(lhs);
    let (assumption, must_have) = if rhs == Formula::FALSE {
        (Formula::TRUE, fixed_lhs)
    } else {
        (fixed_lhs, !rhs)
    };

    state.get_all_muss(assumption, must_have, quals_list)
}

// -- | 'filterSubsets' @check n@: all minimal subsets of indexes from [0..@n@) that satisfy @check@,
// -- where @check@ is monotone (if a set satisfies @check@, then every superset also satisfies @check@);
// -- performs breadth-first search.
// filterSubsets :: MonadSMT s => (Set Int -> FixPointSolver s Bool) -> Int -> FixPointSolver s [Set Int]
// filterSubsets check n = go [] [Set.empty]
//   where
//     go solutions candidates = if null candidates
//       then return solutions
//       else let new = filter (\c -> not $ any (`Set.isSubsetOf` c) solutions) candidates
//         in do
//           results <- zip new <$> mapM check new
//           let (valids, invalids) = partition snd results
//           go (solutions ++ map fst valids) (concatMap children (map fst invalids))
//     children idxs = let lower = if Set.null idxs then 0 else Set.findMax idxs + 1
//       in map (`Set.insert` idxs) [lower..(n - 1)]

/// All minimal subsets of indexes from [0..`n`) that satisfy `check`
/// where `check` is monotone (if a set satisfies `check`, then every superset also satisfies `check`)
/// performs breadth-first search
pub fn filter_subsets(
    check: impl FnMut(BTreeSet<usize>) -> bool,
    n: usize,
) -> Vec<BTreeSet<usize>> {
    fn go(
        mut check: impl FnMut(BTreeSet<usize>) -> bool,
        n: usize,
        solutions: Vec<BTreeSet<usize>>,
        candidates: Vec<BTreeSet<usize>>,
    ) -> Vec<BTreeSet<usize>> {
        if candidates.is_empty() {
            return solutions;
        }

        let new = candidates
            .into_iter()
            .filter(|c| !solutions.iter().any(|s| c.is_subset(s)))
            .collect::<Vec<_>>();

        let results = new
            .into_iter()
            .map(|c| (c.clone(), check(c)))
            .collect::<Vec<_>>();
        let (valids, invalids): (Vec<_>, Vec<_>) =
            results.into_iter().partition(|(_, valid)| *valid);

        go(
            check,
            n,
            solutions
                .into_iter()
                .chain(valids.into_iter().map(|(idxs, _)| idxs))
                .collect(),
            invalids
                .into_iter()
                .flat_map(|(idxs, _)| {
                    let lower = if idxs.is_empty() {
                        0
                    } else {
                        *idxs.iter().max().unwrap() + 1
                    };

                    (lower..n)
                        .map(|i| {
                            let mut idxs = idxs.clone();
                            idxs.insert(i);

                            idxs
                        })
                        .collect::<Vec<_>>()
                })
                .collect(),
        )
    }

    go(check, n, vec![], vec![BTreeSet::new()])
}

// -- | 'weaken' @fml sol@: a minimal weakening of @sol@ that make @fml@ valid;
// -- | @fml@ must have the form "const ==> const && /\ Ui" or "const ==> Ui".
// weaken :: MonadSMT s => Formula -> Solution -> FixPointSolver s (Maybe Solution)
// weaken (Binary Implies lhs (Unknown subst u)) sol = do
//   let quals = Set.toList (sol Map.! u)
//   quals' <- filterM (\q -> isValidFml (Binary Implies lhs (substitute subst q))) quals
//   writeLog 3 (text "Weakened" <+> text u <+> text "to" <+> pretty quals')
//   return (Just $ Map.insert u (Set.fromList quals') sol)
// weaken (Binary Implies lhs _) sol = return Nothing

/// A minimal weakening of `sol` that make `fml` valid;
/// `fml` must have the form "const ==> const && /\ Ui" or "const ==> Ui".
pub fn weaken(fml: Formula, mut sol: Solution, state: &mut Z3State) -> Option<Solution> {
    match fml {
        Formula::Binary(BinOp::Implies, lhs, rhs) => match *rhs {
            Formula::Unknown(subst, u) => {
                let quals = sol.as_mut().get_mut(&u).unwrap().as_mut();

                *quals = quals
                    .iter()
                    .filter(|q| {
                        is_valid_fml(lhs.clone().implies((*q).clone().substitute(&subst)), state)
                    })
                    .cloned()
                    .collect();

                log::info!("Weakened {u} to {quals:?}");

                Some(sol)
            }
            _ => None,
        },
        _ => panic!("expected Binary Implies"),
    }
}

// -- | 'pruneSolutions' @sols@: eliminate from @sols@ all solutions that are semantically stronger on all unknowns than another solution in @sols@
// pruneSolutions :: MonadSMT s => [Formula] -> [Solution] -> FixPointSolver s [Solution]
// pruneSolutions unknowns solutions =
//   let isSubsumed sol = anyM (\s -> allM (\u -> isValidFml $ (conjunction $ valuation sol u) |=>| (conjunction $ valuation s u)) unknowns)
//   in prune isSubsumed solutions

/// Eliminate from `sols` all solutions that are semantically stronger on all unknowns than another solution in `sols`
pub fn prune_solutions(
    unknowns: BTreeSet<Formula>,
    solutions: Vec<Solution>,
    state: &mut Z3State,
) -> Vec<Solution> {
    let is_subsumed = |sol: &Solution, solutions: &[Solution]| {
        unknowns.iter().any(|u| {
            solutions.iter().all(|s| {
                is_valid_fml(
                    Formula::conjunction(sol.valuation(u).into())
                        .implies(Formula::conjunction(s.valuation(u).into())),
                    state,
                )
            })
        })
    };

    prune(is_subsumed, solutions)
}

// -- | 'pruneValuations' @vals@: eliminate from @vals@ all valuations that are semantically stronger than another pValuation in @vals@
// pruneValuations :: MonadSMT s => Formula -> [Valuation] -> FixPointSolver s [Valuation]
// pruneValuations assumption vals =
//   let
//       strictlyImplies ls rs = do
//         let l = conjunction ls
//         let r = conjunction rs
//         res1 <- isValidFml $ (assumption |&| l) |=>| r
//         res2 <- isValidFml $ (assumption |&| r) |=>| l
//         return $ (res1 && (not res2 || (Set.size ls > Set.size rs)))
//       isSubsumed val = anyM (\v -> strictlyImplies val v)
//   in prune isSubsumed vals

/// Eliminate from `vals` all valuations that are semantically stronger than another pValuation in `vals`
pub fn prune_valuations(
    assumption: Formula,
    vals: Vec<Valuation>,
    state: &mut Z3State,
) -> Vec<Valuation> {
    let mut strictly_implies = |ls: Valuation, rs: Valuation| {
        let ls: BTreeSet<Formula> = ls.into();
        let ls_len = ls.len();
        let l = Formula::conjunction(ls);

        let rs: BTreeSet<Formula> = rs.into();
        let rs_len = rs.len();
        let r = Formula::conjunction(rs);

        let res1 = is_valid_fml(
            (assumption.clone().and(l.clone())).implies(r.clone()),
            state,
        );
        let res2 = is_valid_fml(
            (assumption.clone().and(r.clone())).implies(l.clone()),
            state,
        );

        res1 && (!res2 || ls_len > rs_len)
    };

    let is_subsumed = |val: &Valuation, vals: &[Valuation]| {
        vals.iter()
            .any(|v| strictly_implies(val.clone(), v.clone()))
    };

    prune(is_subsumed, vals)
}

// -- | 'pruneQualifiers' @quals@: eliminate logical duplicates from @quals@
// pruneQSpace :: MonadSMT s => QSpace -> FixPointSolver s QSpace
// pruneQSpace qSpace = let isSubsumed qual = anyM (\q -> isValidFml $ qual |<=>| q)
//   in do
//     quals' <- filterM (\q -> ifM (isValidFml q) (return False) (not <$> isValidFml (fnot q))) (qSpace ^. qualifiers)
//     quals <- prune isSubsumed quals'
//     return $ set qualifiers quals qSpace

/// Eliminate logical duplicates from `quals`
pub fn prune_q_space(q_space: QSpace, state: &mut Z3State) -> QSpace {
    let quals_prime = q_space
        .qualifiers
        .iter()
        .filter(|q| {
            if is_valid_fml((*q).clone(), state) {
                false
            } else {
                !is_valid_fml(!(*q).clone(), state)
            }
        })
        .cloned()
        .collect();

    let is_subsumed = |qual: &Formula, quals: &[Formula]| {
        quals
            .iter()
            .any(|q| is_valid_fml(qual.clone().iff(q.clone()), state))
    };

    let quals = prune(is_subsumed, quals_prime);

    QSpace {
        qualifiers: quals,
        ..q_space
    }
}

// -- | 'prune' @isSubsumed xs@ : prune all elements of @xs@ subsumed by another element according to @isSubsumed@
// prune :: MonadSMT s => (a -> [a] -> FixPointSolver s Bool) -> [a] -> FixPointSolver s [a]
// prune _ [] = return []
// prune isSubsumed (x:xs) = prune' [] x xs
//   where
//     prune' lefts x [] = ifM (isSubsumed x lefts) (return lefts) (return $ x:lefts)
//     prune' lefts x rights@(y:ys) = ifM (isSubsumed x (lefts ++ rights)) (prune' lefts y ys) (prune' (lefts ++ [x]) y ys)

/// Prune all elements of `xs` subsumed by another element according to `isSubsumed`
pub fn prune<T, F: FnMut(&T, &[T]) -> bool>(mut is_subsumed: F, xs: Vec<T>) -> Vec<T> {
    let mut lefts = Vec::new();

    for x in xs {
        if is_subsumed(&x, &lefts) {
            lefts.push(x);
        }
    }

    lefts
}

// -- | 'isValid' @fml@: is @fml@ valid (free variables are implicitly universally quantified)?
// isValidFml :: MonadSMT s => Formula -> FixPointSolver s Bool
// isValidFml fml = not <$> lift (isSat $ fnot fml)

/// Is `fml` valid (free variables are implicitly universally quantified)?
pub fn is_valid_fml(fml: Formula, state: &mut Z3State) -> bool {
    !state.is_sat(&!fml)
}

// -- | 'isSat' @fml@: is @fml@ satisfiable (free variables are implicitly existentially quantified)?
// isSatFml :: MonadSMT s => Formula -> FixPointSolver s Bool
// isSatFml = lift . isSat

/// Is `fml` satisfiable (free variables are implicitly existentially quantified)?
pub fn is_sat_fml(fml: Formula, state: &mut Z3State) -> bool {
    state.is_sat(&fml)
}

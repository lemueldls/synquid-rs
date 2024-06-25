use std::collections::BTreeSet;

use hashbrown::HashSet;

use crate::{
    logic::{BinOp, Candidate, ExtractAssumptions, Formula, QMap, QSpace, Solution, Valuation},
    smt::Z3State,
};

/// Strategies for picking the next candidate solution to strengthen
#[derive(Debug)]
pub enum CandidatePickStrategy {
    FirstCandidate,
    ValidWeakCandidate,
    InitializedWeakCandidate,
}

/// Strategies for picking the next constraint to solve
#[derive(Debug)]
pub enum ConstraintPickStrategy {
    FirstConstraint,
    SmallSpaceConstraint,
}

/// MUS search strategies
#[derive(Debug)]
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
            .chain(std::iter::once(*lhs.clone()))
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

// // -- | 'maxValSize' @qmap sol unknowns@: Upper bound on the size of valuations of a conjunction of @unknowns@ when strengthening @sol@
// // maxValSize :: QMap -> Solution -> Set Formula -> Int
// // maxValSize qmap sol unknowns = let
// //     usedQuals = setConcatMap (valuation sol) unknowns
// //   in Set.foldl (\n u -> n + lookupQuals qmap maxCount u) 0 unknowns - Set.size usedQuals

// /// Upper bound on the size of valuations of a conjunction of `unknowns` when strengthening `sol`
// pub fn max_val_size(
//     quals: &QMap,
//     sol: &Solution,
//     unknowns: &BTreeSet<Formula>,
//     state: &mut Z3State,
// ) -> usize {
//     todo!()
// }

// // pickConstraint (Candidate sol valids invalids _) strategy = case strategy of
// //   FirstConstraint -> return $ Set.findMin invalids
// //   SmallSpaceConstraint -> do
// //     let spaceSize fml = maxValSize quals sol (unknownsOf (leftHandSide fml))
// //     return $ minimumBy (\x y -> compare (spaceSize x) (spaceSize y)) (Set.toList invalids)

// fn pick_constraint(
//     candidate: &Candidate,
//     strategy: ConstraintPickStrategy,
//     state: &mut Z3State,
// ) -> Formula {
//     match strategy {
//         ConstraintPickStrategy::FirstConstraint => {
//             candidate.invalid_constraints.iter().next().unwrap().clone()
//         }
//         ConstraintPickStrategy::SmallSpaceConstraint => {
//             let space_size = |fml: &Formula| {
//                 let lhs = fml.left_hand_side();
//                 let unknowns = lhs.unknowns();
//                 let quals = candidate.solution.valuation(&lhs);
//                 max_val_size(&quals, &candidate.solution, &unknowns, state)
//             };

//             candidate
//                 .invalid_constraints
//                 .iter()
//                 .min_by(|x, y| space_size(x).cmp(&space_size(y)))
//                 .unwrap()
//                 .clone()
//         }
//     }
// }

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
                // let quals = sol.as_ref().get(&u).unwrap();
                // let quals_prime = quals
                //     .as_ref()
                //     .iter()
                //     .filter(|q| {
                //         is_valid_fml(lhs.clone().implies((*q).clone().substitute(&subst)), state)
                //     })
                //     .cloned()
                //     .collect();

                // sol.as_mut().insert(u, Valuation::new(quals_prime));

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
    unknowns: Vec<Formula>,
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

/// Is `fml` valid (free variables are implicitly universally quantified)?
pub fn is_valid_fml(fml: Formula, state: &mut Z3State) -> bool {
    !crate::smt::is_sat(&!fml, state)
}

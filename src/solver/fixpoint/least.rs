use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    iter,
};

use hashbrown::{HashMap, HashSet};
use itertools::Itertools;
use owo_colors::OwoColorize;

use crate::{
    logic::{BinOp, Candidate, ExtractAssumptions, Formula, QMap, QSpace, Solution, Valuation},
    smt::Z3State,
    solver::horn::{
        check, filter_subsets, horn_apply_solution, initial_solution, is_sat_fml, is_valid_fml,
        max_val_size, optimal_valuations, optimal_valuations_bfs, optimal_valuations_macro,
        preprocess, prune, prune_q_space, prune_solutions, prune_valuations, refine, strengthen,
        weaken, CandidatePickStrategy, ConstraintPickStrategy, FixPointSolver, HornSolverParams,
        OptimalValuationsStrategy,
    },
    util::{self, Id},
};

// -- | 'leastFixPoint' @constraints@: strongest solution for a system of second-order constraints @constraints@.
// leastFixPoint :: MonadSMT s => ExtractAssumptions -> [Candidate] -> FixPointSolver s [Candidate]
// leastFixPoint _ [] = return []
// leastFixPoint extractAssumptions (cand@(Candidate sol _ _ _):rest) = do
//     fml <- asks constraintPickStrategy >>= pickConstraint cand
//     let (Binary Implies lhs rhs) = fml
//     let lhs' = applySolution sol lhs
//     let assumptions = extractAssumptions lhs' `Set.union` extractAssumptions (applySolution sol rhs)

//     let modifiedConstraint = Binary Implies (conjunction $ Set.insert lhs' assumptions) rhs

//     debugOutput cand fml modifiedConstraint
//     solMb' <- weaken modifiedConstraint sol
//     case solMb' of
//       Nothing -> do
//                   writeLog 3 (text "All constraints:" $+$ vsep (map pretty (Set.toList $ validConstraints cand `Set.union` invalidConstraints cand)))
//                   leastFixPoint extractAssumptions rest -- No way to weaken this candidate, see if there are more
//       Just sol' -> do
//                       cand' <- updateCandidate fml cand sol'
//                       if (Set.null . invalidConstraints) cand'
//                         then return $ cand' : rest -- Solution found
//                         else leastFixPoint extractAssumptions (cand' : rest)

//   where
//     -- | Re-evaluate affected clauses in @valids@ and @otherInvalids@ after solution has been strengthened from @sol@ to @sol'@ in order to fix @fml@
//     updateCandidate fml (Candidate sol valids invalids label) sol' = do
//       -- let modifiedUnknowns = Map.keysSet $ Map.differenceWith (\v1 v2 -> if v1 == v2 then Nothing else Just v2) sol sol'
//       let modifiedUnknowns = posUnknowns $ rightHandSide fml
//       let (unaffectedValids, affectedValids) = Set.partition (\fml -> negUnknowns fml `disjoint` modifiedUnknowns) (Set.insert fml valids) -- fml should be re-evaluated if it happens to have the same unknowns also on the right
//       let (unaffectedInvalids, affectedInvalids) = Set.partition (\fml -> posUnknowns fml `disjoint` modifiedUnknowns) (Set.delete fml invalids)
//       (newValids, newInvalids) <- setPartitionM (isValidFml . hornApplySolution extractAssumptions sol') $ affectedValids `Set.union` affectedInvalids
//       return $ Candidate sol' (unaffectedValids `Set.union` newValids) (unaffectedInvalids `Set.union` newInvalids) label

//     pickConstraint (Candidate sol valids invalids _) strategy = case strategy of
//       FirstConstraint -> return $ Set.findMin invalids
//       SmallSpaceConstraint -> do
//         let spaceSize fml = Set.size (unknownsOf (rightHandSide fml))
//         return $ minimumBy (\x y -> compare (spaceSize x) (spaceSize y)) (Set.toList invalids)

/// Strongest solution for a system of second-order constraints.
pub fn least_fix_point(
    extract_assumptions: &ExtractAssumptions,
    mut candidates: Vec<Candidate>,
    params: &HornSolverParams,
    state: &mut Z3State,
) -> Vec<Candidate> {
    if candidates.is_empty() {
        return vec![];
    }

    let cand = candidates.remove(0);
    let rest = candidates;

    let fml = pick_constraint(&cand, &params.constraint_pick_strategy).clone();
    let Formula::Binary(BinOp::Implies, lhs, rhs) = fml.clone() else {
        unreachable!()
    };
    let lhs_prime = lhs.apply_solution(&cand.solution);
    let assumptions = extract_assumptions.as_ref()(lhs_prime.clone())
        .into_iter()
        .chain(extract_assumptions.as_ref()(
            rhs.clone().apply_solution(&cand.solution),
        ))
        .collect::<HashSet<_>>();

    let modified_constraints = Formula::Binary(
        BinOp::Implies,
        Box::new(Formula::conjunction(
            assumptions
                .into_iter()
                .chain(iter::once(lhs_prime))
                .collect(),
        )),
        rhs,
    );

    debug_output(&cand, &fml, &modified_constraints);

    let sol_mb = weaken(modified_constraints, cand.solution.clone(), state);

    match sol_mb {
        None => {
            log::debug!(
                "All constraints: {:?}",
                cand.invalid_constraints
                    .union(&cand.valid_constraints)
                    .format("\n")
            );

            least_fix_point(extract_assumptions, rest, params, state)
        }
        Some(sol) => {
            let cand = update_candidate(extract_assumptions, &fml, cand, sol, state);

            if cand.invalid_constraints.is_empty() {
                iter::once(cand).chain(rest.into_iter()).collect()
            } else {
                least_fix_point(
                    extract_assumptions,
                    iter::once(cand).chain(rest).collect(),
                    params,
                    state,
                )
            }
        }
    }
}

fn update_candidate(
    extract_assumptions: &ExtractAssumptions,
    fml: &Formula,
    candidate: Candidate,
    sol_prime: Solution,
    state: &mut Z3State,
) -> Candidate {
    let modified_unknowns = fml.right_hand_side().clone().pos_unknowns();

    let (unaffected_valids, affected_valids): (HashSet<Formula>, HashSet<Formula>) = candidate
        .valid_constraints
        .into_iter()
        .chain(iter::once(fml.clone()))
        .partition(|fml| fml.clone().neg_unknowns().is_disjoint(&modified_unknowns));
    let (unaffected_invalids, affected_invalids): (HashSet<Formula>, HashSet<Formula>) = candidate
        .invalid_constraints
        .into_iter()
        .chain(iter::once(fml.clone()))
        .partition(|fml| fml.clone().pos_unknowns().is_disjoint(&modified_unknowns));

    let (new_valids, new_invalids): (HashSet<_>, HashSet<_>) = affected_valids
        .into_iter()
        .chain(affected_invalids.into_iter())
        .partition(|fml| {
            is_valid_fml(
                horn_apply_solution(extract_assumptions, &sol_prime, (*fml).clone()),
                state,
            )
        });

    Candidate {
        solution: sol_prime,
        valid_constraints: unaffected_valids
            .into_iter()
            .chain(new_valids.into_iter())
            .collect(),
        invalid_constraints: unaffected_invalids
            .into_iter()
            .chain(new_invalids.into_iter())
            .collect(),
        label: candidate.label,
    }
}

fn pick_constraint<'c>(candidate: &'c Candidate, strategy: &ConstraintPickStrategy) -> &'c Formula {
    match strategy {
        ConstraintPickStrategy::FirstConstraint => {
            candidate.invalid_constraints.iter().next().unwrap()
        }
        ConstraintPickStrategy::SmallSpaceConstraint => candidate
            .invalid_constraints
            .iter()
            .min_by_key(|fml| fml.right_hand_side().clone().pos_unknowns().len())
            .unwrap(),
    }
}

fn debug_output(cand: &Candidate, inv: &Formula, modified: &Formula) {
    log::debug!("Candidate: {cand:?}\nInvalid: {inv:?}\nModified: {modified:?}");
}

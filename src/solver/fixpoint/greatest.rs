use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    iter,
};

use hashbrown::{HashMap, HashSet};
use itertools::Itertools;

use crate::{
    logic::{BinOp, Candidate, ExtractAssumptions, Formula, QMap, QSpace, Solution, Valuation},
    smt::Z3State,
    solver::horn::{
        check, filter_subsets, horn_apply_solution, initial_solution, is_sat_fml, is_valid_fml,
        max_val_size, optimal_valuations, optimal_valuations_bfs, optimal_valuations_macro,
        preprocess, prune, prune_q_space, prune_solutions, prune_valuations, refine, strengthen,
        CandidatePickStrategy, ConstraintPickStrategy, FixPointSolver, HornSolverParams,
        OptimalValuationsStrategy,
    },
    util::{self, Id},
};

// -- | 'greatestFixPoint' @quals constraints@: weakest solution for a system of second-order constraints @constraints@ over qualifiers @quals@.
// greatestFixPoint :: MonadSMT s => QMap -> ExtractAssumptions -> [Candidate] -> FixPointSolver s [Candidate]
// greatestFixPoint _ _ [] = return []
// greatestFixPoint quals extractAssumptions candidates = do
//     (cand@(Candidate sol _ _ _), rest) <- pickCandidate candidates <$> asks candidatePickStrategy
//     fml <- asks constraintPickStrategy >>= pickConstraint cand
//     let modifiedConstraint = instantiateRhs sol fml
//     debugOutput candidates cand fml modifiedConstraint
//     diffs <- strengthen quals extractAssumptions modifiedConstraint sol
//     (newCandidates, rest') <- if length diffs == 1
//       then do -- Propagate the diff to all equivalent candidates
//         let unknowns = Set.map unknownName $ unknownsOf fml
//         let (equivs, nequivs) = partition (\(Candidate s valids invalids _) -> restrictDomain unknowns s == restrictDomain unknowns sol && Set.member fml invalids) rest
//         nc <- mapM (\c -> updateCandidate fml c diffs (head diffs)) (cand : equivs)
//         return (nc, nequivs)
//       else do -- Only update the current candidate
//         nc <- mapM (updateCandidate fml cand diffs) diffs
//         return (nc, rest)
//     case find (Set.null . invalidConstraints) newCandidates of
//       Just cand' -> return $ cand' : (delete cand' newCandidates ++ rest')  -- Solution found
//       Nothing -> greatestFixPoint quals extractAssumptions (newCandidates ++ rest')

//   where
//     instantiateRhs sol (Binary Implies lhs rhs) = Binary Implies lhs (applySolution sol rhs)

//     -- | Re-evaluate affected clauses in @valids@ and @otherInvalids@ after solution has been strengthened from @sol@ to @sol'@ in order to fix @fml@
//     updateCandidate fml (Candidate sol valids invalids label) diffs diff = do
//       let sol' = merge sol diff
//       let modifiedUnknowns = Map.keysSet $ Map.filter (not . Set.null) diff
//       let (unaffectedValids, affectedValids) = Set.partition (\fml -> posUnknowns fml `disjoint` modifiedUnknowns) (Set.insert fml valids) -- fml should be re-evaluated if it happens to have the same unknowns also on the right
//       let (unaffectedInvalids, affectedInvalids) = Set.partition (\fml -> negUnknowns fml `disjoint` modifiedUnknowns) (Set.delete fml invalids)
//       (newValids, newInvalids) <- setPartitionM (isValidFml . hornApplySolution extractAssumptions sol') $ affectedValids `Set.union` affectedInvalids
//       let newLabel = if length diffs == 1 then label else label ++ "." ++ show (fromJust $ elemIndex diff diffs)
//       return $ Candidate sol' (unaffectedValids `Set.union` newValids) (unaffectedInvalids `Set.union` newInvalids) newLabel

//     nontrivCount = Map.size . Map.filter (not . Set.null) -- number of unknowns with a non-top valuation
//     totalQCount = sum . map Set.size . Map.elems          -- total number of qualifiers in a solution

//     pickCandidate :: [Candidate] -> CandidatePickStrategy -> (Candidate, [Candidate])
//     pickCandidate (cand:rest) FirstCandidate = (cand, rest)
//     pickCandidate cands ValidWeakCandidate = let
//         res = maximumBy (mappedCompare $ \(Candidate s valids invalids _) -> (- Set.size invalids, - totalQCount s, nontrivCount s)) cands  -- maximize correctness and minimize strength
//       in (res, delete res cands)
//     pickCandidate cands InitializedWeakCandidate = let
//         res = maximumBy (mappedCompare $ \(Candidate s valids invalids _) -> (nontrivCount s, - totalQCount s)) cands  -- maximize the number of initialized unknowns and minimize strength
//       in (res, delete res cands)

//     pickConstraint (Candidate sol valids invalids _) strategy = case strategy of
//       FirstConstraint -> return $ Set.findMin invalids
//       SmallSpaceConstraint -> do
//         let spaceSize fml = maxValSize quals sol (unknownsOf (leftHandSide fml))
//         return $ minimumBy (\x y -> compare (spaceSize x) (spaceSize y)) (Set.toList invalids)

//     debugOutput cands cand inv modified =
//       writeLog 3 (vsep [
//         nest 2 $ text "Candidates" <+> parens (pretty $ length cands) $+$ (vsep $ map pretty cands),
//         text "Chosen candidate:" <+> pretty cand,
//         text "Invalid Constraint:" <+> pretty inv,
//         text "Strengthening:" <+> pretty modified])

/// Weakest solution for a system of second-order constraints `constraints` over qualifiers `quals`
pub fn greatest_fix_point(
    qmap: &QMap,
    extract_assumptions: &ExtractAssumptions,
    candidates: Vec<Candidate>,
    params: &FixPointSolver,
    state: &mut Z3State,
) -> Vec<Candidate> {
    if candidates.is_empty() {
        return vec![];
    }

    let (cand, rest) = pick_candidate(&candidates, &params.candidate_pick_strategy);
    let fml = pick_constraint(cand, &params.constraint_pick_strategy);
    let modified_constraint = instantiate_rhs(&cand.solution, fml.clone());
    debug_output(&candidates, &cand, fml, &modified_constraint);
    let diffs = strengthen(
        qmap,
        extract_assumptions,
        fml.clone(),
        &cand.solution,
        state,
        params,
    );

    let (new_candidates, rest_prime) = if diffs.len() == 1 {
        let unknowns = fml.unknowns();
        let (equivs, nequivs): (Vec<Candidate>, Vec<Candidate>) = rest.into_iter().partition(|c| {
            let unknowns = unknowns
                .iter()
                .map(|u| u.unknown_name().clone())
                .collect::<HashSet<_>>();

            (util::restrict_domain(&unknowns, c.solution.as_ref())
                == util::restrict_domain(&unknowns, cand.solution.as_ref()))
                && c.invalid_constraints.contains(fml)
        });

        let nc = iter::once(cand.clone())
            .chain(equivs.into_iter())
            .map(|c| {
                update_candidate(
                    extract_assumptions,
                    fml.clone(),
                    c,
                    &diffs,
                    &diffs[0],
                    state,
                )
            })
            .collect::<Vec<_>>();

        (nc, nequivs)
    } else {
        let nc = diffs
            .iter()
            .map(|diff| {
                update_candidate(
                    extract_assumptions,
                    fml.clone(),
                    cand.clone(),
                    &diffs,
                    diff,
                    state,
                )
            })
            .collect::<Vec<_>>();

        (nc, rest)
    };

    match new_candidates
        .iter()
        .find(|c| c.invalid_constraints.is_empty())
        .cloned()
    {
        Some(cand_prime) => rest_prime
            .into_iter()
            .chain(new_candidates)
            .filter(|c| *c != cand_prime)
            .chain(iter::once(cand_prime.clone()))
            .collect(),
        None => greatest_fix_point(qmap, extract_assumptions, new_candidates, params, state),
    }
}

fn instantiate_rhs(sol: &Solution, fml: Formula) -> Formula {
    match fml {
        Formula::Binary(BinOp::Implies, lhs, rhs) => {
            Formula::Binary(BinOp::Implies, lhs, Box::new(rhs.apply_solution(sol)))
        }
        _ => panic!("expected implication"),
    }
}

/// Re-evaluate affected clauses in `valids` and `other_invalids` after solution has been strengthened from `sol` to `sol'` in order to fix `fml`
fn update_candidate(
    extract_assumptions: &ExtractAssumptions,
    fml: Formula,
    cand: Candidate,
    diffs: &[Solution],
    diff: &Solution,
    state: &mut Z3State,
) -> Candidate {
    let Candidate {
        solution: sol,
        valid_constraints: valids,
        invalid_constraints: invalids,
        label,
    } = cand;

    let sol = sol.merge(diff);

    let modified_unknowns = diff.as_ref().keys().cloned().collect::<HashSet<_>>();
    let (unaffected_valids, affected_valids): (HashSet<Formula>, HashSet<Formula>) = valids
        .into_iter()
        .chain(iter::once(fml.clone()))
        .partition(|fml| fml.clone().pos_unknowns().is_disjoint(&modified_unknowns));
    let (unaffected_invalids, affected_invalids): (HashSet<Formula>, HashSet<Formula>) = invalids
        .into_iter()
        .filter(|f| *f != fml)
        .partition(|fml| fml.clone().neg_unknowns().is_disjoint(&modified_unknowns));

    let (new_valids, new_invalids): (HashSet<Formula>, HashSet<Formula>) = affected_valids
        .into_iter()
        .chain(affected_invalids.into_iter())
        .partition(|fml| {
            is_valid_fml(
                horn_apply_solution(&extract_assumptions, &sol, fml.clone()),
                state,
            )
        });

    let new_label = if diffs.len() == 1 {
        label.clone()
    } else {
        format!("{label}.{}", diffs.iter().position(|d| d == diff).unwrap())
    };

    Candidate {
        solution: sol,
        valid_constraints: unaffected_valids
            .into_iter()
            .chain(new_valids.into_iter())
            .collect(),
        invalid_constraints: unaffected_invalids
            .into_iter()
            .chain(new_invalids.into_iter())
            .collect(),
        label: new_label,
    }
}

fn nontriv_count(sol: &Solution) -> usize {
    sol.as_ref()
        .iter()
        .filter(|(_, q_space)| !q_space.as_ref().is_empty())
        .count()
}

fn total_q_count(sol: &Solution) -> usize {
    sol.as_ref()
        .values()
        .map(|q_space| q_space.as_ref().len())
        .sum()
}

fn pick_candidate<'c>(
    cands: &'c [Candidate],
    strategy: &CandidatePickStrategy,
) -> (&'c Candidate, Vec<Candidate>) {
    match strategy {
        CandidatePickStrategy::FirstCandidate => (
            cands.first().unwrap(),
            cands.iter().skip(1).cloned().collect(),
        ),
        CandidatePickStrategy::ValidWeakCandidate => {
            let res = cands.iter().max_by(|x, y| {
                let x_nontriv = nontriv_count(&x.solution);
                let y_nontriv = nontriv_count(&y.solution);
                let x_total = total_q_count(&x.solution);
                let y_total = total_q_count(&y.solution);

                // (
                //     -(x.invalid_constraints.len() as isize),
                //     -(x_total as isize),
                //     x_nontriv,
                // )
                //     .cmp(&(
                //         -(y.invalid_constraints.len() as isize),
                //         -(y_total as isize),
                //         y_nontriv,
                //     ))
                (y.invalid_constraints.len(), y_total, x_nontriv).cmp(&(
                    x.invalid_constraints.len(),
                    x_total,
                    y_nontriv,
                ))
            });

            (
                res.unwrap(),
                cands
                    .iter()
                    .filter(|c| *c != res.unwrap())
                    .cloned()
                    .collect(),
            )
        }
        CandidatePickStrategy::InitializedWeakCandidate => {
            let res = cands.iter().max_by(|x, y| {
                let x_nontriv = nontriv_count(&x.solution);
                let y_nontriv = nontriv_count(&y.solution);
                let x_total = total_q_count(&x.solution);
                let y_total = total_q_count(&y.solution);

                // (x_nontriv, -x_total).cmp(&(y_nontriv, -y_total))
                (x_nontriv, y_total).cmp(&(y_nontriv, x_total))
            });

            (
                res.unwrap(),
                cands
                    .iter()
                    .filter(|c| *c != res.unwrap())
                    .cloned()
                    .collect(),
            )
        }
    }
}

fn pick_constraint<'c>(cand: &'c Candidate, strategy: &ConstraintPickStrategy) -> &'c Formula {
    match strategy {
        ConstraintPickStrategy::FirstConstraint => cand.invalid_constraints.first().unwrap(),
        ConstraintPickStrategy::SmallSpaceConstraint => {
            let space_size = |fml: &Formula| fml.right_hand_side().unknowns().len();

            cand.invalid_constraints
                .iter()
                .min_by(|x, y| space_size(x).cmp(&space_size(y)))
                .unwrap()
        }
    }
}

fn debug_output(cands: &[Candidate], cand: &Candidate, inv: &Formula, modified: &Formula) {
    log::debug!(
        "Candidates: {cands:?}\nChosen candidate: {cand}\nInvalid Constraint: {inv}\nStrengthening: {modified}"
    );
}

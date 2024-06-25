use std::collections::{BTreeMap, HashMap};

use crate::{
    logic::{unify_sorts, Formula, Substitution},
    program::Environment,
    solver::horn::FixPointSolver,
};

// -- | 'allSubstitutions' @env qual nonsubstActuals formals actuals@:
// -- all well-typed substitutions of @actuals@ for @formals@ in a qualifier @qual@
// allRawSubstitutions :: Environment -> Formula -> [Formula] -> [Formula] -> [Formula] -> [Formula] -> [Formula]
// allRawSubstitutions _ (BoolLit True) _ _ _ _ = []
// allRawSubstitutions env qual formals actuals fixedFormals fixedActuals = do
//   let tvs = Set.fromList (env ^. boundTypeVars)
//   case unifySorts tvs (map sortOf fixedFormals) (map sortOf fixedActuals) of
//     Left _ -> []
//     Right fixedSortSubst -> do
//       let fixedSubst = Map.fromList $ zip (map varName fixedFormals) fixedActuals
//       let qual' = substitute fixedSubst qual
//       (sortSubst, subst, _) <- foldM (go tvs) (fixedSortSubst, Map.empty, actuals) formals
//       return $ substitute subst $ sortSubstituteFml sortSubst qual'
//   where
//     go tvs (sortSubst, subst, actuals) formal = do
//       let formal' = sortSubstituteFml sortSubst formal
//       actual <- actuals
//       case unifySorts tvs [sortOf formal'] [sortOf actual] of
//         Left _ -> mzero
//         Right sortSubst' -> return (sortSubst `Map.union` sortSubst', Map.insert (varName formal) actual subst, delete actual actuals)

// allSubstitutions :: Environment -> Formula -> [Formula] -> [Formula] -> [Formula] -> [Formula] -> [Formula]
// allSubstitutions env qual formals actuals fixedFormals fixedActuals = do
//   qual' <- allRawSubstitutions env qual formals actuals fixedFormals fixedActuals
//   case resolveRefinement env qual' of
//     Left _ -> [] -- Variable sort mismatch
//     Right resolved -> return resolved

/// All well-typed substitutions of `actuals` for `formals` in a qualifier `qual`
pub fn all_raw_substitutions(
    env: Environment,
    qual: Formula,
    formals: Vec<Formula>,
    actuals: Vec<Formula>,
    fixed_formals: Vec<Formula>,
    fixed_actuals: Vec<Formula>,
) -> Vec<Formula> {
    if qual == Formula::BoolLit(true) {
        return Vec::new();
    }

    let tvs = env.bound_type_vars;

    match unify_sorts(
        &tvs,
        fixed_formals.iter().map(|f| f.sort()).collect(),
        fixed_actuals.iter().map(|f| f.sort()).collect(),
    ) {
        Err(_) => Vec::new(),
        Ok(fixed_sort_subst) => {
            let fixed_subst = Substitution::new(
                fixed_formals
                    .iter()
                    .map(|f| (f.var_name().clone(), f.clone()))
                    .collect::<BTreeMap<_, _>>(),
            );
            let qual = qual.substitute(&fixed_subst);

            let (sort_subst, mut subst, mut actuals) = formals.iter().fold(
                (fixed_sort_subst, BTreeMap::default(), actuals),
                |(mut sort_subst, mut subst, mut actuals), formal| {
                    let formal = sort_subst.sort_substitute_fml(formal.clone());
                    let actual = actuals.remove(0);

                    match unify_sorts(&tvs, vec![formal.sort()], vec![actual.sort()]) {
                        Err(_) => (sort_subst, subst, actuals),
                        Ok(sort_subst_) => {
                            sort_subst.as_mut().extend(sort_subst_.into_iter());

                            subst.insert(formal.var_name().clone(), actual);
                            (sort_subst, subst, actuals)
                        }
                    }
                },
            );

            // sort_subst
            //     .sort_substitute_fml(qual)
            //     .substitute(&Substitution::new(subst))
            todo!("supposed to be a vec??")
        }
    }
}

// allSubstitutions :: Environment -> Formula -> [Formula] -> [Formula] -> [Formula] -> [Formula] -> [Formula]
// allSubstitutions env qual formals actuals fixedFormals fixedActuals = do
//   qual' <- allRawSubstitutions env qual formals actuals fixedFormals fixedActuals
//   case resolveRefinement env qual' of
//     Left _ -> [] -- Variable sort mismatch
//     Right resolved -> return resolved

pub fn all_substitutions(
    env: Environment,
    qual: Formula,
    formals: Vec<Formula>,
    actuals: Vec<Formula>,
    fixed_formals: Vec<Formula>,
    fixed_actuals: Vec<Formula>,
) -> Vec<Formula> {
    let qual = all_raw_substitutions(env, qual, formals, actuals, fixed_formals, fixed_actuals);

    todo!()
}

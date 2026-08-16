//! Top-level synthesizer interface.

use std::{collections::BTreeMap, rc::Rc};

use crate::{
    cli::{ExplorerParams, HornSolverParams},
    error::ErrorMessage,
    horn_solver::FixPointSolver,
    logic::{
        atoms_of, conjuncts_of, de_brujns, distinct_type_vars, is_data, sort_of, sort_substitute,
        sort_substitute_fml, substitute, to_space, unify_sorts, var_name, vars_of, BinOp, Formula,
        Sort, SortSubstitution, Substitution, DONT_CARE, VALUE_VAR_NAME,
    },
    program::{all_symbols, DatatypeDef, Environment, Goal, RProgram},
    resolver::resolve_refinement,
    tc_solver::{CondQualsGen, MatchQualsGen, PredQualsGen, TypeQualsGen, TypingParams},
    type_checker::reconstruct,
    types::{
        all_arg_types, last_type, to_monotype, to_sort, type_vars_of, BaseType, RType, TypeSkeleton,
    },
};

/// `synthesize`: synthesize a program that has the spec
/// of `goal`, using conditional qualifiers `cquals` and type qualifiers
/// `tquals`.
pub fn synthesize(
    explorer_params: &ExplorerParams,
    _solver_params: &HornSolverParams,
    goal: &Goal,
    cquals: &[Formula],
    tquals: &[Formula],
    horn: &mut FixPointSolver,
) -> Result<RProgram, ErrorMessage> {
    let typing_params = TypingParams {
        cond_quals_gen: cond_quals(cquals.to_vec(), goal.clone()),
        match_quals_gen: match_quals(goal.clone()),
        type_quals_gen: type_quals(cquals.to_vec(), tquals.to_vec(), goal.clone()),
        pred_quals_gen: pred_quals(cquals.to_vec(), goal.clone()),
        tc_solver_split_measures: explorer_params.split_measures,
        tc_solver_log_level: explorer_params.explorer_log_level,
    };
    reconstruct(explorer_params, &typing_params, goal, horn)
}

/// Qualifier generator for conditionals.
#[must_use]
pub fn cond_quals(cquals: Vec<Formula>, goal: Goal) -> CondQualsGen {
    Rc::new(move |env, vars| {
        let components = components_in(&goal.g_environment);
        let synt_goal = to_monotype(&goal.g_spec);
        let mut quals = Vec::new();
        for q in &cquals {
            quals.extend(instantiate_cond_qualifier(false, env, vars, q));
        }
        let mut types = components;
        types.extend(all_arg_types(&synt_goal));
        for t in &types {
            quals.extend(extract_cond_from_type(env, vars, t));
        }
        to_space(None, quals)
    })
}

/// Qualifier generator for match scrutinees.
#[must_use]
pub fn match_quals(goal: Goal) -> MatchQualsGen {
    Rc::new(move |env, vars| {
        let mut quals = Vec::new();
        for (dt_name, dt_def) in &goal.g_environment.datatypes {
            quals.extend(extract_match_qgen(env, vars, dt_name, dt_def));
        }
        to_space(Some(1), quals)
    })
}

/// Qualifier generator for types.
#[must_use]
pub fn type_quals(cquals: Vec<Formula>, tquals: Vec<Formula>, goal: Goal) -> TypeQualsGen {
    Rc::new(move |env, val, vars| {
        let synt_goal = to_monotype(&goal.g_spec);
        let mut quals = Vec::new();
        quals.extend(extract_qgen_from_type(false, env, val, vars, &synt_goal));
        quals.extend(extract_qgen_from_type(true, env, val, vars, &synt_goal));
        for q in &tquals {
            quals.extend(instantiate_type_qualifier(env, val, vars, q));
        }
        for t in &components_in(&goal.g_environment) {
            quals.extend(extract_qgen_from_type(false, env, val, vars, t));
        }
        let _ = cquals;
        to_space(None, quals)
    })
}

/// Qualifier generator for bound predicates.
#[must_use]
pub fn pred_quals(cquals: Vec<Formula>, goal: Goal) -> PredQualsGen {
    Rc::new(move |env, params, vars| {
        let synt_goal = to_monotype(&goal.g_spec);
        let mut types = vec![synt_goal.clone()];
        types.extend(components_in(&goal.g_environment));
        let mut quals = Vec::new();
        for t in &types {
            quals.extend(extract_pred_qgen_from_type(true, env, params, vars, t));
        }
        if params.is_empty() {
            for q in &cquals {
                quals.extend(instantiate_cond_qualifier(false, env, vars, q));
            }
            let mut cond_types = components_in(&goal.g_environment);
            cond_types.extend(all_arg_types(&synt_goal));
            for t in &cond_types {
                quals.extend(extract_cond_from_type(env, vars, t));
            }
        }
        to_space(None, quals)
    })
}

fn components_in(env: &Environment) -> Vec<RType> {
    all_symbols(env).values().map(to_monotype).collect()
}

/// `instantiateTypeQualifier`: qualifier generator that
/// treats free variables of `qual` except `_v` as parameters.
fn instantiate_type_qualifier(
    env: &Environment,
    actual_val: &Formula,
    actual_vars: &[Formula],
    qual: &Formula,
) -> Vec<Formula> {
    if matches!(qual, Formula::BoolLit(true)) {
        return Vec::new();
    }
    let mut formal_vals = Vec::new();
    let mut formal_vars = Vec::new();
    for v in vars_of(qual) {
        if var_name(&v) == VALUE_VAR_NAME {
            formal_vals.push(v);
        } else {
            formal_vars.push(v);
        }
    }
    if formal_vals.len() == 1 {
        all_substitutions(
            env,
            qual,
            &formal_vars,
            actual_vars,
            &formal_vals,
            std::slice::from_ref(actual_val),
        )
    } else {
        Vec::new()
    }
}

/// `instantiateCondQualifier`: qualifier generator that
/// treats free variables of `qual` as parameters.
fn instantiate_cond_qualifier(
    allow_dt_eq: bool,
    env: &Environment,
    vars: &[Formula],
    qual: &Formula,
) -> Vec<Formula> {
    let formals: Vec<Formula> = vars_of(qual).into_iter().collect();
    all_substitutions(env, qual, &formals, vars, &[], &[])
        .into_iter()
        .filter(|q| allow_dt_eq || !is_data_eq(q))
        .collect()
}

/// `isDataEq`.
fn is_data_eq(fml: &Formula) -> bool {
    match fml {
        Formula::Binary(op, e1, _) if matches!(op, BinOp::Eq | BinOp::Neq) => is_data(&sort_of(e1)),
        _ => false,
    }
}

/// `extractMatchQGen`: qualifier generator that
/// generates qualifiers of the form `x == ctor`, for all scalar constructors
/// `ctor` of datatype `dt_name`.
fn extract_match_qgen(
    env: &Environment,
    vars: &[Formula],
    dt_name: &str,
    dt_def: &DatatypeDef,
) -> Vec<Formula> {
    let mut quals = Vec::new();
    let all = all_symbols(env);
    let t_params = &dt_def.type_params;
    let sort_inst: SortSubstitution = t_params
        .iter()
        .zip(
            distinct_type_vars(t_params.len())
                .into_iter()
                .map(Sort::VarS),
        )
        .map(|(k, v)| (k.clone(), v))
        .collect();
    for ctor in &dt_def.constructors {
        if let TypeSkeleton::ScalarT(base_t, fml) = to_monotype(&all[ctor]) {
            let fml_prime = sort_substitute_fml(&sort_inst, &fml);
            let value = Formula::Var(
                Box::new(sort_substitute(&sort_inst, to_sort(&base_t))),
                VALUE_VAR_NAME.to_string(),
            );
            quals.extend(all_substitutions(env, &fml_prime, &[value], vars, &[], &[]));
        }
    }
    let _ = dt_name;
    quals
}

/// `extractQGenFromType`: qualifier generator that
/// extracts all conjuncts from refinements of `t` and treats their free
/// variables as parameters.
fn extract_qgen_from_type(
    positive: bool,
    env: &Environment,
    val: &Formula,
    vars: &[Formula],
    t: &RType,
) -> Vec<Formula> {
    match t {
        TypeSkeleton::ScalarT(base_t, fml) => {
            if !positive {
                return Vec::new();
            }
            let mut quals = Vec::new();
            let sort_inst: SortSubstitution = type_vars_of(t)
                .iter()
                .zip(
                    distinct_type_vars(type_vars_of(t).len())
                        .into_iter()
                        .map(Sort::VarS),
                )
                .map(|(k, v)| (k.clone(), v))
                .collect();
            for f in conjuncts_of(&sort_substitute_fml(&sort_inst, fml)) {
                quals.extend(instantiate_type_qualifier(env, val, vars, &f));
            }
            if let BaseType::DatatypeT(dt_name, t_args, p_args) = base_t {
                let dt_def = &env.datatypes[dt_name];
                let p_params = &dt_def.pred_params;
                for ta in t_args {
                    quals.extend(extract_qgen_from_type(true, env, val, vars, ta));
                }
                for (pp, pa) in p_params.iter().zip(p_args) {
                    quals.extend(extract_qgen_from_pred(env, val, vars, pp, pa, &sort_inst));
                }
            }
            quals
        }
        TypeSkeleton::FunctionT(_, t_arg, t_res) => {
            let mut quals = Vec::new();
            if positive {
                quals.extend(extract_qgen_from_type(true, env, val, vars, t_res));
            } else {
                quals.extend(extract_qgen_from_type(true, env, val, vars, t_arg));
                quals.extend(extract_qgen_from_type(false, env, val, vars, t_res));
            }
            quals
        }
        _ => Vec::new(),
    }
}

/// `extractQGenFromPred`: extract type qualifiers from
/// a predicate argument of a datatype.
fn extract_qgen_from_pred(
    env: &Environment,
    val: &Formula,
    vars: &[Formula],
    sig: &crate::logic::PredSig,
    fml: &Formula,
    sort_inst: &SortSubstitution,
) -> Vec<Formula> {
    if sig.pred_sig_arg_sorts.is_empty() {
        return Vec::new();
    }
    let last_sort = sig.pred_sig_arg_sorts.last().unwrap().clone();
    let last_param = de_brujns(sig.pred_sig_arg_sorts.len()).pop().unwrap();
    let sub: Substitution = BTreeMap::from([(
        last_param,
        Formula::Var(Box::new(last_sort), VALUE_VAR_NAME.to_string()),
    )]);
    let fmls = conjuncts_of(&sort_substitute_fml(
        sort_inst,
        &substitute(&sub, fml.clone()),
    ));
    let mut quals = Vec::new();
    for f in fmls {
        quals.extend(instantiate_type_qualifier(env, val, vars, &f));
    }
    quals
}

/// `extractCondFromType`: extract conditional
/// qualifiers from the types of boolean functions.
fn extract_cond_from_type(env: &Environment, vars: &[Formula], t: &RType) -> Vec<Formula> {
    if !matches!(t, TypeSkeleton::FunctionT(..)) {
        return Vec::new();
    }
    match last_type(t) {
        TypeSkeleton::ScalarT(BaseType::BoolT, fml) => match fml {
            Formula::Binary(BinOp::Eq, e1, rhs) => {
                if let Formula::Var(s, v) = e1.as_ref()
                    && v == VALUE_VAR_NAME
                    && s.as_ref() == &Sort::BoolS
                {
                    let sort_inst: SortSubstitution = type_vars_of(t)
                        .iter()
                        .zip(
                            distinct_type_vars(type_vars_of(t).len())
                                .into_iter()
                                .map(Sort::VarS),
                        )
                        .map(|(k, v)| (k.clone(), v))
                        .collect();
                    let fml_prime = sort_substitute_fml(&sort_inst, rhs.as_ref());
                    let formals: Vec<Formula> = vars_of(&fml_prime).into_iter().collect();
                    return all_substitutions(env, &fml_prime, &formals, vars, &[], &[])
                        .into_iter()
                        .filter(|q| !is_data_eq(q))
                        .collect();
                }
                Vec::new()
            }
            _ => Vec::new(),
        },
        _ => Vec::new(),
    }
}

/// `extractPredQGenFromType`: extract predicate
/// qualifiers from a type refinement.
fn extract_pred_qgen_from_type(
    use_all_args: bool,
    env: &Environment,
    actual_params: &[Formula],
    actual_vars: &[Formula],
    t: &RType,
) -> Vec<Formula> {
    fn extract_from_refinement(
        use_all_args: bool,
        env: &Environment,
        actual_params: &[Formula],
        actual_vars: &[Formula],
        sort_inst: &SortSubstitution,
        fml: &Formula,
    ) -> Vec<Formula> {
        if actual_params.is_empty() {
            return Vec::new();
        }
        let fml_prime = sort_substitute_fml(sort_inst, fml);
        let mut formal_vals = Vec::new();
        let mut formal_vars = Vec::new();
        for v in vars_of(&fml_prime) {
            if var_name(&v) == VALUE_VAR_NAME {
                formal_vals.push(v);
            } else {
                formal_vars.push(v);
            }
        }
        let mut params = actual_params.to_vec();
        let last_param = params.pop().unwrap();
        let mut actuals = actual_vars.to_vec();
        actuals.extend(params);
        let mut quals = Vec::new();
        for c in conjuncts_of(&fml_prime) {
            let qs = all_substitutions(
                env,
                &c,
                &formal_vars,
                &actuals,
                &formal_vals,
                std::slice::from_ref(&last_param),
            );
            if use_all_args {
                let param_set: BTreeMap<String, ()> = actual_params
                    .iter()
                    .map(|p| (var_name(p).clone(), ()))
                    .collect();
                for q in qs {
                    // `filterAllArgs`: keep qualifiers that use all predicate
                    // parameters (`params ⊆ varsOf q`); free variables other
                    // than the parameters are allowed.
                    let q_vars: BTreeMap<String, ()> = vars_of(&q)
                        .iter()
                        .map(|v| (var_name(v).clone(), ()))
                        .collect();
                    if param_set.keys().all(|p| q_vars.contains_key(p)) {
                        quals.push(q);
                    }
                }
            } else {
                quals.extend(qs);
            }
        }
        quals
    }
    fn is_param(f: &Formula) -> bool {
        match f {
            Formula::Var(_, name) => name.starts_with(DONT_CARE),
            _ => false,
        }
    }
    let sort_inst: SortSubstitution = type_vars_of(t)
        .iter()
        .zip(
            distinct_type_vars(type_vars_of(t).len())
                .into_iter()
                .map(Sort::VarS),
        )
        .map(|(k, v)| (k.clone(), v))
        .collect();
    match t {
        TypeSkeleton::ScalarT(BaseType::DatatypeT(_dt_name, t_args, p_args), fml) => {
            let mut quals = extract_from_refinement(
                use_all_args,
                env,
                actual_params,
                actual_vars,
                &sort_inst,
                fml,
            );
            for p_arg in p_args {
                let p_arg_prime = sort_substitute_fml(&sort_inst, p_arg);
                let mut formal_params = Vec::new();
                let mut formal_vars = Vec::new();
                for v in vars_of(&p_arg_prime) {
                    if is_param(&v) {
                        formal_params.push(v);
                    } else {
                        formal_vars.push(v);
                    }
                }
                let mut actuals = actual_vars.to_vec();
                actuals.extend(actual_params.iter().cloned());
                for atom in atoms_of(&p_arg_prime) {
                    let qs = all_substitutions(env, &atom, &formal_vars, &actuals, &[], &[]);
                    if use_all_args {
                        let param_set: BTreeMap<String, ()> = actual_params
                            .iter()
                            .map(|p| (var_name(p).clone(), ()))
                            .collect();
                        for q in qs {
                            if vars_of(&q)
                                .iter()
                                .all(|v| param_set.contains_key(var_name(v)))
                            {
                                quals.push(q);
                            }
                        }
                    } else {
                        quals.extend(qs);
                    }
                }
                let _ = formal_params;
            }
            for ta in t_args {
                quals.extend(extract_pred_qgen_from_type(
                    use_all_args,
                    env,
                    actual_params,
                    actual_vars,
                    ta,
                ));
            }
            quals
        }
        TypeSkeleton::ScalarT(_, fml) => extract_from_refinement(
            use_all_args,
            env,
            actual_params,
            actual_vars,
            &sort_inst,
            fml,
        ),
        TypeSkeleton::FunctionT(_, t_arg, t_res) => {
            let mut quals =
                extract_pred_qgen_from_type(use_all_args, env, actual_params, actual_vars, t_arg);
            quals.extend(extract_pred_qgen_from_type(
                use_all_args,
                env,
                actual_params,
                actual_vars,
                t_res,
            ));
            quals
        }
        _ => Vec::new(),
    }
}

/// `allRawSubstitutions`: all well-typed substitutions
/// of `actuals` for `formals` in a qualifier `qual`.
fn all_raw_substitutions(
    env: &Environment,
    qual: &Formula,
    formals: &[Formula],
    actuals: &[Formula],
    fixed_formals: &[Formula],
    fixed_actuals: &[Formula],
) -> Vec<Formula> {
    if matches!(qual, Formula::BoolLit(true)) {
        return Vec::new();
    }
    let tvs: std::collections::BTreeSet<String> = env.bound_type_vars.iter().cloned().collect();
    let fixed_sorts: Vec<Sort> = fixed_formals.iter().map(sort_of).collect();
    let actual_sorts: Vec<Sort> = fixed_actuals.iter().map(sort_of).collect();
    let fixed_sort_subst = match unify_sorts(&tvs, &fixed_sorts, &actual_sorts) {
        Err(_) => return Vec::new(),
        Ok(s) => s,
    };
    let fixed_subst: Substitution = fixed_formals
        .iter()
        .zip(fixed_actuals.iter())
        .map(|(f, a)| (var_name(f).clone(), a.clone()))
        .collect();
    let qual_prime = substitute(&fixed_subst, qual.clone());
    let mut results = Vec::new();
    go(
        env,
        &tvs,
        &fixed_sort_subst,
        Substitution::new(),
        actuals.to_vec(),
        formals,
        &mut results,
    );
    results
        .into_iter()
        .map(|(ss, s)| sort_substitute_fml(&ss, &substitute(&s, qual_prime.clone())))
        .collect()
}

fn go(
    env: &Environment,
    tvs: &std::collections::BTreeSet<String>,
    sort_subst: &SortSubstitution,
    subst: Substitution,
    actuals: Vec<Formula>,
    formals: &[Formula],
    out: &mut Vec<(SortSubstitution, Substitution)>,
) {
    let Some((formal, rest_formals)) = formals.split_first() else {
        out.push((sort_subst.clone(), subst));
        return;
    };
    let formal_prime = sort_substitute_fml(sort_subst, formal);
    let formal_sort = sort_of(&formal_prime);
    for i in 0..actuals.len() {
        let actual = &actuals[i];
        let mut rest: Vec<Formula> = Vec::with_capacity(actuals.len() - 1);
        rest.extend(actuals[..i].iter().cloned());
        rest.extend(actuals[i + 1..].iter().cloned());
        match unify_sorts(tvs, std::slice::from_ref(&formal_sort), &[sort_of(actual)]) {
            Err(_) => {}
            Ok(ss_prime) => {
                let mut merged = ss_prime;
                merged.extend(sort_subst.iter().map(|(k, v)| (k.clone(), v.clone())));
                let mut subst_prime = subst.clone();
                subst_prime.insert(var_name(&formal_prime).clone(), actual.clone());
                go(env, tvs, &merged, subst_prime, rest, rest_formals, out);
            }
        }
    }
}

/// `allSubstitutions`: like `allRawSubstitutions`, but
/// checks that the result is well-sorted.
fn all_substitutions(
    env: &Environment,
    qual: &Formula,
    formals: &[Formula],
    actuals: &[Formula],
    fixed_formals: &[Formula],
    fixed_actuals: &[Formula],
) -> Vec<Formula> {
    let mut out = Vec::new();
    for qual_prime in
        all_raw_substitutions(env, qual, formals, actuals, fixed_formals, fixed_actuals)
    {
        if let Ok(resolved) = resolve_refinement(env, &qual_prime) {
            out.push(resolved);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn is_data_eq_detects_datatype_equality() {
        let fml = Formula::Binary(
            BinOp::Eq,
            Box::new(Formula::Var(
                Box::new(Sort::DataS("List".to_string(), vec![])),
                "v".to_string(),
            )),
            Box::new(Formula::Var(
                Box::new(Sort::DataS("List".to_string(), vec![])),
                "w".to_string(),
            )),
        );
        assert!(is_data_eq(&fml));
        let int_eq = Formula::Binary(
            BinOp::Eq,
            Box::new(Formula::Var(Box::new(Sort::IntS), "v".to_string())),
            Box::new(Formula::Var(Box::new(Sort::IntS), "w".to_string())),
        );
        assert!(!is_data_eq(&int_eq));
    }
}

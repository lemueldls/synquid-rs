//! Refinement type reconstruction for programs with holes.

use std::{collections::BTreeMap, rc::Rc};

use crate::{
    cli::{ExplorerParams, FixpointStrategy},
    error::{ErrorKind, ErrorMessage, no_pos},
    explorer::{
        ExplorerCtx, Reconstructor, Step, add_constraint, app_type, case_symbols, check_e,
        current_valuation, cut, enqueue_goal, fresh_id, fresh_var, generate_aux_goals,
        generate_condition, generate_e_up_to, generate_error, generate_i, in_context, instantiate,
        local, mplus, optional_in_partial, ret, run_explorer, run_in_solver, symbol_type,
        throw_error, to_var,
    },
    horn_solver::FixPointSolver,
    logic::{
        Formula, Sort, Substitution, UnOp, VALUE_VAR_NAME, and, and_clean, conjunction, ffalse,
        fnot, ge, int_lit, int_var, le, lt, or_clean, substitute, val_int,
    },
    pretty::{pretty_program, pretty_type as pretty_type_doc, text, vsp},
    program::{
        BareProgram, Case, Constraint, Environment, Goal, RProgram, UProgram, add_assumption,
        add_bound_predicate, add_poly_variable, add_scrutinee, add_type_var, add_variable,
        all_symbols, embed_context, is_bound, lookup_symbol, refine_bot, refine_top,
        rename_as_impl, symbol_list, type_substitute_env, u_hole, unfold_all_variables, untyped,
    },
    resolver::resolve_refined_type,
    tc_solver::{
        TypingParams, current_assignment, finalize_program, finalize_type, init_typing_state,
        match_cons_type, solve_type_constraints,
    },
    types::{
        BaseType, RType, SchemaSkeleton, TypeSkeleton, add_refinement, arity, base_type_of,
        bool_all, has_set, intersection, is_function_type, last_type, rename_var, shape,
        to_monotype, to_sort, type_substitute,
    },
};

/// `?`-style short-circuit on `Step`: propagate failure.
macro_rules! try_step {
    ($e:expr) => {
        match $e {
            Step::Fail => return Step::Fail,
            Step::Ok { value, .. } => value,
        }
    };
}

/// `reconstruct`: reconstruct missing types and terms in
/// the body of `goal` so that it represents a valid type judgment; return a
/// type error if that is impossible.
pub fn reconstruct(
    e_params: &ExplorerParams,
    t_params: &TypingParams,
    goal: &Goal,
    horn: &mut FixPointSolver,
) -> Result<RProgram, ErrorMessage> {
    let init_ts = Rc::new(init_typing_state(&goal.g_environment));
    let e_params = ExplorerParams {
        source_pos: goal.g_source_pos.clone(),
        ..e_params.clone()
    };
    let aux_depth = e_params.aux_depth;
    let goal = goal.clone();
    let reconstructor: Reconstructor =
        Rc::new(reconstruct_top_level as for<'x> fn(&mut ExplorerCtx<'x>, &Goal) -> Step<RProgram>);
    run_explorer(
        horn,
        Rc::new(e_params),
        Rc::new(t_params.clone()),
        reconstructor,
        init_ts,
        move |ctx| {
            let mut goal = goal.clone();
            goal.g_depth = aux_depth;
            let p_main = try_step!(reconstruct_top_level(ctx, &goal));
            let solved = ctx.state.solved_aux_goals.clone();
            let p = insert_aux_solutions(&solved, &p_main);
            run_in_solver(ctx, |s| Ok(finalize_program(s, &p)))
        },
    )
}

/// `reconstructTopLevel`: reconstruct the top-level goal,
/// descending through quantifiers.
pub fn reconstruct_top_level(ctx: &mut ExplorerCtx<'_>, goal: &Goal) -> Step<RProgram> {
    match &goal.g_spec {
        SchemaSkeleton::ForallT(a, sch) => {
            let goal2 = Goal {
                g_environment: Rc::new(add_type_var(a, &goal.g_environment)),
                g_spec: (**sch).clone(),
                ..goal.clone()
            };
            reconstruct_top_level(ctx, &goal2)
        }
        SchemaSkeleton::ForallP(sig, sch) => {
            let goal2 = Goal {
                g_environment: Rc::new(add_bound_predicate(sig.clone(), &goal.g_environment)),
                g_spec: (**sch).clone(),
                ..goal.clone()
            };
            reconstruct_top_level(ctx, &goal2)
        }
        SchemaSkeleton::Monotype(TypeSkeleton::FunctionT(..)) => {
            let depth = goal.g_depth;
            let goal = goal.clone();
            local(
                ctx,
                |p| {
                    ExplorerParams {
                        aux_depth: depth,
                        ..p.clone()
                    }
                },
                move |ctx| reconstruct_fix(ctx, &goal),
            )
        }
        SchemaSkeleton::Monotype(t) => {
            let depth = goal.g_depth;
            let env = goal.g_environment.clone();
            let t = t.clone();
            let impl_ = goal.g_impl.clone();
            local(
                ctx,
                |p| {
                    ExplorerParams {
                        aux_depth: depth,
                        ..p.clone()
                    }
                },
                move |ctx| reconstruct_i(ctx, &env, &t, &impl_),
            )
        }
    }
}

/// Port of the `reconstructFix` local function:
/// reconstruct a (possibly recursive) function definition.
fn reconstruct_fix(ctx: &mut ExplorerCtx<'_>, goal: &Goal) -> Step<RProgram> {
    let env = goal.g_environment.clone();
    let impl_ = goal.g_impl.clone();
    let fun_name = goal.g_name.clone();
    let typ = match &goal.g_spec {
        SchemaSkeleton::Monotype(t @ TypeSkeleton::FunctionT(..)) => t.clone(),
        _ => unreachable!("reconstructFix: not a function type"),
    };
    let typ_prime = rename_as_impl(&|x| is_bound(&env, x), &impl_, &typ);
    let t0 = try_step!(run_in_solver(ctx, |s| {
        Ok(current_assignment(s, &typ_prime))
    }));
    let rec_calls = try_step!(recursive_calls(
        ctx,
        &env,
        &fun_name,
        goal.g_synthesize,
        &t0
    ));
    let polymorphic = ctx.reader.params.poly_recursion;
    let pred_polymorphic = ctx.reader.params.pred_poly_recursion;
    let tvs = env.bound_type_vars.clone();
    let pvs = env.bound_predicates.clone();
    let pred_generalized = |sch: RSchema| -> RSchema {
        if pred_polymorphic {
            pvs.iter().rev().fold(sch, |acc, pv| {
                SchemaSkeleton::ForallP(pv.clone(), Box::new(acc))
            })
        } else {
            sch
        }
    };
    let type_generalized = |sch: RSchema| -> RSchema {
        if polymorphic {
            tvs.iter().rev().fold(sch, |acc, tv| {
                SchemaSkeleton::ForallT(tv.clone(), Box::new(acc))
            })
        } else {
            sch
        }
    };
    let mut env_prime = (*env).clone();
    for (f, t) in &rec_calls {
        let sch = type_generalized(pred_generalized(SchemaSkeleton::Monotype(t.clone())));
        env_prime = add_poly_variable(f, sch, &env_prime);
        env_prime
            .shape_constraints
            .insert(f.clone(), shape(&typ_prime));
    }
    let wrap: Rc<dyn Fn(&RProgram) -> RProgram> = if rec_calls.is_empty() {
        Rc::new(|p| p.clone())
    } else {
        let names: Vec<String> = rec_calls.iter().map(|(f, _)| f.clone()).collect();
        let typ_prime = typ_prime.clone();
        Rc::new(move |p| {
            RProgram {
                content: BareProgram::PFix(names.clone(), Box::new(p.clone())),
                type_of: typ_prime.clone(),
            }
        })
    };
    let p = try_step!(in_context(ctx, wrap.clone(), |ctx| {
        reconstruct_i(ctx, &Rc::new(env_prime.clone()), &typ_prime, &impl_)
    }));
    ret(ctx, wrap(&p))
}

type RSchema = SchemaSkeleton<Formula>;

/// `recursiveCalls`: name-type pairs for recursive calls
/// to a function with type `t` (0 or 1).
fn recursive_calls(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    fun_name: &String,
    synth: bool,
    t: &RType,
) -> Step<Vec<(String, RType)>> {
    if !synth {
        return ret(ctx, vec![(fun_name.clone(), t.clone())]);
    }
    match ctx.reader.params.fix_strategy {
        FixpointStrategy::AllArguments => {
            let (rec_type, _) = try_step!(recursive_type_tuple(ctx, env, t, ffalse()));
            if rec_type == *t {
                ret(ctx, Vec::new())
            } else {
                ret(ctx, vec![(fun_name.clone(), rec_type)])
            }
        }
        FixpointStrategy::FirstArgument => {
            let rec_type = try_step!(recursive_type_first(ctx, env, t));
            if rec_type == *t {
                ret(ctx, Vec::new())
            } else {
                ret(ctx, vec![(fun_name.clone(), rec_type)])
            }
        }
        FixpointStrategy::DisableFixpoint => ret(ctx, Vec::new()),
        FixpointStrategy::Nonterminating => ret(ctx, vec![(fun_name.clone(), t.clone())]),
    }
}

/// `recursiveTypeTuple`: type of the recursive call to a
/// function of type `t` when a lexicographic tuple of all recursible arguments
/// decreases.
fn recursive_type_tuple(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    t: &RType,
    fml: Formula,
) -> Step<(RType, bool)> {
    match t {
        TypeSkeleton::FunctionT(x, t_arg, t_res) => {
            match termination_refinement(env, x, t_arg) {
                None => {
                    let (t_res_prime, seen) = try_step!(recursive_type_tuple(ctx, env, t_res, fml));
                    ret(
                        ctx,
                        (
                            TypeSkeleton::FunctionT(
                                x.clone(),
                                t_arg.clone(),
                                Box::new(t_res_prime),
                            ),
                            seen,
                        ),
                    )
                }
                Some((arg_lt, arg_le)) => {
                    let y = try_step!(fresh_var(ctx, env, "x"));
                    let y_for_val: Substitution = BTreeMap::from([(
                        VALUE_VAR_NAME.to_string(),
                        Formula::Var(Box::new(to_sort(&base_type_of(t_arg))), y.clone()),
                    )]);
                    let fml_prime = or_clean(fml.clone(), substitute(&y_for_val, arg_lt.clone()));
                    let (t_res_prime, seen) = try_step!(recursive_type_tuple(
                        ctx,
                        env,
                        &rename_var(&|b| is_bound(env, b), x, &y, t_arg, t_res),
                        fml_prime,
                    ));
                    let arg_t = (**t_arg).clone();
                    if seen {
                        ret(
                            ctx,
                            (
                                TypeSkeleton::FunctionT(
                                    y,
                                    Box::new(add_refinement(arg_t, &arg_le)),
                                    Box::new(t_res_prime),
                                ),
                                true,
                            ),
                        )
                    } else if fml == ffalse() {
                        ret(
                            ctx,
                            (
                                TypeSkeleton::FunctionT(
                                    y,
                                    Box::new(add_refinement(arg_t, &arg_lt)),
                                    Box::new(t_res_prime),
                                ),
                                true,
                            ),
                        )
                    } else {
                        ret(
                            ctx,
                            (
                                TypeSkeleton::FunctionT(
                                    y,
                                    Box::new(add_refinement(
                                        arg_t,
                                        &and_clean(arg_le, or_clean(fml, arg_lt)),
                                    )),
                                    Box::new(t_res_prime),
                                ),
                                true,
                            ),
                        )
                    }
                }
            }
        }
        _ => ret(ctx, (t.clone(), false)),
    }
}

/// `recursiveTypeFirst`: type of the recursive call to a
/// function of type `t` when only the first recursible argument decreases.
fn recursive_type_first(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    t: &RType,
) -> Step<RType> {
    match t {
        TypeSkeleton::FunctionT(x, t_arg, t_res) => {
            match termination_refinement(env, x, t_arg) {
                None => {
                    let t_res_prime = try_step!(recursive_type_first(ctx, env, t_res));
                    ret(
                        ctx,
                        TypeSkeleton::FunctionT(x.clone(), t_arg.clone(), Box::new(t_res_prime)),
                    )
                }
                Some((arg_lt, _)) => {
                    let y = try_step!(fresh_var(ctx, env, "x"));
                    let t_res_prime = rename_var(&|b| is_bound(env, b), x, &y, t_arg, t_res);
                    ret(
                        ctx,
                        TypeSkeleton::FunctionT(
                            y,
                            Box::new(add_refinement((**t_arg).clone(), &arg_lt)),
                            Box::new(t_res_prime),
                        ),
                    )
                }
            }
        }
        _ => ret(ctx, t.clone()),
    }
}

/// `terminationRefinement`: if argument `arg_name` of
/// type `t_arg` is recursible, return its strict and non-strict termination
/// refinements, otherwise `None`.
fn termination_refinement(
    env: &Rc<Environment>,
    arg_name: &String,
    t_arg: &RType,
) -> Option<(Formula, Formula)> {
    match t_arg {
        TypeSkeleton::ScalarT(BaseType::IntT, _) => {
            let strict = and(ge(val_int(), int_lit(0)), lt(val_int(), int_var(arg_name)));
            let nonstrict = and(ge(val_int(), int_lit(0)), le(val_int(), int_var(arg_name)));
            Some((strict, nonstrict))
        }
        TypeSkeleton::ScalarT(BaseType::DatatypeT(name, ..), _) => {
            let m_name = env.datatypes.get(name)?.wf_metric.clone()?;
            let metric = |x: Formula| Formula::Pred(Box::new(Sort::IntS), m_name.clone(), vec![x]);
            let arg_sort = to_sort(&base_type_of(t_arg));
            let val = Formula::Var(Box::new(arg_sort.clone()), VALUE_VAR_NAME.to_string());
            let arg = Formula::Var(Box::new(arg_sort), arg_name.clone());
            let strict = and(
                ge(metric(val.clone()), int_lit(0)),
                lt(metric(val.clone()), metric(arg.clone())),
            );
            let nonstrict = and(
                ge(metric(val.clone()), int_lit(0)),
                le(metric(val), metric(arg)),
            );
            Some((strict, nonstrict))
        }
        _ => None,
    }
}

/// `reconstructI`: reconstruct unknown types and terms
/// in a judgment `env` |- `impl` :: `t` where `impl` is a (possibly)
/// introduction term (top-down phase of bidirectional reconstruction).
fn reconstruct_i(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    t: &RType,
    impl_: &UProgram,
) -> Step<RProgram> {
    match &impl_.type_of {
        TypeSkeleton::AnyT => reconstruct_i_prime(ctx, env, t, &impl_.content),
        t_a => {
            let t_prime2 = try_step!(check_annotation(ctx, env, t, t_a, &impl_.content));
            reconstruct_i_prime(ctx, env, &t_prime2, &impl_.content)
        }
    }
}

#[allow(clippy::too_many_lines)]
fn reconstruct_i_prime(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    t: &RType,
    p: &BareProgram<RType>,
) -> Step<RProgram> {
    match p {
        BareProgram::PErr => generate_error(ctx, env),
        BareProgram::PHole => {
            mplus(
                ctx,
                Rc::new({
                    let env = env.clone();
                    move |ctx| generate_error(ctx, &env)
                }),
                Rc::new({
                    let env = env.clone();
                    let t = t.clone();
                    move |ctx| generate_i(ctx, &env, &t)
                }),
            )
        }
        BareProgram::PLet(x, i_def, i_body) if matches!(i_def.content, BareProgram::PFun(..)) => {
            Rc::make_mut(&mut ctx.state.lambda_lets)
                .insert(x.clone(), (env.clone(), (**i_def).clone()));
            let env = env.clone();
            let wrap: Rc<dyn Fn(&RProgram) -> RProgram> = {
                let x = x.clone();
                let t = t.clone();
                Rc::new(move |p| {
                    RProgram {
                        content: BareProgram::PLet(
                            x.clone(),
                            Box::new(u_hole()),
                            Box::new(p.clone()),
                        ),
                        type_of: t.clone(),
                    }
                })
            };
            let p_body = try_step!(in_context(ctx, wrap.clone(), |ctx| {
                reconstruct_i(ctx, &env, t, i_body)
            }));
            ret(ctx, wrap(&p_body))
        }
        _ => {
            match t {
                TypeSkeleton::LetT(x, t_def, t_body) => {
                    let env_prime = Rc::new(add_variable(x, t_def, env));
                    reconstruct_i_prime(ctx, &env_prime, t_body, p)
                }
                TypeSkeleton::FunctionT(_, t_arg, t_res) => {
                    match p {
                        BareProgram::PFun(y, impl_body) => {
                            let wrap: Rc<dyn Fn(&RProgram) -> RProgram> = {
                                let y = y.clone();
                                let t = t.clone();
                                Rc::new(move |p| {
                                    RProgram {
                                        content: BareProgram::PFun(y.clone(), Box::new(p.clone())),
                                        type_of: t.clone(),
                                    }
                                })
                            };
                            let t_arg = (**t_arg).clone();
                            let t_res = (**t_res).clone();
                            let env2 = Rc::new(unfold_all_variables(&add_variable(y, &t_arg, env)));
                            let p_body = try_step!(in_context(ctx, wrap.clone(), |ctx| {
                                reconstruct_i(ctx, &env2, &t_res, impl_body)
                            }));
                            ret(ctx, wrap(&p_body))
                        }
                        BareProgram::PSymbol(f) => {
                            let fun = try_step!(eta_expand(ctx, t, f));
                            reconstruct_i_prime(ctx, env, t, &fun.content)
                        }
                        _ => {
                            throw_error(
                                ctx,
                                &ErrorMessage::new(
                                    ErrorKind::TypeError,
                                    ctx.reader.params.source_pos.clone(),
                                    text(&format!(
                                        "Cannot assign function type {} to non-lambda term {}",
                                        pretty_type(t),
                                        pretty_pgm(&untyped(p.clone())),
                                    )),
                                ),
                            )
                        }
                    }
                }
                TypeSkeleton::ScalarT(..) => {
                    match p {
                        BareProgram::PFun(..) => {
                            throw_error(
                                ctx,
                                &ErrorMessage::new(
                                    ErrorKind::TypeError,
                                    ctx.reader.params.source_pos.clone(),
                                    text(&format!(
                                        "Cannot assign non-function type {} to lambda term {}",
                                        pretty_type(t),
                                        pretty_pgm(&untyped(p.clone())),
                                    )),
                                ),
                            )
                        }
                        BareProgram::PLet(x, i_def, i_body) => {
                            let wrap_def: Rc<dyn Fn(&RProgram) -> RProgram> = {
                                let x = x.clone();
                                let t = t.clone();
                                Rc::new(move |p| {
                                    RProgram {
                                        content: BareProgram::PLet(
                                            x.clone(),
                                            Box::new(p.clone()),
                                            Box::new(RProgram {
                                                content: BareProgram::PHole,
                                                type_of: t.clone(),
                                            }),
                                        ),
                                        type_of: t.clone(),
                                    }
                                })
                            };
                            let p_def = try_step!(in_context(ctx, wrap_def, |ctx| {
                                reconstruct_e_top_level(ctx, env, &TypeSkeleton::AnyT, i_def)
                            }));
                            let (env_prime, t_def) = embed_context(env, &p_def.type_of);
                            let wrap_body: Rc<dyn Fn(&RProgram) -> RProgram> = {
                                let x = x.clone();
                                let t = t.clone();
                                let p_def = p_def.clone();
                                Rc::new(move |p| {
                                    RProgram {
                                        content: BareProgram::PLet(
                                            x.clone(),
                                            Box::new(p_def.clone()),
                                            Box::new(p.clone()),
                                        ),
                                        type_of: t.clone(),
                                    }
                                })
                            };
                            let env_prime2 = Rc::new(add_variable(x, &t_def, &env_prime));
                            let p_body = try_step!(in_context(ctx, wrap_body, |ctx| {
                                reconstruct_i(ctx, &env_prime2, t, i_body)
                            }));
                            ret(ctx, RProgram {
                                content: BareProgram::PLet(
                                    x.clone(),
                                    Box::new(p_def),
                                    Box::new(p_body),
                                ),
                                type_of: t.clone(),
                            })
                        }
                        BareProgram::PIf(i_cond, i_then, i_else)
                            if matches!(i_cond.content, BareProgram::PHole)
                                && i_cond.type_of == TypeSkeleton::AnyT =>
                        {
                            let c_unknown =
                                Formula::Unknown(BTreeMap::new(), try_step!(fresh_id(ctx, "C")));
                            add_constraint(
                                ctx,
                                Constraint::WellFormedCond(env.clone(), c_unknown.clone()),
                            );
                            let env_then = Rc::new(add_assumption(c_unknown.clone(), env));
                            let wrap_then: Rc<dyn Fn(&RProgram) -> RProgram> = {
                                let t = t.clone();
                                Rc::new(move |p| {
                                    RProgram {
                                        content: BareProgram::PIf(
                                            Box::new(RProgram {
                                                content: BareProgram::PHole,
                                                type_of: bool_all(),
                                            }),
                                            Box::new(p.clone()),
                                            Box::new(RProgram {
                                                content: BareProgram::PHole,
                                                type_of: t.clone(),
                                            }),
                                        ),
                                        type_of: t.clone(),
                                    }
                                })
                            };
                            let p_then = try_step!(in_context(ctx, wrap_then, |ctx| {
                                reconstruct_i(ctx, &env_then, t, i_then)
                            }));
                            let cond = conjunction(&try_step!(current_valuation(ctx, &c_unknown)));
                            let wrap_cond: Rc<dyn Fn(&RProgram) -> RProgram> = {
                                let t = t.clone();
                                Rc::new(move |p| {
                                    RProgram {
                                        content: BareProgram::PIf(
                                            Box::new(p.clone()),
                                            Box::new(u_hole()),
                                            Box::new(u_hole()),
                                        ),
                                        type_of: t.clone(),
                                    }
                                })
                            };
                            let p_cond = try_step!(in_context(ctx, wrap_cond, |ctx| {
                                generate_condition(ctx, env, &cond)
                            }));
                            let p_cond_c = p_cond.clone();
                            let p_then_c = p_then.clone();
                            let env_c = env.clone();
                            let cond_c = cond.clone();
                            let t_c = t.clone();
                            let p_else = try_step!(optional_in_partial(ctx, t, {
                                move |ctx| {
                                    let wrap_else: Rc<dyn Fn(&RProgram) -> RProgram> = {
                                        let t = t_c.clone();
                                        Rc::new(move |p| {
                                            RProgram {
                                                content: BareProgram::PIf(
                                                    Box::new(p_cond_c.clone()),
                                                    Box::new(p_then_c.clone()),
                                                    Box::new(p.clone()),
                                                ),
                                                type_of: t.clone(),
                                            }
                                        })
                                    };
                                    in_context(ctx, wrap_else, |ctx| {
                                        let env_else =
                                            Rc::new(add_assumption(fnot(cond_c.clone()), &env_c));
                                        reconstruct_i(ctx, &env_else, &t_c, i_else)
                                    })
                                }
                            }));
                            ret(ctx, RProgram {
                                content: BareProgram::PIf(
                                    Box::new(p_cond),
                                    Box::new(p_then),
                                    Box::new(p_else),
                                ),
                                type_of: t.clone(),
                            })
                        }
                        BareProgram::PIf(i_cond, i_then, i_else) => {
                            let wrap_cond: Rc<dyn Fn(&RProgram) -> RProgram> = {
                                let t = t.clone();
                                Rc::new(move |p| {
                                    RProgram {
                                        content: BareProgram::PIf(
                                            Box::new(p.clone()),
                                            Box::new(RProgram {
                                                content: BareProgram::PHole,
                                                type_of: t.clone(),
                                            }),
                                            Box::new(RProgram {
                                                content: BareProgram::PHole,
                                                type_of: t.clone(),
                                            }),
                                        ),
                                        type_of: t.clone(),
                                    }
                                })
                            };
                            let p_cond = try_step!(in_context(ctx, wrap_cond, |ctx| {
                                reconstruct_e_top_level(
                                    ctx,
                                    env,
                                    &TypeSkeleton::ScalarT(BaseType::BoolT, crate::logic::ftrue()),
                                    i_cond,
                                )
                            }));
                            let (env_prime, cond) = match embed_context(env, &p_cond.type_of) {
                                (env_prime, TypeSkeleton::ScalarT(BaseType::BoolT, cond)) => {
                                    (env_prime, cond)
                                }
                                _ => unreachable!("reconstructI': non-bool condition"),
                            };
                            let sub =
                                |v: Formula| Substitution::from([(VALUE_VAR_NAME.to_string(), v)]);
                            let wrap_then: Rc<dyn Fn(&RProgram) -> RProgram> = {
                                let t = t.clone();
                                let p_cond = p_cond.clone();
                                Rc::new(move |p| {
                                    RProgram {
                                        content: BareProgram::PIf(
                                            Box::new(p_cond.clone()),
                                            Box::new(p.clone()),
                                            Box::new(RProgram {
                                                content: BareProgram::PHole,
                                                type_of: t.clone(),
                                            }),
                                        ),
                                        type_of: t.clone(),
                                    }
                                })
                            };
                            let env_then = Rc::new(add_assumption(
                                substitute(&sub(crate::logic::ftrue()), cond.clone()),
                                &env_prime,
                            ));
                            let p_then = try_step!(in_context(ctx, wrap_then, |ctx| {
                                reconstruct_i(ctx, &env_then, t, i_then)
                            }));
                            let wrap_else: Rc<dyn Fn(&RProgram) -> RProgram> = {
                                let t = t.clone();
                                let p_cond = p_cond.clone();
                                let p_then = p_then.clone();
                                Rc::new(move |p| {
                                    RProgram {
                                        content: BareProgram::PIf(
                                            Box::new(p_cond.clone()),
                                            Box::new(p_then.clone()),
                                            Box::new(p.clone()),
                                        ),
                                        type_of: t.clone(),
                                    }
                                })
                            };
                            let env_else = Rc::new(add_assumption(
                                substitute(&sub(crate::logic::ffalse()), cond),
                                &env_prime,
                            ));
                            let p_else = try_step!(in_context(ctx, wrap_else, |ctx| {
                                reconstruct_i(ctx, &env_else, t, i_else)
                            }));
                            ret(ctx, RProgram {
                                content: BareProgram::PIf(
                                    Box::new(p_cond),
                                    Box::new(p_then),
                                    Box::new(p_else),
                                ),
                                type_of: t.clone(),
                            })
                        }
                        BareProgram::PMatch(i_scr, i_cases) => {
                            let cons = try_step!(check_cases(ctx, None, i_cases, env));
                            let cons_types: Vec<RType> =
                                cons.iter().map(|(_, t)| t.clone()).collect();
                            let scr_t = refine_top(env, &shape(&last_type(&cons_types[0])));
                            let t = t.clone();
                            let wrap_scr: Rc<dyn Fn(&RProgram) -> RProgram> = {
                                let t = t.clone();
                                Rc::new(move |p| {
                                    RProgram {
                                        content: BareProgram::PMatch(
                                            Box::new(p.clone()),
                                            Vec::new(),
                                        ),
                                        type_of: t.clone(),
                                    }
                                })
                            };
                            let p_scrutinee = try_step!(in_context(ctx, wrap_scr, |ctx| {
                                reconstruct_e_top_level(ctx, env, &scr_t, i_scr)
                            }));
                            let env_prime = embed_context(env, &p_scrutinee.type_of).0;
                            let scrutinee_symbols = symbol_list(&p_scrutinee);
                            let is_good_scrutinee = scrutinee_symbols
                                .first()
                                .is_none_or(|h| !cons.iter().any(|(c, _)| c == h))
                                && scrutinee_symbols.iter().any(|x| !env.constants.contains(x));
                            if !is_good_scrutinee {
                                return throw_error(
                                    ctx,
                                    &ErrorMessage::new(
                                        ErrorKind::TypeError,
                                        ctx.reader.params.source_pos.clone(),
                                        text(&format!(
                                            "Match scrutinee {} is constant",
                                            pretty_pgm(&p_scrutinee),
                                        )),
                                    ),
                                );
                            }
                            let (env_prime2, x) = try_step!(to_var(
                                ctx,
                                &Rc::new(add_scrutinee(p_scrutinee.clone(), &env_prime)),
                                &p_scrutinee,
                            ));
                            let mut p_cases = Vec::new();
                            for (i_case, cons_t) in i_cases.iter().zip(&cons_types) {
                                let c = try_step!(reconstruct_case(
                                    ctx,
                                    &env_prime2,
                                    &x,
                                    &p_scrutinee,
                                    &t,
                                    i_case,
                                    cons_t,
                                ));
                                p_cases.push(c);
                            }
                            ret(ctx, RProgram {
                                content: BareProgram::PMatch(Box::new(p_scrutinee), p_cases),
                                type_of: t,
                            })
                        }
                        _ => reconstruct_e_top_level(ctx, env, t, &untyped(p.clone())),
                    }
                }
                TypeSkeleton::AnyT => reconstruct_e_top_level(ctx, env, t, &untyped(p.clone())),
            }
        }
    }
}

/// `checkCases`: check that all constructors are known
/// and belong to the same datatype; return (name, instantiated type) pairs.
fn check_cases(
    ctx: &mut ExplorerCtx<'_>,
    m_name: Option<&String>,
    cases: &[Case<RType>],
    env: &Rc<Environment>,
) -> Step<Vec<(String, RType)>> {
    let Some(first) = cases.first() else {
        return ret(ctx, Vec::new());
    };
    let cons_name = &first.constructor;
    let all_syms = all_symbols(env);
    let cons_sch = match all_syms.get(cons_name) {
        None => {
            return throw_error(
                ctx,
                &ErrorMessage::new(
                    ErrorKind::TypeError,
                    ctx.reader.params.source_pos.clone(),
                    text(&format!("Not in scope: data constructor {cons_name}")),
                ),
            );
        }
        Some(sch) => sch,
    };
    let cons_t = try_step!(instantiate(ctx, env, cons_sch, true, &first.arg_names));
    match &last_type(&cons_t) {
        TypeSkeleton::ScalarT(BaseType::DatatypeT(dt_name, ..), _) => {
            if let Some(name) = m_name
                && name != dt_name
            {
                return throw_error(
                    ctx,
                    &ErrorMessage::new(
                        ErrorKind::TypeError,
                        ctx.reader.params.source_pos.clone(),
                        text(&format!(
                            "Expected constructor of datatype {name} and got constructor {cons_name} of datatype {dt_name}",
                        )),
                    ),
                );
            }
            let expected = arity(&to_monotype(cons_sch));
            if expected != first.arg_names.len() {
                return throw_error(
                    ctx,
                    &ErrorMessage::new(
                        ErrorKind::TypeError,
                        ctx.reader.params.source_pos.clone(),
                        text(&format!(
                            "Constructor {} expected {} binder(s) and got {}",
                            cons_name,
                            expected,
                            first.arg_names.len(),
                        )),
                    ),
                );
            }
            let mut v = vec![(cons_name.clone(), cons_t)];
            v.extend(try_step!(check_cases(ctx, Some(dt_name), &cases[1..], env)));
            ret(ctx, v)
        }
        _ => {
            throw_error(
                ctx,
                &ErrorMessage::new(
                    ErrorKind::TypeError,
                    ctx.reader.params.source_pos.clone(),
                    text(&format!("Not in scope: data constructor {cons_name}")),
                ),
            )
        }
    }
}

/// `reconstructCase`.
fn reconstruct_case(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    scr_var: &Formula,
    p_scrutinee: &RProgram,
    t: &RType,
    i_case: &Case<RType>,
    cons_t: &RType,
) -> Step<Case<RType>> {
    cut(ctx, move |ctx| {
        try_step!(run_in_solver(ctx, |s| {
            match_cons_type(s, &last_type(cons_t), &p_scrutinee.type_of)
        }));
        let cons_t_a = try_step!(run_in_solver(ctx, |s| Ok(current_assignment(s, cons_t))));
        let (syms, ass) = try_step!(case_symbols(
            ctx,
            env,
            scr_var,
            &i_case.arg_names,
            &cons_t_a
        ));
        let mut case_env: Rc<Environment> = Rc::new(add_assumption(ass, env));
        for (sym, t_sym) in syms {
            case_env = Rc::new(add_variable(&sym, &t_sym, &case_env));
        }
        let depth = ctx.reader.params.match_depth;
        let t = t.clone();
        let p_scrutinee = p_scrutinee.clone();
        let i_case = i_case.clone();
        let i_case_wrap = i_case.clone();
        let t_wrap = t.clone();
        let p_scrutinee_wrap = p_scrutinee;
        local(
            ctx,
            move |p| {
                ExplorerParams {
                    match_depth: depth - 1,
                    ..p.clone()
                }
            },
            move |ctx| {
                let wrap: Rc<dyn Fn(&RProgram) -> RProgram> = Rc::new(move |p| {
                    RProgram {
                        content: BareProgram::PMatch(Box::new(p_scrutinee_wrap.clone()), vec![
                            Case {
                                constructor: i_case_wrap.constructor.clone(),
                                arg_names: i_case_wrap.arg_names.clone(),
                                expr: p.clone(),
                            },
                        ]),
                        type_of: t_wrap.clone(),
                    }
                });
                let p_case_expr = try_step!(in_context(ctx, wrap, |ctx| {
                    reconstruct_i(ctx, &case_env, &t, &i_case.expr)
                },));
                ret(ctx, Case {
                    constructor: i_case.constructor.clone(),
                    arg_names: i_case.arg_names.clone(),
                    expr: p_case_expr,
                })
            },
        )
    })
}

/// `reconstructETopLevel`.
fn reconstruct_e_top_level(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    t: &RType,
    impl_: &UProgram,
) -> Step<RProgram> {
    let p_term = try_step!(reconstruct_e(ctx, env, t, impl_));
    try_step!(generate_aux_goals(ctx));
    let p_typ = try_step!(run_in_solver(ctx, |s| {
        Ok(current_assignment(s, &p_term.type_of))
    }));
    ret(ctx, RProgram {
        content: p_term.content,
        type_of: p_typ,
    })
}

/// `reconstructE`: reconstruct unknown types and terms
/// in a judgment `env` |- `impl` :: `t` where `impl` is an elimination term
/// (bottom-up phase of bidirectional reconstruction).
fn reconstruct_e(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    t: &RType,
    impl_: &UProgram,
) -> Step<RProgram> {
    match &impl_.type_of {
        TypeSkeleton::AnyT => reconstruct_e_prime(ctx, env, t, &impl_.content),
        t_a => {
            let t_prime2 = try_step!(check_annotation(ctx, env, t, t_a, &impl_.content));
            reconstruct_e_prime(ctx, env, &t_prime2, &impl_.content)
        }
    }
}

#[allow(clippy::too_many_lines)]
fn reconstruct_e_prime(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    typ: &RType,
    p: &BareProgram<RType>,
) -> Step<RProgram> {
    match p {
        BareProgram::PHole => {
            let d = ctx.reader.params.e_guess_depth;
            generate_e_up_to(ctx, env, typ, d)
        }
        BareProgram::PSymbol(name) => {
            let sch = match lookup_symbol(name, arity(typ), has_set(typ), env) {
                None => {
                    return throw_error(
                        ctx,
                        &ErrorMessage::new(
                            ErrorKind::TypeError,
                            ctx.reader.params.source_pos.clone(),
                            text(&format!("Not in scope: {name}")),
                        ),
                    );
                }
                Some(sch) => sch,
            };
            let t = try_step!(symbol_type(ctx, env, name, &sch));
            let p_ = RProgram {
                content: BareProgram::PSymbol(name.clone()),
                type_of: t,
            };
            *Rc::make_mut(&mut ctx.state.symbol_use_count)
                .entry(name.clone())
                .or_insert(0) += 1;
            if let Some(sc) = env.shape_constraints.get(name) {
                add_constraint(
                    ctx,
                    Constraint::Subtype(
                        env.clone(),
                        refine_bot(env, &shape(&p_.type_of)),
                        refine_top(env, sc),
                        false,
                        String::new(),
                    ),
                );
            }
            try_step!(check_e(ctx, env, typ, &p_));
            ret(ctx, p_)
        }
        BareProgram::PApp(i_fun, i_arg) => {
            let x = try_step!(fresh_var(ctx, env, "x"));
            let wrap_fun: Rc<dyn Fn(&RProgram) -> RProgram> = {
                let typ = typ.clone();
                Rc::new(move |p| {
                    RProgram {
                        content: BareProgram::PApp(Box::new(p.clone()), Box::new(u_hole())),
                        type_of: typ.clone(),
                    }
                })
            };
            let p_fun = try_step!(in_context(ctx, wrap_fun, |ctx| {
                reconstruct_e(
                    ctx,
                    env,
                    &TypeSkeleton::FunctionT(
                        x.clone(),
                        Box::new(TypeSkeleton::AnyT),
                        Box::new(typ.clone()),
                    ),
                    i_fun,
                )
            }));
            let (x, t_arg, t_res) = match &p_fun.type_of {
                TypeSkeleton::FunctionT(x, t_arg, t_res) => {
                    ((*x).clone(), (**t_arg).clone(), (**t_res).clone())
                }
                _ => unreachable!("reconstructE': non-function application"),
            };
            let p_app = if is_function_type(&t_arg) {
                let d = ctx.reader.params.aux_depth;
                let p_arg = try_step!(generate_ho_arg(ctx, env, &t_arg, i_arg, d - 1));
                RProgram {
                    content: BareProgram::PApp(Box::new(p_fun), Box::new(p_arg)),
                    type_of: t_res,
                }
            } else {
                let wrap_arg: Rc<dyn Fn(&RProgram) -> RProgram> = {
                    let typ = typ.clone();
                    let p_fun = p_fun.clone();
                    Rc::new(move |p| {
                        RProgram {
                            content: BareProgram::PApp(
                                Box::new(p_fun.clone()),
                                Box::new(p.clone()),
                            ),
                            type_of: typ.clone(),
                        }
                    })
                };
                let p_arg = try_step!(in_context(ctx, wrap_arg, |ctx| {
                    reconstruct_e(ctx, env, &t_arg, i_arg)
                }));
                let t_res_prime = app_type(env, &p_arg, &x, &t_res);
                RProgram {
                    content: BareProgram::PApp(Box::new(p_fun), Box::new(p_arg)),
                    type_of: t_res_prime,
                }
            };
            try_step!(check_e(ctx, env, typ, &p_app));
            ret(ctx, p_app)
        }
        _ => {
            throw_error(
                ctx,
                &ErrorMessage::new(
                    ErrorKind::TypeError,
                    no_pos(),
                    text(&format!(
                        "Expected application term of type {} and got {}",
                        pretty_type(typ),
                        pretty_pgm(&untyped(p.clone())),
                    )),
                ),
            )
        }
    }
}

/// `generateHOArg`: higher-order argument: its value is
/// not required for the function type, so enqueue an auxiliary goal.
fn generate_ho_arg(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    t_arg: &RType,
    i_arg: &UProgram,
    d: usize,
) -> Step<RProgram> {
    if let BareProgram::PSymbol(f) = &i_arg.content {
        match ctx.state.lambda_lets.get(f) {
            None => {
                let impl_ = try_step!(eta_expand(ctx, t_arg, f));
                let _ = try_step!(enqueue_goal(ctx, env, t_arg, &impl_, d));
                ret(ctx, i_arg.clone())
            }
            Some((env_prime, def)) => {
                Rc::make_mut(&mut ctx.state.aux_goals).insert(0, Goal {
                    g_name: f.clone(),
                    g_environment: env_prime.clone(),
                    g_spec: SchemaSkeleton::Monotype(t_arg.clone()),
                    g_impl: def.clone(),
                    g_depth: d,
                    g_source_pos: no_pos(),
                    g_synthesize: true,
                });
                ret(ctx, i_arg.clone())
            }
        }
    } else {
        let _ = try_step!(enqueue_goal(ctx, env, t_arg, i_arg, d));
        ret(ctx, i_arg.clone())
    }
}

/// `checkAnnotation`: if user annotation `t_a` for
/// program `p` is a subtype of the goal type `t`, return resolved `t_a`,
/// otherwise fail.
fn check_annotation(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    t: &RType,
    t_a: &RType,
    p: &BareProgram<RType>,
) -> Step<RType> {
    let tass = &ctx.state.typing_state.type_assignment;
    let t_prime2 = match resolve_refined_type(&type_substitute_env(tass, env), t_a) {
        Err(err) => return throw_error(ctx, &err),
        Ok(t_prime2) => t_prime2,
    };
    let ctx_p = ctx.reader.context.clone();
    add_constraint(
        ctx,
        Constraint::Subtype(
            env.clone(),
            t_prime2.clone(),
            t.clone(),
            true,
            String::new(),
        ),
    );
    let f_t = try_step!(run_in_solver(ctx, |s| Ok(finalize_type(s, t))));
    let f_t_prime2 = try_step!(run_in_solver(ctx, |s| Ok(finalize_type(s, &t_prime2))));
    let pos = ctx.reader.params.source_pos.clone();
    ctx.state.typing_mut().error_context = (
        pos,
        crate::pretty::soft_break(
            crate::pretty::soft_break(
                crate::pretty::soft_break(
                    crate::pretty::soft_break(
                        text("when checking consistency of type annotation"),
                        pretty_type_doc(&f_t_prime2),
                    ),
                    text("with"),
                ),
                pretty_type_doc(&f_t),
            ),
            vsp(
                text("in"),
                pretty_program(&ctx_p(&RProgram {
                    content: p.clone(),
                    type_of: t_prime2.clone(),
                })),
            ),
        ),
    );
    try_step!(run_in_solver(ctx, solve_type_constraints));
    ctx.state.typing_mut().error_context = (no_pos(), crate::pretty::empty());
    let tass_prime = ctx.state.typing_state.type_assignment.clone();
    ret(
        ctx,
        intersection(
            &|x| is_bound(env, x),
            &t_prime2,
            &type_substitute(&tass_prime, t),
        ),
    )
}

/// `etaExpand`: for a symbol `f` of a function type `t`,
/// the term `\X0 . ... \XN . f X0 ... XN` where `f` is fully applied.
fn eta_expand(ctx: &mut ExplorerCtx<'_>, t: &RType, f: &String) -> Step<UProgram> {
    let n = arity(t);
    let mut args = Vec::new();
    for _ in 0..n {
        args.push(try_step!(fresh_id(ctx, "X")));
    }
    let mut body = untyped(BareProgram::PSymbol(f.clone()));
    for a in &args {
        body = untyped(BareProgram::PApp(
            Box::new(body),
            Box::new(untyped(BareProgram::PSymbol(a.clone()))),
        ));
    }
    for a in args.into_iter().rev() {
        body = untyped(BareProgram::PFun(a, Box::new(body)));
    }
    ret(ctx, body)
}

/// `insertAuxSolutions`: insert solutions stored in
/// `p_auxs` indexed by names of auxiliary goals `x` into `p_main`.
fn insert_aux_solutions(p_auxs: &BTreeMap<String, RProgram>, p: &RProgram) -> RProgram {
    let body = match &p.content {
        BareProgram::PLet(y, def, body) => {
            match p_auxs.get(y) {
                None => {
                    BareProgram::PLet(
                        y.clone(),
                        Box::new(insert_aux_solutions(p_auxs, def)),
                        Box::new(insert_aux_solutions(p_auxs, body)),
                    )
                }
                Some(p_aux) => {
                    let mut rest = p_auxs.clone();
                    rest.remove(y);
                    BareProgram::PLet(
                        y.clone(),
                        Box::new(p_aux.clone()),
                        Box::new(insert_aux_solutions(&rest, body)),
                    )
                }
            }
        }
        BareProgram::PSymbol(y) => {
            match p_auxs.get(y) {
                None => p.content.clone(),
                Some(p_aux) => p_aux.content.clone(),
            }
        }
        BareProgram::PApp(f, a) => {
            BareProgram::PApp(
                Box::new(insert_aux_solutions(p_auxs, f)),
                Box::new(insert_aux_solutions(p_auxs, a)),
            )
        }
        BareProgram::PFun(y, b) => {
            BareProgram::PFun(y.clone(), Box::new(insert_aux_solutions(p_auxs, b)))
        }
        BareProgram::PIf(c, a, b) => {
            BareProgram::PIf(
                Box::new(insert_aux_solutions(p_auxs, c)),
                Box::new(insert_aux_solutions(p_auxs, a)),
                Box::new(insert_aux_solutions(p_auxs, b)),
            )
        }
        BareProgram::PMatch(s, cases) => {
            BareProgram::PMatch(
                Box::new(insert_aux_solutions(p_auxs, s)),
                cases
                    .iter()
                    .map(|c| {
                        Case {
                            constructor: c.constructor.clone(),
                            arg_names: c.arg_names.clone(),
                            expr: insert_aux_solutions(p_auxs, &c.expr),
                        }
                    })
                    .collect(),
            )
        }
        BareProgram::PFix(ys, b) => {
            BareProgram::PFix(ys.clone(), Box::new(insert_aux_solutions(p_auxs, b)))
        }
        other => other.clone(),
    };
    RProgram {
        content: body,
        type_of: p.type_of.clone(),
    }
}

// ─────────────────────── pretty helpers (error messages)
// ───────────────────────

fn pretty_pgm(p: &RProgram) -> String {
    let mut s = String::new();
    pretty_pgm_into(p, &mut s);
    s
}

fn pretty_pgm_into(p: &RProgram, s: &mut String) {
    match &p.content {
        BareProgram::PSymbol(x) => s.push_str(x),
        BareProgram::PApp(f, a) => {
            s.push('(');
            pretty_pgm_into(f, s);
            s.push(' ');
            pretty_pgm_into(a, s);
            s.push(')');
        }
        BareProgram::PFun(x, b) => {
            s.push('\\');
            s.push_str(x);
            s.push_str(". ");
            pretty_pgm_into(b, s);
        }
        BareProgram::PIf(c, t, e) => {
            s.push_str("if ");
            pretty_pgm_into(c, s);
            s.push_str(" then ");
            pretty_pgm_into(t, s);
            s.push_str(" else ");
            pretty_pgm_into(e, s);
        }
        BareProgram::PMatch(scr, cases) => {
            s.push_str("match ");
            pretty_pgm_into(scr, s);
            for case in cases {
                s.push_str(" | ");
                s.push_str(&case.constructor);
                s.push(' ');
                s.push_str(&case.arg_names.join(" "));
                s.push_str(" -> ");
                pretty_pgm_into(&case.expr, s);
            }
        }
        BareProgram::PFix(args, body) => {
            s.push_str("fix ");
            s.push_str(&args.join(" "));
            s.push_str(". ");
            pretty_pgm_into(body, s);
        }
        BareProgram::PLet(x, def, body) => {
            s.push_str("let ");
            s.push_str(x);
            s.push_str(" = ");
            pretty_pgm_into(def, s);
            s.push_str(" in ");
            pretty_pgm_into(body, s);
        }
        BareProgram::PHole => s.push_str("??"),
        BareProgram::PErr => s.push_str("Error"),
    }
}

fn pretty_type(t: &RType) -> String {
    match t {
        TypeSkeleton::ScalarT(BaseType::BoolT, fml) => {
            format!("bool{{{{{}}}}}", pretty_fml(fml))
        }
        TypeSkeleton::ScalarT(BaseType::IntT, fml) => format!("int{{{{{}}}}}", pretty_fml(fml)),
        TypeSkeleton::ScalarT(BaseType::DatatypeT(name, args, _fmls), _) => {
            if args.is_empty() {
                name.clone()
            } else {
                let args: Vec<String> = args.iter().map(pretty_type).collect();
                format!("{} {}", name, args.join(" "))
            }
        }
        TypeSkeleton::ScalarT(BaseType::TypeVarT(_, a), _) => (*a).clone(),
        TypeSkeleton::FunctionT(_x, t_arg, t_res) => {
            format!("{} -> {}", pretty_type(t_arg), pretty_type(t_res))
        }
        TypeSkeleton::LetT(x, t_def, t_body) => {
            format!(
                "let {} = {} in {}",
                x,
                pretty_type(t_def),
                pretty_type(t_body)
            )
        }
        TypeSkeleton::AnyT => "?".to_string(),
    }
}

fn pretty_fml(f: &Formula) -> String {
    let mut s = String::new();
    let _ = write_fml(f, &mut s);
    s
}

fn write_fml(f: &Formula, s: &mut String) -> std::fmt::Result {
    use std::fmt::Write;
    match f {
        Formula::BoolLit(c) => write!(s, "{c}"),
        Formula::IntLit(i) => write!(s, "{i}"),
        Formula::SetLit(_, elems) => {
            let es: Vec<String> = elems.iter().map(pretty_fml).collect();
            write!(s, "{{{}}}", es.join(", "))
        }
        Formula::Var(_, v) => write!(s, "{v}"),
        Formula::Unknown(_, u) => write!(s, "{u}"),
        Formula::Unary(op, x) => {
            let op = match op {
                UnOp::Not => "!",
                UnOp::Neg => "-",
            };
            write!(s, "({}{})", op, pretty_fml(x))
        }
        Formula::Binary(op, l, r) => {
            s.push('(');
            write_fml(l, s)?;
            s.push(' ');
            s.push_str(bin_op_str(op));
            s.push(' ');
            write_fml(r, s)?;
            s.push(')');
            Ok(())
        }
        Formula::Ite(c, a, b) => {
            write!(
                s,
                "(ite {} {} {})",
                pretty_fml(c),
                pretty_fml(a),
                pretty_fml(b),
            )
        }
        Formula::Pred(_, name, args) => {
            write!(s, "{name}")?;
            let args: Vec<String> = args.iter().map(pretty_fml).collect();
            write!(s, "({})", args.join(", "))
        }
        Formula::Cons(_, name, args) => {
            write!(s, "{name}")?;
            let args: Vec<String> = args.iter().map(pretty_fml).collect();
            write!(s, "({})", args.join(", "))
        }
        Formula::All(x, body) => {
            write!(s, "forall {} . {}", pretty_fml(x), pretty_fml(body))
        }
    }
}

const fn bin_op_str(op: &crate::logic::BinOp) -> &'static str {
    use crate::logic::BinOp;
    match op {
        BinOp::Times => "*",
        BinOp::Plus => "+",
        BinOp::Minus => "-",
        BinOp::Eq => "==",
        BinOp::Neq => "!=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::And => "&&",
        BinOp::Or => "||",
        BinOp::Implies => "=>",
        BinOp::Iff => "<=>",
        BinOp::Union => "U",
        BinOp::Intersect => "cap",
        BinOp::Diff => "\\\\",
        BinOp::Member => "in",
        BinOp::Subset => "subseteq",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn termination_refinement_int() {
        let env = crate::program::empty_env();
        let t = TypeSkeleton::ScalarT(BaseType::IntT, crate::logic::ffalse());
        let (strict, nonstrict) =
            termination_refinement(&Rc::new(env), &"x".to_string(), &t).unwrap();
        assert_eq!(
            strict,
            and(ge(val_int(), int_lit(0)), lt(val_int(), int_var("x")))
        );
        assert_eq!(
            nonstrict,
            and(ge(val_int(), int_lit(0)), le(val_int(), int_var("x")))
        );
    }

    #[test]
    fn insert_aux_solutions_let_and_symbol() {
        let aux = RProgram {
            content: BareProgram::PSymbol("soln".to_string()),
            type_of: TypeSkeleton::AnyT,
        };
        let mut map = BTreeMap::new();
        map.insert("g".to_string(), aux.clone());
        let p = RProgram {
            content: BareProgram::PLet(
                "g".to_string(),
                Box::new(u_hole()),
                Box::new(RProgram {
                    content: BareProgram::PSymbol("g".to_string()),
                    type_of: TypeSkeleton::AnyT,
                }),
            ),
            type_of: TypeSkeleton::AnyT,
        };
        let out = insert_aux_solutions(&map, &p);
        match &out.content {
            BareProgram::PLet(y, def, body) => {
                assert_eq!(y, "g");
                assert_eq!(def.content, BareProgram::PSymbol("soln".to_string()));
                assert_eq!(body.content, BareProgram::PSymbol("g".to_string()));
            }
            _ => panic!("expected PLet"),
        }
    }
}

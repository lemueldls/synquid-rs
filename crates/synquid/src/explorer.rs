//! Program-space search (mirror of `Synquid.Explorer`).
//!
//! The reference computation is the monad stack
//! `StateT ExplorerState (ReaderT (ExplorerParams, TypingParams, Reconstructor)
//!   (LogicT (StateT PersistentState s)))` driven by `observeManyT 1`.
//! Per the plan we do not port a monad transformer stack:
//! - `ExplorerState` is threaded by value; every search step carries the
//!   snapshot to install before resuming (the `StateT` layer).
//! - `PersistentState` accumulates monotonically and is never rolled back (the
//!   outer `StateT PersistentState`).
//! - `LogicT` is emulated as an explicit stream of search steps: failure, or a
//!   value plus a suspension (state + reader snapshot + resume closure).
//!   `mplus` on such a stream is the reference's depth-first disjunction; `cut`
//!   (= `once`) truncates to the first result; `ifte` is `msplit t >>= maybe el
//!   (\(a, s) -> th a `mplus` (s >>= th . return))`.

use std::{
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

use crate::{
    cli::ExplorerParams,
    error::{ErrorKind, ErrorMessage, no_pos},
    horn_solver::FixPointSolver,
    logic::{
        BinOp, Formula, Sort, Substitution, VALUE_VAR_NAME, conjunction, conjuncts_of, de_brujns,
        eq, ffalse, fnot, ftrue, is_executable, sort_substitute, substitute, unknown_name,
        val_bool, valuation, vars_of,
    },
    pretty::{Doc, empty, pretty_program, pretty_type, program_node_count, soft_break, text, vsp},
    program::{
        BareProgram, Case, Constraint, Environment, Goal, Program, RProgram, add_assumption,
        add_let_bound, add_scrutinee, add_variable, all_symbols, bin_op_type, embed_context,
        error_program, fml_to_program, is_bound, is_hole, lookup_constructor, refine_bot,
        refine_top, symbol_as_formula, symbol_list, symbols_of, symbols_of_arity,
        type_substitute_env, u_hole, unfold_all_variables, untyped,
    },
    tc_solver::{
        TcSolver, TypingParams, TypingState, add_fixed_unknown, add_typing_constraint, all_scalars,
        current_assignment_tass, finalize_type_state, has_potential_scrutinees_tass,
        match_cons_type, run_tc_solver, set_unknown_recheck, solve_all_candidates,
        solve_type_constraints,
    },
    tokens::{bin_op_tokens, is_literal},
    types::{
        BaseType, RSchema, RType, SType, SchemaSkeleton, TypeSkeleton, any_datatype, arity,
        base_type_of, bool, bool_all, contextual, is_function_type, last_type, rename_var, shape,
        substitute_in_type, to_monotype, to_sort, type_substitute, type_substitute_pred,
        var_refinement, vart_all,
    },
    util::{Id, disjoint, mapped_compare, set_compare},
};

/// Type of programs with unknown types (`Program RType`).
type UProgram = crate::program::UProgram;

/// Recursive call-back into the type checker for auxiliary goals
/// (mirror of `Reconstructor s`).
pub type Reconstructor = Rc<dyn for<'x> Fn(&mut ExplorerCtx<'x>, &Goal) -> Step<RProgram>>;

/// A search computation packaged as a re-usable value (used for actions that
/// are stored, e.g. the `recheck` computations of `generateCase`).
pub type ExplorerFn<A> = Rc<dyn for<'x> Fn(&mut ExplorerCtx<'x>) -> Step<A>>;

/// A closure taking a context and an additional argument (used for the
/// per-scrutinee attempt of `generateMatch`).
type AttemptFn = Rc<dyn for<'x> Fn(&mut ExplorerCtx<'x>, RProgram) -> Step<RProgram>>;

/// Reader components of an exploration (mirror of the `ReaderT` layer).
#[derive(Clone)]
pub struct ExplorerReader {
    pub params: Rc<ExplorerParams>,
    pub typing_params: Rc<TypingParams>,
    pub reconstructor: Reconstructor,
    pub context: Rc<dyn Fn(&RProgram) -> RProgram>,
}

/// State of program exploration (mirror of `ExplorerState`).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ExplorerState {
    /// Type-checking state (shared copy-on-write: snapshots are O(1), the
    /// content is cloned only on mutation via `typing_mut`).
    pub typing_state: Rc<TypingState>,
    /// Auxiliary goals to be synthesized independently.
    pub aux_goals: Rc<Vec<Goal>>,
    /// Synthesized auxiliary goals, indexed by their names.
    pub solved_aux_goals: Rc<BTreeMap<Id, RProgram>>,
    /// Local bindings to be checked upon use (in typechecking mode).
    pub lambda_lets: Rc<BTreeMap<Id, (Rc<Environment>, UProgram)>>,
    /// Number of uses of each symbol in the program so far.
    pub symbol_use_count: Rc<BTreeMap<Id, usize>>,
}

impl ExplorerState {
    /// Initial explorer state: no accumulated goals or bindings.
    #[must_use]
    pub fn initial(init_ts: Rc<TypingState>) -> ExplorerState {
        ExplorerState {
            typing_state: init_ts,
            aux_goals: Rc::new(Vec::new()),
            solved_aux_goals: Rc::new(BTreeMap::new()),
            lambda_lets: Rc::new(BTreeMap::new()),
            symbol_use_count: Rc::new(BTreeMap::new()),
        }
    }

    /// Read access to the type-checking state.
    #[must_use]
    pub fn typing(&self) -> &TypingState {
        &self.typing_state
    }

    /// Mutate the type-checking state, cloning it if it is shared with a
    /// snapshot (copy-on-write).
    pub fn typing_mut(&mut self) -> &mut TypingState {
        Rc::make_mut(&mut self.typing_state)
    }
}

/// Persistent state across explorations (mirror of `PersistentState`).
///
/// Shared between branches and intentionally **not** rolled back (matching the
/// outer `StateT PersistentState` of the reference stack).
#[derive(Clone, Debug, Default)]
pub struct PersistentState {
    /// Memoized terms, keyed by arity/shape/state/depth (most recent first).
    pub term_memo: BTreeMap<MemoKey, Vec<(RProgram, ExplorerState)>>,
    /// Recorded type errors, chronologically (most recent last).
    pub type_errors: Vec<ErrorMessage>,
}

/// Key in the memoization store (mirror of `MemoKey`).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MemoKey {
    key_type_arity: usize,
    key_last_shape: SType,
    key_state: ExplorerState,
    key_depth: usize,
}

/// The machine running explorations: the horn solver (base monad), the
/// reader, the current `ExplorerState`, and the monotonic `PersistentState`.
pub struct ExplorerCtx<'a> {
    pub horn: &'a mut FixPointSolver,
    pub reader: ExplorerReader,
    pub state: ExplorerState,
    pub persistent: PersistentState,
}

// ─────────────────────── LogicT emulation ───────────────────────

/// One step of a search: exhausted, or a value plus how to keep searching.
pub enum Step<A> {
    /// No (more) results.
    Fail,
    /// A solution, together with the snapshot to restore and the resumption.
    Ok { value: A, suspend: Suspend<A> },
}

/// Suspension of a search: the state and reader to install before resuming.
pub struct Suspend<A> {
    state: ExplorerState,
    reader: ExplorerReader,
    next: Next<A>,
}

pub type Next<A> = Box<dyn FnOnce(&mut ExplorerCtx<'_>) -> Step<A>>;

/// Run `sus` from the snapshot it carries.
fn resume<A>(ctx: &mut ExplorerCtx<'_>, sus: Suspend<A>) -> Step<A> {
    ctx.state = sus.state;
    let old = std::mem::replace(&mut ctx.reader, sus.reader);
    let step = (sus.next)(ctx);
    ctx.reader = old;
    step
}

/// Success: `return a`.
pub fn ret<A>(ctx: &mut ExplorerCtx<'_>, value: A) -> Step<A> {
    Step::Ok {
        value,
        suspend: Suspend {
            state: ctx.state.clone(),
            reader: ctx.reader.clone(),
            next: Box::new(|_| Step::Fail),
        },
    }
}

/// Failure: `mzero`.
#[must_use]
pub const fn mzero<A>() -> Step<A> {
    Step::Fail
}

/// `guard`: fail unless the condition holds.
pub fn guard(ctx: &mut ExplorerCtx<'_>, cond: bool) -> Step<()> {
    if cond { ret(ctx, ()) } else { mzero() }
}

/// `(>>=)`: for each result `a` of `m`, run `f(a)`; when `f(a)` is exhausted,
/// continue with the next result of `m` (depth-first, like the reference's
/// `LogicT` instance in the `logict` package).
pub fn bind<A, B, M, F>(ctx: &mut ExplorerCtx<'_>, m: M, mut f: F) -> Step<B>
where
    A: 'static,
    B: 'static,
    M: FnOnce(&mut ExplorerCtx<'_>) -> Step<A>,
    F: FnMut(&mut ExplorerCtx<'_>, A) -> Step<B> + 'static, {
    match m(ctx) {
        Step::Fail => Step::Fail,
        Step::Ok {
            value: a,
            suspend: sus_m,
        } => {
            match f(ctx, a) {
                Step::Fail => bind_rest(ctx, sus_m, f),
                Step::Ok {
                    value: b,
                    suspend: sus_f,
                } => {
                    Step::Ok {
                        value: b,
                        suspend: Suspend {
                            state: sus_f.state.clone(),
                            reader: ctx.reader.clone(),
                            next: Box::new(move |ctx2| {
                                match resume(ctx2, sus_f) {
                                    Step::Fail => bind_rest(ctx2, sus_m, f),
                                    ok => ok,
                                }
                            }),
                        },
                    }
                }
            }
        }
    }
}

/// The continuation part of `(>>=)` once `m`'s current fresh result has been
/// consumed by `f` and failed; also drives the remaining tail of `m` through
/// `f`.
fn bind_rest<A, B, F>(ctx: &mut ExplorerCtx<'_>, sus_m: Suspend<A>, mut f: F) -> Step<B>
where
    A: 'static,
    B: 'static,
    F: FnMut(&mut ExplorerCtx<'_>, A) -> Step<B> + 'static, {
    match resume(ctx, sus_m) {
        Step::Fail => Step::Fail,
        Step::Ok {
            value: a,
            suspend: sus_m2,
        } => {
            match f(ctx, a) {
                Step::Fail => bind_rest(ctx, sus_m2, f),
                Step::Ok {
                    value: b,
                    suspend: sus_f,
                } => {
                    Step::Ok {
                        value: b,
                        suspend: Suspend {
                            state: sus_f.state.clone(),
                            reader: ctx.reader.clone(),
                            next: Box::new(move |ctx2| {
                                match resume(ctx2, sus_f) {
                                    Step::Fail => bind_rest(ctx2, sus_m2, f),
                                    ok => ok,
                                }
                            }),
                        },
                    }
                }
            }
        }
    }
}

/// `mplus`: all results of `m1` (depth-first), then all results of `m2`
/// starting from the fork point.
pub fn mplus<A: 'static>(
    ctx: &mut ExplorerCtx<'_>,
    m1: ExplorerFn<A>,
    m2: ExplorerFn<A>,
) -> Step<A> {
    let fork_state = ctx.state.clone();
    match m1(ctx) {
        Step::Fail => {
            ctx.state = fork_state;
            m2(ctx)
        }
        Step::Ok {
            value: a,
            suspend: sus1,
        } => {
            let reader = ctx.reader.clone();
            Step::Ok {
                value: a,
                suspend: Suspend {
                    state: sus1.state.clone(),
                    reader: reader.clone(),
                    next: mplus_next(sus1, fork_state, m2, reader),
                },
            }
        }
    }
}

/// The continuation of `mplus m1 m2`: the remaining results of `m1`, and
/// then `m2` (mirroring `m1' \`mplus\` m2` in the reference's `msplit`).
/// Each successful resume re-wraps the remaining `m1` suspension so that `m2`
/// is eventually tried when `m1` is exhausted.
fn mplus_next<A: 'static>(
    sus1: Suspend<A>,
    fork_state: ExplorerState,
    m2: ExplorerFn<A>,
    _reader: ExplorerReader,
) -> Next<A> {
    Box::new(move |ctx| {
        match resume(ctx, sus1) {
            Step::Fail => {
                ctx.state = fork_state;
                m2(ctx)
            }
            Step::Ok {
                value: v,
                suspend: sus1,
            } => {
                let fork_state = fork_state.clone();
                let m2 = m2.clone();
                let reader = ctx.reader.clone();
                Step::Ok {
                    value: v,
                    suspend: Suspend {
                        state: sus1.state.clone(),
                        reader: reader.clone(),
                        next: mplus_next(sus1, fork_state, m2, reader),
                    },
                }
            }
        }
    })
}

/// `msum` over the alternatives (depth-first; equivalent to a right fold of
/// `mplus` since all alternatives are created at the same point).
pub fn choice<A: 'static>(ctx: &mut ExplorerCtx<'_>, alts: Vec<ExplorerFn<A>>) -> Step<A> {
    let mut it = alts.into_iter();
    let mut cur: ExplorerFn<A> = match it.next() {
        None => return Step::Fail,
        Some(m) => m,
    };
    for alt in it {
        let prev = cur;
        cur = Rc::new(move |ctx2| mplus(ctx2, prev.clone(), alt.clone()));
    }
    cur(ctx)
}

/// `once`: perform `m` and keep only its first result.
pub fn cut<A, M>(ctx: &mut ExplorerCtx<'_>, m: M) -> Step<A>
where
    A: 'static,
    M: FnOnce(&mut ExplorerCtx<'_>) -> Step<A>, {
    match m(ctx) {
        Step::Fail => Step::Fail,
        Step::Ok {
            value: a,
            suspend: _,
        } => {
            Step::Ok {
                value: a,
                suspend: Suspend {
                    state: ctx.state.clone(),
                    reader: ctx.reader.clone(),
                    next: Box::new(|_| Step::Fail),
                },
            }
        }
    }
}

/// `ifte t th el`: if `t` has a result, feed it (and, on backtracking, its
/// remaining results) to `th`; otherwise run `el`.
pub fn ifte<A, B, T, TH, EL>(ctx: &mut ExplorerCtx<'_>, t: T, mut th: TH, el: EL) -> Step<B>
where
    A: 'static,
    B: 'static,
    T: FnOnce(&mut ExplorerCtx<'_>) -> Step<A>,
    TH: FnMut(&mut ExplorerCtx<'_>, A) -> Step<B> + 'static,
    EL: FnOnce(&mut ExplorerCtx<'_>) -> Step<B>, {
    let fork_state = ctx.state.clone();
    match t(ctx) {
        Step::Fail => {
            ctx.state = fork_state;
            el(ctx)
        }
        Step::Ok {
            value: a,
            suspend: sus_t,
        } => {
            match th(ctx, a) {
                Step::Fail => ifte_rest(ctx, sus_t, th),
                Step::Ok {
                    value: b,
                    suspend: sus_th,
                } => {
                    Step::Ok {
                        value: b,
                        suspend: Suspend {
                            state: sus_th.state.clone(),
                            reader: ctx.reader.clone(),
                            next: Box::new(move |ctx2| {
                                match resume(ctx2, sus_th) {
                                    Step::Fail => ifte_rest(ctx2, sus_t, th),
                                    ok => ok,
                                }
                            }),
                        },
                    }
                }
            }
        }
    }
}

/// The continuation part of `ifte` once `t`'s first result has been consumed
/// by `th` and failed: feed `t`'s remaining results to `th`.
fn ifte_rest<A, B, TH>(ctx: &mut ExplorerCtx<'_>, sus_t: Suspend<A>, mut th: TH) -> Step<B>
where
    A: 'static,
    B: 'static,
    TH: FnMut(&mut ExplorerCtx<'_>, A) -> Step<B> + 'static, {
    match resume(ctx, sus_t) {
        Step::Fail => Step::Fail,
        Step::Ok {
            value: a,
            suspend: sus_t2,
        } => {
            match th(ctx, a) {
                Step::Fail => ifte_rest(ctx, sus_t2, th),
                Step::Ok {
                    value: b,
                    suspend: sus_th,
                } => {
                    Step::Ok {
                        value: b,
                        suspend: Suspend {
                            state: sus_th.state.clone(),
                            reader: ctx.reader.clone(),
                            next: Box::new(move |ctx2| {
                                match resume(ctx2, sus_th) {
                                    Step::Fail => ifte_rest(ctx2, sus_t2, th),
                                    ok => ok,
                                }
                            }),
                        },
                    }
                }
            }
        }
    }
}

/// Run the first result of `m`, then continue from its successor (`msplit`'s
/// handling of the tail mirrors the reference's `msplit t >>= \\(a, s) ->
/// ...`).
#[allow(dead_code)]
fn msplit<A, M>(ctx: &mut ExplorerCtx<'_>, m: M) -> Step<(A, ExplorerFn<A>)>
where
    A: 'static,
    M: FnOnce(&mut ExplorerCtx<'_>) -> Step<A>, {
    match m(ctx) {
        Step::Fail => Step::Fail,
        Step::Ok { value: a, suspend } => {
            let suspend = Rc::new(std::cell::RefCell::new(Some(suspend)));
            Step::Ok {
                value: (
                    a,
                    Rc::new(move |ctx2| {
                        match suspend.borrow_mut().take() {
                            Some(s) => resume(ctx2, s),
                            None => Step::Fail,
                        }
                    }),
                ),
                suspend: Suspend {
                    state: ctx.state.clone(),
                    reader: ctx.reader.clone(),
                    next: Box::new(|_| Step::Fail),
                },
            }
        }
    }
}

// ─────────────────────── Explorer utilities ───────────────────────

/// Run a reader-local computation: install a modified `ExplorerParams` while
/// `f` runs (its suspensions carry the modified copy), then restore.
pub fn local<A, P, F>(ctx: &mut ExplorerCtx<'_>, update: P, f: F) -> Step<A>
where
    P: Fn(&ExplorerParams) -> ExplorerParams,
    F: FnOnce(&mut ExplorerCtx<'_>) -> Step<A>, {
    let new_params = Rc::new(update(&ctx.reader.params));
    let old = std::mem::replace(&mut ctx.reader.params, new_params);
    let res = f(ctx);
    ctx.reader.params = old;
    res
}

/// Run `f` with the given program context.
pub fn in_context<A, F>(
    ctx: &mut ExplorerCtx<'_>,
    c: Rc<dyn Fn(&RProgram) -> RProgram>,
    f: F,
) -> Step<A>
where
    F: FnOnce(&mut ExplorerCtx<'_>) -> Step<A>,
{
    let old_ctx = ctx.reader.context.clone();
    let old = std::mem::replace(&mut ctx.reader.context, Rc::new(move |p| old_ctx(&c(p))));
    let res = f(ctx);
    ctx.reader.context = old;
    res
}

/// Impose typing constraint `c` on the programs.
pub fn add_constraint(ctx: &mut ExplorerCtx<'_>, c: Constraint) {
    add_typing_constraint(ctx.state.typing_mut(), &c);
}

/// Record a type error and backtrack.
pub fn throw_error<A>(ctx: &mut ExplorerCtx<'_>, e: &ErrorMessage) -> Step<A> {
    ctx.persistent.type_errors.push(e.clone());
    Step::Fail
}

/// Record a type error described by `description` and backtrack.
fn throw_error_with_description<A>(ctx: &mut ExplorerCtx<'_>, description: Doc) -> Step<A> {
    let pos = ctx.reader.params.source_pos.clone();
    throw_error(
        ctx,
        &ErrorMessage::new(ErrorKind::TypeError, pos, description),
    )
}

/// Embed a type-constraint-checker computation `f` in the explorer;
/// on a type error, record the error and backtrack.
pub fn run_in_solver<A, F>(ctx: &mut ExplorerCtx<'_>, f: F) -> Step<A>
where F: FnOnce(&mut TcSolver<'_>) -> Result<A, ErrorMessage> {
    let t_state = (*ctx.state.typing_state).clone();
    let params = ctx.reader.typing_params.clone();
    let horn = &mut *ctx.horn;
    match run_tc_solver(&params, t_state, horn, f) {
        Err(err) => throw_error(ctx, &err),
        Ok((res, st)) => {
            ctx.state.typing_state = Rc::new(st);
            ret(ctx, res)
        }
    }
}

/// `freshId`.
///
/// Unlike the reference (which routes every id allocation through its solver
/// monad), a fresh-id allocation can never fail, so we mutate the typing
/// state in place (copy-on-write) instead of cloning it per call: the
/// reference's `runInSolver` re-snapshot is O(1) for it (immutable sharing),
/// and `Rc::make_mut` gives us the same laziness here.
pub fn fresh_id(ctx: &mut ExplorerCtx<'_>, prefix: &str) -> Step<Id> {
    let st = Rc::make_mut(&mut ctx.state.typing_state);
    let i = st.id_count.get(prefix).copied().unwrap_or(0);
    st.id_count.insert(prefix.to_string(), i + 1);
    ret(ctx, format!("{prefix}{i}"))
}

/// `freshVar`: a fresh variable of `env` with the given
/// prefix.
pub fn fresh_var(ctx: &mut ExplorerCtx<'_>, env: &Rc<Environment>, prefix: &str) -> Step<Id> {
    let x = match fresh_id(ctx, prefix) {
        Step::Fail => return Step::Fail,
        Step::Ok { value: x, suspend } => {
            let _ = suspend;
            x
        }
    };
    if all_symbols(env).contains_key(&x) {
        fresh_var(ctx, env, prefix)
    } else {
        ret(ctx, x)
    }
}

/// A fresh unknown (predicate variable) with the given prefix.
pub fn fresh_unknown(ctx: &mut ExplorerCtx<'_>, prefix: &str) -> Step<Formula> {
    let x = match fresh_id(ctx, prefix) {
        Step::Fail => return Step::Fail,
        Step::Ok { value: x, suspend } => {
            let _ = suspend;
            x
        }
    };
    ret(ctx, Formula::Unknown(Substitution::new(), x))
}

/// `currentValuation`: current valuation of unknown `u`;
/// candidate valuations are grouped from weakest to strongest and each group
/// is tried in order.
pub fn current_valuation(ctx: &mut ExplorerCtx<'_>, u: &Formula) -> Step<BTreeSet<Formula>> {
    let u = u.clone();
    let val = |c: &crate::logic::Candidate| valuation(&c.solution, &u);
    match run_in_solver(ctx, solve_all_candidates) {
        Step::Fail => Step::Fail,
        Step::Ok { value: (), suspend } => {
            let _ = suspend;
            let mut cands = ctx.state.typing_state.candidates.clone();
            cands.sort_by(|c1, c2| set_compare(&val(c1), &val(c2)));
            let mut groups: Vec<Vec<crate::logic::Candidate>> = Vec::new();
            for c in cands {
                match groups.last_mut() {
                    Some(g) if val(&g[0]) == val(&c) => g.push(c),
                    _ => groups.push(vec![c]),
                }
            }
            let alts: Vec<ExplorerFn<BTreeSet<Formula>>> = groups
                .into_iter()
                .map(|g| -> ExplorerFn<BTreeSet<Formula>> {
                    let g0 = g[0].clone();
                    let u = u.clone();
                    Rc::new(move |ctx2: &mut ExplorerCtx<'_>| {
                        ctx2.state.typing_mut().candidates = g.clone();
                        ret(ctx2, valuation(&g0.solution, &u))
                    })
                })
                .collect();
            choice(ctx, alts)
        }
    }
}

/// `inContext`, via [`in_context`].

///

/// `instantiate`: replace all bound type and predicate
/// variables of `sch` with fresh free variables; if `top` is `False`,
/// instantiate predicate variables with `false` (bottom).
pub fn instantiate(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    sch: &RSchema,
    top: bool,
    arg_names: &[Id],
) -> Step<RType> {
    let mut subst = crate::types::TypeSubstitution::new();
    let mut p_subst = Substitution::new();
    let mut sch_body = sch.clone();
    loop {
        match sch_body {
            SchemaSkeleton::ForallT(a, rest) => {
                let a1 = match fresh_id(ctx, "A") {
                    Step::Fail => return Step::Fail,
                    Step::Ok { value: a1, suspend } => {
                        let _ = suspend;
                        a1
                    }
                };
                add_constraint(ctx, Constraint::WellFormed(env.clone(), vart_all(&a1)));
                subst.insert(
                    a.clone(),
                    TypeSkeleton::ScalarT(
                        BaseType::TypeVarT(Substitution::new(), a1.clone()),
                        Formula::BoolLit(top),
                    ),
                );
                sch_body = *rest;
            }
            SchemaSkeleton::ForallP(sig, rest) => {
                let arg_sorts: Vec<Sort> = sig
                    .pred_sig_arg_sorts
                    .iter()
                    .map(|s| sort_substitute(&crate::types::as_sort_subst(&subst), s.clone()))
                    .collect();
                let fml = if top {
                    let p1 = match fresh_id(ctx, &sig.pred_sig_name.to_uppercase()) {
                        Step::Fail => return Step::Fail,
                        Step::Ok { value: p1, suspend } => {
                            let _ = suspend;
                            p1
                        }
                    };
                    add_constraint(
                        ctx,
                        Constraint::WellFormedPredicate(env.clone(), arg_sorts.clone(), p1.clone()),
                    );
                    let args: Vec<Formula> = arg_sorts
                        .iter()
                        .zip(de_brujns(arg_sorts.len()))
                        .map(|(s, n)| Formula::Var(Box::new(s.clone()), n))
                        .collect();
                    Formula::Pred(Box::new(Sort::BoolS), p1, args)
                } else {
                    ffalse()
                };
                p_subst.insert(sig.pred_sig_name.clone(), fml);
                sch_body = *rest;
            }
            SchemaSkeleton::Monotype(t) => {
                return instantiate_go(ctx, env, &subst, &p_subst, arg_names, &t);
            }
        }
    }
}

/// The `go` helper of `instantiate`.
fn instantiate_go(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    subst: &crate::types::TypeSubstitution,
    p_subst: &Substitution,
    arg_names: &[Id],
    t: &RType,
) -> Step<RType> {
    if let TypeSkeleton::FunctionT(x, t_arg, t_res) = t {
        let x1 = match arg_names.first() {
            None => {
                match fresh_var(ctx, env, "x") {
                    Step::Fail => return Step::Fail,
                    Step::Ok { value: x1, suspend } => {
                        let _ = suspend;
                        x1
                    }
                }
            }
            Some(arg_name) => arg_name.clone(),
        };
        let t_arg1 = match instantiate_go(ctx, env, subst, p_subst, &[], t_arg) {
            Step::Fail => return Step::Fail,
            Step::Ok {
                value: t_arg1,
                suspend,
            } => {
                let _ = suspend;
                t_arg1
            }
        };
        let is_bound_tv = |a: &Id| subst.contains_key(a) || env.bound_type_vars.contains(a);
        let rest_args = if arg_names.len() > 1 {
            &arg_names[1..]
        } else {
            &[]
        };
        let t_res_renamed = rename_var(&is_bound_tv, x, &x1, t_arg, t_res);
        let t_res1 = match instantiate_go(ctx, env, subst, p_subst, rest_args, &t_res_renamed) {
            Step::Fail => return Step::Fail,
            Step::Ok {
                value: t_res1,
                suspend,
            } => {
                let _ = suspend;
                t_res1
            }
        };
        ret(
            ctx,
            TypeSkeleton::FunctionT(x1, Box::new(t_arg1), Box::new(t_res1)),
        )
    } else {
        let t1 = type_substitute_pred(p_subst, &type_substitute(subst, t));
        ret(ctx, t1)
    }
}

/// `symbolType`: precise type of symbol `x` with schema
/// `sch` in `env`; scalar variables get `_v == x` as refinement, polytypes are
/// instantiated freshly.
pub fn symbol_type(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    name: &Id,
    sch: &RSchema,
) -> Step<RType> {
    if let SchemaSkeleton::Monotype(t @ TypeSkeleton::ScalarT(b, _)) = sch {
        if is_literal(name) || lookup_constructor(name, env).is_some() {
            ret(ctx, t.clone())
        } else {
            ret(
                ctx,
                TypeSkeleton::ScalarT(b.clone(), var_refinement(name, &to_sort(b))),
            )
        }
    } else {
        let arity0 = arity(&to_monotype(sch)) == 0;
        instantiate(ctx, env, sch, !arity0, &[])
    }
}

/// `toVar`: a variable representing `p` (either `p`
/// itself, or a fresh ghost).
pub fn to_var(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    p: &RProgram,
) -> Step<(Rc<Environment>, Formula)> {
    match &p.content {
        BareProgram::PSymbol(name) => {
            ret(ctx, (env.clone(), symbol_as_formula(env, name, &p.type_of)))
        }
        _ => {
            match fresh_id(ctx, "G") {
                Step::Fail => Step::Fail,
                Step::Ok { value: g, suspend } => {
                    let _ = suspend;
                    let env1 = Rc::new(add_let_bound(&g, &p.type_of, env));
                    ret(
                        ctx,
                        (
                            env1,
                            Formula::Var(Box::new(to_sort(&base_type_of(&p.type_of))), g),
                        ),
                    )
                }
            }
        }
    }
}

/// `appType`: a type semantically equivalent to
/// `[p/x]tRes`; if `p` is not a variable, use the contextual type
/// `let x : typeOf p in tRes`.
#[must_use]
pub fn app_type(env: &Rc<Environment>, p: &RProgram, x: &Id, t_res: &RType) -> RType {
    match &p.content {
        BareProgram::PSymbol(name) => {
            substitute_in_type(
                &|a| is_bound(env, a),
                &BTreeMap::from([(x.clone(), symbol_as_formula(env, name, &p.type_of))]),
                t_res,
            )
        }
        _ => contextual(x.clone(), p.type_of.clone(), t_res),
    }
}

/// `caseSymbols`: bind the constructor arguments of
/// `consT` to the given fresh binders; returns the bindings and the return
/// type applied to the scrutinee.
pub fn case_symbols(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    x: &Formula,
    names: &[Id],
    cons_t: &RType,
) -> Step<(Vec<(Id, RType)>, Formula)> {
    match (names, cons_t) {
        ([], TypeSkeleton::ScalarT(_, fml)) => {
            let sub = Substitution::from([(VALUE_VAR_NAME.to_string(), x.clone())]);
            ret(ctx, (Vec::new(), substitute(&sub, fml.clone())))
        }
        ([name, rest @ ..], TypeSkeleton::FunctionT(y, t_arg, t_res)) => {
            let renamed = rename_var(&|a| is_bound(env, a), y, name, t_arg, t_res);
            match case_symbols(ctx, env, x, rest, &renamed) {
                Step::Fail => Step::Fail,
                Step::Ok {
                    value: (mut syms, ass),
                    suspend,
                } => {
                    let _ = suspend;
                    syms.push((name.clone(), (**t_arg).clone()));
                    ret(ctx, (syms, ass))
                }
            }
        }
        _ => Step::Fail,
    }
}

/// `enqueueGoal`: queue an auxiliary goal with a fresh
/// name and return a placeholder symbol of type `typ`.
pub fn enqueue_goal(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    typ: &RType,
    impl_: &UProgram,
    depth: usize,
) -> Step<RProgram> {
    match fresh_var(ctx, env, "f") {
        Step::Fail => Step::Fail,
        Step::Ok { value: g, suspend } => {
            let _ = suspend;
            Rc::make_mut(&mut ctx.state.aux_goals).insert(0, Goal {
                g_name: g.clone(),
                g_environment: env.clone(),
                g_spec: SchemaSkeleton::Monotype(typ.clone()),
                g_impl: impl_.clone(),
                g_depth: depth,
                g_source_pos: no_pos(),
                g_synthesize: true,
            });
            ret(ctx, Program {
                content: BareProgram::PSymbol(g),
                type_of: typ.clone(),
            })
        }
    }
}

/// `generateError`: make the environment inconsistent
/// (if possible with the current unknown assumptions).
pub fn generate_error(ctx: &mut ExplorerCtx<'_>, env: &Rc<Environment>) -> Step<RProgram> {
    let ctx_p = ctx.reader.context.clone();
    let env1 = type_substitute_env(&ctx.state.typing().type_assignment, env);
    let trivial: BTreeSet<Formula> = all_scalars(&env1)
        .into_iter()
        .map(|v| eq(v.clone(), v))
        .collect();
    add_constraint(
        ctx,
        Constraint::Subtype(
            env.clone(),
            crate::types::int(conjunction(&trivial)),
            crate::types::int(ffalse()),
            false,
            String::new(),
        ),
    );
    let pos = ctx.reader.params.source_pos.clone();
    ctx.state.typing_mut().error_context = (
        pos,
        soft_break(
            soft_break(text("when checking"), pretty_program(&error_program())),
            vsp(text("in"), pretty_program(&ctx_p(&error_program()))),
        ),
    );
    match run_in_solver(ctx, solve_type_constraints) {
        Step::Fail => Step::Fail,
        Step::Ok { value: (), suspend } => {
            let _ = suspend;
            ctx.state.typing_mut().error_context = (no_pos(), empty());
            ret(ctx, error_program())
        }
    }
}

/// `generateCondition`: a program with the same value as
/// `fml`, built from executable conjuncts or generated Bool terms.
pub fn generate_condition(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    fml: &Formula,
) -> Step<RProgram> {
    let conjuncts: Vec<Formula> = conjuncts_of(fml).into_iter().collect();
    let mut partial: Option<RProgram> = None;
    for c in conjuncts {
        let p = if is_executable(&c) {
            ret(ctx, fml_to_program(&c))
        } else {
            cut(ctx, |ctx2| {
                generate_e(ctx2, env, &bool(eq(val_bool(), c.clone())))
            })
        };
        let p = match p {
            Step::Fail => return Step::Fail,
            Step::Ok { value: p, suspend } => {
                let _ = suspend;
                p
            }
        };
        let and_symb = Program {
            content: BareProgram::PSymbol(
                bin_op_tokens()
                    .iter()
                    .find(|(op, _)| *op == BinOp::And)
                    .map(|(_, t)| t.to_string())
                    .unwrap_or_else(|| "&&".to_string()),
            ),
            type_of: to_monotype(&bin_op_type(BinOp::And)),
        };
        let conjoin = |p1: &RProgram, p2: &RProgram| {
            Program {
                content: BareProgram::PApp(
                    Box::new(Program {
                        content: BareProgram::PApp(Box::new(and_symb), Box::new(p1.clone())),
                        type_of: bool_all(),
                    }),
                    Box::new(p2.clone()),
                ),
                type_of: bool_all(),
            }
        };
        partial = Some(match partial {
            None => p,
            Some(prev) => conjoin(&prev, &p),
        });
    }
    let p = match partial {
        None => return Step::Fail,
        Some(p) => p,
    };
    let body = crate::types::add_refinement(p.type_of.clone(), &eq(val_bool(), fml.clone()));
    ret(ctx, Program {
        content: p.content,
        type_of: body,
    })
}

// ─────────────────────── Search functions ───────────────────────

/// `generateI`: explore all terms that have refined type
/// `t` in `env` (top-down phase of bidirectional typechecking).
pub fn generate_i(ctx: &mut ExplorerCtx<'_>, env: &Rc<Environment>, t: &RType) -> Step<RProgram> {
    match t {
        TypeSkeleton::FunctionT(x, t_arg, t_res) => {
            let env1 = Rc::new(unfold_all_variables(&add_variable(x, t_arg, env)));
            let t = t.clone();
            let x1 = x.clone();
            let ctx_fn = {
                let x = x.clone();
                let t = t.clone();
                Rc::new(move |p: &RProgram| {
                    Program {
                        content: BareProgram::PFun(x.clone(), Box::new(p.clone())),
                        type_of: t.clone(),
                    }
                })
            };
            let p_body = match in_context(ctx, ctx_fn, |ctx2| generate_i(ctx2, &env1, t_res)) {
                Step::Fail => return Step::Fail,
                Step::Ok { value: p, suspend } => {
                    let _ = suspend;
                    p
                }
            };
            ret(ctx, Program {
                content: BareProgram::PFun(x1, Box::new(p_body)),
                type_of: t,
            })
        }
        TypeSkeleton::ScalarT(..) => {
            let ma_enabled = ctx.reader.params.abduce_scrutinees;
            let d = ctx.reader.params.match_depth;
            let tass = ctx.state.typing().type_assignment.clone();
            let ma_possible = has_potential_scrutinees_tass(&tass, env);
            if ma_enabled && d > 0 && ma_possible {
                generate_maybe_match_if(ctx, env, t)
            } else {
                generate_maybe_if(ctx, env, t)
            }
        }
        TypeSkeleton::LetT(..) | TypeSkeleton::AnyT => Step::Fail,
    }
}

/// `generateMaybeIf`: generate a possibly conditional
/// term of type `t`, depending on whether a condition is abduced.
pub fn generate_maybe_if(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    t: &RType,
) -> Step<RProgram> {
    // Guess an E-term and abduce a condition for it.
    let env_then = env.clone();
    let t_then = t.clone();
    let generate_then: ExplorerFn<(Formula, Id, RProgram)> = Rc::new(move |ctx2| {
        match fresh_unknown(ctx2, "C") {
            Step::Fail => Step::Fail,
            Step::Ok {
                value: c_unknown,
                suspend,
            } => {
                let _ = suspend;
                add_constraint(
                    ctx2,
                    Constraint::WellFormedCond(env_then.clone(), c_unknown.clone()),
                );
                let env_ass = Rc::new(add_assumption(c_unknown.clone(), &env_then));
                let p_then = match cut(ctx2, |ctx3| generate_e(ctx3, &env_ass, &t_then)) {
                    Step::Fail => return Step::Fail,
                    Step::Ok { value: p, suspend } => {
                        let _ = suspend;
                        p
                    }
                };
                let cond_set = match current_valuation(ctx2, &c_unknown) {
                    Step::Fail => return Step::Fail,
                    Step::Ok { value: s, suspend } => {
                        let _ = suspend;
                        s
                    }
                };
                let cond = conjunction(&cond_set);
                ret(ctx2, (cond, unknown_name(&c_unknown).clone(), p_then))
            }
        }
    });
    let env2 = env.clone();
    let t2 = t.clone();
    let generate_else = Rc::new(
        move |ctx2: &mut ExplorerCtx<'_>,
              (cond, cond_unknown, p_then): (Formula, Id, RProgram)|
              -> Step<RProgram> {
            generate_else(ctx2, &env2, &t2, &cond, &cond_unknown, &p_then)
        },
    );
    let env3 = env.clone();
    let t3 = t.clone();
    let generate_match_fn: ExplorerFn<RProgram> =
        Rc::new(move |ctx2| generate_match(ctx2, &env3, &t3));
    let ge = generate_else.clone();
    ifte(
        ctx,
        |c2| generate_then.clone()(c2),
        move |c2, v| ge(c2, v),
        |c2| generate_match_fn.clone()(c2),
    )
}

/// `generateElse`: proceed after a solution `pThen` has
/// been found under assumption `cond`.
pub fn generate_else(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    t: &RType,
    cond: &Formula,
    cond_unknown: &Id,
    p_then: &RProgram,
) -> Step<RProgram> {
    if cond == &ftrue() {
        // `pThen` is valid under no assumptions: return it.
        return ret(ctx, p_then.clone());
    }
    // `pThen` is valid under a nontrivial assumption: look for the solution
    // over the rest of the inputs.
    let p_cond = {
        let t = t.clone();
        match in_context(
            ctx,
            Rc::new(move |p: &RProgram| {
                Program {
                    content: BareProgram::PIf(
                        Box::new(p.clone()),
                        Box::new(u_hole()),
                        Box::new(u_hole()),
                    ),
                    type_of: t.clone(),
                }
            }),
            |ctx2| generate_condition(ctx2, env, cond),
        ) {
            Step::Fail => return Step::Fail,
            Step::Ok { value: p, suspend } => {
                let _ = suspend;
                p
            }
        }
    };
    // Create a fixed-valuation unknown to assume `!cond`.
    let c_unknown = match fresh_unknown(ctx, "C") {
        Step::Fail => return Step::Fail,
        Step::Ok { value: u, suspend } => {
            let _ = suspend;
            u
        }
    };
    match run_in_solver(ctx, |solver| {
        add_fixed_unknown(
            solver,
            unknown_name(&c_unknown),
            &BTreeSet::from([fnot(cond.clone())]),
        );
        Ok(())
    }) {
        Step::Fail => return Step::Fail,
        Step::Ok { value: (), suspend } => {
            let _ = suspend;
        }
    }
    let p_else = {
        let t_wrap = t.clone();
        let t_gen = t.clone();
        let p_cond = p_cond.clone();
        let p_then = p_then.clone();
        let cond_env = Rc::new(add_assumption(c_unknown.clone(), env));
        let gen_fn = |ctx2: &mut ExplorerCtx<'_>| {
            in_context(
                ctx2,
                Rc::new(move |p: &RProgram| {
                    Program {
                        content: BareProgram::PIf(
                            Box::new(p_cond.clone()),
                            Box::new(p_then.clone()),
                            Box::new(p.clone()),
                        ),
                        type_of: t_wrap.clone(),
                    }
                }),
                |ctx3| generate_i(ctx3, &cond_env, &t_gen),
            )
        };
        let t = t.clone();
        match optional_in_partial(ctx, &t, gen_fn) {
            Step::Fail => return Step::Fail,
            Step::Ok { value: p, suspend } => {
                let _ = suspend;
                p
            }
        }
    };
    // Re-check Horn constraints after retracting the branch guard.
    let cond_unknown = cond_unknown.clone();
    let recheck: ExplorerFn<()> = Rc::new(move |ctx2| {
        run_in_solver(ctx2, |solver| {
            set_unknown_recheck(
                solver,
                unknown_name(&c_unknown),
                &BTreeSet::new(),
                &BTreeSet::from([cond_unknown.clone()]),
            )
        })
    });
    match try_eliminate_branching(ctx, &p_else, recheck) {
        Step::Fail => Step::Fail,
        Step::Ok {
            value: true,
            suspend,
        } => {
            let _ = suspend;
            ret(ctx, p_else)
        }
        Step::Ok {
            value: false,
            suspend,
        } => {
            let _ = suspend;
            ret(ctx, Program {
                content: BareProgram::PIf(
                    Box::new(p_cond),
                    Box::new(p_then.clone()),
                    Box::new(p_else),
                ),
                type_of: t.clone(),
            })
        }
    }
}

/// `tryEliminateBranching`.
pub fn try_eliminate_branching(
    ctx: &mut ExplorerCtx<'_>,
    branch: &RProgram,
    recheck: ExplorerFn<()>,
) -> Step<bool> {
    if is_hole(branch) {
        return ret(ctx, false);
    }
    let fork_state = ctx.state.clone();
    // Mirror `tryEliminateBranching`: `ifte recheck
    // (const mzero) (return False) `mplus` (recheck >> return True)`.
    let recheck_a = recheck.clone();
    let recheck_b = recheck.clone();
    let ifte_fn: ExplorerFn<bool> = Rc::new(move |ctx2| {
        ifte(
            ctx2,
            |c3| recheck_a(c3),
            |_, ()| mzero(),
            |c3| ret(c3, false),
        )
    });
    let recheck_true: ExplorerFn<bool> =
        Rc::new(move |ctx2| bind(ctx2, |c3| recheck_b(c3), |c3, ()| ret(c3, true)));
    let m = mplus(ctx, ifte_fn, recheck_true);
    match m {
        Step::Fail => {
            ctx.state = fork_state;
            ret(ctx, false)
        }
        ok => ok,
    }
}

/// `optionalInPartial`: if partial solutions are
/// accepted, try `gen_fn`, and if it fails, just leave a hole of type `t`;
/// otherwise run `gen_fn`.
pub fn optional_in_partial<G>(ctx: &mut ExplorerCtx<'_>, t: &RType, gen_fn: G) -> Step<RProgram>
where G: FnOnce(&mut ExplorerCtx<'_>) -> Step<RProgram> {
    if ctx.reader.params.partial_solution {
        let t = t.clone();
        ifte(ctx, gen_fn, ret, |ctx2| {
            ret(ctx2, Program {
                content: BareProgram::PHole,
                type_of: t.clone(),
            })
        })
    } else {
        gen_fn(ctx)
    }
}

/// `generateMatch`: generate a match term of type `t`.
pub fn generate_match(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    t: &RType,
) -> Step<RProgram> {
    let d = ctx.reader.params.match_depth;
    if d == 0 {
        return mzero();
    }
    // Generate a scrutinee of an arbitrary type (with reduced depth). The
    // enumeration is resumed on failure of the whole match, mirroring the
    // reference's `(Program p tScr) <- ... $ generateE env anyDatatype`
    //: the next scrutinee candidate is tried after the
    // previous one's match body fails.
    let scr_depth = ctx.reader.params.scrutinee_depth;
    let env_g = env.clone();
    let t_g = t.clone();
    let scrutinee_gen: ExplorerFn<RProgram> = Rc::new(move |ctx2| {
        let env = env_g.clone();
        let t = t_g.clone();
        local(
            ctx2,
            move |params| {
                let mut params = params.clone();
                params.e_guess_depth = scr_depth;
                params
            },
            move |ctx3| {
                in_context(
                    ctx3,
                    Rc::new(move |p: &RProgram| {
                        Program {
                            content: BareProgram::PMatch(Box::new(p.clone()), Vec::new()),
                            type_of: t.clone(),
                        }
                    }),
                    move |ctx4| generate_e(ctx4, &env, &any_datatype()),
                )
            },
        )
    });
    let env_a = env.clone();
    let t_a = t.clone();
    type AttemptFn = Rc<dyn Fn(&mut ExplorerCtx<'_>, RProgram) -> Step<RProgram>>;
    let attempt: AttemptFn = Rc::new(move |ctx2, p| scrutinee_attempt(ctx2, &env_a, &t_a, &p));
    match scrutinee_gen(ctx) {
        Step::Fail => Step::Fail,
        Step::Ok { value: p, suspend } => {
            match attempt(ctx, p) {
                Step::Fail => match_scrutinee_resume(ctx, suspend, attempt),
                Step::Ok {
                    value,
                    suspend: sus_a,
                } => {
                    Step::Ok {
                        value,
                        suspend: Suspend {
                            state: sus_a.state.clone(),
                            reader: ctx.reader.clone(),
                            next: Box::new(move |ctx2| {
                                match resume(ctx2, sus_a) {
                                    Step::Fail => match_scrutinee_resume(ctx2, suspend, attempt),
                                    ok => ok,
                                }
                            }),
                        },
                    }
                }
            }
        }
    }
}

/// Resume the scrutinee enumeration of `generateMatch` after a failed
/// `scrutinee_attempt` and retry with the next candidate.
fn match_scrutinee_resume(
    ctx: &mut ExplorerCtx<'_>,
    sus: Suspend<RProgram>,
    attempt: AttemptFn,
) -> Step<RProgram> {
    // Iterative loop over scrutinee candidates (like `check_e_loop`).
    let mut cur: Option<Suspend<RProgram>> = Some(sus);
    loop {
        let Some(s) = cur.take() else {
            return Step::Fail;
        };
        match resume(ctx, s) {
            Step::Fail => return Step::Fail,
            Step::Ok { value: p, suspend } => {
                match attempt(ctx, p) {
                    Step::Fail => {
                        cur = Some(suspend);
                    }
                    Step::Ok {
                        value,
                        suspend: sus_a,
                    } => {
                        return Step::Ok {
                            value,
                            suspend: Suspend {
                                state: sus_a.state.clone(),
                                reader: ctx.reader.clone(),
                                next: Box::new(move |ctx2| {
                                    match resume(ctx2, sus_a) {
                                        Step::Fail => {
                                            match_scrutinee_resume(ctx2, suspend, attempt)
                                        }
                                        ok => ok,
                                    }
                                }),
                            },
                        };
                    }
                }
            }
        }
    }
}

/// The body of `generateMatch` after the scrutinee `p` (with its raw type)
/// has been generated: guard, bind the scrutinee variable, generate the
/// cases, and finish with `generateElse`.
fn scrutinee_attempt(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    t: &RType,
    p: &RProgram,
) -> Step<RProgram> {
    let (p_term, t_scr) = match p {
        Program { content, type_of } => (content.clone(), type_of.clone()),
    };
    let (env1, t_scr1) = embed_context(env, &t_scr);
    let p_scrutinee = Program {
        content: p_term,
        type_of: t_scr1,
    };
    // Type of the scrutinee must be a datatype.
    let TypeSkeleton::ScalarT(BaseType::DatatypeT(scr_dt, ..), _) = &t_scr else {
        return mzero();
    };
    let ctors = env
        .datatypes
        .get(scr_dt)
        .map(|dt| dt.constructors.clone())
        .unwrap_or_default();
    let scrutinee_symbols = symbol_list(&p_scrutinee);
    let is_good_scrutinee = !ctors.is_empty()
        && !env.used_scrutinees.contains(&p_scrutinee)
        && !scrutinee_symbols.first().is_some_and(|h| ctors.contains(h))
        && scrutinee_symbols.iter().any(|s| !env.constants.contains(s));
    match guard(ctx, is_good_scrutinee) {
        Step::Fail => return Step::Fail,
        Step::Ok { .. } => {}
    }
    let (env2, x) = match to_var(
        ctx,
        &Rc::new(add_scrutinee(p_scrutinee.clone(), &env1)),
        &p_scrutinee,
    ) {
        Step::Fail => return Step::Fail,
        Step::Ok { value: v, suspend } => {
            let _ = suspend;
            v
        }
    };
    // First case generated separately in an attempt to abduce a condition
    // for the whole match.
    let (p_case, cond, cond_unknown) = match cut(ctx, |ctx2| {
        generate_first_case(ctx2, &env2, &x, &p_scrutinee, t, &ctors[0])
    }) {
        Step::Fail => return Step::Fail,
        Step::Ok { value: v, suspend } => {
            let _ = suspend;
            v
        }
    };
    // Generate a case for each of the remaining constructors, under the
    // assumption `cond`.
    let mut p_cases: Vec<Case<RType>> = Vec::new();
    for ctor in &ctors[1..] {
        let env3 = Rc::new(add_assumption(cond.clone(), &env2));
        let (c, _recheck) = match cut(ctx, |ctx2| {
            generate_case(ctx2, &env3, &x, &p_scrutinee, t, ctor)
        }) {
            Step::Fail => return Step::Fail,
            Step::Ok { value: v, suspend } => {
                let _ = suspend;
                v
            }
        };
        p_cases.push(c);
    }
    let mut cases = vec![p_case];
    cases.append(&mut p_cases);
    let p_then = Program {
        content: BareProgram::PMatch(Box::new(p_scrutinee), cases),
        type_of: t.clone(),
    };
    generate_else(ctx, env, t, &cond, &cond_unknown, &p_then)
}

/// `generateFirstCase`: generate the pack of the first
/// constructor, abducing a vacuousness condition if possible.
pub fn generate_first_case(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    scr_var: &Formula,
    p_scrutinee: &RProgram,
    t: &RType,
    cons_name: &Id,
) -> Step<(Case<RType>, Formula, Id)> {
    let (_cons_t, binders, _syms, case_env, ass) =
        match case_common(ctx, env, scr_var, p_scrutinee, cons_name) {
            Step::Fail => return Step::Fail,
            Step::Ok { value: v, suspend } => {
                let _ = suspend;
                v
            }
        };
    // `generateFirstCase` assumes the raw `ass`.
    let case_env = Rc::new(add_assumption(ass, &case_env));
    let t = t.clone();
    let p_scrutinee2 = p_scrutinee.clone();
    let cons_name_v = cons_name.clone();
    let binders_v = binders.clone();
    // Try to find a vacuousness condition.
    let vacuous = |ctx2: &mut ExplorerCtx<'_>| {
        let dead_unknown = match fresh_unknown(ctx2, "C") {
            Step::Fail => return Step::Fail,
            Step::Ok { value: u, suspend } => {
                let _ = suspend;
                u
            }
        };
        add_constraint(
            ctx2,
            Constraint::WellFormedCond(env.clone(), dead_unknown.clone()),
        );
        let dead_case_env = Rc::new(add_assumption(dead_unknown.clone(), &case_env));
        let t = t.clone();
        let c_name = cons_name_v.clone();
        let b_names = binders_v.clone();
        let err = match in_context(
            ctx2,
            Rc::new(move |p: &RProgram| {
                Program {
                    content: BareProgram::PMatch(Box::new(p_scrutinee2.clone()), vec![Case {
                        constructor: c_name.clone(),
                        arg_names: b_names.clone(),
                        expr: p.clone(),
                    }]),
                    type_of: t.clone(),
                }
            }),
            |ctx3| generate_error(ctx3, &dead_case_env),
        ) {
            Step::Fail => return Step::Fail,
            Step::Ok { value: e, suspend } => {
                let _ = suspend;
                e
            }
        };
        let dead_valuation = match current_valuation(ctx2, &dead_unknown) {
            Step::Fail => return Step::Fail,
            Step::Ok { value: s, suspend } => {
                let _ = suspend;
                conjunction(&s)
            }
        };
        // The error must be possible only in this case.
        match ifte(
            ctx2,
            |c3| {
                let dead_env = Rc::new(add_assumption(dead_valuation.clone(), env));
                generate_error(c3, &dead_env)
            },
            |_, _| mzero(),
            |c3| ret(c3, ()),
        ) {
            Step::Fail => return Step::Fail,
            Step::Ok { value: (), suspend } => {
                let _ = suspend;
            }
        }
        ret(
            ctx2,
            (
                Case {
                    constructor: cons_name_v,
                    arg_names: binders_v,
                    expr: err,
                },
                dead_valuation,
                unknown_name(&dead_unknown).clone(),
            ),
        )
    };
    let regular = |ctx2: &mut ExplorerCtx<'_>| {
        let p_case_expr = match local(
            ctx2,
            |params| {
                let mut params = params.clone();
                params.match_depth -= 1;
                params
            },
            |ctx3| {
                let t_wrap = t.clone();
                let t_gen = t.clone();
                let p_scrutinee = p_scrutinee.clone();
                let cons_name = cons_name.clone();
                let binders = binders.clone();
                in_context(
                    ctx3,
                    Rc::new(move |p: &RProgram| {
                        Program {
                            content: BareProgram::PMatch(Box::new(p_scrutinee.clone()), vec![
                                Case {
                                    constructor: cons_name.clone(),
                                    arg_names: binders.clone(),
                                    expr: p.clone(),
                                },
                            ]),
                            type_of: t_wrap.clone(),
                        }
                    }),
                    |ctx4| generate_i(ctx4, &case_env, &t_gen),
                )
            },
        ) {
            Step::Fail => return Step::Fail,
            Step::Ok { value: v, suspend } => {
                let _ = suspend;
                v
            }
        };
        ret(
            ctx2,
            (
                Case {
                    constructor: cons_name.clone(),
                    arg_names: binders.clone(),
                    expr: p_case_expr,
                },
                ftrue(),
                crate::logic::DONT_CARE.to_string(),
            ),
        )
    };
    ifte(ctx, vacuous, ret, regular)
}

/// Shared preamble of `generateFirstCase` and `generateCase`: instantiate the
/// constructor, unify with the scrutinee type, bind the arguments, and return
/// the bound types, binder names, bindings, the case environment (with the
/// applicability assumption), and the applicability assumption `ass`.
fn case_common(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    scr_var: &Formula,
    p_scrutinee: &RProgram,
    cons_name: &Id,
) -> Step<(RType, Vec<Id>, Vec<(Id, RType)>, Rc<Environment>, Formula)> {
    let cons_sch = match all_symbols(env).get(cons_name) {
        None => {
            return throw_error_with_description(
                ctx,
                text(&format!(
                    "Datatype constructor {cons_name} not found in the environment"
                )),
            );
        }
        Some(sch) => sch.clone(),
    };
    let cons_t = match instantiate(ctx, env, &cons_sch, true, &[]) {
        Step::Fail => return Step::Fail,
        Step::Ok { value: t, suspend } => {
            let _ = suspend;
            t
        }
    };
    match run_in_solver(ctx, |solver| {
        match_cons_type(solver, &last_type(&cons_t), &p_scrutinee.type_of)
    }) {
        Step::Fail => return Step::Fail,
        Step::Ok { value: (), suspend } => {
            let _ = suspend;
        }
    }
    let cons_t1 = current_assignment_tass(&ctx.state.typing().type_assignment, &cons_t);
    let mut binders = Vec::new();
    for _ in 0..arity(&cons_t1) {
        match fresh_var(ctx, env, "x") {
            Step::Fail => return Step::Fail,
            Step::Ok { value: x, suspend } => {
                let _ = suspend;
                binders.push(x);
            }
        }
    }
    let (syms, ass) = match case_symbols(ctx, env, scr_var, &binders, &cons_t1) {
        Step::Fail => return Step::Fail,
        Step::Ok { value: v, suspend } => {
            let _ = suspend;
            v
        }
    };
    // NOTE: `ass` is the return type of the constructor applied to the
    // scrutinee; the binders are added in reverse order (mirroring the
    // reference's `foldr`). The assumption itself is added by the callers:
    // `generateFirstCase` assumes the raw `ass`, while `generateCase` assumes
    // its fresh fixed-valuation unknown (so that the recheck can retract it).
    let mut case_env: Rc<Environment> = env.clone();
    for (name, typ) in syms.iter().rev() {
        case_env = Rc::new(add_variable(name, typ, &case_env));
    }
    ret(ctx, (cons_t1, binders, syms, case_env, ass))
}

/// `generateCase`: generate one case of a match.
pub fn generate_case(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    scr_var: &Formula,
    p_scrutinee: &RProgram,
    t: &RType,
    cons_name: &Id,
) -> Step<(Case<RType>, ExplorerFn<()>)> {
    let (_cons_t, binders, _syms, case_env, ass) =
        match case_common(ctx, env, scr_var, p_scrutinee, cons_name) {
            Step::Fail => return Step::Fail,
            Step::Ok { value: v, suspend } => {
                let _ = suspend;
                v
            }
        };
    let unfold_syms = ctx.reader.params.unfold_locals;
    let c_unknown = match fresh_unknown(ctx, "M") {
        Step::Fail => return Step::Fail,
        Step::Ok { value: u, suspend } => {
            let _ = suspend;
            u
        }
    };
    match run_in_solver(ctx, |solver| {
        add_fixed_unknown(
            solver,
            unknown_name(&c_unknown),
            &BTreeSet::from([ass.clone()]),
        );
        Ok(())
    }) {
        Step::Fail => return Step::Fail,
        Step::Ok { value: (), suspend } => {
            let _ = suspend;
        }
    }
    // `generateCase` assumes the fresh fixed-valuation unknown, not the raw `ass`.
    let case_env = Rc::new(add_assumption(c_unknown.clone(), &case_env));
    let case_env = if unfold_syms {
        Rc::new(unfold_all_variables(&case_env))
    } else {
        case_env
    };
    let p_case_expr = {
        let t = t.clone();
        let t_ref = t.clone();
        let p_scrutinee = p_scrutinee.clone();
        let cons_name = cons_name.clone();
        let binders = binders.clone();
        let gen_fn = move |ctx2: &mut ExplorerCtx<'_>| {
            let t1 = t.clone();
            let p_scrutinee1 = p_scrutinee.clone();
            let cons_name1 = cons_name.clone();
            let binders1 = binders.clone();
            let ctx_wrap = Rc::new(move |p: &RProgram| {
                Program {
                    content: BareProgram::PMatch(Box::new(p_scrutinee1.clone()), vec![Case {
                        constructor: cons_name1.clone(),
                        arg_names: binders1.clone(),
                        expr: p.clone(),
                    }]),
                    type_of: t1.clone(),
                }
            });
            local(
                ctx2,
                |params| {
                    let mut params = params.clone();
                    params.match_depth -= 1;
                    params
                },
                |ctx3| {
                    let t2 = t.clone();
                    let case_env1 = case_env.clone();
                    let err_gen: ExplorerFn<RProgram> =
                        Rc::new(move |c4| generate_error(c4, &case_env1));
                    let case_env2 = case_env.clone();
                    let i_gen: ExplorerFn<RProgram> =
                        Rc::new(move |c4| generate_i(c4, &case_env2, &t2));
                    in_context(ctx3, ctx_wrap, |ctx4| mplus(ctx4, err_gen, i_gen))
                },
            )
        };
        match optional_in_partial(ctx, &t_ref, gen_fn) {
            Step::Fail => return Step::Fail,
            Step::Ok { value: p, suspend } => {
                let _ = suspend;
                p
            }
        }
    };
    let recheck: ExplorerFn<()> = if disjoint(
        &symbols_of(&p_case_expr),
        &binders.iter().cloned().collect::<BTreeSet<Id>>(),
    ) {
        Rc::new(move |ctx2| {
            run_in_solver(ctx2, |solver| {
                set_unknown_recheck(
                    solver,
                    unknown_name(&c_unknown),
                    &BTreeSet::new(),
                    &BTreeSet::new(),
                )
            })
        })
    } else {
        Rc::new(|_| mzero())
    };
    ret(
        ctx,
        (
            Case {
                constructor: cons_name.clone(),
                arg_names: binders,
                expr: p_case_expr,
            },
            recheck,
        ),
    )
}

/// `generateMaybeMatchIf`: generate a possibly
/// conditional, possibly matching term, depending on which conditions are
/// abduced.
pub fn generate_maybe_match_if(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    t: &RType,
) -> Step<RProgram> {
    let env_ob = env.clone();
    let t_ob = t.clone();
    // Guess an E-term and abduce a condition and a match-condition for it.
    let one_branch: ExplorerFn<(Vec<Formula>, Formula, Id, RProgram)> = Rc::new(move |ctx2| {
        let match_unknown = match fresh_unknown(ctx2, "M") {
            Step::Fail => return Step::Fail,
            Step::Ok { value: u, suspend } => {
                let _ = suspend;
                u
            }
        };
        add_constraint(
            ctx2,
            Constraint::WellFormedMatchCond(env_ob.clone(), match_unknown.clone()),
        );
        let cond_unknown = match fresh_unknown(ctx2, "C") {
            Step::Fail => return Step::Fail,
            Step::Ok { value: u, suspend } => {
                let _ = suspend;
                u
            }
        };
        add_constraint(
            ctx2,
            Constraint::WellFormedCond(env_ob.clone(), cond_unknown.clone()),
        );
        let match_unknown_1 = match_unknown.clone();
        let cond_unknown_1 = cond_unknown.clone();
        let match_unknown_2 = match_unknown.clone();
        let cond_unknown_2 = cond_unknown.clone();
        cut(ctx2, |ctx3| {
            // `generateEOrError (addAssumption matchUnknown . addAssumption
            // condUnknown $ env) t` is bound with `<-`
            // INSIDE this continuation: when `generateError` succeeds but the
            // `badError` guard below fails, the `mzero` backtracks into the
            // `generateError mplus generateE` and resumes the E-term
            // enumeration (`generateEOrError env typ = generateError env
            // mplus generateE env typ`). Using `bind` (not `cut`) keeps that
            // suspension alive.
            let match_unknown_b = match_unknown_1.clone();
            let cond_unknown_b = cond_unknown_1.clone();
            let mu_outer = match_unknown_2.clone();
            let cu_outer = cond_unknown_2.clone();
            bind(
                ctx3,
                |c4| {
                    let env_ass = Rc::new(add_assumption(match_unknown_b.clone(), &env_ob));
                    let env_ass = Rc::new(add_assumption(cond_unknown_b.clone(), &env_ass));
                    let env_e = env_ass.clone();
                    let err_gen: ExplorerFn<RProgram> =
                        Rc::new(move |c5| generate_error(c5, &env_e));
                    let env_e2 = env_ass;
                    let e_t = t_ob.clone();
                    let e_gen: ExplorerFn<RProgram> =
                        Rc::new(move |c5| generate_e(c5, &env_e2, &e_t));
                    mplus(c4, err_gen, e_gen)
                },
                move |c4, p0| {
                    let mu = mu_outer.clone();
                    let cu = cu_outer.clone();
                    let cu_name = unknown_name(&cond_unknown_2).clone();
                    // `matchValuation <- Set.toList <$> currentValuation
                    // matchUnknown`: the valuation groups are ordered weakest
                    // to strongest; a failing guard below resumes the next
                    // group before the E-term enumeration.
                    bind(
                        c4,
                        move |c5| current_valuation(c5, &mu),
                        move |c5, match_valuation| {
                            let match_vars: Vec<Formula> = match_valuation
                                .iter()
                                .flat_map(vars_of)
                                .collect::<BTreeSet<Formula>>()
                                .into_iter()
                                .collect();
                            let cu1 = cu.clone();
                            let p0c = p0.clone();
                            let cu_name1 = cu_name.clone();
                            bind(
                                c5,
                                move |c6| current_valuation(c6, &cu1),
                                move |c6, cond_valuation| {
                                    // Have we abduced a nontrivial vacuousness
                                    // condition that is not a match branch?
                                    // Such vacuousness conditions are not
                                    // productive, so discard the error
                                    // (backtracking into the valuation groups
                                    // and then the E-term enumeration).
                                    let bad_error = is_error(&p0c) && match_vars.len() != 1;
                                    if bad_error {
                                        return Step::Fail;
                                    }
                                    // Group the match conditions by the
                                    // variable they mention.
                                    let match_conds: Vec<Formula> = match_vars
                                        .iter()
                                        .map(|var| {
                                            conjunction(
                                                &match_valuation
                                                    .iter()
                                                    .filter(|f| vars_of(f).contains(var))
                                                    .cloned()
                                                    .collect(),
                                            )
                                        })
                                        .collect();
                                    let d = c6.reader.params.match_depth;
                                    if match_conds.len() > d {
                                        return Step::Fail;
                                    }
                                    ret(
                                        c6,
                                        (
                                            match_conds,
                                            conjunction(&cond_valuation),
                                            cu_name1.clone(),
                                            p0c.clone(),
                                        ),
                                    )
                                },
                            )
                        },
                    )
                },
            )
        })
    });
    // Proceed after a solution under assumption `cond` and match-assumption.
    let env2 = env.clone();
    let t2 = t.clone();
    let other_branches = Rc::new(
        move |ctx2: &mut ExplorerCtx<'_>,
              (match_conds, cond, cond_unknown, p0): (Vec<Formula>, Formula, Id, RProgram)|
              -> Step<RProgram> {
            let env_cond = Rc::new(add_assumption(cond.clone(), &env2));
            let p_then = match cut(ctx2, |ctx3| {
                generate_matches_for(ctx3, &env_cond, &match_conds, &p0, &t2)
            }) {
                Step::Fail => return Step::Fail,
                Step::Ok { value: p, suspend } => {
                    let _ = suspend;
                    p
                }
            };
            generate_else(ctx2, &env2, &t2, &cond, &cond_unknown, &p_then)
        },
    );
    let env3 = env.clone();
    let t3 = t.clone();
    let generate_match_fn: ExplorerFn<RProgram> =
        Rc::new(move |ctx2| generate_match(ctx2, &env3, &t3));
    let branch_fn: ExplorerFn<RProgram> = Rc::new(move |ctx2| {
        let one_branch = one_branch.clone();
        let other_branches = other_branches.clone();
        bind(
            ctx2,
            move |c| one_branch(c),
            move |c, t| other_branches(c, t),
        )
    });
    mplus(ctx, branch_fn, generate_match_fn)
}

/// `generateMatchesFor`: generate the matches for the
/// abduced match conditions.
pub fn generate_matches_for(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    match_conds: &[Formula],
    p_base_case: &RProgram,
    t: &RType,
) -> Step<RProgram> {
    let (first, rest) = match match_conds.split_first() {
        None => return ret(ctx, p_base_case.clone()),
        Some(v) => v,
    };
    let Formula::Binary(BinOp::Eq, match_var, rhs) = first else {
        return Step::Fail;
    };
    let scr_var = match &**match_var {
        Formula::Var(_, x) => x.clone(),
        _ => return Step::Fail,
    };
    let c = match &**rhs {
        Formula::Cons(_, c, _) => c.clone(),
        _ => return Step::Fail,
    };
    let scr_sch = match symbols_of_arity(0, env).get(&scr_var) {
        None => return Step::Fail,
        Some(sch) => sch.clone(),
    };
    let scr_t =
        current_assignment_tass(&ctx.state.typing().type_assignment, &to_monotype(&scr_sch));
    let TypeSkeleton::ScalarT(BaseType::DatatypeT(scr_dt, ..), _) = &scr_t else {
        return Step::Fail;
    };
    let p_scrutinee = Program {
        content: BareProgram::PSymbol(scr_var),
        type_of: scr_t.clone(),
    };
    let ctors = env
        .datatypes
        .get(scr_dt)
        .map(|dt| dt.constructors.clone())
        .unwrap_or_default();
    let env1 = Rc::new(add_scrutinee(p_scrutinee.clone(), env));
    // The base case (under the match condition).
    let p_base_case1 = match cut(ctx, |ctx2| {
        let env2 = Rc::new(add_assumption(first.clone(), &env1));
        let p_scrutinee = p_scrutinee.clone();
        let t1 = t.clone();
        let t3 = t1.clone();
        let c = c.clone();
        in_context(
            ctx2,
            Rc::new(move |p: &RProgram| {
                Program {
                    content: BareProgram::PMatch(Box::new(p_scrutinee.clone()), vec![Case {
                        constructor: c.clone(),
                        arg_names: Vec::new(),
                        expr: p.clone(),
                    }]),
                    type_of: t1.clone(),
                }
            }),
            move |ctx3| generate_matches_for(&mut *ctx3, &env2, rest, p_base_case, &t3),
        )
    }) {
        Step::Fail => return Step::Fail,
        Step::Ok { value: v, suspend } => {
            let _ = suspend;
            v
        }
    };
    // Generate the other cases, eliminating branches when possible.
    let mut previous_cases = vec![Case {
        constructor: c.clone(),
        arg_names: Vec::new(),
        expr: p_base_case1,
    }];
    let mut other_ctors: Vec<Id> = ctors.iter().filter(|ctor| *ctor != &c).cloned().collect();
    loop {
        let ctor = match other_ctors.first() {
            None => {
                return ret(ctx, Program {
                    content: BareProgram::PMatch(Box::new(p_scrutinee.clone()), previous_cases),
                    type_of: t.clone(),
                });
            }
            Some(ctor) => ctor.clone(),
        };
        other_ctors = other_ctors[1..].to_vec();
        let (case, recheck) = match cut(ctx, |ctx2| {
            generate_case(
                ctx2,
                &env1,
                &scr_var_formula(&p_scrutinee),
                &p_scrutinee,
                t,
                &ctor,
            )
        }) {
            Step::Fail => return Step::Fail,
            Step::Ok { value: v, suspend } => {
                let _ = suspend;
                v
            }
        };
        let eliminated = match try_eliminate_branching(ctx, &case.expr, recheck) {
            Step::Fail => return Step::Fail,
            Step::Ok { value: b, suspend } => {
                let _ = suspend;
                b
            }
        };
        if eliminated {
            return ret(ctx, case.expr);
        }
        previous_cases.push(case);
    }
}

/// The formula representing the scrutinee variable (its name).
fn scr_var_formula(p_scrutinee: &RProgram) -> Formula {
    let BareProgram::PSymbol(x) = &p_scrutinee.content else {
        panic!("scr_var_formula: scrutinee is not a variable");
    };
    Formula::Var(
        Box::new(to_sort(&base_type_of(&p_scrutinee.type_of))),
        x.clone(),
    )
}

/// `generateE`: explore all elimination terms of type
/// `typ` in `env` (bottom-up phase of bidirectional typechecking).
///
/// Mirrors the reference's lazy `(Program pTerm pTyp) <- generateEUpTo env typ
/// d`: on failure of the final checks, the E-term enumeration is resumed with
/// the next candidate.
pub fn generate_e(ctx: &mut ExplorerCtx<'_>, env: &Rc<Environment>, typ: &RType) -> Step<RProgram> {
    // Starting E-term enumeration in a new environment: clear the store.
    ctx.persistent.term_memo = BTreeMap::new();
    let d = ctx.reader.params.e_guess_depth;
    let env = env.clone();
    let typ = typ.clone();
    match generate_e_up_to(ctx, &env, &typ, d) {
        Step::Fail => Step::Fail,
        Step::Ok { value: p, suspend } => generate_e_rest(ctx, &env, &typ, p, suspend),
    }
}

/// The tail of `generateE` after the first enumerated candidate `p`: final
/// type check, auxiliary goals, type finalization and lambda-lets; on
/// failure, resume the enumeration with the next candidate (iteratively).
fn generate_e_rest(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    typ: &RType,
    p: RProgram,
    suspend: Suspend<RProgram>,
) -> Step<RProgram> {
    let mut cur = (p, suspend);
    loop {
        let (p, suspend) = cur;
        let (p_term, p_typ) = (p.content, p.type_of);
        // Final type checking pass that eliminates all free type variables.
        match run_in_solver(ctx, |solver| {
            solver.state.is_final = true;
            let res = solve_type_constraints(solver);
            solver.state.is_final = false;
            res
        }) {
            Step::Fail => {
                match resume(ctx, suspend) {
                    Step::Fail => return Step::Fail,
                    Step::Ok {
                        value: p2,
                        suspend: sus2,
                    } => {
                        cur = (p2, sus2);
                        continue;
                    }
                }
            }
            Step::Ok { value: (), suspend } => {
                let _ = suspend;
            }
        }
        // Remember the unsolved auxiliary goals.
        let new_goals: Vec<Id> = ctx
            .state
            .aux_goals
            .iter()
            .map(|g| g.g_name.clone())
            .collect();
        match generate_aux_goals(ctx) {
            Step::Fail => {
                match resume(ctx, suspend) {
                    Step::Fail => return Step::Fail,
                    Step::Ok {
                        value: p2,
                        suspend: sus2,
                    } => {
                        cur = (p2, sus2);
                        continue;
                    }
                }
            }
            Step::Ok { value: (), suspend } => {
                let _ = suspend;
            }
        }
        // Finalize the type of the synthesized term.
        let p_typ1 = current_assignment_tass(&ctx.state.typing().type_assignment, &p_typ);
        let body = Program {
            content: p_term,
            type_of: p_typ1.clone(),
        };
        let env = env.clone();
        let typ = typ.clone();
        let suspend = suspend;
        return match add_lambda_lets(ctx, &p_typ1, body, &new_goals) {
            Step::Fail => generate_e_next(ctx, &env, &typ, suspend),
            Step::Ok {
                value,
                suspend: sus_ll,
            } => {
                Step::Ok {
                    value,
                    suspend: Suspend {
                        state: sus_ll.state.clone(),
                        reader: ctx.reader.clone(),
                        next: Box::new(move |ctx2| {
                            match resume(ctx2, sus_ll) {
                                Step::Fail => generate_e_next(ctx2, &env, &typ, suspend),
                                ok => ok,
                            }
                        }),
                    },
                }
            }
        };
    }
}

/// Resume the E-term enumeration for the next candidate and run the tail of
/// `generateE` on it.
fn generate_e_next(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    typ: &RType,
    suspend: Suspend<RProgram>,
) -> Step<RProgram> {
    match resume(ctx, suspend) {
        Step::Fail => Step::Fail,
        Step::Ok { value: p, suspend } => generate_e_rest(ctx, env, typ, p, suspend),
    }
}

/// `addLambdaLets`: check if some of the auxiliary goal
/// solutions are large and have to be lifted into lambda-lets.
fn add_lambda_lets(
    ctx: &mut ExplorerCtx<'_>,
    t: &RType,
    body: RProgram,
    goals: &[Id],
) -> Step<RProgram> {
    let (g, rest) = match goals.split_first() {
        None => return ret(ctx, body),
        Some(v) => v,
    };
    let p_aux = match ctx.state.solved_aux_goals.get(g) {
        None => panic!("addLambdaLets: no solution for goal {g}"),
        Some(p) => p.clone(),
    };
    if program_node_count(&p_aux) > 5 {
        add_lambda_lets(
            ctx,
            t,
            Program {
                content: BareProgram::PLet(g.clone(), Box::new(u_hole()), Box::new(body)),
                type_of: t.clone(),
            },
            rest,
        )
    } else {
        add_lambda_lets(ctx, t, body, rest)
    }
}

/// `generateEUpTo`: explore all applications of type
/// `typ` in `env` of depth up to `d`.
pub fn generate_e_up_to(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    typ: &RType,
    d: usize,
) -> Step<RProgram> {
    let env = env.clone();
    let typ = typ.clone();
    let alts: Vec<ExplorerFn<RProgram>> = (0..=d)
        .map(|i| -> ExplorerFn<RProgram> {
            let env = env.clone();
            let typ = typ.clone();
            Rc::new(move |ctx2: &mut ExplorerCtx<'_>| generate_e_at(ctx2, &env, &typ, i))
        })
        .collect();
    choice(ctx, alts)
}

/// `generateEAt`: explore all applications of type
/// `typ` in `env` of depth exactly `d`.
pub fn generate_e_at(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    typ: &RType,
    d: usize,
) -> Step<RProgram> {
    let use_mem = ctx.reader.params.use_memoization;
    if !use_mem || d == 0 {
        let p = match enumerate_at(ctx, env, typ, d) {
            Step::Fail => return Step::Fail,
            Step::Ok { value: p, suspend } => (p, suspend),
        };
        return check_e_loop(ctx, env, typ, p.0, p.1, None);
    }
    // Try to fetch from the memoization store.
    let start_state = ctx.state.clone();
    let memo_key = MemoKey {
        key_type_arity: arity(typ),
        key_last_shape: shape(&type_substitute(
            &ctx.state.typing().type_assignment,
            &last_type(typ),
        )),
        key_state: start_state,
        key_depth: d,
    };
    let memo_results = ctx.persistent.term_memo.get(&memo_key).cloned();
    if let Some(results) = memo_results {
        let env = env.clone();
        let typ = typ.clone();
        let alts: Vec<ExplorerFn<RProgram>> = results
            .into_iter()
            .map(|(p, final_state)| -> ExplorerFn<RProgram> {
                let env = env.clone();
                let typ = typ.clone();
                Rc::new(move |ctx2: &mut ExplorerCtx<'_>| {
                    ctx2.state = final_state.clone();
                    match check_e(ctx2, &env, &typ, &p) {
                        Step::Fail => Step::Fail,
                        Step::Ok { value: (), suspend } => {
                            let _ = suspend;
                            ret(ctx2, p.clone())
                        }
                    }
                })
            })
            .collect();
        choice(ctx, alts)
    } else {
        let p = match enumerate_at(ctx, env, typ, d) {
            Step::Fail => return Step::Fail,
            Step::Ok { value: p, suspend } => (p, suspend),
        };
        check_e_loop(ctx, env, typ, p.0, p.1, Some(Rc::new(memo_key)))
    }
}

/// Check `p` against `typ`; on failure, resume the enumerator `suspend` and
/// check the next candidate (mirroring the reference's `p <- enumerateAt ...
/// checkE env typ p`, where `mzero` from `checkE` backtracks into the
/// `msum`).
///
/// With memoization, EVERY candidate is stored under `memo_key` before its
/// check (the reference's `p <- enumerateAt ...; memoize (p, finalState);
/// checkE`, where the continuation re-runs per candidate and the memo list
/// grows with `Map.insertWith (flip (++))`): a later hit replays the list in
/// order until one candidate passes.
fn check_e_loop(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    typ: &RType,
    p: RProgram,
    suspend: Suspend<RProgram>,
    memo_key: Option<Rc<MemoKey>>,
) -> Step<RProgram> {
    let env = env.clone();
    let typ = typ.clone();
    // Iterative loop: candidate failures resume the enumerator in a flat
    // loop (recursing per candidate would nest one frame per candidate and
    // hold a cloned environment in each).
    let mut cur = (p, suspend);
    loop {
        // Store the candidate (and the state before its check) in the memo
        // (the reference's `p <- enumerateAt ...; memoize (p, finalState);
        // checkE` re-runs this continuation per candidate).
        if let Some(key) = &memo_key {
            let final_state = ctx.state.clone();
            // The key itself never changes inside this loop: clone it only
            // when the entry is created for the first time.
            match ctx.persistent.term_memo.get_mut(key) {
                Some(list) => list.push((cur.0.clone(), final_state)),
                None => {
                    ctx.persistent
                        .term_memo
                        .insert((**key).clone(), vec![(cur.0.clone(), final_state)]);
                }
            }
        }
        match check_e(ctx, &env, &typ, &cur.0) {
            Step::Fail => {
                match resume(ctx, cur.1) {
                    Step::Fail => return Step::Fail,
                    Step::Ok {
                        value: p2,
                        suspend: sus2,
                    } => {
                        cur = (p2, sus2);
                    }
                }
            }
            Step::Ok {
                value: (),
                suspend: _,
            } => {
                let state = ctx.state.clone();
                let reader = ctx.reader.clone();
                let env1 = env.clone();
                let typ1 = typ.clone();
                let cur1 = cur;
                return Step::Ok {
                    value: cur1.0.clone(),
                    suspend: Suspend {
                        state,
                        reader,
                        next: Box::new(move |ctx2| {
                            match resume(ctx2, cur1.1) {
                                Step::Fail => Step::Fail,
                                Step::Ok {
                                    value: p2,
                                    suspend: sus2,
                                } => check_e_loop(ctx2, &env1, &typ1, p2, sus2, memo_key.clone()),
                            }
                        }),
                    },
                };
            }
        }
    }
}

/// `checkE`: perform a gradual check that `p` has type
/// `typ` in `env`.
pub fn check_e(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    typ: &RType,
    p: &RProgram,
) -> Step<()> {
    let incremental = ctx.reader.params.incremental_checking;
    let consistency = ctx.reader.params.consistency_checking;
    // Add a subtyping check, unless it's a function type and incremental
    // checking is disabled.
    if incremental || arity(typ) == 0 {
        add_constraint(
            ctx,
            Constraint::Subtype(
                env.clone(),
                p.type_of.clone(),
                typ.clone(),
                false,
                String::new(),
            ),
        );
    }
    // Add a consistency constraint for function types.
    if consistency && arity(typ) > 0 {
        add_constraint(
            ctx,
            Constraint::Subtype(
                env.clone(),
                p.type_of.clone(),
                typ.clone(),
                true,
                String::new(),
            ),
        );
    }
    let f_typ = finalize_type_state(ctx.state.typing(), typ);
    let pos = ctx.reader.params.source_pos.clone();
    let ctx_p = ctx.reader.context.clone();
    ctx.state.typing_mut().error_context = (
        pos,
        soft_break(
            soft_break(
                soft_break(
                    soft_break(text("when checking"), pretty_program(p)),
                    text("::"),
                ),
                pretty_type(&f_typ),
            ),
            vsp(text("in"), pretty_program(&ctx_p(p))),
        ),
    );
    match run_in_solver(ctx, solve_type_constraints) {
        Step::Fail => return Step::Fail,
        Step::Ok { value: (), suspend } => {
            let _ = suspend;
        }
    }
    ctx.state.typing_mut().error_context = (no_pos(), empty());
    ret(ctx, ())
}

/// `enumerateAt`: enumerate programs of type `typ` in
/// `env` of depth exactly `d`.
pub fn enumerate_at(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    typ: &RType,
    d: usize,
) -> Step<RProgram> {
    if d == 0 {
        enumerate_at_zero(ctx, env, typ)
    } else {
        let max_arity = env.symbols.last_key_value().map(|(k, _)| *k).unwrap_or(0);
        match guard(ctx, arity(typ) < max_arity) {
            Step::Fail => return Step::Fail,
            Step::Ok { .. } => {}
        }
        type GenFn = Rc<dyn Fn(&mut ExplorerCtx<'_>, &RType) -> Step<RProgram>>;
        let typ = typ.clone();
        let env1 = env.clone();
        let gen_fun_up_to: GenFn =
            Rc::new(move |ctx2, t| generate_e_up_to(&mut *ctx2, &env1, t, d - 1));
        let env2 = env.clone();
        let gen_arg_exact: GenFn =
            Rc::new(move |ctx2, t| generate_e_at(&mut *ctx2, &env2, t, d - 1));
        let env3 = env.clone();
        let gen_fun_exact: GenFn = Rc::new(move |ctx2, t| generate_e_at(&mut *ctx2, &env3, t, d));
        let env4 = env.clone();
        let gen_arg_up_to: GenFn =
            Rc::new(move |ctx2, t| generate_e_up_to(&mut *ctx2, &env4, t, d - 1));
        let env5 = env.clone();
        let typ1 = typ.clone();
        let app1: ExplorerFn<RProgram> = Rc::new(move |ctx2| {
            generate_app(
                ctx2,
                &env5,
                &typ1,
                gen_fun_up_to.clone(),
                gen_arg_exact.clone(),
            )
        });
        let env6 = env.clone();
        let typ2 = typ;
        let app2: ExplorerFn<RProgram> = Rc::new(move |ctx2| {
            generate_app(
                ctx2,
                &env6,
                &typ2,
                gen_fun_exact.clone(),
                gen_arg_up_to.clone(),
            )
        });
        mplus(ctx, app1, app2)
    }
}

/// `enumerateAt` at depth 0.
fn enumerate_at_zero(
    ctx: &mut ExplorerCtx<'_>,
    env: &Rc<Environment>,
    typ: &RType,
) -> Step<RProgram> {
    let a = arity(typ);
    let _ = a;
    let symbols: Vec<(Id, RSchema)> = symbols_of_arity(arity(typ), env).into_iter().collect();
    let set_constructors = [
        crate::types::EMPTY_SET_CTOR,
        crate::types::SINGLETON_CTOR,
        crate::types::INSERT_SET_CTOR,
    ];
    let use_counts = ctx.state.symbol_use_count.clone();
    let mut symbols: Vec<(Id, RSchema)> = symbols
        .into_iter()
        .filter(|(x, _)| !set_constructors.contains(&x.as_str()))
        .collect();
    if arity(typ) == 0 {
        symbols.sort_by(|a, b| {
            let ka = (
                env.constants.contains(&a.0),
                use_counts.get(&a.0).copied().unwrap_or(0),
            );
            let kb = (
                env.constants.contains(&b.0),
                use_counts.get(&b.0).copied().unwrap_or(0),
            );
            mapped_compare(|k: &(bool, usize)| k, &ka, &kb)
        });
    } else {
        symbols.sort_by(|a, b| {
            let ka = (
                !env.constants.contains(&a.0),
                use_counts.get(&a.0).copied().unwrap_or(0),
            );
            let kb = (
                !env.constants.contains(&b.0),
                use_counts.get(&b.0).copied().unwrap_or(0),
            );
            mapped_compare(|k: &(bool, usize)| k, &ka, &kb)
        });
    }
    let env = env.clone();
    let alts: Vec<ExplorerFn<RProgram>> = symbols
        .into_iter()
        .map(|(name, sch)| -> ExplorerFn<RProgram> {
            let env = env.clone();
            Rc::new(move |ctx2: &mut ExplorerCtx<'_>| {
                if env.let_bound.contains(&name) {
                    return Step::Fail;
                }
                let t = match symbol_type(ctx2, &env, &name, &sch) {
                    Step::Fail => return Step::Fail,
                    Step::Ok { value: t, suspend } => {
                        let _ = suspend;
                        t
                    }
                };
                let p = Program {
                    content: BareProgram::PSymbol(name.clone()),
                    type_of: t,
                };
                let n = Rc::make_mut(&mut ctx2.state.symbol_use_count)
                    .entry(name.clone())
                    .or_insert(0);
                *n += 1;
                if let Some(sc) = env.shape_constraints.get(&name) {
                    add_constraint(
                        ctx2,
                        Constraint::Subtype(
                            env.clone(),
                            refine_bot(&env, &shape(&p.type_of)),
                            refine_top(&env, sc),
                            false,
                            String::new(),
                        ),
                    );
                }
                ret(ctx2, p)
            })
        })
        .collect();
    choice(ctx, alts)
}

/// `generateApp`: generate an application of a function
/// of type `? -> typ`.
///
/// Mirrors the reference's `fun <- genFun ...; arg <- genArg ...; return
/// (PApp fun arg)`: the suspensions of both the function and the argument
/// enumerations are preserved, so on backtracking the next argument is tried
/// first, and only when the argument enumeration is exhausted is the next
/// function candidate picked.
fn generate_app<'a>(
    ctx: &mut ExplorerCtx<'a>,
    env: &Rc<Environment>,
    typ: &RType,
    gen_fun: Rc<dyn Fn(&mut ExplorerCtx<'_>, &RType) -> Step<RProgram>>,
    gen_arg: Rc<dyn Fn(&mut ExplorerCtx<'_>, &RType) -> Step<RProgram>>,
) -> Step<RProgram> {
    let x = match fresh_id(ctx, "X") {
        Step::Fail => return Step::Fail,
        Step::Ok { value: x, suspend } => {
            let _ = suspend;
            x
        }
    };
    // Find all functions that unify with `? -> typ`.
    let x1 = x;
    let typ1 = typ.clone();
    let fun = match in_context(
        ctx,
        Rc::new(move |p: &RProgram| {
            Program {
                content: BareProgram::PApp(Box::new(p.clone()), Box::new(u_hole())),
                type_of: typ1.clone(),
            }
        }),
        |ctx2| {
            gen_fun(
                ctx2,
                &TypeSkeleton::FunctionT(
                    x1.clone(),
                    Box::new(TypeSkeleton::AnyT),
                    Box::new(typ.clone()),
                ),
            )
        },
    ) {
        Step::Fail => return Step::Fail,
        Step::Ok { value: f, suspend } => (f, suspend),
    };
    let (fun, sus_fun) = fun;
    let (x_name, t_arg, t_res) = match &fun.type_of {
        TypeSkeleton::FunctionT(x, t_arg, t_res) => {
            (x.clone(), (**t_arg).clone(), (**t_res).clone())
        }
        _ => return Step::Fail,
    };
    if is_function_type(&t_arg) {
        // Higher-order argument: its value is not required for the function
        // type, return a placeholder and enqueue an auxiliary goal. The
        // function enumeration is NOT exhausted here: the reference's
        // `fun <- ...` bind keeps the stream alive, so if this application
        // fails (or no auxiliary functions are allowed), backtracking
        // resumes the enumeration with the next function candidate.
        let d = ctx.reader.params.aux_depth;
        if d <= 0 {
            let env = env.clone();
            let gen_arg = gen_arg.clone();
            return resume_next_fun(ctx, &env, &gen_arg, sus_fun);
        }
        let arg = match enqueue_goal(ctx, env, &t_arg, &untyped(BareProgram::PHole), d - 1) {
            Step::Fail => {
                let env = env.clone();
                let gen_arg = gen_arg.clone();
                return resume_next_fun(ctx, &env, &gen_arg, sus_fun);
            }
            Step::Ok { value: a, suspend } => {
                let _ = suspend;
                a
            }
        };
        let app = Program {
            content: BareProgram::PApp(Box::new(fun), Box::new(arg)),
            type_of: t_res,
        };
        let env = env.clone();
        let gen_arg = gen_arg.clone();
        Step::Ok {
            value: app,
            suspend: Suspend {
                state: ctx.state.clone(),
                reader: ctx.reader.clone(),
                next: Box::new(move |ctx2| resume_next_fun(ctx2, &env, &gen_arg, sus_fun)),
            },
        }
    } else {
        // First-order argument: generate now, resuming the argument
        // enumeration on backtracking (`arg <- ... genArg env tArg`).
        let env = env.clone();
        let gen_arg = gen_arg.clone();
        apps_with_args(
            ctx,
            &env,
            &x_name,
            &t_arg,
            &t_res,
            &fun,
            gen_arg,
            Some(sus_fun),
        )
    }
}

/// Enumerate `PApp fun arg` for all arguments `arg` of `gen_arg`; when the
/// argument enumeration is exhausted, resume the function enumeration `sus_fun`
/// and start over (the continuation of `arg <- genArg env tArg` in
/// `generateApp`).
#[allow(clippy::too_many_arguments)]
fn apps_with_args<'a>(
    ctx: &mut ExplorerCtx<'a>,
    env: &Rc<Environment>,
    x_name: &Id,
    t_arg: &RType,
    t_res: &RType,
    fun: &RProgram,
    gen_arg: Rc<dyn Fn(&mut ExplorerCtx<'_>, &RType) -> Step<RProgram>>,
    sus_fun: Option<Suspend<RProgram>>,
) -> Step<RProgram> {
    // The argument enumeration runs under `local (eGuessDepth - 1)` and the
    // application context; its suspensions carry that reader, so every resume
    // re-enters the same local/context scope.
    let fun1 = fun.clone();
    let t_res1 = t_res.clone();
    let gen_arg1 = gen_arg.clone();
    let arg = match local(
        ctx,
        |params| {
            let mut params = params.clone();
            params.e_guess_depth -= 1;
            params
        },
        |ctx2| {
            let fun = fun1.clone();
            let t_res = t_res1.clone();
            in_context(
                ctx2,
                Rc::new(move |p: &RProgram| {
                    Program {
                        content: BareProgram::PApp(Box::new(fun.clone()), Box::new(p.clone())),
                        type_of: t_res.clone(),
                    }
                }),
                |ctx3| gen_arg1(ctx3, t_arg),
            )
        },
    ) {
        Step::Fail => {
            return match sus_fun {
                None => Step::Fail,
                Some(sus_fun) => resume_next_fun(ctx, env, &gen_arg, sus_fun),
            };
        }
        Step::Ok { value: a, suspend } => (a, suspend),
    };
    let (a, sus_arg) = arg;
    let env = env.clone();
    let x_name = x_name.clone();
    let t_arg = t_arg.clone();
    let t_res = t_res.clone();
    let fun = fun.clone();
    build_app_cont(
        ctx, &env, &x_name, &t_arg, &t_res, &fun, a, sus_arg, gen_arg, sus_fun,
    )
}

/// Build `PApp fun a` with type `appType env a x tRes` and return it together
/// with a suspension that continues with the next argument (or, once the
/// argument enumeration is exhausted, with the next function candidate).
#[allow(clippy::too_many_arguments)]
fn build_app_cont<'a>(
    ctx: &ExplorerCtx<'a>,
    env: &Rc<Environment>,
    x_name: &Id,
    t_arg: &RType,
    t_res: &RType,
    fun: &RProgram,
    a: RProgram,
    sus_arg: Suspend<RProgram>,
    gen_arg: Rc<dyn Fn(&mut ExplorerCtx<'_>, &RType) -> Step<RProgram>>,
    sus_fun: Option<Suspend<RProgram>>,
) -> Step<RProgram> {
    let t_res1 = app_type(env, &a, x_name, t_res);
    let app = Program {
        content: BareProgram::PApp(Box::new(fun.clone()), Box::new(a)),
        type_of: t_res1,
    };
    let env = env.clone();
    let x_name = x_name.clone();
    let t_arg = t_arg.clone();
    let t_res = t_res.clone();
    let fun = fun.clone();
    let gen_arg = gen_arg.clone();
    let next = Box::new(move |ctx2: &mut ExplorerCtx<'_>| {
        match resume(ctx2, sus_arg) {
            Step::Fail => {
                match sus_fun {
                    None => Step::Fail,
                    Some(sus_fun) => resume_next_fun(ctx2, &env, &gen_arg, sus_fun),
                }
            }
            Step::Ok {
                value: a,
                suspend: sus_arg,
            } => {
                build_app_cont(
                    ctx2, &env, &x_name, &t_arg, &t_res, &fun, a, sus_arg, gen_arg, sus_fun,
                )
            }
        }
    });
    Step::Ok {
        value: app,
        suspend: Suspend {
            state: ctx.state.clone(),
            reader: ctx.reader.clone(),
            next,
        },
    }
}

/// Continue with the next function candidate from the function enumeration
/// and enumerate its arguments (`generateApp`'s `fun <- genFun ...` bind).
fn resume_next_fun<'a>(
    ctx: &mut ExplorerCtx<'a>,
    env: &Rc<Environment>,
    gen_arg: &Rc<dyn Fn(&mut ExplorerCtx<'_>, &RType) -> Step<RProgram>>,
    sus_fun: Suspend<RProgram>,
) -> Step<RProgram> {
    match resume(ctx, sus_fun) {
        Step::Fail => Step::Fail,
        Step::Ok {
            value: f,
            suspend: sus_fun,
        } => {
            let (x_name, t_arg, t_res) = match &f.type_of {
                TypeSkeleton::FunctionT(x, t_arg, t_res) => {
                    (x.clone(), (**t_arg).clone(), (**t_res).clone())
                }
                _ => return Step::Fail,
            };
            if is_function_type(&t_arg) {
                // Higher-order argument: enqueue an auxiliary goal. The
                // stream continues: failure resumes the next function
                // candidate (mirrors the reference's bind in `generateApp`).
                let d = ctx.reader.params.aux_depth;
                if d <= 0 {
                    let env = env.clone();
                    let gen_arg = gen_arg.clone();
                    return resume_next_fun(ctx, &env, &gen_arg, sus_fun);
                }
                let arg = match enqueue_goal(ctx, env, &t_arg, &untyped(BareProgram::PHole), d - 1)
                {
                    Step::Fail => {
                        let env = env.clone();
                        let gen_arg = gen_arg.clone();
                        return resume_next_fun(ctx, &env, &gen_arg, sus_fun);
                    }
                    Step::Ok { value: a, suspend } => {
                        let _ = suspend;
                        a
                    }
                };
                let app = Program {
                    content: BareProgram::PApp(Box::new(f), Box::new(arg)),
                    type_of: t_res,
                };
                let env = env.clone();
                let gen_arg = gen_arg.clone();
                Step::Ok {
                    value: app,
                    suspend: Suspend {
                        state: ctx.state.clone(),
                        reader: ctx.reader.clone(),
                        next: Box::new(move |ctx2| resume_next_fun(ctx2, &env, &gen_arg, sus_fun)),
                    },
                }
            } else {
                let gen_arg = gen_arg.clone();
                apps_with_args(
                    ctx,
                    env,
                    &x_name,
                    &t_arg,
                    &t_res,
                    &f,
                    gen_arg,
                    Some(sus_fun),
                )
            }
        }
    }
}

/// `generateAuxGoals`: synthesize the auxiliary goals
/// accumulated in `aux_goals` and store the results in `solved_aux_goals`.
pub fn generate_aux_goals(ctx: &mut ExplorerCtx<'_>) -> Step<()> {
    let (g, gs) = {
        let aux = &*ctx.state.aux_goals;
        let (g, gs) = match aux.split_first() {
            None => return ret(ctx, ()),
            Some(v) => v,
        };
        (g.clone(), gs.to_vec())
    };
    ctx.state.aux_goals = Rc::new(gs);
    let reconstructor = ctx.reader.reconstructor.clone();
    let p = match reconstructor(ctx, &g) {
        Step::Fail => return Step::Fail,
        Step::Ok { value: p, suspend } => {
            let _ = suspend;
            p
        }
    };
    let p = eta_contract(p);
    Rc::make_mut(&mut ctx.state.solved_aux_goals).insert(g.g_name, p);
    generate_aux_goals(ctx)
}

/// `etaContract`.
fn eta_contract(p: RProgram) -> RProgram {
    match eta_contract_prime(&[], &p.content) {
        None => p,
        Some(f) => {
            Program {
                content: f,
                type_of: p.type_of,
            }
        }
    }
}

fn eta_contract_prime<R: Clone>(
    binders: &[Id],
    content: &BareProgram<R>,
) -> Option<BareProgram<R>> {
    match content {
        BareProgram::PFix(_, p) if binders.is_empty() => eta_contract_prime(&[], &p.content),
        BareProgram::PFun(x, p) => {
            let mut binders = binders.to_vec();
            binders.insert(0, x.clone());
            eta_contract_prime(&binders, &p.content)
        }
        BareProgram::PApp(p_fun, arg) if matches!(&arg.content, BareProgram::PSymbol(y) if Some(y) == binders.first().map(|b| b)) => {
            eta_contract_prime(&binders[1..], &p_fun.content)
        }
        BareProgram::PSymbol(_) if binders.is_empty() => Some(content.clone()),
        _ => None,
    }
}

/// `runExplorer`: execute exploration `go` with explorer
/// parameters `e_params` and typing parameters `t_params` in typing state
/// `init_ts`, returning either the first produced program or the most recent
/// type error.
pub fn run_explorer<'a>(
    horn: &'a mut FixPointSolver,
    e_params: Rc<ExplorerParams>,
    t_params: Rc<TypingParams>,
    reconstructor: Reconstructor,
    init_ts: Rc<TypingState>,
    go: impl FnOnce(&mut ExplorerCtx<'a>) -> Step<RProgram>,
) -> Result<RProgram, ErrorMessage> {
    let mut ctx = ExplorerCtx {
        horn,
        reader: ExplorerReader {
            params: e_params.clone(),
            typing_params: t_params,
            reconstructor,
            context: Rc::new(|p| p.clone()),
        },
        state: ExplorerState::initial(init_ts),
        persistent: PersistentState::default(),
    };
    match go(&mut ctx) {
        Step::Ok { value, suspend: _ } => Ok(value),
        Step::Fail => {
            match ctx.persistent.type_errors.last() {
                Some(e) => Err(e.clone()),
                None => {
                    Err(ErrorMessage::new(
                        ErrorKind::SynthesisError,
                        e_params.source_pos.clone(),
                        text(
                            "Synthesis goal is impossible: components or search parameters are insufficient.",
                        ),
                    ))
                }
            }
        }
    }
}

/// Whether `p` is an error program (mirror of `isError`).
#[must_use]
pub const fn is_error(p: &RProgram) -> bool {
    matches!(p.content, BareProgram::PErr)
}

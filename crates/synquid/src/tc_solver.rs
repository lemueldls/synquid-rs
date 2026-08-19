//! Incremental solving of subtyping and well-formedness constraints
//! (mirror of `Synquid.TypeConstraintSolver`).
//!
//! The Haskell reference is the monad stack
//! `StateT TypingState (ReaderT TypingParams (ExceptT ErrorMessage s))` over
//! the horn solver `s`; per the plan we thread state explicitly: `TcSolver`
//! below borrows the `FixPointSolver` (the base monad), the `TypingParams`
//! (reader), and owns the `TypingState`; errors are plain `Result`s (the
//! `ExceptT` layer).

use std::{
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

use crate::{
    error::{ErrorKind, ErrorMessage, SourcePos, no_pos},
    horn_solver::FixPointSolver,
    logic::{
        BinOp, Formula, QMap, QSpace, Sort, Substitution, VALUE_VAR_NAME, conjunction,
        conjuncts_of, de_brujns, ffalse, ftrue, sort_args_of, sort_substitute, sort_substitute_fml,
        split_by_predicate, substitute, substitute_predicate, to_space, unknown_name, unknowns_of,
        var_name, var_sort_name, vars_of,
    },
    pretty::{Doc, Pretty, hsp, show_doc, squotes, text, vsp},
    program::{
        Constraint, Environment, add_variable, all_measure_postconditions, all_measures_of,
        all_predicates, all_symbols, is_bound, remove_variable, symbols_of_arity,
        type_substitute_env,
    },
    resolver::add_all_variables,
    types::{
        BaseType, RType, TypeSkeleton, TypeSubstitution, as_sort_subst, base_type_of, int,
        is_scalar_type, rename_var, shape, to_sort, type_apply_solution, type_substitute,
        type_substitute_pred, type_vars_of,
    },
    util::{Id, disjoint, restrict_domain, set_concat_map, to_disjoint_groups},
};

/// Qualifier generator for conditionals.
pub type CondQualsGen = Rc<dyn Fn(&Environment, &[Formula]) -> QSpace>;
/// Qualifier generator for match scrutinees.
pub type MatchQualsGen = Rc<dyn Fn(&Environment, &[Formula]) -> QSpace>;
/// Qualifier generator for types.
pub type TypeQualsGen = Rc<dyn Fn(&Environment, &Formula, &[Formula]) -> QSpace>;
/// Qualifier generator for bound predicates.
pub type PredQualsGen = Rc<dyn Fn(&Environment, &[Formula], &[Formula]) -> QSpace>;

/// Parameters of type constraint solving (mirror of `TypingParams`).
#[derive(Clone)]
pub struct TypingParams {
    pub cond_quals_gen: CondQualsGen,
    pub match_quals_gen: MatchQualsGen,
    pub type_quals_gen: TypeQualsGen,
    pub pred_quals_gen: PredQualsGen,
    pub tc_solver_split_measures: bool,
    pub tc_solver_log_level: usize,
}

impl std::fmt::Debug for TypingParams {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TypingParams")
            .field("tc_solver_split_measures", &self.tc_solver_split_measures)
            .field("tc_solver_log_level", &self.tc_solver_log_level)
            .finish_non_exhaustive()
    }
}

/// State of type constraint solving (mirror of `TypingState`).
#[derive(Clone)]
pub struct TypingState {
    /// Typing constraints yet to be converted to horn clauses.
    pub typing_constraints: Vec<Constraint>,
    /// Current assignment to free type variables.
    pub type_assignment: TypeSubstitution,
    /// Current assignment to free predicate variables.
    pub pred_assignment: Substitution,
    /// Current state space for predicate unknowns.
    pub qualifier_map: QMap,
    /// Current set of candidate liquid assignments to unknowns.
    pub candidates: Vec<crate::logic::Candidate>,
    /// Initial environment.
    /// Initial environment (immutable; shared between state snapshots).
    pub init_env: Rc<Environment>,
    /// Number of unique identifiers issued so far.
    pub id_count: BTreeMap<Id, usize>,
    /// Has the entire program been seen?
    pub is_final: bool,
    /// Typing constraints that cannot be simplified anymore.
    pub simple_constraints: Vec<Constraint>,
    /// Horn clauses generated from subtyping constraints.
    pub horn_clauses: Vec<(Formula, Id)>,
    /// Formulas generated from type consistency constraints.
    pub consistency_checks: Vec<Formula>,
    /// Information to be added to all type errors.
    pub error_context: (SourcePos, Doc),
}

impl std::fmt::Debug for TypingState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TypingState")
            .field("typing_constraints", &self.typing_constraints)
            .field("type_assignment", &self.type_assignment)
            .field("pred_assignment", &self.pred_assignment)
            .field("qualifier_map", &self.qualifier_map)
            .field("candidates", &self.candidates)
            .field("id_count", &self.id_count)
            .field("is_final", &self.is_final)
            .field("simple_constraints", &self.simple_constraints)
            .field("horn_clauses", &self.horn_clauses)
            .field("consistency_checks", &self.consistency_checks)
            .field("error_context", &show_doc(&self.error_context.1))
            .finish_non_exhaustive()
    }
}

impl PartialEq for TypingState {
    fn eq(&self, other: &Self) -> bool {
        let ids = BTreeSet::from(["a".to_string(), "u".to_string()]);
        restrict_domain(&ids, &self.id_count) == restrict_domain(&ids, &other.id_count)
            && self.type_assignment == other.type_assignment
            && self.candidates == other.candidates
    }
}

impl Eq for TypingState {}

impl PartialOrd for TypingState {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TypingState {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let ids = BTreeSet::from(["a".to_string(), "u".to_string()]);
        let c1 = restrict_domain(&ids, &self.id_count).cmp(&restrict_domain(&ids, &other.id_count));
        let c2 = self.type_assignment.cmp(&other.type_assignment);
        let c3 = self.candidates.cmp(&other.candidates);
        // Note: the reference's instance is the product order (not lexicographic).
        if c1 != std::cmp::Ordering::Equal {
            c1
        } else if c2 != std::cmp::Ordering::Equal {
            c2
        } else {
            c3
        }
    }
}

/// A typing computation: state + parameters + horn solver (the base monad).
pub struct TcSolver<'a> {
    pub state: TypingState,
    pub params: &'a TypingParams,
    pub horn: &'a mut FixPointSolver,
}

/// `runTCSolver`.
///
/// Execute a typing computation with typing parameters `params` in a typing
/// state `state`, returning the result together with the final typing state.
pub fn run_tc_solver<R>(
    params: &TypingParams,
    state: TypingState,
    horn: &mut FixPointSolver,
    go: impl FnOnce(&mut TcSolver) -> Result<R, ErrorMessage>,
) -> Result<(R, TypingState), ErrorMessage> {
    let mut solver = TcSolver {
        state,
        params,
        horn,
    };
    let result = go(&mut solver)?;
    Ok((result, solver.state))
}

/// `initTypingState`: initial typing state in
/// the initial environment `env`.
#[must_use]
pub fn init_typing_state(env: &Environment) -> TypingState {
    TypingState {
        typing_constraints: Vec::new(),
        type_assignment: BTreeMap::new(),
        pred_assignment: BTreeMap::new(),
        qualifier_map: BTreeMap::new(),
        candidates: vec![crate::logic::initial_candidate()],
        init_env: Rc::new((*env).clone()),
        id_count: BTreeMap::new(),
        is_final: false,
        simple_constraints: Vec::new(),
        horn_clauses: Vec::new(),
        consistency_checks: Vec::new(),
        error_context: (no_pos(), crate::pretty::empty()),
    }
}

/// `throwError`: signal a type error.
fn throw_error(state: &TypingState, msg: Doc) -> ErrorMessage {
    let (pos, ec) = &state.error_context;
    ErrorMessage::new(ErrorKind::TypeError, pos.clone(), vsp(msg, ec.clone()))
}

/// `addTypingConstraint`: impose typing
/// constraint `c` on the programs (`nub (c :)`).
pub fn add_typing_constraint(state: &mut TypingState, c: &Constraint) {
    let mut tcs = vec![c.clone()];
    tcs.extend(
        state
            .typing_constraints
            .iter()
            .filter(|x| **x != *c)
            .cloned(),
    );
    state.typing_constraints = tcs;
}

/// `solveTypeConstraints`: solve
/// `typingConstraints`: either strengthen the current candidates and return
/// shapeless type constraints or fail.
pub fn solve_type_constraints(solver: &mut TcSolver) -> Result<(), ErrorMessage> {
    simplify_all_constraints(solver)?;

    process_all_predicates(solver);
    process_all_constraints(solver);
    generate_all_horn_clauses(solver);

    solve_horn_clauses(solver)?;
    check_type_consistency(solver)?;

    solver.state.horn_clauses = Vec::new();
    solver.state.consistency_checks = Vec::new();
    Ok(())
}

/// `simplifyAllConstraints`: decompose and
/// unify typing constraints; return shapeless type constraints.
fn simplify_all_constraints(solver: &mut TcSolver) -> Result<(), ErrorMessage> {
    let tcs = std::mem::take(&mut solver.state.typing_constraints);
    let tass_len = solver.state.type_assignment.len();
    for c in tcs {
        simplify_constraint(solver, c)?;
    }
    if solver.state.type_assignment.len() > tass_len {
        simplify_all_constraints(solver)?;
    }
    Ok(())
}

/// `processAllPredicates`: assign unknowns to
/// all free predicate variables.
fn process_all_predicates(solver: &mut TcSolver) {
    let tcs = std::mem::take(&mut solver.state.typing_constraints);
    for c in tcs {
        process_predicate(solver, c);
    }
}

/// `processAllConstraints`: eliminate type and
/// predicate variables, generate qualifier maps.
fn process_all_constraints(solver: &mut TcSolver) {
    let tcs = std::mem::take(&mut solver.state.simple_constraints);
    for c in tcs {
        process_constraint(solver, c);
    }
}

/// `generateAllHornClauses`: convert simple
/// subtyping constraints into horn clauses.
fn generate_all_horn_clauses(solver: &mut TcSolver) {
    let tcs = std::mem::take(&mut solver.state.simple_constraints);
    for c in tcs {
        generate_horn_clauses(solver, c);
    }
}

/// `solveHornClauses`: refine the current
/// liquid assignments using the horn clauses.
fn solve_horn_clauses(solver: &mut TcSolver) -> Result<(), ErrorMessage> {
    let fmls: Vec<Formula> = solver
        .state
        .horn_clauses
        .iter()
        .map(|(f, _)| f.clone())
        .collect();
    let qmap = &solver.state.qualifier_map;
    let cands = &solver.state.candidates;
    let env = solver.state.init_env.clone();
    let extract = instantiate_cons_axioms_curried(&env);
    let cands1 = solver.horn.refine_candidates(&fmls, qmap, &extract, cands);
    if cands1.is_empty() {
        return Err(throw_error(
            &solver.state,
            text("Cannot find sufficiently strong refinements"),
        ));
    }
    solver.state.candidates = cands1;
    Ok(())
}

/// `solveAllCandidates`: solve all current
/// candidates until they have no invalid constraints left.
pub fn solve_all_candidates(solver: &mut TcSolver) -> Result<(), ErrorMessage> {
    let cands = std::mem::take(&mut solver.state.candidates);
    let mut cands1 = Vec::new();
    for c in cands {
        cands1.extend(solve_candidate(solver, c)?);
    }
    solver.state.candidates = cands1;
    Ok(())
}

fn solve_candidate(
    solver: &mut TcSolver,
    c: crate::logic::Candidate,
) -> Result<Vec<crate::logic::Candidate>, ErrorMessage> {
    if c.invalid_constraints.is_empty() {
        return Ok(vec![c]);
    }
    let env = solver.state.init_env.clone();
    let extract = instantiate_cons_axioms_curried(&env);
    let cands1 = solver
        .horn
        .refine_candidates(&[], &solver.state.qualifier_map, &extract, &[c]);
    let mut out = Vec::new();
    for c1 in cands1 {
        out.extend(solve_candidate(solver, c1)?);
    }
    Ok(out)
}

/// `checkTypeConsistency`: filter out liquid
/// assignments that are too strong for current consistency checks.
fn check_type_consistency(solver: &mut TcSolver) -> Result<(), ErrorMessage> {
    let env = solver.state.init_env.clone();
    let extract = instantiate_cons_axioms_curried(&env);
    let cands1 = solver.horn.check_candidates(
        true,
        &solver.state.consistency_checks,
        &extract,
        &solver.state.candidates,
    );
    if cands1.is_empty() {
        return Err(throw_error(
            &solver.state,
            text("Found inconsistent refinements"),
        ));
    }
    solver.state.candidates = cands1;
    Ok(())
}

fn instantiate_cons_axioms_curried(env: &Environment) -> crate::logic::ExtractAssumptions {
    let env = env.clone();
    Box::new(move |fml: &Formula| instantiate_cons_axioms(&env, None, fml))
}

/// `simplifyConstraint`: simplify `c` into a
/// set of simple and shapeless constraints, possibly extending the current
/// type assignment or predicate assignment.
fn simplify_constraint(solver: &mut TcSolver, c: Constraint) -> Result<(), ErrorMessage> {
    simplify_constraint_impl(solver, c)
}

fn simplify_constraint_impl(solver: &mut TcSolver, c: Constraint) -> Result<(), ErrorMessage> {
    match c {
        // Any type: drop
        Constraint::Subtype(_, _, TypeSkeleton::AnyT, ..) => Ok(()),
        Constraint::Subtype(_, TypeSkeleton::AnyT, ..) => Ok(()),
        Constraint::WellFormed(_, TypeSkeleton::AnyT) => Ok(()),
        // Any datatype: drop only if lhs is a datatype
        Constraint::Subtype(_, TypeSkeleton::ScalarT(BaseType::DatatypeT(..), _), t, ..)
            if t == crate::types::any_datatype() =>
        {
            Ok(())
        }
        // Well-formedness of a known predicate: drop
        Constraint::WellFormedPredicate(_, _, p)
            if solver.state.pred_assignment.contains_key(&p) =>
        {
            Ok(())
        }
        // Type variable with known assignment: substitute
        Constraint::Subtype(env, tv, t, consistent, label)
            if let TypeSkeleton::ScalarT(BaseType::TypeVarT(_, a), _) = &tv
                && solver.state.type_assignment.contains_key(a) =>
        {
            simplify_constraint_impl(
                solver,
                Constraint::Subtype(
                    env,
                    type_substitute(&solver.state.type_assignment, &tv),
                    t,
                    consistent,
                    label,
                ),
            )
        }
        Constraint::Subtype(env, t, tv, consistent, label)
            if let TypeSkeleton::ScalarT(BaseType::TypeVarT(_, a), _) = &tv
                && solver.state.type_assignment.contains_key(a) =>
        {
            simplify_constraint_impl(
                solver,
                Constraint::Subtype(
                    env,
                    t,
                    type_substitute(&solver.state.type_assignment, &tv),
                    consistent,
                    label,
                ),
            )
        }
        Constraint::WellFormed(env, tv)
            if let TypeSkeleton::ScalarT(BaseType::TypeVarT(_, a), _) = &tv
                && solver.state.type_assignment.contains_key(a) =>
        {
            simplify_constraint_impl(
                solver,
                Constraint::WellFormed(env, type_substitute(&solver.state.type_assignment, &tv)),
            )
        }
        // Two unknown free variables: nothing can be done for now
        Constraint::Subtype(ref env, ref tv1, ref tv2, ref consistent, ref label)
            if let TypeSkeleton::ScalarT(BaseType::TypeVarT(_, a), _) = tv1
                && let TypeSkeleton::ScalarT(BaseType::TypeVarT(_, b), _) = tv2
                && !is_bound(env, a)
                && !is_bound(env, b) =>
        {
            if a == b {
                panic!("simplifyConstraint: equal type variables on both sides");
            } else if solver.state.is_final {
                // This is a final pass: assign an arbitrary type to one of the variables
                add_type_assignment(solver, a, crate::types::int_all());
                simplify_constraint_impl(
                    solver,
                    Constraint::Subtype(
                        env.clone(),
                        tv1.clone(),
                        tv2.clone(),
                        *consistent,
                        label.clone(),
                    ),
                )
            } else {
                add_typing_constraint(
                    &mut solver.state,
                    &Constraint::Subtype(
                        env.clone(),
                        tv1.clone(),
                        tv2.clone(),
                        *consistent,
                        label.clone(),
                    ),
                );
                Ok(())
            }
        }
        Constraint::WellFormed(env, tv)
            if let TypeSkeleton::ScalarT(BaseType::TypeVarT(_, a), _) = &tv
                && !is_bound(&env, a) =>
        {
            add_typing_constraint(&mut solver.state, &Constraint::WellFormed(env, tv));
            Ok(())
        }
        Constraint::WellFormedPredicate(env, arg_sorts, p) => {
            add_typing_constraint(
                &mut solver.state,
                &Constraint::WellFormedPredicate(env, arg_sorts, p),
            );
            Ok(())
        }
        // Let types: extend environment (before trying to extend the type assignment)
        Constraint::Subtype(env, TypeSkeleton::LetT(x, t_def, t_body), t, consistent, label) => {
            simplify_constraint_impl(
                solver,
                Constraint::Subtype(
                    Rc::new(add_variable(&x, &t_def, &env)),
                    (*t_body).clone(),
                    t,
                    consistent,
                    label,
                ),
            )
        }
        Constraint::Subtype(env, t, TypeSkeleton::LetT(x, t_def, t_body), consistent, label) => {
            simplify_constraint_impl(
                solver,
                Constraint::Subtype(
                    Rc::new(add_variable(&x, &t_def, &env)),
                    t,
                    (*t_body).clone(),
                    consistent,
                    label,
                ),
            )
        }
        // Unknown free variable and a type: extend type assignment
        Constraint::Subtype(ref env, ref tv, ref t, ref consistent, ref label)
            if let TypeSkeleton::ScalarT(BaseType::TypeVarT(_, a), _) = tv
                && !is_bound(env, a) =>
        {
            unify(solver, env, a, t);
            simplify_constraint_impl(
                solver,
                Constraint::Subtype(
                    env.clone(),
                    tv.clone(),
                    t.clone(),
                    *consistent,
                    label.clone(),
                ),
            )
        }
        Constraint::Subtype(ref env, ref t, ref tv, ref consistent, ref label)
            if let TypeSkeleton::ScalarT(BaseType::TypeVarT(_, a), _) = tv
                && !is_bound(env, a) =>
        {
            unify(solver, env, a, t);
            simplify_constraint_impl(
                solver,
                Constraint::Subtype(
                    env.clone(),
                    t.clone(),
                    tv.clone(),
                    *consistent,
                    label.clone(),
                ),
            )
        }
        // Compound types: decompose. The reference's rules match only when
        // BOTH sides have a non-empty tArg list, and (once tArgs are exhausted)
        // when both have non-empty pArgs lists; anything else falls through to
        // the simple-constraint arm (equal base types are accepted, otherwise
        // the shape check fails).
        Constraint::Subtype(
            env,
            TypeSkeleton::ScalarT(BaseType::DatatypeT(name, t_args, p_args), fml),
            TypeSkeleton::ScalarT(BaseType::DatatypeT(name1, t_args1, p_args1), fml1),
            consistent,
            label,
        ) => {
            if let (Some(t_arg), Some(t_arg1)) = (t_args.first(), t_args1.first()) {
                simplify_constraint_impl(
                    solver,
                    Constraint::Subtype(
                        env.clone(),
                        t_arg.clone(),
                        t_arg1.clone(),
                        consistent,
                        label.clone(),
                    ),
                )?;
                simplify_constraint_impl(
                    solver,
                    Constraint::Subtype(
                        env,
                        TypeSkeleton::ScalarT(
                            BaseType::DatatypeT(name, t_args[1..].to_vec(), p_args),
                            fml,
                        ),
                        TypeSkeleton::ScalarT(
                            BaseType::DatatypeT(name1, t_args1[1..].to_vec(), p_args1),
                            fml1,
                        ),
                        consistent,
                        label,
                    ),
                )
            } else if t_args.is_empty()
                && t_args1.is_empty()
                && let (Some(p_arg), Some(p_arg1)) = (p_args.first(), p_args1.first())
            {
                let variances = solver.state.init_env.datatypes[&name]
                    .pred_variances
                    .clone();
                let is_contra = variances[variances.len() - p_args.len()];
                if is_contra {
                    simplify_constraint_impl(
                        solver,
                        Constraint::Subtype(
                            env.clone(),
                            int(p_arg1.clone()),
                            int(p_arg.clone()),
                            consistent,
                            label.clone(),
                        ),
                    )?;
                } else {
                    simplify_constraint_impl(
                        solver,
                        Constraint::Subtype(
                            env.clone(),
                            int(p_arg.clone()),
                            int(p_arg1.clone()),
                            consistent,
                            label.clone(),
                        ),
                    )?;
                }
                simplify_constraint_impl(
                    solver,
                    Constraint::Subtype(
                        env,
                        TypeSkeleton::ScalarT(
                            BaseType::DatatypeT(name, Vec::new(), p_args[1..].to_vec()),
                            fml,
                        ),
                        TypeSkeleton::ScalarT(
                            BaseType::DatatypeT(name1, Vec::new(), p_args1[1..].to_vec()),
                            fml1,
                        ),
                        consistent,
                        label,
                    ),
                )
            } else {
                // Fall through to the simple-constraint arm with the ORIGINAL
                // constraint: equal base types (name, tArgs, pArgs) are
                // accepted regardless of refinements; anything else fails the
                // shape check.
                let base_equal = name == name1 && t_args == t_args1 && p_args == p_args1;
                if base_equal {
                    solver.state.simple_constraints.push(Constraint::Subtype(
                        env,
                        TypeSkeleton::ScalarT(BaseType::DatatypeT(name, t_args, p_args), fml),
                        TypeSkeleton::ScalarT(BaseType::DatatypeT(name1, t_args1, p_args1), fml1),
                        consistent,
                        label,
                    ));
                    Ok(())
                } else {
                    let t_full = TypeSkeleton::<Formula>::ScalarT(
                        BaseType::DatatypeT(name, t_args, p_args),
                        fml,
                    );
                    let t_full1 = TypeSkeleton::<Formula>::ScalarT(
                        BaseType::DatatypeT(name1, t_args1, p_args1),
                        fml1,
                    );
                    Err(throw_error(
                        &solver.state,
                        hsp(
                            text("Cannot match shape"),
                            vsp(
                                squotes(shape(&t_full).pretty()),
                                hsp(text("with shape"), squotes(shape(&t_full1).pretty())),
                            ),
                        ),
                    ))
                }
            }
        }
        // Function types, not consistent: contravariant argument, covariant result
        Constraint::Subtype(
            env,
            TypeSkeleton::FunctionT(x, t_arg1, t_res1),
            TypeSkeleton::FunctionT(y, t_arg2, t_res2),
            false,
            label,
        ) => {
            simplify_constraint_impl(
                solver,
                Constraint::Subtype(
                    env.clone(),
                    (*t_arg2).clone(),
                    (*t_arg1).clone(),
                    false,
                    label.clone(),
                ),
            )?;
            if is_scalar_type(&t_arg1) {
                simplify_constraint_impl(
                    solver,
                    Constraint::Subtype(
                        Rc::new(add_variable(&y, &t_arg2, &env)),
                        rename_var(&|a| is_bound(&env, a), &x, &y, &t_arg1, &t_res1),
                        (*t_res2).clone(),
                        false,
                        label,
                    ),
                )
            } else {
                simplify_constraint_impl(
                    solver,
                    Constraint::Subtype(env, (*t_res1).clone(), (*t_res2).clone(), false, label),
                )
            }
        }
        // Function types, consistent: covariant in both positions (with bindings)
        Constraint::Subtype(
            env,
            TypeSkeleton::FunctionT(x, t_arg1, t_res1),
            TypeSkeleton::FunctionT(y, _t_arg2, t_res2),
            true,
            label,
        ) => {
            if is_scalar_type(&t_arg1) {
                let _ = y;
                simplify_constraint_impl(
                    solver,
                    Constraint::Subtype(
                        Rc::new(add_variable(&x, &t_arg1, &env)),
                        (*t_res1).clone(),
                        (*t_res2).clone(),
                        true,
                        label,
                    ),
                )
            } else {
                simplify_constraint_impl(
                    solver,
                    Constraint::Subtype(env, (*t_res1).clone(), (*t_res2).clone(), true, label),
                )
            }
        }
        // Well-formedness of a datatype: check arguments, then remember the whole
        Constraint::WellFormed(
            env,
            ref c @ TypeSkeleton::ScalarT(BaseType::DatatypeT(_, ref t_args, _), _),
        ) => {
            for t_arg in t_args {
                simplify_constraint_impl(
                    solver,
                    Constraint::WellFormed(env.clone(), t_arg.clone()),
                )?;
            }
            solver
                .state
                .simple_constraints
                .push(Constraint::WellFormed(env, c.clone()));
            Ok(())
        }
        Constraint::WellFormed(env, TypeSkeleton::FunctionT(x, t_arg, t_res)) => {
            simplify_constraint_impl(
                solver,
                Constraint::WellFormed(env.clone(), (*t_arg).clone()),
            )?;
            simplify_constraint_impl(
                solver,
                Constraint::WellFormed(Rc::new(add_variable(&x, &t_arg, &env)), (*t_res).clone()),
            )
        }
        Constraint::WellFormed(env, TypeSkeleton::LetT(x, t_def, t_body)) => {
            simplify_constraint_impl(
                solver,
                Constraint::WellFormed(Rc::new(add_variable(&x, &t_def, &env)), (*t_body).clone()),
            )
        }
        // Simple constraint: return
        Constraint::Subtype(
            ref env,
            ref t1 @ TypeSkeleton::ScalarT(ref base_t, _),
            ref t2 @ TypeSkeleton::ScalarT(ref base_t1, _),
            ref consistent,
            ref label,
        ) if base_t == base_t1 => {
            solver.state.simple_constraints.push(Constraint::Subtype(
                env.clone(),
                t1.clone(),
                t2.clone(),
                *consistent,
                label.clone(),
            ));
            Ok(())
        }
        Constraint::WellFormed(env, t @ TypeSkeleton::ScalarT(..)) => {
            solver
                .state
                .simple_constraints
                .push(Constraint::WellFormed(env, t));
            Ok(())
        }
        Constraint::WellFormedCond(env, fml) => {
            solver
                .state
                .simple_constraints
                .push(Constraint::WellFormedCond(env, fml));
            Ok(())
        }
        Constraint::WellFormedMatchCond(env, fml) => {
            solver
                .state
                .simple_constraints
                .push(Constraint::WellFormedMatchCond(env, fml));
            Ok(())
        }
        // Otherwise (shape mismatch): fail
        Constraint::Subtype(_, t, t1, ..) => {
            Err(throw_error(
                &solver.state,
                hsp(
                    text("Cannot match shape"),
                    vsp(
                        squotes(shape(&t).pretty()),
                        hsp(text("with shape"), squotes(shape(&t1).pretty())),
                    ),
                ),
            ))
        }
        #[allow(unreachable_patterns)]
        Constraint::WellFormed(_, t) => {
            Err(throw_error(
                &solver.state,
                hsp(text("Cannot match shape"), squotes(shape(&t).pretty())),
            ))
        }
    }
}

/// `unify`: unify type variable `a` with type
/// `t` or fail if `a` occurs in `t`.
fn unify(solver: &mut TcSolver, env: &Environment, a: &Id, t: &RType) {
    assert!(
        !type_vars_of(t).contains(a),
        "simplifyConstraint: type variable occurs in the other type"
    );
    let t1 = fresh(solver, env, t);
    add_type_assignment(solver, a, t1);
}

/// `processPredicate`: predicate
/// well-formedness: shapeless or simple depending on type variables.
fn process_predicate(solver: &mut TcSolver, c: Constraint) {
    match c {
        Constraint::WellFormedPredicate(env, arg_sorts, p) => {
            let has_free = arg_sorts
                .iter()
                .flat_map(crate::logic::type_vars_of_sort)
                .collect::<BTreeSet<Id>>()
                .iter()
                .any(|a| !is_bound(&env, a) && !solver.state.type_assignment.contains_key(a));
            if has_free {
                add_typing_constraint(
                    &mut solver.state,
                    &Constraint::WellFormedPredicate(env, arg_sorts, p),
                );
            } else {
                let u = p.clone();
                let arg_sorts1: Vec<Sort> = arg_sorts
                    .iter()
                    .map(|s| {
                        sort_substitute(&as_sort_subst(&solver.state.type_assignment), s.clone())
                    })
                    .collect();
                let args: Vec<Formula> = arg_sorts1
                    .iter()
                    .zip(de_brujns(arg_sorts1.len()))
                    .map(|(s, n)| Formula::Var(Box::new(s.clone()), n))
                    .collect();
                let env1 = type_substitute_env(&solver.state.type_assignment, &env);
                add_pred_assignment(solver, &p, Formula::Unknown(BTreeMap::new(), u.clone()));
                let vars = all_scalars(&env1);
                let pq = solver.params.pred_quals_gen.clone();
                let quals = pq(&add_all_variables(&env1, &args), &args, &vars);
                add_quals(solver, &u, quals);
            }
        }
        other => add_typing_constraint(&mut solver.state, &other),
    }
}

/// `processConstraint`: eliminate type and
/// predicate variables from simple constraints, create qualifier maps, split
/// measure-based subtyping constraints.
fn process_constraint(solver: &mut TcSolver, c: Constraint) {
    match c {
        Constraint::Subtype(
            env,
            TypeSkeleton::ScalarT(base_l, l),
            TypeSkeleton::ScalarT(base_r, r),
            false,
            label,
        ) => {
            assert!(base_l == base_r, "processConstraint: base type mismatch");
            if l == ffalse() || r == ftrue() {
                return;
            }
            let subst = |fml: &Formula| {
                sort_substitute_fml(
                    &as_sort_subst(&solver.state.type_assignment),
                    &substitute_predicate(&solver.state.pred_assignment, fml),
                )
            };
            let l1 = subst(&l);
            let r1 = subst(&r);
            let c1 = Constraint::Subtype(
                env.clone(),
                TypeSkeleton::ScalarT(base_l.clone(), l1.clone()),
                TypeSkeleton::ScalarT(base_r.clone(), r1.clone()),
                false,
                label.clone(),
            );
            let free_preds: BTreeSet<Id> = preds_of(&l1).union(&preds_of(&r1)).cloned().collect();
            let known_preds: BTreeSet<Id> = all_predicates(&env).into_keys().collect();
            if free_preds.is_subset(&known_preds) {
                match &base_l {
                    BaseType::DatatypeT(dt_name, ..) => {
                        let measures: BTreeSet<Id> =
                            all_measures_of(dt_name, &env).into_keys().collect();
                        let is_abstract = env.datatypes[dt_name].constructors.is_empty();
                        let vals: Vec<Formula> = vars_of(&r1)
                            .into_iter()
                            .filter(|v| var_name(v) == VALUE_VAR_NAME)
                            .collect();
                        let r_conjuncts = conjuncts_of(&r1);
                        let do_split = solver.params.tc_solver_split_measures;
                        let has_unknowns = !unknowns_of(&and(&l1, &r1)).is_empty();
                        if !do_split || is_abstract || vals.is_empty() || has_unknowns {
                            solver.state.simple_constraints.push(c1);
                        } else {
                            let val = vals[0].clone();

                            match split_by_predicate(
                                &measures,
                                &val,
                                &Vec::from_iter(r_conjuncts.iter().cloned()),
                            ) {
                                None => solver.state.simple_constraints.push(c1),
                                Some(mr) => {
                                    let mr_union: BTreeSet<Formula> =
                                        mr.values().flat_map(|s| s.iter().cloned()).collect();
                                    if r_conjuncts.is_subset(&mr_union) {
                                        let l_conjuncts =
                                            conjuncts_of(&instantiate_cons(&env, &val, &l1));
                                        let l_conjuncts: Vec<Formula> =
                                            Vec::from_iter(l_conjuncts.iter().cloned());
                                        match split_by_predicate(&measures, &val, &l_conjuncts) {
                                            None => solver.state.simple_constraints.push(c1),
                                            Some(ml) => {
                                                let base_l1 = base_l.clone();
                                                for group in to_disjoint_groups(&mr) {
                                                    add_split_constraint(
                                                        solver, &env, &base_l1, &ml, group, &label,
                                                    );
                                                }
                                            }
                                        }
                                    } else {
                                        solver.state.simple_constraints.push(c1);
                                    }
                                }
                            }
                        }
                    }
                    _ => solver.state.simple_constraints.push(c1),
                }
            } else {
                add_typing_constraint(
                    &mut solver.state,
                    &Constraint::Subtype(
                        env,
                        TypeSkeleton::ScalarT(base_l, l),
                        TypeSkeleton::ScalarT(base_r, r),
                        false,
                        label,
                    ),
                );
            }
        }
        Constraint::Subtype(
            env,
            TypeSkeleton::ScalarT(base_l, l),
            TypeSkeleton::ScalarT(base_r, r),
            true,
            label,
        ) => {
            assert!(base_l == base_r, "processConstraint: base type mismatch");
            let subst = |fml: &Formula| {
                sort_substitute_fml(
                    &as_sort_subst(&solver.state.type_assignment),
                    &substitute_predicate(&solver.state.pred_assignment, fml),
                )
            };
            let l1 = subst(&l);
            let r1 = subst(&r);
            if l1 == ftrue() || r1 == ftrue() {
                return;
            }
            solver.state.simple_constraints.push(Constraint::Subtype(
                env,
                TypeSkeleton::ScalarT(base_l, l1),
                TypeSkeleton::ScalarT(base_r, r1),
                true,
                label,
            ));
        }
        Constraint::WellFormed(env, ref t @ TypeSkeleton::ScalarT(ref base_t, ref fml)) => {
            if let Formula::Unknown(_, u) = fml {
                let tq = solver.params.type_quals_gen.clone();
                let env1 = type_substitute_env(&solver.state.type_assignment, &env);
                let env2 = add_variable(&VALUE_VAR_NAME.to_string(), t, &env1);
                if !solver.state.qualifier_map.contains_key(u) {
                    let quals = tq(
                        &env2,
                        &Formula::Var(Box::new(to_sort(base_t)), VALUE_VAR_NAME.to_string()),
                        &all_scalars(&env1),
                    );
                    add_quals(solver, u, quals);
                }
            }
        }
        Constraint::WellFormedCond(env, Formula::Unknown(_, u)) => {
            let cq = solver.params.cond_quals_gen.clone();
            let env1 = type_substitute_env(&solver.state.type_assignment, &env);
            let quals = cq(&env1, &all_scalars(&env1));
            add_quals(solver, &u, quals);
        }
        Constraint::WellFormedMatchCond(env, Formula::Unknown(_, u)) => {
            let mq = solver.params.match_quals_gen.clone();
            let env1 = type_substitute_env(&solver.state.type_assignment, &env);
            let quals = mq(&env1, &all_potential_scrutinees(&env1));
            add_quals(solver, &u, quals);
        }
        other => panic!("processConstraint: not a simple constraint {other:?}"),
    }
}

fn preds_of(fml: &Formula) -> BTreeSet<Id> {
    crate::logic::preds_of(fml)
}

fn and(l: &Formula, r: &Formula) -> Formula {
    crate::logic::and(l.clone(), r.clone())
}

/// `instantiateCons` (in `processConstraint`).
fn instantiate_cons(env: &Environment, val: &Formula, fml: &Formula) -> Formula {
    match fml {
        Formula::Binary(BinOp::Eq, v, rhs)
            if v.as_ref() == val && matches!(rhs.as_ref(), Formula::Cons(..)) =>
        {
            conjunction(&instantiate_cons_axioms(env, Some(val), fml))
        }
        _ => fml.clone(),
    }
}

/// `addSplitConstraint` (in `processConstraint`).
fn add_split_constraint(
    solver: &mut TcSolver,
    env: &Environment,
    base_t: &BaseType<Formula>,
    ml: &BTreeMap<Id, BTreeSet<Formula>>,
    (measures, r_conjuncts): (BTreeSet<Id>, BTreeSet<Formula>),
    label: &Id,
) {
    let rhs = conjunction(&r_conjuncts);
    let lhs_formulas: BTreeSet<Formula> = measures
        .iter()
        .flat_map(|measure| {
            ml.get(measure)
                .map(|s| s.iter().cloned().collect::<Vec<_>>())
                .unwrap_or_default()
        })
        .collect();
    let lhs = conjunction(&lhs_formulas);
    let c1 = Constraint::Subtype(
        Rc::new((*env).clone()),
        TypeSkeleton::ScalarT(base_t.clone(), lhs),
        TypeSkeleton::ScalarT(base_t.clone(), rhs),
        false,
        label.clone(),
    );
    solver.state.simple_constraints.push(c1);
}

/// `generateHornClauses`: convert a simple
/// subtyping constraint into horn clauses (or a consistency check).
fn generate_horn_clauses(solver: &mut TcSolver, c: Constraint) {
    match c {
        Constraint::Subtype(
            env,
            TypeSkeleton::ScalarT(base_l, l),
            TypeSkeleton::ScalarT(base_r, r),
            false,
            label,
        ) => {
            assert!(base_l == base_r, "generateHornClauses: base type mismatch");
            let relevant_vars = potential_vars(&solver.state.qualifier_map, &and(&l, &r));
            let emb = embedding(solver, &env, &relevant_vars, true);
            let clause = implies(conjunction(&insert(l, &emb)), r);
            let clauses = solver.horn.preprocess_constraint(&clause);
            let mut new_clauses: Vec<(Formula, Id)> =
                clauses.into_iter().map(|f| (f, label.clone())).collect();
            new_clauses.extend(solver.state.horn_clauses.iter().cloned());
            solver.state.horn_clauses = new_clauses;
        }
        Constraint::Subtype(
            env,
            TypeSkeleton::ScalarT(base_l, l),
            TypeSkeleton::ScalarT(base_r, r),
            true,
            _,
        ) => {
            assert!(base_l == base_r, "generateHornClauses: base type mismatch");
            let relevant_vars = potential_vars(&solver.state.qualifier_map, &and(&l, &r));
            let emb = embedding(solver, &env, &relevant_vars, false);
            let mut clause_set: BTreeSet<Formula> = emb;
            clause_set.insert(l);
            clause_set.insert(r);
            solver
                .state
                .consistency_checks
                .push(conjunction(&clause_set));
        }
        other => panic!("generateHornClauses: not a simple subtyping constraint {other:?}"),
    }
}

fn insert(fml: Formula, set: &BTreeSet<Formula>) -> BTreeSet<Formula> {
    let mut s = set.clone();
    s.insert(fml);
    s
}

fn implies(l: Formula, r: Formula) -> Formula {
    crate::logic::implies(l, r)
}

/// `allScalars`: logic terms for all scalar
/// symbols in `env`.
#[must_use]
pub fn all_scalars(env: &Environment) -> Vec<Formula> {
    symbols_of_arity(0, env)
        .into_iter()
        .filter_map(|(x, sch)| to_formula_scalar(env, x, sch))
        .collect()
}

fn to_formula_scalar(env: &Environment, x: Id, sch: crate::types::RSchema) -> Option<Formula> {
    use crate::types::SchemaSkeleton::{ForallP, ForallT, Monotype};
    match sch {
        ForallT(..) | ForallP(..) => None,
        Monotype(_) if env.let_bound.contains(&x) => None,
        Monotype(t) => {
            match t {
                TypeSkeleton::ScalarT(BaseType::IntT, Formula::Binary(BinOp::Eq, _, rhs)) => {
                    match *rhs {
                        Formula::IntLit(n) => Some(Formula::IntLit(n)),
                        _ => None,
                    }
                }
                TypeSkeleton::ScalarT(BaseType::BoolT, Formula::Var(..)) => {
                    Some(Formula::BoolLit(true))
                }
                TypeSkeleton::ScalarT(
                    BaseType::BoolT,
                    Formula::Unary(crate::logic::UnOp::Not, e),
                ) => {
                    match *e {
                        Formula::Var(..) => Some(Formula::BoolLit(false)),
                        _ => None,
                    }
                }
                TypeSkeleton::ScalarT(
                    BaseType::DatatypeT(dt, t_args, p_args),
                    Formula::Binary(BinOp::Eq, _, rhs),
                ) if t_args.is_empty() && p_args.is_empty() => {
                    match *rhs {
                        Formula::Cons(_, name, args) if args.is_empty() && x == name => {
                            Some(Formula::Cons(
                                Box::new(Sort::DataS(dt, Vec::new())),
                                name,
                                Vec::new(),
                            ))
                        }
                        _ => None,
                    }
                }
                TypeSkeleton::ScalarT(b, _) => Some(Formula::Var(Box::new(to_sort(&b)), x)),
                _ => None,
            }
        }
    }
}

/// `allPotentialScrutinees`: logic terms for
/// all scalar datatype symbols in `env` that can be scrutinized.
#[must_use]
pub fn all_potential_scrutinees(env: &Environment) -> Vec<Formula> {
    symbols_of_arity(0, env)
        .into_iter()
        .filter_map(|(x, sch)| to_formula_scrutinee(env, x, sch))
        .collect()
}

fn to_formula_scrutinee(env: &Environment, x: Id, sch: crate::types::RSchema) -> Option<Formula> {
    use crate::types::SchemaSkeleton::{ForallP, ForallT, Monotype};
    match sch {
        ForallT(..) | ForallP(..) => None,
        Monotype(t) => {
            match t {
                TypeSkeleton::ScalarT(b @ BaseType::DatatypeT(..), _) => {
                    let is_scrutinized = env.used_scrutinees.iter().any(|p| {
                        matches!(
                            &p.content,
                            crate::program::BareProgram::PSymbol(y) if *y == x
                        )
                    });
                    if env.unfolded_vars.contains(&x) && !is_scrutinized {
                        Some(Formula::Var(Box::new(to_sort(&b)), x))
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
    }
}

/// `hasPotentialScrutinees`.
#[must_use]
pub fn has_potential_scrutinees(solver: &TcSolver, env: &Environment) -> bool {
    !all_potential_scrutinees(&type_substitute_env(&solver.state.type_assignment, env)).is_empty()
}

/// Read-only variant of [`has_potential_scrutinees`] on the type assignment
/// alone (the explorer calls it without cloning the whole typing state).
#[must_use]
pub fn has_potential_scrutinees_tass(tass: &TypeSubstitution, env: &Environment) -> bool {
    !all_potential_scrutinees(&type_substitute_env(tass, env)).is_empty()
}

/// `embedding`: assumptions encoded in an
/// environment.
fn embedding(
    solver: &TcSolver,
    env: &Environment,
    vars: &BTreeSet<Id>,
    include_quantified: bool,
) -> BTreeSet<Formula> {
    let ass: BTreeSet<Formula> = env
        .assumptions
        .iter()
        .map(|f| substitute_predicate(&solver.state.pred_assignment, f))
        .collect();
    let all_vars: BTreeSet<Id> = vars
        .union(&potential_vars(
            &solver.state.qualifier_map,
            &conjunction(&ass),
        ))
        .cloned()
        .collect();
    add_bindings(
        env,
        &solver.state.type_assignment,
        &solver.state.pred_assignment,
        &solver.state.qualifier_map,
        ass,
        all_vars,
        include_quantified,
    )
}

fn add_bindings(
    env: &Environment,
    tass: &TypeSubstitution,
    pass: &Substitution,
    qmap: &QMap,
    fmls: BTreeSet<Formula>,
    vars: BTreeSet<Id>,
    include_quantified: bool,
) -> BTreeSet<Formula> {
    use crate::types::SchemaSkeleton::{ForallP, ForallT, Monotype};
    if vars.is_empty() {
        return fmls;
    }
    let mut vars = vars;
    let vars_full = vars.clone();
    let x = vars.iter().next().expect("embedding: empty vars").clone();
    vars.remove(&x);
    match all_symbols(env).get(&x) {
        Some(Monotype(t)) => {
            match type_substitute(tass, t) {
                TypeSkeleton::ScalarT(base_t, fml) => {
                    let mut fmls1: Vec<Formula> = vec![substitute_predicate(pass, &fml)];
                    fmls1.extend(
                        all_measure_postconditions(include_quantified, &base_t, env)
                            .iter()
                            .map(|f| substitute_predicate(pass, f)),
                    );
                    let mut subst = Substitution::new();
                    subst.insert(
                        VALUE_VAR_NAME.to_string(),
                        Formula::Var(Box::new(to_sort(&base_t)), x.clone()),
                    );
                    let fmls1: BTreeSet<Formula> =
                        fmls1.into_iter().map(|f| substitute(&subst, f)).collect();
                    let new_vars: BTreeSet<Id> = set_concat_map(
                        |f| potential_vars(qmap, f),
                        &fmls1.iter().cloned().collect(),
                    )
                    .into_iter()
                    .filter(|v| *v != x)
                    .collect();
                    let fmls2: BTreeSet<Formula> = fmls.union(&fmls1).cloned().collect();
                    let vars1: BTreeSet<Id> = vars.union(&new_vars).cloned().collect();
                    add_bindings(env, tass, pass, qmap, fmls2, vars1, include_quantified)
                }
                TypeSkeleton::LetT(y, t_def, t_body) => {
                    let env1 = add_variable(
                        &y,
                        &t_def,
                        &add_variable(&x, &t_body, &remove_variable(&x, env)),
                    );
                    add_bindings(&env1, tass, pass, qmap, fmls, vars_full, include_quantified)
                }
                TypeSkeleton::AnyT => BTreeSet::from([ffalse()]),
                TypeSkeleton::FunctionT(..) => {
                    panic!("embedding: encountered non-scalar variable {x} in 0-arity bucket")
                }
            }
        }
        Some(ForallT(..) | ForallP(..)) | None => {
            add_bindings(env, tass, pass, qmap, fmls, vars, include_quantified)
        }
    }
}

/// `bottomValuation`.
fn bottom_valuation(qmap: &QMap, fml: &Formula) -> Formula {
    let unknowns = unknowns_of(fml);
    let mut bottom_solution: BTreeMap<Id, BTreeSet<Formula>> = BTreeMap::new();
    for u in &unknowns {
        let name = unknown_name(u).clone();
        let quals: BTreeSet<Formula> = crate::logic::lookup_quals_subst(qmap, u)
            .into_iter()
            .collect();
        bottom_solution.insert(name, quals);
    }
    crate::logic::apply_solution(&bottom_solution, fml)
}

/// `potentialVars`: variables of `fml` if all
/// unknowns get strongest valuation according to `quals`.
#[must_use]
pub fn potential_vars(qmap: &QMap, fml: &Formula) -> BTreeSet<Id> {
    vars_of(&bottom_valuation(qmap, fml))
        .into_iter()
        .map(|v| var_name(&v).clone())
        .collect()
}

/// `freshId`: fresh identifier starting with
/// `prefix`.
pub fn fresh_id(solver: &mut TcSolver, prefix: &str) -> Id {
    let i = solver.state.id_count.get(prefix).copied().unwrap_or(0);
    solver.state.id_count.insert(prefix.to_string(), i + 1);
    format!("{prefix}{i}")
}

/// `freshVar`.
pub fn fresh_var(solver: &mut TcSolver, env: &Environment, prefix: &str) -> Id {
    let x = fresh_id(solver, prefix);
    if all_symbols(env).contains_key(&x) {
        fresh_var(solver, env, prefix)
    } else {
        x
    }
}

/// `somewhatFreshVar`: a variable of sort
/// `sort` not bound in `env`.
#[must_use]
pub fn somewhat_fresh_var(env: &Environment, prefix: &str, s: Sort) -> Formula {
    let mut n = 0usize;
    let mut v = format!("{prefix}{n}");
    while all_symbols(env).contains_key(&v) {
        v = format!("{v}{n}");
        n += 1;
    }
    Formula::Var(Box::new(s), v)
}

/// `fresh`: a type with the same shape as `t`
/// but fresh type variables, fresh predicate variables, and fresh unknowns as
/// refinements.
fn fresh(solver: &mut TcSolver, env: &Environment, t: &RType) -> RType {
    match t {
        TypeSkeleton::ScalarT(BaseType::TypeVarT(v_subst, a), _) if !is_bound(env, a) => {
            let a1 = fresh_id(solver, "A");
            TypeSkeleton::ScalarT(BaseType::TypeVarT(v_subst.clone(), a1), ftrue())
        }
        TypeSkeleton::ScalarT(base_t, _) => {
            let base_t1 = fresh_base(solver, env, base_t);
            let u = fresh_id(solver, "U");
            TypeSkeleton::ScalarT(base_t1, Formula::Unknown(BTreeMap::new(), u))
        }
        TypeSkeleton::FunctionT(x, t_arg, t_fun) => {
            let t_arg1 = fresh(solver, env, t_arg);
            let t_fun1 = fresh(solver, env, t_fun);
            TypeSkeleton::FunctionT(x.clone(), Box::new(t_arg1), Box::new(t_fun1))
        }
        TypeSkeleton::LetT(..) | TypeSkeleton::AnyT => {
            let (env1, t1) = crate::program::embed_context(env, t);
            fresh(solver, &env1, &t1)
        }
    }
}

fn fresh_base(
    solver: &mut TcSolver,
    env: &Environment,
    base_t: &BaseType<Formula>,
) -> BaseType<Formula> {
    match base_t {
        BaseType::DatatypeT(name, t_args, _) => {
            let t_args1: Vec<RType> = t_args.iter().map(|t| fresh(solver, env, t)).collect();
            let p_params = env.datatypes[name].pred_params.clone();
            let p_args1: Vec<Formula> = p_params
                .iter()
                .map(|sig| {
                    let sorts: Vec<Sort> = sig
                        .pred_sig_arg_sorts
                        .iter()
                        .map(|s| {
                            crate::logic::noncapture_sort_subst(
                                &env.datatypes[name].type_params,
                                &t_args1
                                    .iter()
                                    .map(|t| to_sort(&base_type_of(t)))
                                    .collect::<Vec<_>>(),
                                s,
                            )
                        })
                        .collect();
                    fresh_pred(solver, env, &sorts)
                })
                .collect();
            BaseType::DatatypeT(name.clone(), t_args1, p_args1)
        }
        other => other.clone(),
    }
}

/// `freshPred`.
fn fresh_pred(solver: &mut TcSolver, env: &Environment, sorts: &[Sort]) -> Formula {
    let p1 = fresh_id(solver, "P");
    add_typing_constraint(
        &mut solver.state,
        &Constraint::WellFormedPredicate(Rc::new((*env).clone()), sorts.to_vec(), p1.clone()),
    );
    let args: Vec<Formula> = sorts
        .iter()
        .zip(de_brujns(sorts.len()))
        .map(|(s, n)| Formula::Var(Box::new(s.clone()), n))
        .collect();
    Formula::Pred(Box::new(Sort::BoolS), p1, args)
}

/// `addTypeAssignment`.
fn add_type_assignment(solver: &mut TcSolver, tv: &Id, t: RType) {
    solver.state.type_assignment.insert(tv.clone(), t);
}

/// `addPredAssignment`.
fn add_pred_assignment(solver: &mut TcSolver, p: &Id, fml: Formula) {
    solver.state.pred_assignment.insert(p.clone(), fml);
}

/// `addQuals`.
fn add_quals(solver: &mut TcSolver, name: &Id, quals: QSpace) {
    let quals1 = solver.horn.prune_qualifiers(quals);
    solver.state.qualifier_map.insert(name.clone(), quals1);
}

/// `addFixedUnknown`: add unknown `name` with
/// valuation `valuation` to solutions of all candidates.
pub fn add_fixed_unknown(solver: &mut TcSolver, name: &Id, valuation: &BTreeSet<Formula>) {
    add_quals(
        solver,
        name,
        to_space(None, valuation.iter().cloned().collect()),
    );
    let mut cands = std::mem::take(&mut solver.state.candidates);
    for cand in &mut cands {
        cand.solution.insert(name.clone(), valuation.clone());
    }
    solver.state.candidates = cands;
}

/// `setUnknownRecheck`: set valuation of
/// unknown `name` to `valuation` and re-check the affected constraints in all
/// candidates.
pub fn set_unknown_recheck(
    solver: &mut TcSolver,
    name: &Id,
    valuation: &BTreeSet<Formula>,
    duals: &BTreeSet<Id>,
) -> Result<(), ErrorMessage> {
    let cand = &solver.state.candidates[0];
    let clauses: BTreeSet<Formula> = cand
        .valid_constraints
        .iter()
        .filter(|fml| {
            unknowns_of(fml)
                .into_iter()
                .map(|u| unknown_name(&u).clone())
                .any(|u| u == *name)
        })
        .cloned()
        .collect();
    let _ = name;
    let cands1: Vec<crate::logic::Candidate> = solver
        .state
        .candidates
        .iter()
        .map(|c| {
            let mut c1 = c.clone();
            c1.solution.insert(name.clone(), valuation.clone());
            c1
        })
        .collect();
    let env = solver.state.init_env.clone();
    let extract = instantiate_cons_axioms_curried(&env);
    let cands2 = solver.horn.check_candidates(
        false,
        &Vec::from_iter(clauses.iter().cloned()),
        &extract,
        &cands1,
    );
    if cands2.is_empty() {
        return Err(throw_error(
            &solver.state,
            text("Re-checking candidates failed"),
        ));
    }
    let live_clauses: BTreeSet<Formula> = cand
        .valid_constraints
        .iter()
        .filter(|fml| {
            let fml_unknowns: BTreeSet<Id> = unknowns_of(fml)
                .into_iter()
                .map(|u| unknown_name(&u).clone())
                .collect();
            disjoint(duals, &fml_unknowns)
        })
        .cloned()
        .collect();
    solver.state.candidates = cands2
        .into_iter()
        .map(|mut c| {
            c.valid_constraints = c
                .valid_constraints
                .intersection(&live_clauses)
                .cloned()
                .collect();
            c.invalid_constraints = c
                .invalid_constraints
                .intersection(&live_clauses)
                .cloned()
                .collect();
            c
        })
        .collect();
    Ok(())
}

/// `instantiateConsAxioms`.
///
/// If `fml` contains constructor applications, return the set of
/// instantiations of constructor axioms for those applications in the
/// environment `env`.
#[must_use]
pub fn instantiate_cons_axioms(
    env: &Environment,
    m_val: Option<&Formula>,
    fml: &Formula,
) -> BTreeSet<Formula> {
    match fml {
        Formula::Cons(res_s, ctor, args) => {
            match res_s.as_ref() {
                Sort::DataS(dt_name, _) => {
                    let mut acc: BTreeSet<Formula> = BTreeSet::new();
                    for (m_name, m) in all_measures_of(dt_name, env) {
                        acc.insert(measure_axiom(res_s, ctor, args, m_val, &m_name, &m));
                    }
                    for arg in args {
                        acc.extend(instantiate_cons_axioms(env, None, arg));
                    }
                    acc
                }
                _ => BTreeSet::new(),
            }
        }
        Formula::Unary(_, e) => instantiate_cons_axioms(env, m_val, e),
        Formula::Binary(_, e1, e2) => {
            let mut acc = instantiate_cons_axioms(env, m_val, e1);
            acc.extend(instantiate_cons_axioms(env, m_val, e2));
            acc
        }
        Formula::Ite(e0, e1, e2) => {
            let mut acc = instantiate_cons_axioms(env, m_val, e0);
            acc.extend(instantiate_cons_axioms(env, m_val, e1));
            acc.extend(instantiate_cons_axioms(env, m_val, e2));
            acc
        }
        Formula::SetLit(_, elems) => {
            let mut acc = BTreeSet::new();
            for e in elems {
                acc.extend(instantiate_cons_axioms(env, m_val, e));
            }
            acc
        }
        Formula::Pred(_, _, args) => {
            let mut acc = BTreeSet::new();
            for arg in args {
                acc.extend(instantiate_cons_axioms(env, m_val, arg));
            }
            acc
        }
        _ => BTreeSet::new(),
    }
}

/// `measureAxiom` (in `instantiateConsAxioms`).
fn measure_axiom(
    res_s: &Sort,
    ctor: &Id,
    args: &[Formula],
    m_val: Option<&Formula>,
    _m_name: &Id,
    m: &crate::program::MeasureDef,
) -> Formula {
    let case = m
        .definitions
        .iter()
        .find(|c| c.constructor == *ctor)
        .expect("measureAxiom: no case for constructor");
    let s_params: Vec<Id> = sort_args_of(&m.in_sort)
        .iter()
        .map(|s| var_sort_name(s).clone())
        .collect();
    let s_args = sort_args_of(res_s);
    let body1 = crate::logic::noncapture_sort_subst_fml(&s_params, &s_args, &case.body);
    let new_value = match m_val {
        Some(v) => v.clone(),
        None => Formula::Cons(Box::new(res_s.clone()), ctor.clone(), args.to_vec()),
    };
    let mut subst: Substitution = BTreeMap::new();
    subst.insert(VALUE_VAR_NAME.to_string(), new_value);
    for (v, a) in case.arg_names.iter().zip(args.iter()) {
        subst.insert(v.clone(), a.clone());
    }
    let v_subst_body = substitute(&subst, body1);
    let mut result = v_subst_body;
    for (x, s) in m.constant_args.iter().rev() {
        result = Formula::All(
            Box::new(Formula::Var(Box::new(s.clone()), x.clone())),
            Box::new(result),
        );
    }
    result
}

/// `matchConsType`: unify constructor return
/// type `formal` with `actual`.
pub fn match_cons_type(
    solver: &mut TcSolver,
    formal: &RType,
    actual: &RType,
) -> Result<(), ErrorMessage> {
    match (formal, actual) {
        (
            TypeSkeleton::ScalarT(BaseType::DatatypeT(d, vars, p_vars), _),
            TypeSkeleton::ScalarT(BaseType::DatatypeT(d1, args, p_args), _),
        ) if d == d1 => {
            for (var, t) in vars.iter().zip(args.iter()) {
                if let TypeSkeleton::ScalarT(BaseType::TypeVarT(_, a), Formula::BoolLit(true)) = var
                {
                    add_type_assignment(solver, a, t.clone());
                }
            }
            for (p_var, fml) in p_vars.iter().zip(p_args.iter()) {
                if let Formula::Pred(_, p, _) = p_var {
                    add_pred_assignment(solver, p, fml.clone());
                }
            }
            Ok(())
        }
        _ => {
            Err(throw_error(
                &solver.state,
                text(&format!(
                    "matchConsType: cannot match {} against {}",
                    show_doc(&formal.pretty()),
                    show_doc(&actual.pretty()),
                )),
            ))
        }
    }
}

/// `currentAssignment`.
#[must_use]
pub fn current_assignment(solver: &TcSolver, t: &RType) -> RType {
    type_substitute(&solver.state.type_assignment, t)
}

/// Read-only variant of [`current_assignment`] on the type assignment alone
/// (the explorer reads it without cloning the typing state).
#[must_use]
pub fn current_assignment_tass(tass: &TypeSubstitution, t: &RType) -> RType {
    type_substitute(tass, t)
}

/// `finalizeType`: substitute type variables,
/// predicate variables, and predicate unknowns in `t`.
#[must_use]
pub fn finalize_type(solver: &TcSolver, t: &RType) -> RType {
    let sol = solver.state.candidates[0].solution.clone();
    type_apply_solution(
        &sol,
        &type_substitute_pred(
            &solver.state.pred_assignment,
            &type_substitute(&solver.state.type_assignment, t),
        ),
    )
}

/// Read-only variant of [`finalize_type`] on the typing state (no TCS run).
#[must_use]
pub fn finalize_type_state(state: &TypingState, t: &RType) -> RType {
    let sol = state.candidates[0].solution.clone();
    type_apply_solution(
        &sol,
        &type_substitute_pred(
            &state.pred_assignment,
            &type_substitute(&state.type_assignment, t),
        ),
    )
}

/// `finalizeProgram`.
#[must_use]
pub fn finalize_program(
    solver: &TcSolver,
    p: &crate::program::RProgram,
) -> crate::program::RProgram {
    let sol = solver.state.candidates[0].solution.clone();
    crate::program::map_type(p, &|t| {
        type_apply_solution(
            &sol,
            &type_substitute_pred(
                &solver.state.pred_assignment,
                &type_substitute(&solver.state.type_assignment, t),
            ),
        )
    })
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeMap, fs};

    use super::*;
    use crate::{
        cli::default_horn_solver_params,
        logic::{Formula, Sort, ftrue, ge, int_lit, le, to_space},
        parser::parse_program,
        program::{Goal, add_variable},
        resolver::resolve_decls,
        types::{int, to_monotype, type_substitute},
    };

    /// Path of a fixture under the workspace root (tests run with the package
    /// manifest dir as CWD, so fixtures resolve through the manifest dir).
    fn repo_root() -> std::path::PathBuf {
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
    }

    fn replicate_goal() -> Goal {
        let src = fs::read_to_string(repo_root().join("specs/test/pldi16/List-Replicate.sq"))
            .expect("read benchmark");
        let decls = parse_program(&src, "List-Replicate.sq").expect("parse benchmark");
        let (goals, ..) = resolve_decls(&decls).expect("resolve benchmark");
        goals
            .into_iter()
            .find(|g| g.g_synthesize)
            .expect("synthesis goal for replicate")
    }

    /// Goal spec of `replicate`, with the type variable `a` instantiated to
    /// `Int`: `n:Nat -> x:Int -> {List Int | len _v == n}`.
    fn replicate_spec(env: &Environment) -> (RType, RType, RType) {
        let goal = replicate_goal();
        let spec = to_monotype(&goal.g_spec);
        let spec = type_substitute(&BTreeMap::from([("a".to_string(), int(ftrue()))]), &spec);
        let TypeSkeleton::FunctionT(_n_name, nat_t, t_rest) = &spec else {
            panic!("spec is not a function type")
        };
        let TypeSkeleton::FunctionT(_x_name, _, t_res) = &**t_rest else {
            panic!("spec is not a two-argument function type")
        };
        assert!(env.datatypes.contains_key("List"));
        ((**nat_t).clone(), (**t_res).clone(), spec)
    }

    fn test_typing_params() -> TypingParams {
        let cond_quals_gen: CondQualsGen = Rc::new(|_, _| to_space(None, vec![]));
        let match_quals_gen: MatchQualsGen = Rc::new(|_, _| to_space(None, vec![]));
        let type_quals_gen: TypeQualsGen = Rc::new(|_, val, _| {
            let is_int = matches!(val, Formula::Var(s, _) if *s.as_ref() == Sort::IntS);
            if is_int {
                to_space(None, vec![
                    ge(val.clone(), int_lit(0)),
                    le(val.clone(), int_lit(0)),
                    crate::logic::eq(val.clone(), int_lit(0)),
                ])
            } else {
                to_space(None, vec![])
            }
        });
        let pred_quals_gen: PredQualsGen = Rc::new(|_, _, _| to_space(None, vec![]));
        TypingParams {
            cond_quals_gen,
            match_quals_gen,
            type_quals_gen,
            pred_quals_gen,
            tc_solver_split_measures: false,
            tc_solver_log_level: 0,
        }
    }

    fn int_unknown(name: &str) -> RType {
        int(Formula::Unknown(BTreeMap::new(), name.to_string()))
    }

    fn list_int(fml: Formula) -> RType {
        TypeSkeleton::ScalarT(
            BaseType::DatatypeT("List".to_string(), vec![int(ftrue())], Vec::new()),
            fml,
        )
    }

    fn type_var_int(name: &str) -> RType {
        TypeSkeleton::ScalarT(
            BaseType::TypeVarT(BTreeMap::new(), name.to_string()),
            ftrue(),
        )
    }

    #[test]
    fn all_scalars_on_replicate_goal_env() {
        let goal = replicate_goal();
        // Only `zero` is a monomorphic nullary symbol: `Nil` and `Emptyset`
        // are polymorphic (ForallT) and excluded.
        assert_eq!(all_scalars(&goal.g_environment), vec![int_lit(0)]);
    }

    #[test]
    fn fresh_ids_and_vars_avoid_bound_symbols() {
        let goal = replicate_goal();
        let env = goal.g_environment;
        let params = test_typing_params();
        let mut horn = FixPointSolver::init_horn_solver(&env, &default_horn_solver_params());
        run_tc_solver(&params, init_typing_state(&env), &mut horn, |solver| {
            // `zero` is bound in the environment; ids are issued by prefix.
            let fv = fresh_var(solver, &env, "zero");
            assert_eq!(fv, "zero0");
            let z1 = fresh_id(solver, "zero");
            let z2 = fresh_id(solver, "zero");
            assert_eq!(z1, "zero1");
            assert_eq!(z2, "zero2");
            // A fresh id colliding with a bound symbol is skipped by recursion.
            solver.state.id_count.insert("x".to_string(), 1);
            let env1 = add_variable(&"x1".to_string(), &int(ftrue()), &env);
            assert_eq!(fresh_var(solver, &env1, "x"), "x2");
            // someWhatFreshVar appends the counter to the prefix.
            let sfv = somewhat_fresh_var(&env, "zero", Sort::IntS);
            assert_eq!(sfv, Formula::Var(Box::new(Sort::IntS), "zero0".to_string()));
            let env2 = add_variable(&"zero0".to_string(), &int(ftrue()), &env);
            let sfv2 = somewhat_fresh_var(&env2, "zero", Sort::IntS);
            assert_eq!(
                sfv2,
                Formula::Var(Box::new(Sort::IntS), "zero00".to_string())
            );
            Ok::<(), ErrorMessage>(())
        })
        .expect("run tc solver");
    }

    #[test]
    fn simplify_unifies_free_type_var_with_nat() {
        let goal = replicate_goal();
        let env = goal.g_environment;
        let (nat_t, ..) = replicate_spec(&env);
        let params = test_typing_params();
        let mut horn = FixPointSolver::init_horn_solver(&env, &default_horn_solver_params());
        let ((), state) = run_tc_solver(&params, init_typing_state(&env), &mut horn, |solver| {
            add_typing_constraint(
                &mut solver.state,
                &Constraint::Subtype(
                    Rc::new((*env).clone()),
                    type_var_int("a"),
                    nat_t.clone(),
                    false,
                    String::new(),
                ),
            );
            simplify_all_constraints(solver)
        })
        .expect("simplify");
        // `a` is unified with a fresh instance of Nat; the substituted
        // constraint remains as a simple constraint.
        assert_eq!(state.type_assignment.get("a"), Some(&int_unknown("U0")));
        assert_eq!(state.simple_constraints, vec![Constraint::Subtype(
            Rc::new((*env).clone()),
            int_unknown("U0"),
            nat_t.clone(),
            false,
            String::new()
        )]);
    }

    #[test]
    fn solve_nat_subtyping_pair_is_deterministic() {
        let goal = replicate_goal();
        let env = goal.g_environment;
        let (nat_t, ..) = replicate_spec(&env);
        let params = test_typing_params();
        let mut horn = FixPointSolver::init_horn_solver(&env, &default_horn_solver_params());
        let run = |horn: &mut FixPointSolver| {
            run_tc_solver(&params, init_typing_state(&env), horn, |solver| {
                let tv = type_var_int("a");
                add_typing_constraint(
                    &mut solver.state,
                    &Constraint::Subtype(
                        Rc::new((*env).clone()),
                        tv.clone(),
                        nat_t.clone(),
                        false,
                        String::new(),
                    ),
                );
                add_typing_constraint(
                    &mut solver.state,
                    &Constraint::WellFormed(Rc::new((*env).clone()), tv),
                );
                solve_type_constraints(solver)
            })
        };
        let ((), state1) = run(&mut horn).expect("solve Nat subtyping pair");
        // The unknown generated for `a` got a qualifier map entry and the
        // constraints are satisfied by at least one candidate valuation.
        assert!(state1.qualifier_map.contains_key("U0"));
        assert!(!state1.candidates.is_empty());
        assert!(
            state1
                .candidates
                .iter()
                .all(|c| c.invalid_constraints.is_empty())
        );
        assert!(state1.candidates.iter().all(|c| !c.solution.is_empty()));
        assert_eq!(state1.type_assignment.get("a"), Some(&int_unknown("U0")));
        // Determinism: a second run from the same initial state ends in the
        // same final state.
        let ((), state2) = run(&mut horn).expect("solve again");
        assert_eq!(state1, state2);
    }

    #[test]
    fn simplify_function_pair_from_spec_decomposes() {
        let goal = replicate_goal();
        let env = goal.g_environment;
        let (nat_t, list_t, spec) = replicate_spec(&env);
        let TypeSkeleton::FunctionT(n_name, _, t_rest) = &spec else {
            unreachable!()
        };
        let TypeSkeleton::FunctionT(x_name, ..) = &**t_rest else {
            unreachable!()
        };
        let n_name = n_name.clone();
        let x_name = x_name.clone();
        let body = TypeSkeleton::FunctionT(
            n_name.clone(),
            Box::new(int_unknown("U0")),
            Box::new(TypeSkeleton::FunctionT(
                x_name.clone(),
                Box::new(int(ftrue())),
                Box::new(list_int(Formula::Unknown(
                    BTreeMap::new(),
                    "U1".to_string(),
                ))),
            )),
        );
        let params = test_typing_params();
        let mut horn = FixPointSolver::init_horn_solver(&env, &default_horn_solver_params());
        let ((), state) = run_tc_solver(&params, init_typing_state(&env), &mut horn, |solver| {
            add_typing_constraint(
                &mut solver.state,
                &Constraint::Subtype(Rc::new((*env).clone()), body, spec, false, String::new()),
            );
            simplify_all_constraints(solver)
        })
        .expect("simplify function pair");
        // The reference binds the right-side (spec) argument name to the
        // right-side (spec) argument type: `addVariable y tArg2 env`, twice
        // for the two nested function types.
        let env1 = add_variable(&n_name, &nat_t, &env);
        let env2 = add_variable(&x_name, &int(ftrue()), &env1);
        let TypeSkeleton::ScalarT(BaseType::DatatypeT(_, t_args, p_args), list_t_fml) = &list_t
        else {
            unreachable!()
        };
        assert!(t_args.len() == 1 && p_args.is_empty());
        let list_t_rest = TypeSkeleton::ScalarT(
            BaseType::DatatypeT("List".to_string(), Vec::new(), Vec::new()),
            list_t_fml.clone(),
        );
        assert_eq!(state.simple_constraints, vec![
            // Contravariant argument check: spec's Nat <: body's U0
            // (`Subtype env tArg2 tArg1`).
            Constraint::Subtype(
                Rc::new((*env).clone()),
                nat_t,
                int_unknown("U0"),
                false,
                String::new()
            ),
            // Covariant result: inner function, contravariant arg int <: int.
            Constraint::Subtype(
                Rc::new(env1),
                int(ftrue()),
                int(ftrue()),
                false,
                String::new()
            ),
            // Covariant result: List type-argument decomposition.
            Constraint::Subtype(
                Rc::new(env2.clone()),
                int(ftrue()),
                int(ftrue()),
                false,
                String::new()
            ),
            // Covariant result: refinements, differing formulas are kept
            // (the reference falls through to the simple-constraint arm).
            Constraint::Subtype(
                Rc::new(env2),
                TypeSkeleton::ScalarT(
                    BaseType::DatatypeT("List".to_string(), Vec::new(), Vec::new()),
                    Formula::Unknown(BTreeMap::new(), "U1".to_string()),
                ),
                list_t_rest,
                false,
                String::new()
            ),
        ]);
    }
}

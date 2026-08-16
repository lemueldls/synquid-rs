//! Resolution of the parsed AST (mirror of `Synquid.Resolver`): fills in
//! unknown sorts, checks that refinement formulas are well-sorted booleans,
//! and extracts synthesis/typechecking goals.

use std::{
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

use crate::{
    error::{no_pos, ErrorKind, ErrorMessage, Pos, SourcePos},
    logic::{
        eq, ftrue, is_set_s, sort_of, sort_substitute, sort_substitute_fml, substitute,
        type_vars_of_sort, unify_sorts, var_name, vars_of, BinOp, Formula, PredSig, Sort,
        SortConstraint, SortSubstitution, Substitution, UnOp, DONT_CARE, VALUE_VAR_NAME,
    },
    pretty::text,
    program::{
        add_bound_predicate, add_datatype, add_global_predicate, add_measure, add_poly_constant,
        add_type_synonym, add_unresolved_constant, add_variable, all_symbols, default_set_type,
        empty_env, generate_schema, is_constant, measure_prog, remove_variable, symbols_of_arity,
        untyped, BareDeclaration, BareProgram, Case, DatatypeDef, Environment, Goal, MeasureCase,
        MeasureDef, RProgram, UProgram,
    },
    types::{
        add_refinement, add_refinement_to_last_sch, all_arg_types, all_args, arity, base_type_of,
        bound_vars_of, from_sort, is_function_type, last_type, noncapture_type_subst, to_monotype,
        to_sort, type_vars_of, vart_all, BaseType, RSchema, RType, SchemaSkeleton, TypeSkeleton,
    },
    util::Id,
};

/// Result of a resolution step.
pub type RRes<T> = Result<T, ErrorMessage>;

/// Names used for de Bruijn indices in predicate arguments (`_.0`, `_.1`, ...).
pub fn de_brujns() -> impl Iterator<Item = Id> {
    (0..).map(|i| format!("_{i}"))
}

fn nominal_pred_app(sig: &PredSig) -> Formula {
    Formula::Pred(
        Box::new(sig.pred_sig_res_sort.clone()),
        sig.pred_sig_name.clone(),
        sig.pred_sig_arg_sorts
            .iter()
            .cloned()
            .zip(de_brujns())
            .map(|(s, x)| Formula::Var(Box::new(s), x))
            .collect(),
    )
}

/// State threaded through declaration resolution.
pub struct ResolverState {
    pub environment: Environment,
    pub goals: Vec<(Id, (UProgram, SourcePos))>,
    pub checking_goals: Vec<(Id, (UProgram, SourcePos))>,
    pub cond_qualifiers: Vec<Formula>,
    pub type_qualifiers: Vec<Formula>,
    pub mutuals: BTreeMap<Id, Vec<Id>>,
    pub inlines: BTreeMap<Id, (Vec<Id>, Formula)>,
    pub sort_constraints: Vec<SortConstraint>,
    pub current_position: SourcePos,
    pub id_count: usize,
}

/// Initial resolver state.
#[must_use]
pub fn init_resolver_state() -> ResolverState {
    ResolverState {
        environment: empty_env(),
        goals: vec![],
        checking_goals: vec![],
        cond_qualifiers: vec![],
        type_qualifiers: vec![],
        mutuals: BTreeMap::new(),
        inlines: BTreeMap::new(),
        sort_constraints: vec![],
        current_position: no_pos(),
        id_count: 0,
    }
}

/// Add all variables `x : s` occurring in `fmls` to the environment.
#[must_use]
pub fn add_all_variables(env: &Environment, fmls: &[Formula]) -> Environment {
    let mut env = env.clone();
    for f in fmls {
        if let Formula::Var(s, x) = f {
            env = add_variable(x, &from_sort(s), &env);
        }
    }
    env
}

/// `instantiateSorts`: replace sort variables with fresh
/// type variables.
#[must_use]
pub fn instantiate_sorts(sorts: &[Sort]) -> Vec<Sort> {
    let mut st = init_resolver_state();
    st.instantiate(sorts)
}

/// `resolveRefinement`: check that `fml` is a well-sorted
/// boolean formula in the environment `env`, resolving and instantiating sort
/// variables.
pub fn resolve_refinement(env: &Environment, fml: &Formula) -> RRes<Formula> {
    let mut st = init_resolver_state();
    st.environment = env.clone();
    st.resolve_type_refinement(Sort::AnyS, fml)
}

/// `resolveRefinedType`: check that the refined type `t` is
/// well-formed in the environment `env`, resolving and instantiating sort
/// variables.
pub fn resolve_refined_type(env: &Environment, t: &RType) -> RRes<RType> {
    let mut st = init_resolver_state();
    st.environment = env.clone();
    st.resolve_type(t)
}

impl ResolverState {
    fn throw_res_error(&self, description: String) -> ErrorMessage {
        ErrorMessage::new(
            ErrorKind::ResolutionError,
            self.current_position.clone(),
            text(&description),
        )
    }

    /// Restore the environment after running `f`.
    fn with_local_env<T>(&mut self, f: impl FnOnce(&mut Self) -> RRes<T>) -> RRes<T> {
        let old_env = self.environment.clone();
        let res = f(self);
        self.environment = old_env;
        res
    }

    fn fresh_sort(&mut self) -> Sort {
        let i = self.id_count;
        self.id_count += 1;
        Sort::VarS(format!("S{i}"))
    }

    /// `freshId p s`: fresh var with prefix `p` of sort `s`.
    fn fresh_id(&mut self, prefix: &Id, s: Sort) -> Formula {
        let i = self.id_count;
        self.id_count += 1;
        Formula::Var(Box::new(s), format!("{prefix}{i}"))
    }

    /// Replace all sort variables in `sorts` with fresh sort variables.
    fn instantiate(&mut self, sorts: &[Sort]) -> Vec<Sort> {
        let tvs: Vec<Id> = sorts
            .iter()
            .flat_map(type_vars_of_sort)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let fresh: SortSubstitution = tvs
            .iter()
            .map(|tv| (tv.clone(), self.fresh_sort()))
            .collect();
        sorts
            .iter()
            .cloned()
            .map(|s| sort_substitute(&fresh, s))
            .collect()
    }

    fn enforce_same(&mut self, sl: Sort, sr: Sort) {
        if sl != sr {
            self.sort_constraints.push(SortConstraint::SameSort(sl, sr));
        }
    }

    fn solve_sort_constraints(&mut self) -> RRes<SortSubstitution> {
        let (unification_cs, type_class_cs): (Vec<SortConstraint>, Vec<SortConstraint>) = self
            .sort_constraints
            .drain(..)
            .partition(|c| matches!(c, SortConstraint::SameSort(_, _)));
        let tvs: BTreeSet<Id> = self.environment.bound_type_vars.iter().cloned().collect();
        self.id_count = 0;
        let (sls, srs): (Vec<Sort>, Vec<Sort>) = unification_cs
            .iter()
            .map(|c| match c {
                SortConstraint::SameSort(s1, s2) => (s1.clone(), s2.clone()),
                SortConstraint::IsOrd(_) => unreachable!("partitioned as SameSort"),
            })
            .unzip();
        let subst = match unify_sorts(&tvs, &sls, &srs) {
            Ok(subst) => subst,
            Err((x, y)) => {
                return Err(self.throw_res_error(format!("Cannot unify sorts {x} and {y}")));
            }
        };
        for c in &type_class_cs {
            if let SortConstraint::IsOrd(s) = c {
                let s1 = sort_substitute(&subst, s.clone());
                match s1 {
                    Sort::IntS | Sort::VarS(_) => {}
                    _ => return Err(self.throw_res_error(format!("Sort {s1} is not ordered"))),
                }
            }
        }
        Ok(subst)
    }

    fn add_new_signature(&mut self, name: &Id, sch: RSchema) -> RRes<()> {
        if is_constant(name, &self.environment) {
            return Err(self.throw_res_error(format!("Duplicate declaration of function {name}")));
        }
        self.environment = add_poly_constant(name, sch.clone(), &self.environment);
        self.environment = add_unresolved_constant(name, sch, &self.environment);
        Ok(())
    }

    fn substitute_type_synonym(&mut self, name: &Id, t_args: &[RType]) -> RRes<RType> {
        match self.environment.type_synonyms.get(name) {
            None => Err(self.throw_res_error(format!("Datatype or synonym {name} is undefined"))),
            Some((t_vars, t)) => {
                if t_args.len() == t_vars.len() {
                    Ok(noncapture_type_subst(t_vars, t_args, t))
                } else {
                    Err(self.throw_res_error(format!(
                        "Type synonym {} expected {} type arguments and got {}",
                        name,
                        t_vars.len(),
                        t_args.len()
                    )))
                }
            }
        }
    }

    /// All predicates (global + bound) visible in the environment.
    fn all_predicates_env(&self) -> BTreeMap<Id, Vec<Sort>> {
        let mut preds: BTreeMap<Id, Vec<Sort>> = self.environment.global_predicates.clone();
        for sig in &self.environment.bound_predicates {
            let mut sorts = vec![sig.pred_sig_res_sort.clone()];
            sorts.extend(sig.pred_sig_arg_sorts.clone());
            preds.insert(sig.pred_sig_name.clone(), sorts);
        }
        preds
    }
}

/// Convert a parsed program AST into synthesis goals and qualifier maps.
pub fn resolve_decls(
    declarations: &[Pos<BareDeclaration>],
) -> Result<(Vec<Goal>, Vec<Formula>, Vec<Formula>), ErrorMessage> {
    let mut st = init_resolver_state();
    let mut decls = vec![Pos::new(no_pos(), default_set_type())];
    decls.extend_from_slice(declarations);
    // Pass 1: collect all declarations and resolve sorts, but not refinements yet.
    for decl in &decls {
        st.current_position = decl.position.clone();
        st.resolve_declaration(&decl.node)?;
    }
    // Pass 2: resolve refinement types in signatures.
    for decl in &decls {
        st.current_position = decl.position.clone();
        st.resolve_signatures(&decl.node)?;
    }
    let all_names: Vec<Id> = st
        .goals
        .iter()
        .chain(st.checking_goals.iter())
        .map(|(name, _)| name.clone())
        .collect();
    let checked: Vec<Goal> = st
        .checking_goals
        .iter()
        .map(|g| make_goal(false, &st.environment, &all_names, &st.mutuals, g))
        .collect();
    let synthesized: Vec<Goal> = st
        .goals
        .iter()
        .map(|g| make_goal(true, &st.environment, &all_names, &st.mutuals, g))
        .collect();
    let mut goals = checked;
    goals.extend(synthesized);
    Ok((
        goals,
        st.cond_qualifiers.clone(),
        st.type_qualifiers.clone(),
    ))
}

fn make_goal(
    synth: bool,
    env: &Environment,
    all_names: &[Id],
    all_mutuals: &BTreeMap<Id, Vec<Id>>,
    (name, (impl_prog, pos)): &(Id, (UProgram, SourcePos)),
) -> Goal {
    let spec = all_symbols(env)
        .get(name)
        .cloned()
        .expect("makeGoal: no spec for goal");
    let my_mutuals = all_mutuals.get(name).cloned().unwrap_or_default();
    // All goals after and including `name`, except mutuals.
    let idx = all_names
        .iter()
        .position(|n| n == name)
        .expect("makeGoal: goal name not in allNames");
    let to_remove: Vec<Id> = all_names[idx..]
        .iter()
        .filter(|n| !my_mutuals.contains(n))
        .cloned()
        .collect();
    let mut env2 = env.clone();
    for v in to_remove {
        env2 = remove_variable(&v, &env2);
    }
    Goal {
        g_name: name.clone(),
        g_environment: Rc::new(env2),
        g_spec: spec,
        g_impl: impl_prog.clone(),
        g_depth: 0,
        g_source_pos: pos.clone(),
        g_synthesize: synth,
    }
}

impl ResolverState {
    fn resolve_declaration(&mut self, d: &BareDeclaration) -> RRes<()> {
        match d {
            BareDeclaration::TypeDecl(type_name, type_vars, type_body) => {
                let type_body2 = self.resolve_type(type_body)?;
                let extra: BTreeSet<Id> = type_vars_of(&type_body2)
                    .difference(&type_vars.iter().cloned().collect())
                    .cloned()
                    .collect();
                if extra.is_empty() {
                    self.environment = add_type_synonym(
                        type_name,
                        type_vars.clone(),
                        type_body2,
                        &self.environment,
                    );
                    Ok(())
                } else {
                    Err(self.throw_res_error(format!(
                        "Type variable(s) {} in the definition of type synonym {} are undefined",
                        extra.iter().cloned().collect::<Vec<_>>().join(", "),
                        type_name
                    )))
                }
            }
            BareDeclaration::FuncDecl(func_name, type_schema) => {
                self.add_new_signature(func_name, type_schema.clone())
            }
            BareDeclaration::DataDecl(dt_name, t_params, p_var_params, ctors) => {
                let (p_params, p_variances): (Vec<PredSig>, Vec<bool>) =
                    p_var_params.iter().cloned().unzip();
                let datatype = DatatypeDef {
                    type_params: t_params.clone(),
                    pred_params: p_params.clone(),
                    pred_variances: p_variances,
                    constructors: ctors.iter().map(|c| c.name.clone()).collect(),
                    wf_metric: None,
                };
                self.environment = add_datatype(dt_name, datatype, &self.environment);
                for ctor in ctors {
                    // `addPreds typ = foldl (flip ForallP) (Monotype typ) pParams`
                    let add_preds = |typ: RType| {
                        p_params
                            .iter()
                            .rev()
                            .fold(SchemaSkeleton::Monotype(typ), |acc, p| {
                                SchemaSkeleton::ForallP(p.clone(), Box::new(acc))
                            })
                    };
                    self.add_new_signature(&ctor.name, add_preds(ctor.rtype.clone()))?;
                }
                Ok(())
            }
            BareDeclaration::MeasureDecl(
                measure_name,
                in_sort,
                out_sort,
                post,
                _def_cases,
                args,
                is_termination,
            ) => {
                let all_in_sorts: Vec<Sort> = args
                    .iter()
                    .map(|(_, s)| s.clone())
                    .chain(std::iter::once(in_sort.clone()))
                    .collect();
                let var_sort_pairs: Vec<(Option<Id>, Sort)> = args
                    .iter()
                    .map(|(n, s)| (Some(n.clone()), s.clone()))
                    .chain(std::iter::once((None, in_sort.clone())))
                    .collect();
                let sch = generate_schema(
                    &self.environment,
                    measure_name,
                    &var_sort_pairs,
                    out_sort,
                    post,
                );
                self.add_new_signature(measure_name, sch)?;
                for (_, s) in args {
                    self.resolve_sort(s)?;
                }
                self.resolve_sort(in_sort)?;
                self.resolve_sort(out_sort)?;
                match in_sort {
                    Sort::DataS(dt_name, _) => {
                        let datatype = self
                            .environment
                            .datatypes
                            .get(dt_name)
                            .expect("resolveDeclaration: datatype not found")
                            .clone();
                        let t_params = datatype.type_params.clone();
                        let decl_dt_sort = Sort::DataS(
                            dt_name.clone(),
                            t_params.iter().map(|p| Sort::VarS(p.clone())).collect(),
                        );
                        if *in_sort != decl_dt_sort {
                            return Err(self.throw_res_error(format!(
                                "Type parameters of measure {measure_name} must be the same as in the datatype declaration"
                            )));
                        }
                        self.environment = add_global_predicate(
                            measure_name,
                            out_sort.clone(),
                            all_in_sorts,
                            &self.environment,
                        );
                        if *is_termination {
                            if datatype.wf_metric.is_some() {
                                return Err(self.throw_res_error(format!(
                                    "Multiple termination metrics defined for datatype {dt_name}"
                                )));
                            } else if *out_sort == Sort::IntS {
                                let mut dt = datatype;
                                dt.wf_metric = Some(measure_name.clone());
                                self.environment = add_datatype(dt_name, dt, &self.environment);
                            } else {
                                return Err(self.throw_res_error(format!(
                                    "Output sort of termination measure {measure_name} must be Int"
                                )));
                            }
                        }
                        Ok(())
                    }
                    _ => Err(self.throw_res_error(format!(
                        "Input sort of measure {measure_name} must be a datatype"
                    ))),
                }
            }
            BareDeclaration::PredDecl(sig) => {
                if self
                    .environment
                    .global_predicates
                    .contains_key(&sig.pred_sig_name)
                {
                    return Err(self.throw_res_error(format!(
                        "Duplicate declaration of predicate {}",
                        sig.pred_sig_name
                    )));
                }
                self.resolve_sort(&sig.pred_sig_res_sort)?;
                for s in &sig.pred_sig_arg_sorts {
                    self.resolve_sort(s)?;
                }
                let arg_sorts2: Vec<(Option<Id>, Sort)> = sig
                    .pred_sig_arg_sorts
                    .iter()
                    .map(|s| (None, s.clone()))
                    .collect();
                let sch = generate_schema(
                    &self.environment,
                    &sig.pred_sig_name,
                    &arg_sorts2,
                    &sig.pred_sig_res_sort,
                    &ftrue(),
                );
                self.add_new_signature(&sig.pred_sig_name, sch)?;
                self.environment = add_global_predicate(
                    &sig.pred_sig_name,
                    sig.pred_sig_res_sort.clone(),
                    sig.pred_sig_arg_sorts.clone(),
                    &self.environment,
                );
                Ok(())
            }
            BareDeclaration::SynthesisGoal(name, impl_prog) => {
                if all_symbols(&self.environment).contains_key(name) {
                    self.goals.push((
                        name.clone(),
                        (normalize_program(impl_prog), self.current_position.clone()),
                    ));
                    Ok(())
                } else {
                    Err(self.throw_res_error(format!(
                        "No specification found for synthesis goal {name}"
                    )))
                }
            }
            BareDeclaration::QualifierDecl(quals) => {
                for q in quals {
                    if vars_of(q).iter().any(|v| var_name(v) == VALUE_VAR_NAME) {
                        self.type_qualifiers.push(q.clone());
                    } else {
                        self.cond_qualifiers.push(q.clone());
                    }
                }
                Ok(())
            }
            BareDeclaration::MutualDecl(names) => {
                for name in names {
                    if self.goals.iter().any(|(n, _)| n == name) {
                        let my_mutuals: Vec<Id> =
                            names.iter().filter(|n| *n != name).cloned().collect();
                        self.mutuals.insert(name.clone(), my_mutuals);
                    } else {
                        return Err(self.throw_res_error(format!(
                            "Synthesis goal {name} in a mutual clause is undefined"
                        )));
                    }
                }
                Ok(())
            }
            BareDeclaration::InlineDecl(name, args, body) => {
                if self.inlines.contains_key(name) {
                    Err(self.throw_res_error(format!("Duplicate definition of inline {name}")))
                } else {
                    let var_names: BTreeSet<Id> =
                        vars_of(body).iter().map(var_name).cloned().collect();
                    let extra: Vec<Id> = var_names
                        .difference(&args.iter().cloned().collect())
                        .cloned()
                        .collect();
                    if extra.is_empty() {
                        self.inlines
                            .insert(name.clone(), (args.clone(), body.clone()));
                        Ok(())
                    } else {
                        Err(self.throw_res_error(format!(
                            "Variables {} undefined in the body of inline {}",
                            extra.join(", "),
                            name
                        )))
                    }
                }
            }
        }
    }
}

impl ResolverState {
    fn resolve_signatures(&mut self, d: &BareDeclaration) -> RRes<()> {
        match d {
            BareDeclaration::FuncDecl(name, _) => {
                let sch = all_symbols(&self.environment)
                    .get(name)
                    .cloned()
                    .expect("resolveSignatures: symbol not found");
                let sch2 = self.resolve_schema(&sch)?;
                self.environment = add_poly_constant(name, sch2, &self.environment);
                Ok(())
            }
            BareDeclaration::DataDecl(dt_name, t_params, p_params, ctors) => {
                for ctor in ctors {
                    let sch = all_symbols(&self.environment)
                        .get(&ctor.name)
                        .cloned()
                        .expect("resolveSignatures: constructor not found");
                    let sch2 = self.resolve_schema(&sch)?;
                    let nominal_type: RType = TypeSkeleton::ScalarT(
                        BaseType::DatatypeT(
                            dt_name.clone(),
                            t_params.iter().map(|p| vart_all(p)).collect(),
                            p_params
                                .iter()
                                .map(|(sig, _)| nominal_pred_app(sig))
                                .collect(),
                        ),
                        ftrue(),
                    );
                    let return_type = last_type(&to_monotype(&sch2));
                    if nominal_type == return_type {
                        let nominal_sort = to_sort(&base_type_of(&nominal_type));
                        let sch3 = add_refinement_to_last_sch(
                            &sch2,
                            eq(
                                Formula::Var(
                                    Box::new(nominal_sort.clone()),
                                    VALUE_VAR_NAME.to_string(),
                                ),
                                Formula::Cons(
                                    Box::new(nominal_sort),
                                    ctor.name.clone(),
                                    all_args(&to_monotype(&sch2)),
                                ),
                            ),
                        );
                        self.environment = add_poly_constant(&ctor.name, sch3, &self.environment);
                    } else {
                        return Err(self.throw_res_error(format!(
                            "Constructor {} must return type {:?}, got {:?}",
                            ctor.name, nominal_type, return_type
                        )));
                    }
                }
                Ok(())
            }
            BareDeclaration::MeasureDecl(
                measure_name,
                _in_sort,
                _out_sort,
                post,
                def_cases,
                args,
                _,
            ) => {
                let sorts = self
                    .environment
                    .global_predicates
                    .get(measure_name)
                    .cloned()
                    .expect("resolveSignatures: measure sorts not found");
                let (out_sort2, m_args) = sorts
                    .split_first()
                    .expect("resolveSignatures: measure sorts empty");
                let in_sort2 = m_args
                    .last()
                    .expect("resolveSignatures: measure has no input sort");
                let datatype_name = match in_sort2 {
                    Sort::DataS(dt_name, _) => dt_name.clone(),
                    _ => {
                        return Err(self.throw_res_error(format!(
                            "Last input of measure {measure_name} must be a datatype"
                        )));
                    }
                };
                let datatype = self
                    .environment
                    .datatypes
                    .get(&datatype_name)
                    .cloned()
                    .expect("resolveSignatures: datatype not found");
                let post2 = self.resolve_type_refinement(out_sort2.clone(), post)?;
                let pos = self.current_position.clone();
                let ctors = datatype.constructors;
                if def_cases.len() != ctors.len() {
                    return Err(self.throw_res_error(format!(
                        "Definition of measure {measure_name} must include one case per constructor of {datatype_name}"
                    )));
                }
                let fresh_consts: Vec<Formula> = args
                    .iter()
                    .map(|(n, s)| self.fresh_id(n, s.clone()))
                    .collect();
                let const_subst: Substitution = args
                    .iter()
                    .zip(fresh_consts.iter())
                    .map(|((n, _), f)| (n.clone(), f.clone()))
                    .collect();
                let mut defs2 = Vec::with_capacity(def_cases.len());
                for case in def_cases {
                    defs2.push(self.resolve_measure_def(
                        measure_name,
                        &ctors,
                        &const_subst,
                        case,
                    )?);
                }
                for case in def_cases {
                    self.check_measure_case(measure_name, args, &case.body)?;
                }
                let sch = all_symbols(&self.environment)
                    .get(measure_name)
                    .cloned()
                    .expect("resolveSignatures: measure symbol not found");
                let sch2 = self.resolve_schema(&sch)?;
                self.environment = add_poly_constant(measure_name, sch2, &self.environment);
                let mut def_cases2 = Vec::with_capacity(def_cases.len());
                for case in def_cases {
                    let body2 = self.resolve_measure_formula(&case.body)?;
                    def_cases2.push(MeasureCase {
                        constructor: case.constructor.clone(),
                        arg_names: case.arg_names.clone(),
                        body: body2,
                    });
                }
                let args2: Vec<(Id, Sort)> = fresh_consts
                    .iter()
                    .map(|f| match f {
                        Formula::Var(s, x) => (x.clone(), (**s).clone()),
                        _ => unreachable!("freshId always returns a Var"),
                    })
                    .collect();
                let m = MeasureDef {
                    in_sort: in_sort2.clone(),
                    out_sort: out_sort2.clone(),
                    definitions: defs2,
                    constant_args: args2,
                    postcondition: post2.clone(),
                };
                self.environment = add_measure(measure_name, m, &self.environment);
                let checking_def = MeasureDef {
                    in_sort: in_sort2.clone(),
                    out_sort: out_sort2.clone(),
                    definitions: def_cases2,
                    constant_args: args.clone(),
                    postcondition: post2,
                };
                let impl_prog = normalize_program(&measure_prog(measure_name, &checking_def));
                self.checking_goals
                    .push((measure_name.clone(), (impl_prog, pos)));
                Ok(())
            }
            BareDeclaration::SynthesisGoal(_, impl_prog) => {
                self.resolve_hole(impl_prog)?;
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn resolve_measure_def(
        &mut self,
        measure_name: &Id,
        all_ctors: &[Id],
        c_sub: &Substitution,
        case: &MeasureCase,
    ) -> RRes<MeasureCase> {
        let ctor_name = &case.constructor;
        if !all_ctors.contains(ctor_name) {
            return Err(self.throw_res_error(format!(
                "Not in scope: data constructor {ctor_name} used in definition of measure"
            )));
        }
        let cons_sch = all_symbols(&self.environment)
            .get(ctor_name)
            .cloned()
            .expect("resolveMeasureDef: constructor not in scope");
        let cons_t = to_monotype(&cons_sch);
        let n = arity(&cons_t);
        if n != case.arg_names.len() {
            return Err(self.throw_res_error(format!(
                "Data constructor {} expected {} binders and got {} in definition of measure",
                ctor_name,
                n,
                case.arg_names.len()
            )));
        }
        let ctor_params = all_args(&cons_t);
        let mut subst: Substitution = c_sub.clone();
        for (binder, param) in case.arg_names.iter().zip(ctor_params.iter()) {
            subst.insert(binder.clone(), param.clone());
        }
        let fml = eq(
            Formula::Pred(
                Box::new(Sort::AnyS),
                measure_name.clone(),
                c_sub
                    .values()
                    .cloned()
                    .chain(std::iter::once(Formula::Var(
                        Box::new(Sort::AnyS),
                        VALUE_VAR_NAME.to_string(),
                    )))
                    .collect(),
            ),
            substitute(&subst, case.body.clone()),
        );
        let value_sort = to_sort(&base_type_of(&last_type(&cons_t)));
        let fml2 = self.with_local_env(|st| {
            st.environment.bound_type_vars = bound_vars_of(&cons_sch);
            st.environment = add_all_variables(&st.environment, &ctor_params);
            let c_sub_vars: Vec<Formula> = c_sub.values().cloned().collect();
            st.environment = add_all_variables(&st.environment, &c_sub_vars);
            st.resolve_type_refinement(value_sort, &fml)
        })?;
        let arg_names: Vec<Id> = ctor_params.iter().map(var_name).cloned().collect();
        Ok(MeasureCase {
            constructor: ctor_name.clone(),
            arg_names,
            body: fml2,
        })
    }

    /// Ensure that measure `m` is called recursively with the same constant
    /// arguments `const_args`.
    fn check_measure_case(
        &mut self,
        measure: &Id,
        const_args: &[(Id, Sort)],
        fml: &Formula,
    ) -> RRes<()> {
        if const_args.is_empty() {
            return Ok(());
        }
        match fml {
            Formula::Unary(_, f) => self.check_measure_case(measure, const_args, f),
            Formula::Binary(_, f, g) => {
                self.check_measure_case(measure, const_args, f)?;
                self.check_measure_case(measure, const_args, g)
            }
            Formula::Ite(f, g, h) => {
                self.check_measure_case(measure, const_args, f)?;
                self.check_measure_case(measure, const_args, g)?;
                self.check_measure_case(measure, const_args, h)
            }
            Formula::Cons(_, _, fs) => {
                for f in fs {
                    self.check_measure_case(measure, const_args, f)?;
                }
                Ok(())
            }
            Formula::Pred(_, x, args) => {
                if x == measure {
                    let num_args = const_args.len();
                    let args_cmp = &args[..num_args];
                    let c_args: Vec<Formula> = const_args
                        .iter()
                        .map(|(x, _)| Formula::Var(Box::new(Sort::AnyS), x.clone()))
                        .collect();
                    if args_cmp != c_args {
                        return Err(self.throw_res_error(format!(
                            "Constant arguments to measure {measure} must not change in recursive call {fml:?}"
                        )));
                    }
                }
                for a in args {
                    self.check_measure_case(measure, const_args, a)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn resolve_hole(&mut self, p: &RProgram) -> RRes<RType> {
        match &p.content {
            BareProgram::PApp(p1, p2) => {
                self.resolve_hole(p1)?;
                self.resolve_hole(p2)
            }
            BareProgram::PFun(_, p) => self.resolve_hole(p),
            BareProgram::PIf(p1, p2, p3) => {
                self.resolve_hole(p1)?;
                self.resolve_hole(p2)?;
                self.resolve_hole(p3)
            }
            BareProgram::PMatch(p, _) => self.resolve_hole(p),
            BareProgram::PFix(_, p) => self.resolve_hole(p),
            BareProgram::PLet(_, p1, p2) => {
                self.resolve_hole(p1)?;
                self.resolve_hole(p2)
            }
            _ => self.resolve_type(&p.type_of),
        }
    }

    fn resolve_schema(&mut self, sch: &RSchema) -> RRes<RSchema> {
        let tvs: Vec<Id> = type_vars_of(&to_monotype(sch)).into_iter().collect();
        let sch2 = self.with_local_env(|st| {
            let mut bound = tvs.clone();
            bound.extend(st.environment.bound_type_vars.clone());
            st.environment.bound_type_vars = bound;
            st.resolve_schema_inner(sch)
        })?;
        Ok(tvs.iter().fold(sch2, |acc, tv| {
            SchemaSkeleton::ForallT(tv.clone(), Box::new(acc))
        }))
    }

    fn resolve_schema_inner(&mut self, sch: &RSchema) -> RRes<RSchema> {
        match sch {
            SchemaSkeleton::ForallP(sig, sch) => {
                let bound_names: Vec<Id> = self
                    .environment
                    .bound_predicates
                    .iter()
                    .map(|s| s.pred_sig_name.clone())
                    .collect();
                if bound_names.contains(&sig.pred_sig_name) {
                    return Err(self.throw_res_error(format!(
                        "Duplicate predicate variables {}",
                        sig.pred_sig_name
                    )));
                }
                for s in &sig.pred_sig_arg_sorts {
                    self.resolve_sort(s)?;
                }
                if sig.pred_sig_res_sort != Sort::BoolS {
                    return Err(self.throw_res_error(format!(
                        "Bound predicate variable {} must return Bool",
                        sig.pred_sig_name
                    )));
                }
                let sch2 = self.with_local_env(|st| {
                    st.environment = add_bound_predicate(sig.clone(), &st.environment);
                    st.resolve_schema_inner(sch)
                })?;
                let extra: BTreeSet<Id> = sig
                    .pred_sig_arg_sorts
                    .iter()
                    .flat_map(type_vars_of_sort)
                    .collect::<BTreeSet<_>>()
                    .difference(&type_vars_of(&to_monotype(&sch2)))
                    .cloned()
                    .collect();
                if !extra.is_empty() {
                    return Err(self.throw_res_error(format!(
                        "Unbound variables {} in sort of bound predicate {}",
                        extra.iter().cloned().collect::<Vec<_>>().join(", "),
                        sig.pred_sig_name
                    )));
                }
                Ok(SchemaSkeleton::ForallP(sig.clone(), Box::new(sch2)))
            }
            SchemaSkeleton::Monotype(t) => Ok(SchemaSkeleton::Monotype(self.resolve_type(t)?)),
            SchemaSkeleton::ForallT(tv, _) => {
                unreachable!("resolveSchema': unexpected ForallT {}", tv)
            }
        }
    }

    fn resolve_type(&mut self, t: &RType) -> RRes<RType> {
        match t {
            TypeSkeleton::ScalarT(BaseType::DatatypeT(name, t_args, p_args), fml) => {
                match self.environment.datatypes.get(name) {
                    None => {
                        let t1 = self.substitute_type_synonym(name, t_args)?;
                        let t2 = self.resolve_type(&t1)?;
                        let fml1 =
                            self.resolve_type_refinement(to_sort(&base_type_of(&t2)), fml)?;
                        Ok(add_refinement(t2, &fml1))
                    }
                    Some(dt) => {
                        if t_args.len() != dt.type_params.len() {
                            return Err(self.throw_res_error(format!(
                                "Datatype {} expected {} type arguments and got {}",
                                name,
                                dt.type_params.len(),
                                t_args.len()
                            )));
                        }
                        if p_args.len() != dt.pred_params.len() {
                            return Err(self.throw_res_error(format!(
                                "Datatype {} expected {} predicate arguments and got {}",
                                name,
                                dt.pred_params.len(),
                                p_args.len()
                            )));
                        }
                        let pred_params = dt.pred_params.clone();
                        let type_params = dt.type_params.clone();
                        let t_args2: Vec<RType> = t_args
                            .iter()
                            .map(|a| self.resolve_type(a))
                            .collect::<RRes<Vec<_>>>()?;
                        let s_args: Vec<Sort> =
                            t_args2.iter().map(|a| to_sort(&base_type_of(a))).collect();
                        let mut p_args2 = Vec::with_capacity(p_args.len());
                        for (sig, arg) in pred_params.iter().zip(p_args.iter()) {
                            let types = type_params.clone();
                            let s_args2 = s_args.clone();
                            let subst = move |s: &Sort| {
                                crate::logic::noncapture_sort_subst(&types, &s_args2, s)
                            };
                            p_args2.push(self.resolve_pred_arg(&subst, sig, arg)?);
                        }
                        let base_t2 = BaseType::DatatypeT(name.clone(), t_args2, p_args2);
                        let fml1 = self.resolve_type_refinement(to_sort(&base_t2), fml)?;
                        Ok(TypeSkeleton::ScalarT(base_t2, fml1))
                    }
                }
            }
            TypeSkeleton::ScalarT(base_t, fml) => {
                let fml1 = self.resolve_type_refinement(to_sort(base_t), fml)?;
                Ok(TypeSkeleton::ScalarT(base_t.clone(), fml1))
            }
            TypeSkeleton::FunctionT(x, t_arg, t_res) => {
                if x == VALUE_VAR_NAME {
                    Err(self
                        .throw_res_error(format!("{VALUE_VAR_NAME} is a reserved variable name")))
                } else if x == DONT_CARE {
                    panic!("resolveType: blank in function type {t:?}")
                } else {
                    let t_arg2 = self.resolve_type(t_arg)?;
                    let t_res2 = self.with_local_env(|st| {
                        if !is_function_type(&t_arg2) {
                            st.environment = add_variable(x, &t_arg2, &st.environment);
                        }
                        st.resolve_type(t_res)
                    })?;
                    Ok(TypeSkeleton::FunctionT(
                        x.clone(),
                        Box::new(t_arg2),
                        Box::new(t_res2),
                    ))
                }
            }
            TypeSkeleton::AnyT => Ok(TypeSkeleton::AnyT),
            TypeSkeleton::LetT(..) => unreachable!("resolveType: unexpected LetT"),
        }
    }

    fn resolve_pred_arg(
        &mut self,
        subst: &impl Fn(&Sort) -> Sort,
        sig: &PredSig,
        fml: &Formula,
    ) -> RRes<Formula> {
        self.with_local_env(|st| {
            let arg_sorts2: Vec<Sort> = sig.pred_sig_arg_sorts.iter().map(subst).collect();
            let vars: Vec<Formula> = arg_sorts2
                .iter()
                .cloned()
                .zip(de_brujns())
                .map(|(s, x)| Formula::Var(Box::new(s), x))
                .collect();
            st.environment = add_all_variables(&st.environment, &vars);
            match fml {
                Formula::Pred(_, p, arg_fmls) if arg_fmls.is_empty() => st.resolve_type_refinement(
                    Sort::AnyS,
                    &Formula::Pred(Box::new(Sort::BoolS), p.clone(), vars),
                ),
                _ => st.resolve_type_refinement(Sort::AnyS, fml),
            }
        })
    }

    fn resolve_sort(&mut self, s: &Sort) -> RRes<()> {
        match s {
            Sort::SetS(el) => self.resolve_sort(el),
            Sort::DataS(name, s_args) => match self.environment.datatypes.get(name) {
                None => {
                    Err(self.throw_res_error(format!("Datatype {name} is undefined in sort {s}")))
                }
                Some(dt) => {
                    let n = dt.type_params.len();
                    if s_args.len() != n {
                        return Err(self.throw_res_error(format!(
                            "Datatype {} expected {} type arguments and got {}",
                            name,
                            n,
                            s_args.len()
                        )));
                    }
                    for a in s_args {
                        self.resolve_sort(a)?;
                    }
                    Ok(())
                }
            },
            _ => Ok(()),
        }
    }

    /// Resolve `fml` as a refinement of sort `value_sort`; a value sort of
    /// `AnyS` means `_v` must not occur.
    fn resolve_type_refinement(&mut self, value_sort: Sort, fml: &Formula) -> RRes<Formula> {
        // Special case to allow undefined value sort for function types.
        if matches!(fml, Formula::BoolLit(true)) {
            return Ok(Formula::BoolLit(true));
        }
        let fml1 = self.with_local_env(|st| {
            if value_sort != Sort::AnyS {
                st.environment = add_variable(
                    &VALUE_VAR_NAME.to_string(),
                    &from_sort(&value_sort),
                    &st.environment,
                );
            }
            st.resolve_formula(fml)
        })?;
        self.enforce_same(sort_of(&fml1), Sort::BoolS);
        let sort_assignment = self.solve_sort_constraints()?;
        let fml2 = sort_substitute_fml(&sort_assignment, &fml1);
        let bound_tvs: BTreeSet<Id> = self.environment.bound_type_vars.iter().cloned().collect();
        let free_tvs: BTreeSet<Id> = type_vars_of_sort(&sort_of(&fml2))
            .difference(&bound_tvs)
            .cloned()
            .collect();
        if free_tvs.is_empty() {
            Ok(fml2)
        } else {
            let const_map: SortSubstitution =
                free_tvs.iter().map(|tv| (tv.clone(), Sort::IntS)).collect();
            Ok(sort_substitute_fml(&const_map, &fml2))
        }
    }

    fn resolve_measure_formula(&mut self, fml: &Formula) -> RRes<Formula> {
        match fml {
            Formula::SetLit(s, fs) => {
                let fs2 = fs
                    .iter()
                    .map(|f| self.resolve_measure_formula(f))
                    .collect::<RRes<Vec<_>>>()?;
                Ok(Formula::SetLit(s.clone(), fs2))
            }
            Formula::Unary(op, f) => Ok(Formula::Unary(
                *op,
                Box::new(self.resolve_measure_formula(f)?),
            )),
            Formula::Binary(op, f1, f2) => Ok(Formula::Binary(
                *op,
                Box::new(self.resolve_measure_formula(f1)?),
                Box::new(self.resolve_measure_formula(f2)?),
            )),
            Formula::Ite(f1, f2, f3) => Ok(Formula::Ite(
                Box::new(self.resolve_measure_formula(f1)?),
                Box::new(self.resolve_measure_formula(f2)?),
                Box::new(self.resolve_measure_formula(f3)?),
            )),
            Formula::Pred(_, name, f) => {
                if let Some((args, body)) = self.inlines.get(name).cloned() {
                    let subst: Substitution = args
                        .iter()
                        .zip(f.iter().cloned())
                        .map(|(a, b)| (a.clone(), b))
                        .collect();
                    self.resolve_measure_formula(&substitute(&subst, body))
                } else {
                    let f2 = f
                        .iter()
                        .map(|x| self.resolve_measure_formula(x))
                        .collect::<RRes<Vec<_>>>()?;
                    Ok(Formula::Pred(Box::new(Sort::AnyS), name.clone(), f2))
                }
            }
            Formula::Cons(s, x, f) => {
                let f2 = f
                    .iter()
                    .map(|a| self.resolve_measure_formula(a))
                    .collect::<RRes<Vec<_>>>()?;
                Ok(Formula::Cons(s.clone(), x.clone(), f2))
            }
            Formula::All(f1, f2) => Ok(Formula::All(
                Box::new(self.resolve_measure_formula(f1)?),
                Box::new(self.resolve_measure_formula(f2)?),
            )),
            _ => Ok(fml.clone()),
        }
    }

    fn resolve_formula(&mut self, fml: &Formula) -> RRes<Formula> {
        match fml {
            Formula::Var(_, x) => {
                let sym0 = symbols_of_arity(0, &self.environment);
                match sym0.get(x) {
                    Some(sch) => match sch {
                        SchemaSkeleton::Monotype(TypeSkeleton::ScalarT(base_t, _)) => {
                            Ok(Formula::Var(Box::new(to_sort(base_t)), x.clone()))
                        }
                        _ => {
                            panic!(
                                "resolveFormula: encountered non-scalar variable {x} in a formula"
                            )
                        }
                    },
                    None => {
                        // Maybe it's a zero-argument predicate?
                        match self.resolve_formula(&Formula::Pred(
                            Box::new(Sort::AnyS),
                            x.clone(),
                            vec![],
                        )) {
                            Err(_) => {
                                Err(self.throw_res_error(format!("Variable {x} is not in scope")))
                            }
                            Ok(f) => Ok(f),
                        }
                    }
                }
            }
            Formula::SetLit(_, elems) => {
                let elem_sort = self.fresh_sort();
                let elems2 = elems
                    .iter()
                    .map(|e| self.resolve_formula(e))
                    .collect::<RRes<Vec<_>>>()?;
                for e in &elems2 {
                    self.enforce_same(sort_of(e), elem_sort.clone());
                }
                Ok(Formula::SetLit(Box::new(elem_sort), elems2))
            }
            Formula::Unary(op, f) => {
                let f1 = self.resolve_formula(f)?;
                let operand_sort = match op {
                    UnOp::Not => Sort::BoolS,
                    UnOp::Neg => Sort::IntS,
                };
                self.enforce_same(sort_of(&f1), operand_sort);
                Ok(Formula::Unary(*op, Box::new(f1)))
            }
            Formula::Binary(op, l, r) => {
                let l1 = self.resolve_formula(l)?;
                let r1 = self.resolve_formula(r)?;
                let op1 = self.add_constraints(*op, &sort_of(&l1), &sort_of(&r1))?;
                Ok(Formula::Binary(op1, Box::new(l1), Box::new(r1)))
            }
            Formula::Ite(c, l, r) => {
                let c1 = self.resolve_formula(c)?;
                let l1 = self.resolve_formula(l)?;
                let r1 = self.resolve_formula(r)?;
                self.enforce_same(sort_of(&c1), Sort::BoolS);
                self.enforce_same(sort_of(&l1), sort_of(&r1));
                Ok(Formula::Ite(Box::new(c1), Box::new(l1), Box::new(r1)))
            }
            Formula::Pred(_, name, arg_fmls) => {
                if let Some((args, body)) = self.inlines.get(name).cloned() {
                    let subst: Substitution = args
                        .iter()
                        .zip(arg_fmls.iter().cloned())
                        .map(|(a, b)| (a.clone(), b))
                        .collect();
                    self.resolve_formula(&substitute(&subst, body))
                } else {
                    let ps = self.all_predicates_env();
                    let sorts = match ps.get(name) {
                        None => {
                            return Err(self.throw_res_error(format!(
                                "Predicate or measure {name} is undefined"
                            )));
                        }
                        Some(sorts) => {
                            if self.environment.global_predicates.contains_key(name) {
                                self.instantiate(sorts)
                            } else {
                                sorts.clone()
                            }
                        }
                    };
                    let (res_sort, arg_sorts) = sorts
                        .split_first()
                        .expect("resolveFormula: predicate with no result sort");
                    if arg_fmls.len() != arg_sorts.len() {
                        return Err(self.throw_res_error(format!(
                            "Expected {} arguments for predicate or measure {} and got {}",
                            arg_sorts.len(),
                            name,
                            arg_fmls.len()
                        )));
                    }
                    let arg_fmls2 = arg_fmls
                        .iter()
                        .map(|f| self.resolve_formula(f))
                        .collect::<RRes<Vec<_>>>()?;
                    for (f, s) in arg_fmls2.iter().zip(arg_sorts.iter()) {
                        self.enforce_same(sort_of(f), s.clone());
                    }
                    Ok(Formula::Pred(
                        Box::new(res_sort.clone()),
                        name.clone(),
                        arg_fmls2,
                    ))
                }
            }
            Formula::Cons(_, name, arg_fmls) => {
                let cons_sch = match all_symbols(&self.environment).get(name) {
                    None => {
                        return Err(
                            self.throw_res_error(format!("Data constructor {name} is undefined"))
                        );
                    }
                    Some(sch) => sch.clone(),
                };
                let cons_t = to_monotype(&cons_sch);
                let mut sorts: Vec<Sort> = std::iter::once(&last_type(&cons_t))
                    .chain(all_arg_types(&cons_t).iter())
                    .map(|t| to_sort(&base_type_of(t)))
                    .collect();
                sorts = self.instantiate(&sorts);
                let (res_sort, arg_sorts) = sorts
                    .split_first()
                    .expect("resolveFormula: constructor with no result sort");
                if arg_fmls.len() != arg_sorts.len() {
                    return Err(self.throw_res_error(format!(
                        "Constructor {} expected {} arguments and got {}",
                        name,
                        arg_sorts.len(),
                        arg_fmls.len()
                    )));
                }
                let arg_fmls2 = arg_fmls
                    .iter()
                    .map(|f| self.resolve_formula(f))
                    .collect::<RRes<Vec<_>>>()?;
                for (f, s) in arg_fmls2.iter().zip(arg_sorts.iter()) {
                    self.enforce_same(sort_of(f), s.clone());
                }
                Ok(Formula::Cons(
                    Box::new(res_sort.clone()),
                    name.clone(),
                    arg_fmls2,
                ))
            }
            _ => Ok(fml.clone()),
        }
    }

    fn add_constraints(&mut self, op: BinOp, sl: &Sort, sr: &Sort) -> RRes<BinOp> {
        match op {
            BinOp::Eq | BinOp::Neq => {
                self.enforce_same(sl.clone(), sr.clone());
                Ok(op)
            }
            BinOp::And | BinOp::Or | BinOp::Implies | BinOp::Iff => {
                self.enforce_same(sl.clone(), Sort::BoolS);
                self.enforce_same(sr.clone(), Sort::BoolS);
                Ok(op)
            }
            BinOp::Member => {
                self.enforce_same(Sort::SetS(Box::new(sl.clone())), sr.clone());
                Ok(op)
            }
            BinOp::Union | BinOp::Intersect | BinOp::Diff | BinOp::Subset => {
                let elem_sort = self.fresh_sort();
                self.enforce_same(sl.clone(), Sort::SetS(Box::new(elem_sort.clone())));
                self.enforce_same(sr.clone(), Sort::SetS(Box::new(elem_sort)));
                Ok(op)
            }
            BinOp::Times | BinOp::Plus | BinOp::Minus => {
                if is_set_s(sl) {
                    let elem_sort = self.fresh_sort();
                    self.enforce_same(sl.clone(), Sort::SetS(Box::new(elem_sort.clone())));
                    self.enforce_same(sr.clone(), Sort::SetS(Box::new(elem_sort)));
                    Ok(to_set_op(op))
                } else {
                    self.enforce_same(sl.clone(), Sort::IntS);
                    self.enforce_same(sr.clone(), Sort::IntS);
                    Ok(op)
                }
            }
            BinOp::Le => {
                if is_set_s(sl) {
                    let elem_sort = self.fresh_sort();
                    self.enforce_same(sl.clone(), Sort::SetS(Box::new(elem_sort.clone())));
                    self.enforce_same(sr.clone(), Sort::SetS(Box::new(elem_sort)));
                    Ok(BinOp::Subset)
                } else {
                    self.enforce_same(sl.clone(), sr.clone());
                    self.sort_constraints
                        .push(SortConstraint::IsOrd(sl.clone()));
                    Ok(op)
                }
            }
            BinOp::Lt | BinOp::Gt | BinOp::Ge => {
                self.enforce_same(sl.clone(), sr.clone());
                self.sort_constraints
                    .push(SortConstraint::IsOrd(sl.clone()));
                Ok(op)
            }
        }
    }
}

fn to_set_op(op: BinOp) -> BinOp {
    match op {
        BinOp::Times => BinOp::Intersect,
        BinOp::Plus => BinOp::Union,
        BinOp::Minus => BinOp::Diff,
        BinOp::Le => BinOp::Subset,
        _ => unreachable!("toSetOp: unexpected operator"),
    }
}

/// Normalize a program: move conditional and match statements to the top
/// level of the program (for typechecking).
#[must_use]
pub fn normalize_program(p: &RProgram) -> RProgram {
    match &p.content {
        BareProgram::PSymbol(name) => untyped(BareProgram::PSymbol(name.clone())),
        BareProgram::PApp(fun, arg) => {
            let fun2 = normalize_program(fun);
            let arg2 = normalize_program(arg);
            let is_cond = |p: &RProgram| {
                matches!(
                    p.content,
                    BareProgram::PIf(_, _, _) | BareProgram::PMatch(_, _)
                )
            };
            match (is_cond(&fun2), is_cond(&arg2)) {
                // Both sides are conditionals; transform the left side.
                (true, true) => transform_l_cond(&fun2, &arg2),
                (true, _) => transform_l_cond(&fun2, &arg2),
                (_, true) => transform_r_cond(&fun2, &arg2),
                _ => untyped(BareProgram::PApp(Box::new(fun2), Box::new(arg2))),
            }
        }
        BareProgram::PFun(name, body) => untyped(BareProgram::PFun(
            name.clone(),
            Box::new(normalize_program(body)),
        )),
        BareProgram::PIf(g, p1, p2) => untyped(BareProgram::PIf(
            Box::new(normalize_program(g)),
            Box::new(normalize_program(p1)),
            Box::new(normalize_program(p2)),
        )),
        BareProgram::PMatch(arg, cases) => untyped(BareProgram::PMatch(
            Box::new(normalize_program(arg)),
            cases
                .iter()
                .map(|c| Case {
                    constructor: c.constructor.clone(),
                    arg_names: c.arg_names.clone(),
                    expr: normalize_program(&c.expr),
                })
                .collect(),
        )),
        BareProgram::PFix(fs, body) => untyped(BareProgram::PFix(
            fs.clone(),
            Box::new(normalize_program(body)),
        )),
        BareProgram::PLet(v, val, body) => untyped(BareProgram::PLet(
            v.clone(),
            Box::new(normalize_program(val)),
            Box::new(normalize_program(body)),
        )),
        _ => p.clone(),
    }
}

/// `prog` applied to the expression of `c`, with each application node untyped.
fn transform_case(prog: &impl Fn(&RProgram) -> RProgram, c: &Case<RType>) -> Case<RType> {
    Case {
        constructor: c.constructor.clone(),
        arg_names: c.arg_names.clone(),
        expr: untyped(prog(&normalize_program(&c.expr)).content),
    }
}

/// Conditional is on the left side of an application.
fn transform_l_cond(l: &RProgram, r: &RProgram) -> RProgram {
    match &l.content {
        BareProgram::PIf(g, t, f) => untyped(BareProgram::PIf(
            g.clone(),
            Box::new(apply(t, r)),
            Box::new(apply(f, r)),
        )),
        BareProgram::PMatch(scr, cases) => untyped(BareProgram::PMatch(
            scr.clone(),
            cases
                .iter()
                .map(|c| transform_case(&|e| apply(e, r), c))
                .collect(),
        )),
        _ => apply(l, r),
    }
}

/// Conditional is on the right side of an application.
fn transform_r_cond(l: &RProgram, r: &RProgram) -> RProgram {
    match &r.content {
        BareProgram::PIf(g, t, f) => untyped(BareProgram::PIf(
            g.clone(),
            Box::new(apply(l, t)),
            Box::new(apply(l, f)),
        )),
        BareProgram::PMatch(scr, cases) => untyped(BareProgram::PMatch(
            scr.clone(),
            cases
                .iter()
                .map(|c| transform_case(&|e| apply(l, e), c))
                .collect(),
        )),
        _ => apply(l, r),
    }
}

fn apply(l: &RProgram, r: &RProgram) -> RProgram {
    untyped(BareProgram::PApp(Box::new(l.clone()), Box::new(r.clone())))
}

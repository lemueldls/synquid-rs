use std::{collections::BTreeSet, iter};

use hashbrown::{HashMap, HashSet};
use itertools::Itertools;

use crate::{
    error::{ErrorKind, ErrorMessage, Pos, SourcePos, NO_POS},
    logic::{
        de_brujns, noncapture_sort_subst, unify_sorts, BinOp, Formula, PredSig, Sort,
        SortConstraint, SortSubstitution, Substitution, UnOp, VALUE_VAR_NAME,
    },
    program::{
        generate_schema, BareDeclaration, BareProgram, Case, DatatypeDef, Declaration, Environment,
        Goal, MeasureCase, MeasureDef, Program, RProgram, UProgram,
    },
    r#type::{non_capture_type_subst, BaseType, RSchema, RType, SchemaSkeleton, TypeSkeleton},
    util::Id,
};

#[derive(Debug, Default)]
pub struct Resolver {
    pub environment: Environment,
    pub goals: Vec<(Id, (UProgram, SourcePos))>,
    pub checking_goals: Vec<(Id, (UProgram, SourcePos))>,
    pub cond_qualifiers: Vec<Formula>,
    pub type_qualifiers: Vec<Formula>,
    pub mutuals: HashMap<Id, Vec<Id>>,
    pub inlines: HashMap<Id, (HashSet<Id>, Formula)>,
    pub sort_constraints: Vec<SortConstraint>,
    pub current_position: SourcePos,
    pub id_count: usize,
}

// type Resolver a = StateT ResolverState (Except ErrorMessage) a

/// Resolve `fml` as a refinement with _v of sort `valueSort`;
/// when `valueSort` is `Any`, _v must not occur
impl Resolver {
    // -- | Convert a parsed program AST into a list of synthesis goals and qualifier maps
    // resolveDecls :: [Declaration] -> Either ErrorMessage ([Goal], [Formula], [Formula])
    // resolveDecls declarations =
    //   case runExcept (execStateT go initResolverState) of
    //     Left msg -> Left msg
    //     Right st ->
    //       Right (typecheckingGoals st ++ synthesisGoals st, st ^. condQualifiers, st ^. typeQualifiers)
    //   where
    //     go = do
    //       -- Pass 1: collect all declarations and resolve sorts, but do not resolve refinement types yet
    //       mapM_ (extractPos resolveDeclaration) declarations'
    //       -- Pass 2: resolve refinement types in signatures
    //       mapM_ (extractPos resolveSignatures) declarations'
    //     declarations' = setDecl : declarations
    //     setDecl = Pos noPos defaultSetType
    //     makeGoal synth env allNames allMutuals (name, (impl, pos)) =
    //       let
    //         spec = allSymbols env Map.! name
    //         myMutuals = Map.findWithDefault [] name allMutuals
    //         toRemove = drop (fromJust $ elemIndex name allNames) allNames \\ myMutuals -- All goals after and including @name@, except mutuals
    //         env' = foldr removeVariable env toRemove
    //       in Goal name env' spec impl 0 pos synth
    //     extractPos pass (Pos pos decl) = do
    //       currentPosition .= pos
    //       pass decl
    //     synthesisGoals st = fmap (makeGoal True (st ^. environment) (map fst ((st ^. goals) ++ (st ^. checkingGoals))) (st ^. mutuals)) (st ^. goals)
    //     typecheckingGoals st = fmap (makeGoal False (st ^. environment) (map fst ((st ^. goals) ++ (st ^. checkingGoals))) (st ^. mutuals)) (st ^. checkingGoals)

    /// Convert a parsed program AST into a list of synthesis goals and qualifier maps
    pub fn resolve_decls(
        &mut self,
        declarations: Vec<Declaration>,
    ) -> Result<(Vec<Goal>, &Vec<Formula>, &Vec<Formula>), ErrorMessage> {
        let set_decl = Pos {
            position: NO_POS,
            node: BareDeclaration::default_set_type(),
        };

        let declarations = iter::once(set_decl)
            .chain(declarations.into_iter().map(Pos::from))
            .collect::<Vec<_>>();

        for decl in declarations.iter().cloned() {
            let Pos {
                position: pos,
                node: decl,
            } = decl.into();
            self.current_position = pos;

            self.resolve_declaration(decl);
        }

        for decl in declarations.iter().cloned() {
            let Pos {
                position: pos,
                node: decl,
            } = decl.into();
            self.current_position = pos;

            self.resolve_declaration(decl);
        }

        let synthesis_goals = self.synthesis_goals();
        let typechecking_goals = self.typechecking_goals();

        let goals = synthesis_goals
            .into_iter()
            .chain(typechecking_goals)
            .collect::<Vec<_>>();

        Ok((goals, &self.cond_qualifiers, &self.type_qualifiers))
    }

    fn make_goal(
        &mut self,
        synth: bool,
        all_names: Vec<Id>,

        (name, (impl_, pos)): &(Id, (UProgram, SourcePos)),
    ) -> Goal {
        let all_mutuals = &self.mutuals;

        let spec = self.environment.all_symbols().get(name).cloned().unwrap();
        let my_mutuals = all_mutuals.get(name).cloned().unwrap_or_default();
        let to_remove = all_names
            .iter()
            .skip_while(|n| *n != name)
            .cloned()
            .filter(|n| !my_mutuals.contains(n))
            .collect::<Vec<_>>();

        for n in to_remove {
            self.environment.remove_variable(&n);
        }

        Goal {
            name: name.clone(),
            // REVIEW - implementation
            environment: self.environment.clone(),
            spec,
            impl_: impl_.clone(),
            depth: 0,
            source_pos: pos.clone(),
            synthesize: synth,
        }
    }

    fn synthesis_goals(&mut self) -> Vec<Goal> {
        let all_names = self
            .environment
            .all_symbols()
            .keys()
            .cloned()
            .collect::<Vec<_>>();

        self.goals
            .clone()
            .iter()
            .map(|goal| self.make_goal(true, all_names.clone(), goal))
            .collect()
    }

    fn typechecking_goals(&mut self) -> Vec<Goal> {
        let all_names = self
            .environment
            .all_symbols()
            .keys()
            .cloned()
            .collect::<Vec<_>>();

        self.checking_goals
            .clone()
            .iter()
            .map(|goal| self.make_goal(false, all_names.clone(), goal))
            .collect()
    }

    // throwResError descr = do
    //   pos <- use currentPosition
    //   throwError $ ErrorMessage ResolutionError pos descr

    pub fn throw_res_error(&self, description: String) -> ErrorMessage {
        ErrorMessage {
            kind: ErrorKind::ResolutionError,
            position: self.current_position.clone(),
            description,
        }
    }

    // resolveRefinement :: Environment -> Formula -> Either ErrorMessage Formula
    // resolveRefinement env fml = runExcept (evalStateT (resolveTypeRefinement AnyS fml) (initResolverState {_environment = env}))

    pub fn resolve_refinement(&mut self, fml: Formula) -> Result<Formula, ErrorMessage> {
        self.resolve_type_refinement(Sort::Any, fml)
    }

    // resolveRefinedType :: Environment -> RType -> Either ErrorMessage RType
    // resolveRefinedType env t = runExcept (evalStateT (resolveType t) (initResolverState {_environment = env}))

    pub fn resolve_refined_type(&mut self, t: RType) -> Result<RType, ErrorMessage> {
        self.resolve_type(t)
    }

    // instantiateSorts :: [Sort] -> [Sort]
    // instantiateSorts sorts = fromRight $ runExcept (evalStateT (instantiate sorts) (initResolverState))

    pub fn instantiate_sorts(&mut self, sorts: Vec<Sort>) -> Vec<Sort> {
        self.instantiate(sorts)
    }

    // addAllVariables :: [Formula] -> Environment -> Environment
    // addAllVariables = flip (foldr (\(Var s x) -> addVariable x (fromSort s)))

    pub fn add_all_variables(&mut self, vars: &Vec<Formula>) {
        for f in vars {
            if let Formula::Var(s, x) = f {
                self.environment
                    .add_variable(x.clone(), RType::from_sort(s));
            } else {
                unreachable!()
            }
        }
    }

    // resolveDeclaration :: BareDeclaration -> Resolver ()
    // resolveDeclaration (TypeDecl typeName typeVars typeBody) = do
    //   typeBody' <- resolveType typeBody
    //   let extraTypeVars = typeVarsOf typeBody' Set.\\ Set.fromList typeVars
    //   if Set.null extraTypeVars
    //     then environment %= addTypeSynonym typeName typeVars typeBody'
    //     else throwResError (text "Type variable(s)" <+> hsep (map text $ Set.toList extraTypeVars) <+>
    //               text "in the definition of type synonym" <+> text typeName <+> text "are undefined")
    // resolveDeclaration (FuncDecl funcName typeSchema) = addNewSignature funcName typeSchema
    // resolveDeclaration d@(DataDecl dtName tParams pVarParams ctors) = do
    //   let
    //     (pParams, pVariances) = unzip pVarParams
    //     datatype = DatatypeDef {
    //       _typeParams = tParams,
    //       _predParams = pParams,
    //       _predVariances = pVariances,
    //       _constructors = map constructorName ctors,
    //       _wfMetric = Nothing
    //     }
    //   environment %= addDatatype dtName datatype
    //   let addPreds typ = foldl (flip ForallP) (Monotype typ) pParams
    //   mapM_ (\(ConstructorSig name typ) -> addNewSignature name $ addPreds typ) ctors
    // resolveDeclaration (MeasureDecl measureName inSort outSort post defCases args isTermination) = do
    //   env <- use environment
    //   let allInSorts = fmap snd args ++ [inSort]
    //   let varSortPairs = fmap (first Just) args ++ [(Nothing, inSort)]
    //   addNewSignature measureName (generateSchema env measureName varSortPairs outSort post)
    //   -- Resolve measure signature:
    //   mapM_ (resolveSort . snd) args
    //   resolveSort inSort
    //   resolveSort outSort
    //   case inSort of
    //     DataS dtName sArgs -> do
    //       -- Check that the input sort of the measure is D a_i, where a_i are the type parameters in the declaration of D:
    //       datatype <- uses (environment . datatypes) (Map.! dtName)
    //       let tParams = datatype ^. typeParams
    //       let declDtSort = DataS dtName (map VarS tParams)
    //       if inSort /= declDtSort
    //         then throwResError (text "Type parameters of measure" <+> text measureName <+> text "must be the same as in the datatype declaration")
    //         else do
    //           environment %= addGlobalPredicate measureName outSort allInSorts
    //           -- Possibly add as termination metric:
    //           when isTermination $
    //             if isJust $ datatype ^. wfMetric
    //               then throwResError (text "Multiple termination metrics defined for datatype" <+> text dtName)
    //               else if outSort == IntS
    //                     then environment %= addDatatype dtName datatype { _wfMetric = Just measureName }
    //                     else throwResError (text "Output sort of termination measure" <+> text measureName <+> text "must be Int")
    //     _ -> throwResError (text "Input sort of measure" <+> text measureName <+> text "must be a datatype")
    // resolveDeclaration (PredDecl (PredSig name argSorts resSort)) = do
    //   ifM (Map.member name <$> use (environment . globalPredicates)) (throwResError (text "Duplicate declaration of predicate" <+> text name)) (return ())
    //   mapM_ resolveSort (resSort : argSorts)
    //   env <- use environment
    //   let argSorts' = fmap (\x -> (Nothing, x)) argSorts
    //   addNewSignature name (generateSchema env name argSorts' resSort ftrue)
    //   environment %= addGlobalPredicate name resSort argSorts
    // resolveDeclaration (SynthesisGoal name impl) = do
    //   syms <- uses environment allSymbols
    //   pos <- use currentPosition
    //   if Map.member name syms
    //     then goals %= (++ [(name, (normalizeProgram impl, pos))])
    //     else throwResError (text "No specification found for synthesis goal" <+> text name)
    // resolveDeclaration (QualifierDecl quals) = mapM_ resolveQualifier quals
    //   where
    //     resolveQualifier q = if Set.member valueVarName (Set.map varName $ varsOf q)
    //       then typeQualifiers %= (q:)
    //       else condQualifiers %= (q:)
    // resolveDeclaration (MutualDecl names) = mapM_ addMutuals names
    //   where
    //     addMutuals name = do
    //       goalMb <- uses goals (lookup name)
    //       case goalMb of
    //         Just _ -> mutuals %= Map.insert name (delete name names)
    //         Nothing -> throwResError (text "Synthesis goal" <+> text name <+> text "in a mutual clause is undefined")
    // resolveDeclaration (InlineDecl name args body) =
    //   ifM (uses inlines (Map.member name))
    //     (throwResError (text "Duplicate definition of inline" <+> text name))
    //     (do
    //       let extraVars = Set.map varName (varsOf body) `Set.difference` Set.fromList args
    //       if not $ Set.null extraVars
    //         then throwResError (text "Variables" <+> hsep (map text $ Set.toList extraVars) <+> text "undefined in the body of inline" <+> text name)
    //         else inlines %= Map.insert name (args, body))

    pub fn resolve_declaration(&mut self, decl: BareDeclaration) -> Result<(), ErrorMessage> {
        match decl {
            BareDeclaration::TypeDecl(type_name, type_vars, type_body) => {
                let type_body = self.resolve_type(type_body)?;
                let extra_type_vars = type_body
                    .type_vars()
                    .difference(&type_vars)
                    .cloned()
                    .collect::<Vec<_>>();
                if extra_type_vars.is_empty() {
                    self.environment
                        .add_type_synonym(type_name, type_vars, type_body);
                } else {
                    return Err(self.throw_res_error(format!(
                        "Type variable(s) {} in the definition of type synonym {type_name} are undefined",
                        extra_type_vars.iter().format(", ")
                    )));
                }
            }
            BareDeclaration::FuncDecl(func_name, type_schema) => {
                self.add_new_signature(func_name, type_schema)?;
            }
            BareDeclaration::DataDecl(dt_name, t_params, p_var_params, ctors) => {
                let (p_params, p_variances): (Vec<_>, Vec<_>) =
                    p_var_params.iter().cloned().unzip();
                let datatype = DatatypeDef {
                    type_params: t_params.clone(),
                    pred_params: p_params.clone(),
                    pred_variances: p_variances.clone(),
                    constructors: ctors.iter().map(|c| c.name().clone()).collect(),
                    wf_metric: None,
                };
                self.environment.add_datatype(dt_name.clone(), datatype);

                let add_preds = |typ| {
                    p_params
                        .iter()
                        .cloned()
                        .rev()
                        .fold(SchemaSkeleton::Monotype(typ), |typ, p| {
                            SchemaSkeleton::ForAllPredicate(p, Box::new(typ))
                        })
                };

                for ctor in ctors {
                    self.add_new_signature(ctor.name().clone(), add_preds(ctor.1.clone()))?;
                }
            }
            BareDeclaration::MeasureDecl(
                measure_name,
                in_sort,
                out_sort,
                post,
                def_cases,
                args,
                is_termination,
            ) => {
                let all_in_sorts = args.iter().map(|(_, s)| s).cloned().collect::<Vec<_>>();
                let var_sort_pairs = args
                    .iter()
                    .map(|(x, s)| (Some(x.clone()), s.clone()))
                    .chain(iter::once((None, in_sort.clone())))
                    .collect::<Vec<_>>();

                self.add_new_signature(
                    measure_name.clone(),
                    generate_schema(
                        &self.environment,
                        &measure_name,
                        &var_sort_pairs,
                        &out_sort,
                        post,
                    ),
                )?;

                for (_, s) in &args {
                    self.resolve_sort(&s)?;
                }
                self.resolve_sort(&in_sort)?;
                self.resolve_sort(&out_sort)?;

                match &in_sort {
                    Sort::Data(dt_name, _s_args) => {
                        let datatype = self.environment.datatypes.get(dt_name).cloned().unwrap();
                        let t_params = datatype.type_params.clone();
                        let decl_dt_sort = Sort::Data(
                            dt_name.clone(),
                            t_params.into_iter().map(Sort::Var).collect(),
                        );
                        if in_sort != decl_dt_sort {
                            return Err(self.throw_res_error(format!(
                                "Type parameters of measure {measure_name} must be the same as in the datatype declaration",
                            )));
                        }

                        self.environment.add_global_predicate(
                            measure_name.clone(),
                            out_sort.clone(),
                            all_in_sorts,
                        );

                        if is_termination {
                            if let Some(_) = datatype.wf_metric {
                                return Err(self.throw_res_error(format!(
                                    "Multiple termination metrics defined for datatype {dt_name}",
                                )));
                            } else if out_sort == Sort::Int {
                                self.environment.add_datatype(
                                    dt_name.clone(),
                                    DatatypeDef {
                                        wf_metric: Some(measure_name.clone()),
                                        ..datatype
                                    },
                                );
                            } else {
                                return Err(self.throw_res_error(format!(
                                    "Output sort of termination measure {measure_name} must be Int",
                                )));
                            }
                        }
                    }
                    _ => {
                        return Err(self.throw_res_error(format!(
                            "Input sort of measure {measure_name} must be a datatype",
                        )));
                    }
                }
            }
            BareDeclaration::PredDecl(PredSig {
                name,
                arg_sorts,
                res_sort,
            }) => {
                if self.environment.global_predicates.contains_key(&name) {
                    return Err(
                        self.throw_res_error(format!("Duplicate declaration of predicate {name}",))
                    );
                }

                for s in arg_sorts.iter().chain(iter::once(&res_sort)) {
                    self.resolve_sort(s)?;
                }

                let arg_sorts = arg_sorts
                    .iter()
                    .cloned()
                    .map(|s| (None, s))
                    .collect::<Vec<_>>();

                self.add_new_signature(
                    name.clone(),
                    generate_schema(
                        &self.environment,
                        &name,
                        &arg_sorts,
                        &res_sort,
                        Formula::TRUE,
                    ),
                )?;

                self.environment.add_global_predicate(
                    name.clone(),
                    res_sort,
                    arg_sorts.iter().map(|(_, s)| s).cloned().collect(),
                );
            }
            BareDeclaration::SynthesisGoal(name, impl_) => {
                let syms = self.environment.all_symbols();
                if syms.contains_key(&name) {
                    self.goals.push((
                        name.clone(),
                        (
                            UProgram::new(normalize_program(impl_.as_ref())),
                            self.current_position.clone(),
                        ),
                    ));
                } else {
                    return Err(self.throw_res_error(format!(
                        "No specification found for synthesis goal {name}",
                    )));
                }
            }
            BareDeclaration::QualifierDecl(quals) => {
                for q in quals {
                    if q.vars()
                        .iter()
                        .map(|f| f.var_name())
                        .contains(&VALUE_VAR_NAME)
                    {
                        self.type_qualifiers.push(q);
                    } else {
                        self.cond_qualifiers.push(q);
                    }
                }
            }
            BareDeclaration::MutualDecl(names) => {
                for name in &names {
                    let goal_mb = self.goals.iter().find(|(n, _)| n == name);
                    match goal_mb {
                        Some(_) => {
                            self.mutuals.insert(
                                name.clone(),
                                names.iter().filter(|n| *n != name).cloned().collect(),
                            );
                        }
                        None => {
                            return Err(self.throw_res_error(format!(
                                "Synthesis goal {name} in a mutual clause is undefined",
                            )));
                        }
                    }
                }
            }
            BareDeclaration::InlineDecl(name, args, body) => {
                if self.inlines.contains_key(&name) {
                    return Err(
                        self.throw_res_error(format!("Duplicate definition of inline {name}",))
                    );
                }

                let extra_vars = body
                    .vars()
                    .iter()
                    .map(|f| f.var_name().clone())
                    .collect::<HashSet<_>>();
                let extra_vars = extra_vars
                    .difference(&args)
                    .cloned()
                    .collect::<HashSet<_>>();

                if !extra_vars.is_empty() {
                    return Err(self.throw_res_error(format!(
                        "Variables {} undefined in the body of inline {name}",
                        extra_vars.iter().format(", ")
                    )));
                }

                self.inlines.insert(name.clone(), (args, body));
            }
        }

        Ok(())
    }

    // resolveSignatures :: BareDeclaration -> Resolver ()
    // resolveSignatures (FuncDecl name _)  = do
    //   sch <- uses environment ((Map.! name) . allSymbols)
    //   sch' <- resolveSchema sch
    //   environment %= addPolyConstant name sch'
    // resolveSignatures (DataDecl dtName tParams pParams ctors) = mapM_ resolveConstructorSignature ctors
    //   where
    //     resolveConstructorSignature (ConstructorSig name _) = do
    //       sch <- uses environment ((Map.! name) . allSymbols)
    //       sch' <- resolveSchema sch
    //       let nominalType = ScalarT (DatatypeT dtName (map vartAll tParams) (map (nominalPredApp  . fst) pParams)) ftrue
    //       let returnType = lastType (toMonotype sch')
    //       if nominalType == returnType
    //         then do
    //           let nominalSort = toSort $ baseTypeOf nominalType
    //           let sch'' = addRefinementToLastSch sch' (Var nominalSort valueVarName |=| Cons nominalSort name (allArgs (toMonotype sch')))
    //           environment %= addPolyConstant name sch''
    //         else throwResError (commaSep [text "Constructor" <+> text name <+> text "must return type" <+> pretty nominalType, text "got" <+> pretty returnType])
    // resolveSignatures (MeasureDecl measureName _ _ post defCases args _) = do
    //   sorts <- uses (environment . globalPredicates) (Map.! measureName)
    //   let (outSort : mArgs) = sorts
    //   case last mArgs of
    //     inSort@(DataS dtName sArgs) -> do
    //       datatype <- uses (environment . datatypes) (Map.! dtName)
    //       post' <- resolveTypeRefinement outSort post
    //       pos <- use currentPosition
    //       let ctors = datatype ^. constructors
    //       let constantArgs = fmap (\(n, s) -> Var s n) args
    //       if length defCases /= length ctors
    //         then throwResError $ text "Definition of measure" <+> text measureName <+> text "must include one case per constructor of" <+> text dtName
    //         else do
    //           freshConsts <- mapM (uncurry freshId) args
    //           let constSubst = zip (fmap fst args) freshConsts
    //           defs' <- mapM (resolveMeasureDef ctors constSubst) defCases
    //           mapM_ (\(MeasureCase _ _ impl) -> checkMeasureCase measureName args impl) defCases
    //           sch <- uses environment ((Map.! measureName) . allSymbols)
    //           sch' <- resolveSchema sch
    //           environment %= addPolyConstant measureName sch'
    //           defCases' <- mapM (\(MeasureCase n args body) -> do
    //             body' <- resolveMeasureFormula body
    //             return (MeasureCase n args body')) defCases
    //           let args' = fmap (\(Var s x) -> (x, s)) freshConsts
    //           environment %= addMeasure measureName (MeasureDef inSort outSort defs' args' post')
    //           checkingGoals %= (++ [(measureName, (impl (MeasureDef inSort outSort defCases' args post'), pos))])
    //     _ -> throwResError $ text "Last input of measure" <+> text measureName <+> text "must be a datatype"
    //   where
    //     impl def = normalizeProgram $ measureProg measureName def
    //     resolveMeasureDef allCtors cSub (MeasureCase ctorName binders body) =
    //       if ctorName `notElem` allCtors
    //         then throwResError $ text "Not in scope: data constructor" <+> text ctorName <+> text "used in definition of measure" <+> text measureName
    //         else do
    //           consSch <- uses environment ((Map.! ctorName) . allSymbols)
    //           let consT = toMonotype consSch
    //           let n = arity consT
    //           if n /= length binders
    //             then throwResError $ text "Data constructor" <+> text ctorName <+> text "expected" <+> pretty n <+> text "binders and got" <+> pretty (length binders) <+> text "in definition of measure" <+> text measureName
    //             else do
    //               let ctorParams = allArgs consT
    //               let subst = Map.fromList $ cSub ++ zip binders ctorParams
    //               let fml = Pred AnyS measureName (map snd cSub ++ [Var AnyS valueVarName]) |=| substitute subst body
    //               fml' <- withLocalEnv $ do
    //                 environment  . boundTypeVars .= boundVarsOf consSch
    //                 environment %= addAllVariables ctorParams
    //                 environment %= addAllVariables (fmap snd cSub)
    //                 resolveTypeRefinement (toSort $ baseTypeOf $ lastType consT) fml
    //               return $ MeasureCase ctorName (map varName ctorParams) fml'
    // resolveSignatures (SynthesisGoal name impl) = do
    //   resolveHole impl
    //   return ()
    // resolveSignatures _ = return ()

    pub fn resolve_signatures(&mut self, decl: BareDeclaration) -> Result<(), ErrorMessage> {
        match decl {
            BareDeclaration::FuncDecl(name, _) => {
                let sch = self.environment.all_symbols().get(&name).cloned().unwrap();
                let sch = self.resolve_schema(sch)?;
                self.environment.add_poly_constant(name, sch);
            }
            BareDeclaration::DataDecl(dt_name, t_params, p_params, ctors) => {
                for ctor in ctors {
                    let sch = self
                        .environment
                        .all_symbols()
                        .get(ctor.name())
                        .cloned()
                        .unwrap();
                    let sch = self.resolve_schema(sch)?;

                    let nominal_type = RType::Scalar(
                        BaseType::Datatype(
                            dt_name.clone(),
                            t_params
                                .iter()
                                .cloned()
                                .map(TypeSkeleton::vart_all)
                                .collect(),
                            p_params
                                .iter()
                                .cloned()
                                .map(|(p, _)| self.nominal_pred_app(p))
                                .collect(),
                        ),
                        Formula::TRUE,
                    );
                    let return_type = sch.to_monotype().last_type();

                    if nominal_type != *return_type {
                        return Err(self.throw_res_error(format!(
                            "Constructor {} must return type {nominal_type}, got {return_type}",
                            ctor.name()
                        )));
                    }

                    let nominal_sort = nominal_type.base_type().to_sort();
                    let sch = sch.clone().add_refinement_to_last_sch(
                        Formula::Var(nominal_sort.clone(), VALUE_VAR_NAME).eq(Formula::Cons(
                            nominal_sort,
                            ctor.name().clone(),
                            sch.to_monotype().clone().all_args(),
                        )),
                    );

                    self.environment.add_poly_constant(ctor.name().clone(), sch);
                }
            }
            BareDeclaration::MeasureDecl(measure_name, _, _, post, def_cases, args, _) => {
                let sorts = self
                    .environment
                    .global_predicates
                    .get(&measure_name)
                    .cloned()
                    .unwrap();
                let (out_sort, m_args) = sorts.split_first().unwrap();
                match m_args.last().unwrap() {
                    Sort::Data(dt_name, s_args) => {
                        let datatype = self.environment.datatypes.get(dt_name).cloned().unwrap();
                        let post = self.resolve_type_refinement(out_sort.clone(), post)?;

                        let ctors = datatype.constructors.clone();
                        let constant_args =
                            args.iter().map(|(n, s)| Formula::Var(s.clone(), n.clone()));

                        if def_cases.len() != ctors.len() {
                            return Err(self.throw_res_error(format!(
                                "Definition of measure {measure_name} must include one case per constructor of {dt_name}",
                            )));
                        }

                        let fresh_consts = args
                            .iter()
                            .map(|(n, s)| self.fresh_id(n.clone(), s.clone()))
                            .collect::<Vec<_>>();
                        let const_subst = args
                            .iter()
                            .map(|(n, _)| n.clone())
                            .zip(fresh_consts.clone())
                            .collect::<Vec<_>>();

                        for def_case in &def_cases {
                            self.check_measure_case(&measure_name, &args, def_case.2.clone())?;
                        }

                        let sch = self
                            .environment
                            .all_symbols()
                            .get(&measure_name)
                            .cloned()
                            .unwrap();
                        let sch = self.resolve_schema(sch)?;

                        self.environment
                            .add_poly_constant(measure_name.clone(), sch);

                        let def_cases = def_cases
                            .iter()
                            .cloned()
                            .map(|MeasureCase(ctor_name, binders, body)| {
                                let body = self.resolve_measure_formula(body)?;
                                Ok(MeasureCase(ctor_name, binders, body))
                            })
                            .collect::<Result<Vec<_>, _>>()?;

                        let args = fresh_consts
                            .iter()
                            .map(|f| (f.var_name().clone(), f.sort().clone()))
                            .collect::<Vec<_>>();

                        let definitions = def_cases
                            .iter()
                            .cloned()
                            .map(|def_case| {
                                self.resolve_measure_def(
                                    &ctors,
                                    &const_subst,
                                    def_case,
                                    &measure_name,
                                )
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                        self.environment.add_measure(
                            measure_name.clone(),
                            MeasureDef {
                                in_sort: out_sort.clone(),
                                out_sort: out_sort.clone(),
                                definitions,
                                constant_args: args,
                                postcondition: post.clone(),
                            },
                        );
                    }
                    _ => {
                        return Err(self.throw_res_error(format!(
                            "Last input of measure {measure_name} must be a datatype",
                        )));
                    }
                }
            }
            BareDeclaration::SynthesisGoal(_name, impl_) => {
                self.resolve_hole(impl_.into())?;
            }
            _ => {}
        }

        Ok(())
    }

    fn resolve_measure_def(
        &mut self,
        all_ctors: &Vec<Id>,
        c_sub: &Vec<(Id, Formula)>,
        MeasureCase(ctor_name, binders, body): MeasureCase,
        measure_name: &Id,
    ) -> Result<MeasureCase, ErrorMessage> {
        if !all_ctors.contains(&ctor_name) {
            return Err(self.throw_res_error(format!(
                "Not in scope: data constructor {ctor_name} used in definition of measure {measure_name}"
            )));
        }

        let cons_sch = self
            .environment
            .all_symbols()
            .get(&ctor_name)
            .cloned()
            .unwrap();
        let cons_t = cons_sch.to_monotype();
        let n = cons_t.arity();

        if n != binders.len() {
            return Err(self.throw_res_error(format!(
                "Data constructor {ctor_name} expected {n} binders and got {} in definition of measure {measure_name}", binders.len()
            )));
        }

        let ctor_params = cons_t.clone().all_args();
        let subst = Substitution::new(
            c_sub
                .iter()
                .cloned()
                .chain(binders.into_iter().zip(ctor_params.clone()))
                .collect(),
        );
        let fml = Formula::Pred(
            Sort::Any,
            measure_name.clone(),
            c_sub
                .iter()
                .map(|(_, s)| s)
                .cloned()
                .chain(iter::once(Formula::Var(Sort::Any, VALUE_VAR_NAME)))
                .collect(),
        )
        .eq(body.substitute(&subst));

        let fml = {
            self.environment.bound_type_vars = cons_sch.bound_vars().into_iter().cloned().collect();
            self.add_all_variables(&ctor_params);
            self.add_all_variables(&c_sub.iter().map(|(_, s)| s).cloned().collect());
            self.resolve_type_refinement(cons_t.last_type().base_type().to_sort(), fml)?
        };

        Ok(MeasureCase(
            ctor_name,
            ctor_params
                .into_iter()
                .map(|f| f.var_name().clone())
                .collect(),
            fml,
        ))
    }

    // -- 'checkMeasureCase' @measure constArgs mCase@ : ensure that measure @name@ is called recursively with the same argumenst @constArgs@
    // checkMeasureCase :: Id -> [(Id, Sort)] -> Formula -> Resolver ()
    // checkMeasureCase measure [] _ = return ()
    // checkMeasureCase measure constArgs (Unary _ f) = checkMeasureCase measure constArgs f
    // checkMeasureCase measure constArgs (Binary _ f g) = do
    //   checkMeasureCase measure constArgs f
    //   checkMeasureCase measure constArgs g
    // checkMeasureCase measure constArgs (Ite f g h) = do
    //   checkMeasureCase measure constArgs f
    //   checkMeasureCase measure constArgs g
    //   checkMeasureCase measure constArgs h
    // checkMeasureCase measure constArgs (Cons _ _ fs) =
    //   mapM_ (checkMeasureCase measure constArgs) fs
    // checkMeasureCase measure constArgs p@(Pred s x args) =
    //   if x == measure
    //     then do
    //       let args' = take numArgs args
    //       let cArgs' = fmap (\(x, _) -> Var AnyS x) constArgs
    //       when (args' /= cArgs') $ throwResError $ text "Constant arguments to measure" <+> text measure <+> text "must not change in recursive call" <+> pretty p
    //     else mapM_ (checkMeasureCase measure constArgs) args
    //   where
    //     numArgs = length constArgs
    // checkMeasureCase _ _ _ = return ()

    /// Ensure that measure `name` is called recursively with the same arguments `const_args`
    pub fn check_measure_case(
        &mut self,
        measure: &Id,
        const_args: &Vec<(Id, Sort)>,
        fml: Formula,
    ) -> Result<(), ErrorMessage> {
        match fml {
            Formula::Unary(_, f) => self.check_measure_case(measure, const_args, *f)?,
            Formula::Binary(_, f, g) => {
                self.check_measure_case(measure, const_args, *f)?;
                self.check_measure_case(measure, const_args, *g)?;
            }
            Formula::Ite(f, g, h) => {
                self.check_measure_case(measure, const_args, *f)?;
                self.check_measure_case(measure, const_args, *g)?;
                self.check_measure_case(measure, const_args, *h)?;
            }
            Formula::Cons(_, _, fs) => {
                for f in fs {
                    self.check_measure_case(measure, const_args, f)?;
                }
            }
            Formula::Pred(s, x, args) => {
                if x == *measure {
                    let args = args.into_iter().take(const_args.len()).collect::<Vec<_>>();
                    let c_args = const_args
                        .iter()
                        .map(|(x, _)| Formula::Var(Sort::Any, x.clone()))
                        .collect::<Vec<_>>();

                    if args != c_args {
                        self.throw_res_error(format!(
                            "Constant arguments to measure {measure} must not change in recursive call {}", Formula::Pred(s, x, args)
                        ));
                    }
                } else {
                    for f in args {
                        self.check_measure_case(measure, const_args, f)?;
                    }
                }
            }
            _ => {}
        }

        Ok(())
    }

    // resolveHole :: Program RType -> Resolver RType
    // resolveHole Program{content = (PApp p1 p2)} = do
    //   resolveHole p1
    //   resolveHole p2
    // resolveHole Program{content = (PFun _ p)} = resolveHole p
    // resolveHole Program{content = (PIf p1 p2 p3)} = do
    //   resolveHole p1
    //   resolveHole p2
    //   resolveHole p3
    // resolveHole Program{content = (PMatch p _)} = resolveHole p
    // resolveHole Program{content = (PFix _ p)} = resolveHole p
    // resolveHole Program{content = (PLet _ p1 p2)} = do
    //   resolveHole p1
    //   resolveHole p2
    // -- Resolve type if hole, symbol, or err:
    // resolveHole Program{content = _, typeOf = t} = resolveType t

    pub fn resolve_hole(&mut self, p: Program<RType>) -> Result<(), ErrorMessage> {
        match *p.content {
            BareProgram::App(p1, p2) => {
                self.resolve_hole(p1)?;
                self.resolve_hole(p2)?;
            }
            BareProgram::Fun(_, p) => {
                self.resolve_hole(p)?;
            }
            BareProgram::If(p1, p2, p3) => {
                self.resolve_hole(p1)?;
                self.resolve_hole(p2)?;
                self.resolve_hole(p3)?;
            }
            BareProgram::Match(p, _) => {
                self.resolve_hole(p)?;
            }
            BareProgram::Fix(_, p) => {
                self.resolve_hole(p)?;
            }
            BareProgram::Let(_, p1, p2) => {
                self.resolve_hole(p1)?;
                self.resolve_hole(p2)?;
            }
            _ => {
                self.resolve_type(p.type_of)?;
            }
        }

        Ok(())
    }

    // resolveSchema :: RSchema -> Resolver RSchema
    // resolveSchema sch = do
    //   let tvs = Set.toList $ typeVarsOf (toMonotype sch)
    //   sch' <- withLocalEnv $ do
    //     environment . boundTypeVars %= (tvs ++)
    //     resolveSchema' sch
    //   return $ Foldable.foldl (flip ForallT) sch' tvs
    //   where
    //     resolveSchema' (ForallP sig@(PredSig predName argSorts resSort) sch) = do
    //       ifM (elem predName <$> uses (environment . boundPredicates) (map predSigName))
    //         (throwResError $ text "Duplicate predicate variables" <+> text predName)
    //         (return ())
    //       mapM_ resolveSort argSorts
    //       when (resSort /= BoolS) $
    //         throwResError (text "Bound predicate variable" <+> text predName <+> text "must return Bool")
    //       sch' <- withLocalEnv $ do
    //         environment %= addBoundPredicate sig
    //         resolveSchema' sch
    //       let extraTypeVars = (Set.unions (map typeVarsOfSort argSorts)) Set.\\ typeVarsOf (toMonotype sch')
    //       unless (Set.null extraTypeVars) $
    //         (throwResError $ text "Unbound variables" <+> (commaSep $ map pretty $ Set.toList extraTypeVars) <+> text "in sort of bound predicate" <+> text predName)
    //       return $ ForallP sig sch'
    //     resolveSchema' (Monotype t) = Monotype <$> resolveType t

    pub fn resolve_schema(&mut self, sch: RSchema) -> Result<RSchema, ErrorMessage> {
        let tvs = sch.to_monotype().type_vars();
        let sch = {
            self.environment.bound_type_vars.extend(tvs.iter().cloned());

            self.resolve_schema_(sch)?
        };

        let sch = tvs
            .into_iter()
            .rev()
            .fold(sch, |sch, tv| RSchema::ForAllType(tv, Box::new(sch)));

        Ok(sch)
    }

    fn resolve_schema_(&mut self, sch: RSchema) -> Result<RSchema, ErrorMessage> {
        match sch {
            RSchema::ForAllPredicate(sig, sch) => {
                if self
                    .environment
                    .bound_predicates
                    .iter()
                    .any(|p| p.name == sig.name)
                {
                    return Err(
                        self.throw_res_error(format!("Duplicate predicate variables {}", sig.name))
                    );
                }

                for s in &sig.arg_sorts {
                    self.resolve_sort(s)?;
                }

                if sig.res_sort != Sort::Bool {
                    return Err(self.throw_res_error(format!(
                        "Bound predicate variable {} must return Bool",
                        sig.name
                    )));
                }

                let sch = {
                    self.environment.add_bound_predicate(sig.clone());
                    self.resolve_schema_(*sch)?
                };

                let extra_type_vars = sig
                    .arg_sorts
                    .iter()
                    .flat_map(|s| s.type_vars())
                    .collect::<BTreeSet<_>>()
                    .difference(&sch.to_monotype().type_vars())
                    .cloned()
                    .collect::<HashSet<_>>();

                if !extra_type_vars.is_empty() {
                    return Err(self.throw_res_error(format!(
                        "Unbound variables {} in sort of bound predicate {}",
                        extra_type_vars.iter().format(", "),
                        sig.name
                    )));
                }

                Ok(RSchema::ForAllPredicate(sig, Box::new(sch)))
            }
            RSchema::Monotype(t) => Ok(RSchema::Monotype(self.resolve_type(t)?)),
            _ => unreachable!(),
        }
    }

    // resolveType :: RType -> Resolver RType
    // resolveType s@(ScalarT (DatatypeT name tArgs pArgs) fml) = do
    //   ds <- use $ environment . datatypes
    //   case Map.lookup name ds of
    //     Nothing -> do
    //       t' <- substituteTypeSynonym name tArgs >>= resolveType
    //       fml' <- resolveTypeRefinement (toSort $ baseTypeOf t') fml
    //       return $ addRefinement t' fml'
    //     Just (DatatypeDef tParams pParams _ _ _) -> do
    //       when (length tArgs /= length tParams) $
    //         throwResError $ text "Datatype" <+> text name <+> text "expected" <+> pretty (length tParams) <+> text "type arguments and got" <+> pretty (length tArgs) <+> pretty tParams
    //       when (length pArgs /= length pParams) $
    //         throwResError $ text "Datatype" <+> text name <+> text "expected" <+> pretty (length pParams) <+> text "predicate arguments and got" <+> pretty (length pArgs)
    //       -- Resolve type arguments:
    //       tArgs' <- mapM resolveType tArgs
    //       -- Resolve predicate arguments:
    //       let subst = noncaptureSortSubst tParams (map (toSort . baseTypeOf) tArgs')
    //       pArgs' <- zipWithM (resolvePredArg subst) pParams pArgs
    //       let baseT' = DatatypeT name tArgs' pArgs'
    //       -- Resolve refinementL
    //       fml' <- resolveTypeRefinement (toSort baseT') fml
    //       return $ ScalarT baseT' fml'
    //   where
    //     resolvePredArg :: (Sort -> Sort) -> PredSig -> Formula -> Resolver Formula
    //     resolvePredArg subst (PredSig _ argSorts BoolS) fml = withLocalEnv $ do
    //       let argSorts' = map subst argSorts
    //       let vars = zipWith Var argSorts' deBrujns
    //       environment %= addAllVariables vars
    //       case fml of
    //         Pred _ p [] -> resolveTypeRefinement AnyS (Pred BoolS p vars)
    //         _ -> resolveTypeRefinement AnyS fml

    // resolveType (ScalarT baseT fml) = ScalarT baseT <$> resolveTypeRefinement (toSort baseT) fml

    // resolveType (FunctionT x tArg tRes) =
    //   if x == valueVarName
    //     then throwResError $ text valueVarName <+> text "is a reserved variable name"
    //     else if x == dontCare
    //       then error $ unwords ["resolveType: blank in function type", show (FunctionT x tArg tRes)] -- Should never happen
    //       else do
    //         tArg' <- resolveType tArg
    //         tRes' <- withLocalEnv $ do
    //           unless (isFunctionType tArg') (environment %= addVariable x tArg')
    //           resolveType tRes
    //         return $ FunctionT x tArg' tRes'

    // resolveType AnyT = return AnyT

    pub fn resolve_type(&mut self, t: RType) -> Result<RType, ErrorMessage> {
        match t {
            RType::Scalar(BaseType::Datatype(name, t_args, p_args), fml) => {
                match self.environment.datatypes.get(&name).cloned() {
                    None => {
                        let t = self.substitute_type_synonym(name, t_args)?;
                        let t = self.resolve_type(t)?;
                        let fml = self.resolve_type_refinement(t.base_type().to_sort(), fml)?;

                        Ok(t.add_refinement(fml))
                    }
                    Some(DatatypeDef {
                        type_params,
                        pred_params,
                        ..
                    }) => {
                        if t_args.len() != type_params.len() {
                            return Err(self.throw_res_error(format!(
                                "Datatype {name} expected {} type arguments and got {} {}",
                                type_params.len(),
                                t_args.len(),
                                type_params.iter().format(", ")
                            )));
                        }

                        if p_args.len() != pred_params.len() {
                            return Err(self.throw_res_error(format!(
                                "Datatype {name} expected {} predicate arguments and got {}",
                                pred_params.len(),
                                p_args.len()
                            )));
                        }

                        let t_args = t_args
                            .into_iter()
                            .map(|t| self.resolve_type(t))
                            .collect::<Result<Vec<_>, _>>()?;

                        let subst = |s: Sort| {
                            noncapture_sort_subst(
                                type_params.clone(),
                                t_args.iter().map(|t| t.base_type().to_sort()).collect(),
                                s,
                            )
                        };

                        let p_args = pred_params
                            .iter()
                            .zip(p_args)
                            .map(|(ps, f)| self.resolve_pred_arg(&subst, ps, f))
                            .collect::<Result<Vec<_>, _>>()?;

                        let base_t = BaseType::Datatype(name, t_args, p_args);
                        let fml = self.resolve_type_refinement(base_t.to_sort(), fml)?;

                        Ok(RType::Scalar(base_t, fml))
                    }
                }
            }
            RType::Scalar(base_t, fml) => {
                let fml = self.resolve_type_refinement(base_t.to_sort(), fml)?;

                Ok(RType::Scalar(base_t, fml))
            }
            RType::Function { x, t_arg, t_res } => {
                if x == VALUE_VAR_NAME {
                    return Err(self
                        .throw_res_error(format!("{VALUE_VAR_NAME} is a reserved variable name")));
                }

                if x.as_str() == "_" {
                    return Err(self.throw_res_error(format!(
                        "resolveType: blank in function type {}",
                        RType::Function { x, t_arg, t_res }
                    )));
                }

                let t_arg = self.resolve_type(*t_arg)?;
                let t_res = {
                    if !t_arg.is_function_type() {
                        self.environment.add_variable(x.clone(), t_arg.clone());
                    }

                    self.resolve_type(*t_res)?
                };

                Ok(RType::Function {
                    x,
                    t_arg: Box::new(t_arg),
                    t_res: Box::new(t_res),
                })
            }
            RType::Any => Ok(RType::Any),
            _ => unreachable!(),
        }
    }

    fn resolve_pred_arg(
        &mut self,
        subst: impl Fn(Sort) -> Sort,
        pred_sig: &PredSig,
        fml: Formula,
    ) -> Result<Formula, ErrorMessage> {
        match pred_sig {
            PredSig {
                name: _,
                arg_sorts,
                res_sort,
            } if res_sort == &Sort::Bool => {
                let arg_sorts = arg_sorts
                    .iter()
                    .map(|s| subst(s.clone()))
                    .collect::<Vec<_>>();
                let vars = de_brujns(&arg_sorts)
                    .into_iter()
                    .zip(arg_sorts)
                    .map(|(db, s)| Formula::Var(s, db))
                    .collect::<Vec<_>>();

                self.add_all_variables(&vars);

                match fml {
                    Formula::Pred(_, p, args) if args.is_empty() => {
                        self.resolve_type_refinement(Sort::Any, Formula::Pred(Sort::Bool, p, vars))
                    }
                    _ => self.resolve_type_refinement(Sort::Any, fml),
                }
            }
            _ => unreachable!(),
        }
    }

    // -- | Check that sort has no unknown datatypes
    // resolveSort :: Sort -> Resolver ()
    // resolveSort (SetS elSort) = resolveSort elSort
    // resolveSort s@(DataS name sArgs) = do
    //   ds <- use $ environment . datatypes
    //   case Map.lookup name ds of
    //     Nothing -> throwResError $ text "Datatype" <+> text name <+> text "is undefined in sort" <+> pretty s
    //     Just (DatatypeDef tParams _ _ _ _) -> do
    //       let n = length tParams
    //       when (length sArgs /= n) $ throwResError $ text "Datatype" <+> text name <+> text "expected" <+> pretty n <+> text "type arguments and got" <+> pretty (length sArgs)
    //       mapM_ resolveSort sArgs
    // resolveSort s = return ()

    /// Check that sort has no unknown datatypes
    pub fn resolve_sort(&self, sort: &Sort) -> Result<(), ErrorMessage> {
        match sort {
            Sort::Set(el_sort) => self.resolve_sort(el_sort),
            Sort::Data(name, s_args) => {
                let ds = &self.environment.datatypes;
                let DatatypeDef { type_params, .. } = ds.get(name).ok_or_else(|| {
                    self.throw_res_error(format!("Datatype {name} is undefined in sort {sort}"))
                })?;

                let n = type_params.len();
                if s_args.len() != n {
                    return Err(self.throw_res_error(format!(
                        "Datatype {name} expected {n} type arguments and got {}",
                        s_args.len()
                    )));
                }

                for s in s_args {
                    self.resolve_sort(s)?;
                }

                Ok(())
            }
            _ => Ok(()),
        }
    }

    // -- | 'resolveTypeRefinement' @valueSort fml@ : resolve @fml@ as a refinement with _v of sort @valueSort@;
    // -- when @valueSort@ is @AnyS@, _v must not occur
    // resolveTypeRefinement :: Sort -> Formula -> Resolver Formula
    // resolveTypeRefinement _ (BoolLit True) = return $ BoolLit True -- Special case to allow undefined value sort for function types
    // resolveTypeRefinement valueSort fml = do
    //   fml' <- withLocalEnv $ do -- Resolve fml with _v : valueSort
    //     case valueSort of
    //       AnyS -> return ()
    //       _ -> environment %= addVariable valueVarName (fromSort valueSort)
    //     resolveFormula fml
    //   enforceSame (sortOf fml') BoolS -- Refinements must have Boolean sort
    //   sortAssignment <- solveSortConstraints -- Solve sort constraints and substitute
    //   let fml'' = sortSubstituteFml sortAssignment fml'

    //   boundTvs <- use $ environment . boundTypeVars
    //   let freeTvs = typeVarsOfSort (sortOf fml'') Set.\\ (Set.fromList boundTvs) -- Remaining free type variables
    //   let resolvedFml = if Set.null freeTvs then fml'' else sortSubstituteFml (constMap freeTvs IntS) fml''

    //   -- boundPreds <- uses (environment . boundPredicates) (Set.fromList . map predSigName)
    //   -- let invalidPreds = negPreds resolvedFml `Set.intersection` boundPreds
    //   -- when (not $ Set.null invalidPreds) $
    //     -- throwResError $ text "Bound predicate(s)" <+> commaSep (map text $ Set.toList invalidPreds)<+> text "occur negatively in a refinement" <+> pretty resolvedFml
    //   return resolvedFml

    /// Resolve `fml` as a refinement with _v of sort `valueSort`;
    /// when `valueSort` is `Any`, _v must not occur
    pub fn resolve_type_refinement(
        &mut self,
        value_sort: Sort,
        fml: Formula,
    ) -> Result<Formula, ErrorMessage> {
        if fml == Formula::BoolLit(true) {
            return Ok(fml);
        }

        match value_sort {
            Sort::Any => {}
            _ => self
                .environment
                .add_variable(VALUE_VAR_NAME, RType::from_sort(&value_sort)),
        }

        let fml = self.resolve_formula(fml)?;

        self.enforce_same(fml.sort(), Sort::Bool);
        let sort_assignment = self.solve_sort_constraints()?;
        let fml = sort_assignment.sort_substitute_fml(fml);

        let free_tvs = fml
            .sort()
            .type_vars()
            .difference(&self.environment.bound_type_vars)
            .cloned()
            .collect::<HashSet<_>>();
        let resolved_fml = if free_tvs.is_empty() {
            fml
        } else {
            let subst =
                SortSubstitution::new(free_tvs.into_iter().map(|tv| (tv, Sort::Int)).collect());

            subst.sort_substitute_fml(fml)
        };

        Ok(resolved_fml)
    }

    // -- Partially resolve formula describing measure case (just replace inline predicates)
    // resolveMeasureFormula :: Formula -> Resolver Formula
    // resolveMeasureFormula (SetLit s fs) = do
    //   fs' <- mapM resolveMeasureFormula fs
    //   return $ SetLit s fs'
    // resolveMeasureFormula (Unary op f) = do
    //   f' <- resolveMeasureFormula f
    //   return $ Unary op f'
    // resolveMeasureFormula (Binary op f1 f2) = do
    //   f1' <- resolveMeasureFormula f1
    //   f2' <- resolveMeasureFormula f2
    //   return $ Binary op f1' f2'
    // resolveMeasureFormula (Ite f1 f2 f3) = do
    //   f1' <- resolveMeasureFormula f1
    //   f2' <- resolveMeasureFormula f2
    //   f3' <- resolveMeasureFormula f3
    //   return $ Ite f1' f2' f3'
    // resolveMeasureFormula (Pred s name f) = do
    //   inlineMb <- uses inlines (Map.lookup name)
    //   case inlineMb of
    //     Just (args, body) -> resolveMeasureFormula (substitute (Map.fromList $ zip args f) body)
    //     Nothing -> do
    //       f' <- mapM resolveMeasureFormula f
    //       return $ Pred s name f'
    // resolveMeasureFormula (Cons s x f) = do
    //   f' <- mapM resolveMeasureFormula f
    //   return $ Cons s x f'
    // resolveMeasureFormula (All f1 f2) = do
    //   f1' <- resolveMeasureFormula f1
    //   f2' <- resolveMeasureFormula f2
    //   return $ All f1' f2'
    // resolveMeasureFormula f = return f

    /// Partially resolve formula describing measure case (just replace inline predicates)
    pub fn resolve_measure_formula(&self, fml: Formula) -> Result<Formula, ErrorMessage> {
        match fml {
            Formula::SetLit(s, fs) => {
                let fs = fs
                    .into_iter()
                    .map(|f| self.resolve_measure_formula(f))
                    .collect::<Result<Vec<_>, _>>()?;

                Ok(Formula::SetLit(s, fs))
            }
            Formula::Unary(op, f) => {
                let f = self.resolve_measure_formula(*f)?;

                Ok(Formula::Unary(op, Box::new(f)))
            }
            Formula::Binary(op, f1, f2) => {
                let f1 = self.resolve_measure_formula(*f1)?;
                let f2 = self.resolve_measure_formula(*f2)?;

                Ok(Formula::Binary(op, Box::new(f1), Box::new(f2)))
            }
            Formula::Ite(f1, f2, f3) => {
                let f1 = self.resolve_measure_formula(*f1)?;
                let f2 = self.resolve_measure_formula(*f2)?;
                let f3 = self.resolve_measure_formula(*f3)?;

                Ok(Formula::Ite(Box::new(f1), Box::new(f2), Box::new(f3)))
            }
            Formula::Pred(s, name, f) => {
                if let Some((args, body)) = self.inlines.get(&name) {
                    let subst =
                        Substitution::new(args.iter().cloned().zip(f.into_iter()).collect());

                    self.resolve_measure_formula(body.clone().substitute(&subst))
                } else {
                    let f = f
                        .into_iter()
                        .map(|f| self.resolve_measure_formula(f))
                        .collect::<Result<Vec<_>, _>>()?;

                    Ok(Formula::Pred(s, name, f))
                }
            }
            Formula::Cons(s, x, f) => {
                let f = f
                    .into_iter()
                    .map(|f| self.resolve_measure_formula(f))
                    .collect::<Result<Vec<_>, _>>()?;

                Ok(Formula::Cons(s, x, f))
            }
            Formula::All(f1, f2) => {
                let f1 = self.resolve_measure_formula(*f1)?;
                let f2 = self.resolve_measure_formula(*f2)?;

                Ok(Formula::All(Box::new(f1), Box::new(f2)))
            }
            f => Ok(f),
        }
    }

    // -- | 'resolveTypeRefinement' @valueSort fml@ : resolve @fml@ as a refinement with _v of sort @valueSort@;
    // -- when @valueSort@ is @AnyS@, _v must not occur
    // resolveTypeRefinement :: Sort -> Formula -> Resolver Formula
    // resolveTypeRefinement _ (BoolLit True) = return $ BoolLit True -- Special case to allow undefined value sort for function types
    // resolveTypeRefinement valueSort fml = do
    //   fml' <- withLocalEnv $ do -- Resolve fml with _v : valueSort
    //     case valueSort of
    //       AnyS -> return ()
    //       _ -> environment %= addVariable valueVarName (fromSort valueSort)
    //     resolveFormula fml
    //   enforceSame (sortOf fml') BoolS -- Refinements must have Boolean sort
    //   sortAssignment <- solveSortConstraints -- Solve sort constraints and substitute
    //   let fml'' = sortSubstituteFml sortAssignment fml'

    //   boundTvs <- use $ environment . boundTypeVars
    //   let freeTvs = typeVarsOfSort (sortOf fml'') Set.\\ (Set.fromList boundTvs) -- Remaining free type variables
    //   let resolvedFml = if Set.null freeTvs then fml'' else sortSubstituteFml (constMap freeTvs IntS) fml''

    //   -- boundPreds <- uses (environment . boundPredicates) (Set.fromList . map predSigName)
    //   -- let invalidPreds = negPreds resolvedFml `Set.intersection` boundPreds
    //   -- when (not $ Set.null invalidPreds) $
    //     -- throwResError $ text "Bound predicate(s)" <+> commaSep (map text $ Set.toList invalidPreds)<+> text "occur negatively in a refinement" <+> pretty resolvedFml
    //   return resolvedFml

    // pub fn resolve_type_refinement(
    //     &mut self,
    //     value_sort: Sort,
    //     fml: Formula,
    // ) -> Result<Formula, ErrorMessage> {
    //     if fml == Formula::BoolLit(true) {
    //         return Ok(fml);
    //     }

    //     match value_sort {
    //         Sort::Any => {}
    //         _ => self
    //             .environment
    //             .add_variable(VALUE_VAR_NAME, RType::from_sort(value_sort)),
    //     }

    //     let fml = self.resolve_formula(fml)?;
    // }

    // resolveFormula :: Formula -> Resolver Formula
    // resolveFormula (Var _ x) = do
    //   env <- use environment
    //   case Map.lookup x (symbolsOfArity 0 env) of
    //     Just sch ->
    //       case sch of
    //         Monotype (ScalarT baseType _) -> do
    //           let s' = toSort baseType
    //           return $ Var s' x
    //         _ -> error $ unwords ["resolveFormula: encountered non-scalar variable", x, "in a formula"]
    //     Nothing -> resolveFormula (Pred AnyS x []) `catchError` -- Maybe it's a zero-argument predicate?
    //                const (throwResError $ text "Variable" <+> text x <+> text "is not in scope")      -- but if not, throw this error to avoid confusion

    // resolveFormula (SetLit _ elems) = do
    //   elemSort <- freshSort
    //   elems' <- mapM resolveFormula elems
    //   zipWithM_ enforceSame (map sortOf elems') (repeat elemSort)
    //   return $ SetLit elemSort elems'

    // resolveFormula (Unary op fml) = fmap (Unary op) $ do
    //   fml' <- resolveFormula fml
    //   enforceSame (sortOf fml') (operandSort op)
    //   return fml'
    //   where
    //     operandSort Not = BoolS
    //     operandSort Neg = IntS

    // resolveFormula (Binary op l r) = do
    //   l' <- resolveFormula l
    //   r' <- resolveFormula r
    //   op' <- addConstraints op (sortOf l') (sortOf r')
    //   return $ Binary op' l' r'
    //   where
    //     addConstraints op sl sr
    //       | op == Eq  || op == Neq
    //         = enforceSame sl sr >> return op
    //       | op == And || op == Or || op == Implies || op == Iff
    //         = enforceSame sl BoolS >> enforceSame sr BoolS >> return op
    //       | op == Member
    //         = enforceSame (SetS sl) sr >> return op
    //       | op == Union || op == Intersect || op == Diff || op == Subset
    //         = do
    //             elemSort <- freshSort
    //             enforceSame sl (SetS elemSort)
    //             enforceSame sr (SetS elemSort)
    //             return op
    //       | op == Times || op == Plus || op == Minus
    //         = if isSetS sl
    //             then do
    //               elemSort <- freshSort
    //               enforceSame sl (SetS elemSort)
    //               enforceSame sr (SetS elemSort)
    //               return $ toSetOp op
    //             else enforceSame sl IntS >> enforceSame sr IntS >> return op
    //       | op == Le
    //         = if isSetS sl
    //             then do
    //               elemSort <- freshSort
    //               enforceSame sl (SetS elemSort)
    //               enforceSame sr (SetS elemSort)
    //               return $ toSetOp op
    //             else enforceSame sl sr >> sortConstraints %= (++ [IsOrd sl]) >> return op
    //       | op == Lt || op == Gt || op == Ge
    //         = enforceSame sl sr >> sortConstraints %= (++ [IsOrd sl]) >> return op

    //     toSetOp Times = Intersect
    //     toSetOp Plus = Union
    //     toSetOp Minus = Diff
    //     toSetOp Le = Subset

    // resolveFormula (Ite cond l r) = do
    //   cond' <- resolveFormula cond
    //   l' <- resolveFormula l
    //   r' <- resolveFormula r
    //   enforceSame (sortOf cond') BoolS
    //   enforceSame (sortOf l') (sortOf r')
    //   return $ Ite cond' l' r'

    // resolveFormula (Pred _ name argFmls) = do
    //   inlineMb <- uses inlines (Map.lookup name)
    //   case inlineMb of
    //     Just (args, body) -> resolveFormula (substitute (Map.fromList $ zip args argFmls) body)
    //     Nothing -> do
    //       ps <- uses environment allPredicates
    //       sorts <- case Map.lookup name ps of
    //                   Nothing -> throwResError $ text "Predicate or measure" <+> text name <+> text "is undefined"
    //                   Just sorts -> ifM (Map.member name <$> use (environment . globalPredicates))
    //                                   (instantiate sorts) -- if global, treat type variables as free
    //                                   (return sorts) -- otherwise, treat type variables as bound
    //       let (resSort : argSorts) = sorts
    //       if length argFmls /= length argSorts
    //           then throwResError $ text "Expected" <+> pretty (length argSorts) <+> text "arguments for predicate or measure" <+> text name <+> text "and got" <+> pretty (length argFmls)
    //           else do
    //             argFmls' <- mapM resolveFormula argFmls
    //             zipWithM_ enforceSame (map sortOf argFmls') argSorts
    //             return $ Pred resSort name argFmls'

    // resolveFormula (Cons _ name argFmls) = do
    //   syms <- uses environment allSymbols
    //   case Map.lookup name syms of
    //     Nothing -> throwResError $ text "Data constructor" <+> text name <+> text "is undefined"
    //     Just consSch -> do
    //       let consT = toMonotype consSch
    //       sorts <- instantiate $ map (toSort . baseTypeOf) $ lastType consT : allArgTypes consT
    //       let (resSort : argSorts) = sorts
    //       if length argSorts /= length argFmls
    //         then throwResError $ text "Constructor" <+> text name <+> text "expected" <+> pretty (length argSorts) <+> text "arguments and got" <+> pretty (length argFmls)
    //         else do
    //             argFmls' <- mapM resolveFormula argFmls
    //             zipWithM_ enforceSame (map sortOf argFmls') argSorts
    //             return $ Cons resSort name argFmls'

    // resolveFormula fml = return fml

    pub fn resolve_formula(&mut self, fml: Formula) -> Result<Formula, ErrorMessage> {
        match fml {
            Formula::Var(_, x) => {
                if let Some(sch) = self.environment.symbols_of_arity(0).get(&x) {
                    match sch {
                        RSchema::Monotype(t) => {
                            let s = t.base_type().to_sort();

                            Ok(Formula::Var(s, x))
                        }
                        _ => Err(self.throw_res_error(format!(
                            "resolveFormula: encountered non-scalar variable {x} in a formula"
                        ))),
                    }
                } else {
                    self.resolve_formula(Formula::Pred(Sort::Any, x.clone(), vec![]))
                        .map_err(|_| self.throw_res_error(format!("Variable {x} is not in scope")))
                }
            }
            Formula::SetLit(_, elems) => {
                let elem_sort = self.fresh_sort();
                let elems = elems
                    .into_iter()
                    .map(|e| self.resolve_formula(e))
                    .collect::<Result<Vec<_>, _>>()?;

                for e in &elems {
                    self.enforce_same(e.sort(), elem_sort.clone());
                }

                Ok(Formula::SetLit(elem_sort, elems))
            }
            Formula::Unary(op, fml) => {
                let fml = self.resolve_formula(*fml)?;
                let sr = match op {
                    UnOp::Not => Sort::Bool,
                    UnOp::Neg => Sort::Int,
                };
                self.enforce_same(fml.sort(), sr);

                Ok(Formula::Unary(op, Box::new(fml)))
            }
            Formula::Binary(op, l, r) => {
                let l = self.resolve_formula(*l)?;
                let r = self.resolve_formula(*r)?;

                let ls = l.sort();
                let rs = r.sort();

                let op = match op {
                    BinOp::Eq | BinOp::Neq => {
                        self.enforce_same(ls.clone(), rs.clone());

                        op
                    }
                    BinOp::And | BinOp::Or | BinOp::Implies | BinOp::Iff => {
                        self.enforce_same(ls.clone(), Sort::Bool);
                        self.enforce_same(rs.clone(), Sort::Bool);

                        op
                    }
                    BinOp::Member => {
                        self.enforce_same(ls.clone(), Sort::Set(Box::new(rs.clone())));

                        op
                    }
                    BinOp::Union | BinOp::Intersect | BinOp::Diff | BinOp::Subset => {
                        let elem_sort = self.fresh_sort();
                        self.enforce_same(ls.clone(), Sort::Set(Box::new(elem_sort.clone())));
                        self.enforce_same(rs.clone(), Sort::Set(Box::new(elem_sort)));

                        op
                    }
                    BinOp::Times | BinOp::Plus | BinOp::Minus => {
                        if ls.is_set() {
                            let elem_sort = self.fresh_sort();
                            self.enforce_same(ls.clone(), Sort::Set(Box::new(elem_sort.clone())));
                            self.enforce_same(rs.clone(), Sort::Set(Box::new(elem_sort)));

                            to_set_op(op)
                        } else {
                            self.enforce_same(ls.clone(), Sort::Int);
                            self.enforce_same(rs.clone(), Sort::Int);

                            op
                        }
                    }
                    BinOp::Le => {
                        if ls.is_set() {
                            let elem_sort = self.fresh_sort();
                            self.enforce_same(ls.clone(), Sort::Set(Box::new(elem_sort.clone())));
                            self.enforce_same(rs.clone(), Sort::Set(Box::new(elem_sort)));

                            to_set_op(op)
                        } else {
                            self.enforce_same(ls.clone(), rs.clone());
                            self.sort_constraints
                                .push(SortConstraint::IsOrd(ls.clone()));

                            op
                        }
                    }
                    BinOp::Lt | BinOp::Gt | BinOp::Ge => {
                        self.enforce_same(ls.clone(), rs.clone());
                        self.sort_constraints
                            .push(SortConstraint::IsOrd(ls.clone()));

                        op
                    }
                };

                fn to_set_op(op: BinOp) -> BinOp {
                    match op {
                        BinOp::Times => BinOp::Intersect,
                        BinOp::Plus => BinOp::Union,
                        BinOp::Minus => BinOp::Diff,
                        BinOp::Le => BinOp::Subset,
                        _ => unreachable!(),
                    }
                }

                Ok(Formula::Binary(op, Box::new(l), Box::new(r)))
            }
            Formula::Ite(cond, l, r) => {
                let cond = self.resolve_formula(*cond)?;
                let l = self.resolve_formula(*l)?;
                let r = self.resolve_formula(*r)?;

                self.enforce_same(cond.sort(), Sort::Bool);
                self.enforce_same(l.sort(), r.sort());

                Ok(Formula::Ite(Box::new(cond), Box::new(l), Box::new(r)))
            }
            Formula::Pred(_, name, arg_fmls) => {
                if let Some((args, body)) = self.inlines.get(&name) {
                    let subst =
                        Substitution::new(args.iter().cloned().zip(arg_fmls.into_iter()).collect());

                    self.resolve_formula(body.clone().substitute(&subst))
                } else {
                    let ps = self.environment.all_predicates();
                    let sorts = ps.get(&name).ok_or_else(|| {
                        self.throw_res_error(format!("Predicate or measure {name} is undefined"))
                    })?;

                    let (res_sort, arg_sorts) = sorts.split_first().unwrap();

                    if arg_fmls.len() != arg_sorts.len() {
                        return Err(self.throw_res_error(format!(
                            "Expected {} arguments for predicate or measure {name} and got {}",
                            arg_sorts.len(),
                            arg_fmls.len()
                        )));
                    }

                    let arg_fmls = arg_fmls
                        .into_iter()
                        .map(|f| self.resolve_formula(f))
                        .collect::<Result<Vec<_>, _>>()?;

                    for (f, s) in arg_fmls.iter().zip(arg_sorts.iter()) {
                        self.enforce_same(f.sort(), s.clone());
                    }

                    Ok(Formula::Pred(res_sort.clone(), name, arg_fmls))
                }
            }
            Formula::Cons(_, name, args_fmls) => {
                let syms = self.environment.all_symbols();
                let cons_sch = syms.get(&name).ok_or_else(|| {
                    self.throw_res_error(format!("Data constructor {name} is undefined"))
                })?;

                let cons_t = cons_sch.to_monotype();
                let sorts = self.instantiate(
                    iter::once(cons_t.last_type())
                        .chain(cons_t.all_arg_types())
                        .map(|t| t.base_type().to_sort())
                        .collect(),
                );

                let (res_sort, arg_sorts) = sorts.split_first().unwrap();

                if arg_sorts.len() != args_fmls.len() {
                    return Err(self.throw_res_error(format!(
                        "Constructor {name} expected {} arguments and got {}",
                        arg_sorts.len(),
                        args_fmls.len()
                    )));
                }

                let args_fmls = args_fmls
                    .into_iter()
                    .map(|f| self.resolve_formula(f))
                    .collect::<Result<Vec<_>, _>>()?;

                for (f, s) in args_fmls.iter().zip(arg_sorts.iter()) {
                    self.enforce_same(f.sort(), s.clone());
                }

                Ok(Formula::Cons(res_sort.clone(), name, args_fmls))
            }

            fml => Ok(fml),
        }
    }

    // addNewSignature name sch = do
    //   ifM (Set.member name <$> use (environment . constants)) (throwResError $ text "Duplicate declaration of function" <+> text name) (return ())
    //   environment %= addPolyConstant name sch
    //   environment %= addUnresolvedConstant name sch

    pub fn add_new_signature(&mut self, name: Id, sch: RSchema) -> Result<(), ErrorMessage> {
        if self.environment.constants.contains(&name) {
            return Err(self.throw_res_error(format!("Duplicate declaration of function {name}")));
        }

        self.environment
            .add_poly_constant(name.clone(), sch.clone());
        self.environment.add_unresolved_constant(name, sch);

        Ok(())
    }

    // nominalPredApp (PredSig pName argSorts resSort) = Pred resSort pName (zipWith Var argSorts deBrujns)

    pub fn nominal_pred_app(&self, pred_sig: PredSig) -> Formula {
        let PredSig {
            name: p_name,
            arg_sorts,
            res_sort,
        } = pred_sig;

        let vars = de_brujns(&arg_sorts)
            .into_iter()
            .zip(arg_sorts)
            .map(|(db, s)| Formula::Var(s, db))
            .collect::<Vec<_>>();

        Formula::Pred(res_sort, p_name, vars)
    }

    // solveSortConstraints :: Resolver SortSubstitution
    // solveSortConstraints = do
    //   (unificationCs, typeClassCs) <- uses sortConstraints (partition isSameSortConstraint)
    //   tvs <- uses (environment . boundTypeVars) Set.fromList
    //   sortConstraints .= []
    //   idCount .= 0
    //   let (sls, srs) = unzip $ map (\(SameSort s1 s2) -> (s1, s2)) unificationCs
    //   subst <- case unifySorts tvs sls srs of
    //     Left (x, y) -> throwResError $ text "Cannot unify sorts" <+> pretty x <+> text "and" <+> pretty y
    //     Right subst -> return subst
    //   mapM_ (checkTypeClass subst) typeClassCs
    //   return subst
    //   where
    //     isSameSortConstraint (SameSort _ _) = True
    //     isSameSortConstraint _ = False

    //     checkTypeClass subst (IsOrd s) = let s' = sortSubstitute subst s in
    //       case s' of
    //         IntS -> return ()
    //         VarS _ -> return ()
    //         _ -> throwResError $ text "Sort" <+> pretty s' <+> text "is not ordered"

    pub fn solve_sort_constraints(&mut self) -> Result<SortSubstitution, ErrorMessage> {
        let (unification_cs, type_class_cs): (Vec<_>, Vec<_>) = self
            .sort_constraints
            .drain(..)
            .partition(|sc| matches!(sc, SortConstraint::SameSort(_, _)));

        let tvs = self
            .environment
            .bound_type_vars
            .iter()
            .cloned()
            .collect::<HashSet<_>>();
        self.id_count = 0;

        let (sls, srs): (Vec<_>, Vec<_>) = unification_cs
            .iter()
            .map(|sc| {
                if let SortConstraint::SameSort(sl, sr) = sc {
                    (sl.clone(), sr.clone())
                } else {
                    unreachable!()
                }
            })
            .unzip();

        let subst = unify_sorts(&tvs, sls, srs)
            .map_err(|(x, y)| self.throw_res_error(format!("Cannot unify sorts {x} and {y}")))?;

        for tcc in type_class_cs {
            if let SortConstraint::IsOrd(s) = tcc {
                let s = subst.sort_substitute(s.clone());
                match s {
                    Sort::Int => {}
                    Sort::Var(_) => {}
                    _ => {
                        return Err(self.throw_res_error(format!("Sort {s} is not ordered")));
                    }
                }
            }
        }

        Ok(subst)
    }

    // substituteTypeSynonym name tArgs = do
    //   tss <- use $ environment . typeSynonyms
    //   case Map.lookup name tss of
    //     Nothing -> throwResError $ text "Datatype or synonym" <+> text name <+> text "is undefined"
    //     Just (tVars, t) -> do
    //       when (length tArgs /= length tVars) $ throwResError $ text "Type synonym" <+> text name <+> text "expected" <+> pretty (length tVars) <+> text "type arguments and got" <+> pretty (length tArgs)
    //       return $ noncaptureTypeSubst tVars tArgs t

    pub fn substitute_type_synonym(
        &self,
        name: Id,
        t_args: Vec<RType>,
    ) -> Result<RType, ErrorMessage> {
        let (t_vars, t) = self.environment.type_synonyms.get(&name).ok_or_else(|| {
            self.throw_res_error(format!("Datatype or synonym {name} is undefined"))
        })?;

        if t_args.len() != t_vars.len() {
            return Err(self.throw_res_error(format!(
                "Type synonym {name} expected {} type arguments and got {}",
                t_vars.len(),
                t_args.len()
            )));
        }

        Ok(non_capture_type_subst(t_vars.clone(), t_args, t.clone()))
    }

    // -- | 'freshId' @prefix@ : fresh identifier starting with @prefix@
    // freshSort :: Resolver Sort
    // freshSort = do
    //   i <- use idCount
    //   idCount %= ( + 1)
    //   return $ VarS ("S" ++ show i)

    /// Fresh identifier starting with `prefix`
    pub fn fresh_sort(&mut self) -> Sort {
        let i = self.id_count;
        self.id_count += 1;

        Sort::Var(Id::Local(format!("S{i}").into_boxed_str()))
    }

    // -- | 'freshId' @p s@ : fresh var with prefix @p@ of sort @s@
    // freshId :: String -> Sort -> Resolver Formula
    // freshId p s = do
    //   i <- use idCount
    //   idCount %= (+ 1)
    //   return $ Var s (p ++ show i)

    /// Fresh var with prefix `p` of sort `s`
    pub fn fresh_id(&mut self, p: Id, s: Sort) -> Formula {
        let i = self.id_count;
        self.id_count += 1;

        Formula::Var(s, Id::Local(format!("{p}{i}").into_boxed_str()))
    }

    // -- | 'instantiate' @sorts@: replace all sort variables in @sorts@ with fresh sort variables
    // instantiate :: [Sort] -> Resolver [Sort]
    // instantiate sorts = do
    //   let tvs = Set.toList $ Set.unions (map typeVarsOfSort sorts)
    //   freshTvs <- replicateM (length tvs) freshSort
    //   return $ map (sortSubstitute $ Map.fromList $ zip tvs freshTvs) sorts

    /// Replace all sort variables in `sorts` with fresh sort variables
    pub fn instantiate(&mut self, sorts: Vec<Sort>) -> Vec<Sort> {
        let tvs = sorts.iter().flat_map(|s| s.type_vars()).collect::<Vec<_>>();
        let fresh_tvs = (0..tvs.len())
            .map(|_| self.fresh_sort())
            .collect::<Vec<_>>();

        let ss = SortSubstitution::new(tvs.into_iter().zip(fresh_tvs.into_iter()).collect());

        sorts.into_iter().map(|s| ss.sort_substitute(s)).collect()
    }

    // enforceSame :: Sort -> Sort -> Resolver ()
    // enforceSame sl sr
    //   | sl == sr    = return ()
    //   | otherwise   = sortConstraints %= (++ [SameSort sl sr])

    pub fn enforce_same(&mut self, sl: Sort, sr: Sort) {
        if sl != sr {
            self.sort_constraints.push(SortConstraint::SameSort(sl, sr));
        }
    }
}

// -- Normalize program form for typechecking:
// -- Move conditional and match statements to top level of untyped program
// normalizeProgram :: UProgram -> UProgram
// normalizeProgram p@Program{content = (PSymbol name)} = p
// -- Ensure no conditionals inside application
// normalizeProgram p@Program{content = (PApp fun arg)} =
//   untypedProg $ case (isCond fun', isCond arg') of
//     -- Both sides are conditionals, can transform either side.
//     (True, True) -> transformLCond fun' arg'
//     -- Transform left side of application
//     (True, _)    -> transformLCond fun' arg'
//     -- Transform right side of application
//     (_, True)    -> transformRCond fun' arg'
//     -- Do not transform
//     _            -> PApp (normalizeProgram fun) (normalizeProgram arg)
//   where
//     fun' = normalizeProgram fun
//     arg' = normalizeProgram arg

//     untypedProg p = Program p AnyT

//     isCond Program{content = (PIf _ _ _)}  = True
//     isCond Program{content = (PMatch _ _)} = True
//     isCond _                               = False

//     transformCase prog (Case con args ex) = Case con args (untypedProg (prog (normalizeProgram ex)))

//     -- Conditional is on left side of application
//     transformLCond p@Program{content = (PIf guard t f)} p2    =
//       PIf guard (untypedProg (PApp t p2)) (untypedProg (PApp f p2))
//     transformLCond p@Program{content = (PMatch scr cases)} p2 =
//       PMatch scr (fmap (transformCase (`PApp` p2)) cases)
//     transformLCond l r = PApp l r

//     -- Conditional is on right side of application
//     transformRCond p2 p@Program{content = (PIf guard t f)}     =
//       PIf guard (untypedProg (PApp p2 t)) (untypedProg (PApp p2 f))
//     transformRCond p2 p@Program{content = (PMatch scr cases)}  =
//       PMatch scr (fmap (transformCase (PApp p2)) cases)
//     transformRCond l r = PApp l r

// normalizeProgram p@Program{content = (PFun name body)} =
//   Program (PFun name (normalizeProgram body)) AnyT
// normalizeProgram p@Program{content = (PIf guard p1 p2)} =
//   Program (PIf (normalizeProgram guard) (normalizeProgram p1) (normalizeProgram p2)) AnyT
// normalizeProgram p@Program{content = (PMatch arg cases)} =
//   Program (PMatch (normalizeProgram arg) (fmap normalizeCase cases)) AnyT
//   where
//     normalizeCase (Case con args expr) = Case con args (normalizeProgram expr)
// normalizeProgram p@Program{content = (PFix fs body)} =
//   Program (PFix fs (normalizeProgram body)) AnyT
// normalizeProgram p@Program{content = (PLet var val body)} =
//   Program (PLet var (normalizeProgram val) (normalizeProgram body)) AnyT
// normalizeProgram p = p

/// Normalize program form for typechecking:
/// Move conditional and match statements to top level of untyped program
pub fn normalize_program(p: &Program<RType>) -> Program<RType> {
    let content = &*p.content;

    match content {
        BareProgram::Symbol(_) => p.clone(),
        BareProgram::App(fun, arg) => {
            let fun = Program::from(normalize_program(fun));
            let arg = Program::from(normalize_program(arg));

            fn untyped_prog(p: BareProgram<RType>) -> Program<RType> {
                Program {
                    content: Box::new(p),
                    type_of: TypeSkeleton::Any,
                }
            }

            fn is_cond(p: &Program<RType>) -> bool {
                matches!(
                    &*p.content,
                    BareProgram::If(_, _, _) | BareProgram::Match(_, _)
                )
            }

            fn transform_case(
                prog: impl FnOnce(Program<RType>) -> BareProgram<RType>,
                Case {
                    constructor,
                    arg_names,
                    expr,
                }: Case<RType>,
            ) -> Case<RType> {
                Case {
                    constructor,
                    arg_names,
                    expr: untyped_prog(prog(Program::from(normalize_program(&expr)))),
                }
            }

            /// Conditional is on left side of application
            fn transform_l_cond(p: Program<RType>, p2: Program<RType>) -> BareProgram<RType> {
                match &*p.content {
                    BareProgram::If(guard, t, f) => BareProgram::If(
                        guard.clone(),
                        untyped_prog(BareProgram::App(t.clone(), p2.clone())),
                        untyped_prog(BareProgram::App(f.clone(), p2)),
                    ),
                    BareProgram::Match(scr, cases) => BareProgram::Match(
                        scr.clone(),
                        cases
                            .into_iter()
                            .map(|c| transform_case(|p| BareProgram::App(p, p2.clone()), c.clone()))
                            .collect(),
                    ),
                    _ => BareProgram::App(p, p2),
                }
            }

            /// Conditional is on right side of application
            fn transform_r_cond(p2: Program<RType>, p: Program<RType>) -> BareProgram<RType> {
                match &*p.content {
                    BareProgram::If(guard, t, f) => BareProgram::If(
                        guard.clone(),
                        untyped_prog(BareProgram::App(p2.clone(), t.clone())),
                        untyped_prog(BareProgram::App(p2, f.clone())),
                    ),
                    BareProgram::Match(scr, cases) => BareProgram::Match(
                        scr.clone(),
                        cases
                            .into_iter()
                            .map(|c| transform_case(|p| BareProgram::App(p2.clone(), p), c.clone()))
                            .collect(),
                    ),
                    _ => BareProgram::App(p2, p),
                }
            }

            untyped_prog(match (is_cond(&fun), is_cond(&arg)) {
                (true, true) => transform_l_cond(fun, arg),
                (true, _) => transform_l_cond(fun, arg),
                (_, true) => transform_r_cond(fun, arg),
                _ => BareProgram::App(fun, arg),
            })
        }
        BareProgram::Fun(name, body) => Program {
            content: Box::new(BareProgram::Fun(name.clone(), normalize_program(body))),
            type_of: TypeSkeleton::Any,
        },
        BareProgram::If(guard, p1, p2) => Program {
            content: Box::new(BareProgram::If(
                normalize_program(guard),
                normalize_program(p1),
                normalize_program(p2),
            )),
            type_of: TypeSkeleton::Any,
        },
        BareProgram::Match(arg, cases) => Program {
            content: Box::new(BareProgram::Match(
                normalize_program(arg),
                cases
                    .iter()
                    .map(|c| Case {
                        constructor: c.constructor.clone(),
                        arg_names: c.arg_names.clone(),
                        expr: normalize_program(&c.expr),
                    })
                    .collect(),
            )),
            type_of: TypeSkeleton::Any,
        },
        BareProgram::Fix(fs, body) => Program {
            content: Box::new(BareProgram::Fix(fs.clone(), normalize_program(body))),
            type_of: TypeSkeleton::Any,
        },
        BareProgram::Let(var, val, body) => Program {
            content: Box::new(BareProgram::Let(
                var.clone(),
                normalize_program(val),
                normalize_program(body),
            )),
            type_of: TypeSkeleton::Any,
        },
        _ => p.clone(),
    }
}

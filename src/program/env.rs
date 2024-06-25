use core::fmt;
use std::{
    collections::{BTreeMap, BTreeSet},
    iter,
};

use hashbrown::{HashMap, HashSet};
use itertools::Itertools;
use num_bigint::BigInt;

use super::{DatatypeDef, MeasureDef, RProgram};
use crate::{
    logic::{Formula, PredSig, Sort, Substitution, VALUE_VAR_NAME},
    r#type::{BaseType, RSchema, RType, SType, TypeSkeleton, TypeSubstitution},
    tokens::{BIN_OP_TOKENS, UN_OP_TOKENS},
    util::{self, Id},
};

/// Typing environment
#[derive(Debug, Default, Clone)]
pub struct Environment {
    // Variable part:
    /// Variables and constants (with their refinement types), indexed by arity
    pub symbols: BTreeMap<usize, BTreeMap<Id, RSchema>>,
    /// Bound type variables
    pub bound_type_vars: HashSet<Id>,
    /// Argument sorts of bound abstract refinements
    pub bound_predicates: Vec<PredSig>,
    /// Unknown assumptions
    pub assumptions: HashSet<Formula>,
    /// For polymorphic recursive calls, the shape their types must have
    pub shape_constraints: HashMap<Id, SType>,
    /// Program terms that has already been scrutinized
    pub used_scrutinees: Vec<RProgram>,
    /// In eager match mode, datatype variables that can be scrutinized
    pub unfolded_vars: HashSet<Id>,
    /// Subset of symbols that are let-bound
    pub let_bound: HashSet<Id>,

    // Constant part:
    /// Subset of symbols that are constants
    pub constants: HashSet<Id>,
    /// Datatype definitions
    pub datatypes: HashMap<Id, DatatypeDef>,
    /// Signatures (resSort:argSorts) of module-level logic functions (measures, predicates)
    pub global_predicates: HashMap<Id, Vec<Sort>>,
    /// Measure definitions
    pub measures: HashMap<Id, MeasureDef>,
    /// Type synonym definitions
    pub type_synonyms: HashMap<Id, (BTreeSet<Id>, RType)>,
    /// Unresolved types of components (used for reporting specifications with macros)
    pub unresolved_constants: BTreeMap<Id, RSchema>,
}

impl Environment {
    /// All symbols of arity `n` in `env`
    pub fn symbols_of_arity(&self, n: usize) -> BTreeMap<Id, RSchema> {
        self.symbols.get(&n).cloned().unwrap_or_default()
    }

    pub fn all_symbols(&self) -> HashMap<Id, RSchema> {
        self.symbols
            .values()
            .flat_map(|m| m.iter())
            .map(|(id, schema)| (id.clone(), schema.clone()))
            .collect()
    }

    // -- | 'lookupSymbol' @name env@ : type of symbol @name@ in @env@, including built-in constants
    // lookupSymbol :: Id -> Int -> Bool -> Environment -> Maybe RSchema
    // lookupSymbol name a hasSet env
    //   | a == 0 && name == "True"                          = Just $ Monotype $ ScalarT BoolT valBool
    //   | a == 0 && name == "False"                         = Just $ Monotype $ ScalarT BoolT (fnot valBool)
    //   | a == 0 && isJust asInt                            = Just $ Monotype $ ScalarT IntT (valInt |=| IntLit (fromJust asInt))
    //   | a == 1 && (name `elem` Map.elems unOpTokens)      = let op = head $ Map.keys $ Map.filter (== name) unOpTokens in Just $ unOpType op
    //   | isBinary && hasSet                                = let ops = Map.keys $ Map.filter (== name) binOpTokens
    //     in Just $ binOpType $ case tail ops of
    //         [] -> head ops
    //         _  -> head $ tail ops -- To account for set operator overloading
    //   | isBinary                                          = let op = head $ Map.keys $ Map.filter (== name) binOpTokens in Just $ binOpType op
    //   | otherwise                                         = Map.lookup name (allSymbols env)
    //   where
    //     isBinary = a == 2 && (name `elem` Map.elems binOpTokens)
    //     asInt = asInteger name

    pub fn lookup_symbol(&self, name: &Id, a: usize, has_set: bool) -> Option<RSchema> {
        if a == 0 {
            if name.as_str() == "True" {
                Some(RSchema::Monotype(RType::Scalar(
                    BaseType::Bool,
                    Formula::VAL_BOOL,
                )))
            } else if name.as_str() == "False" {
                Some(RSchema::Monotype(RType::Scalar(
                    BaseType::Bool,
                    !Formula::VAL_BOOL,
                )))
            } else {
                if let Some(i) = name.as_str().parse::<BigInt>().ok() {
                    Some(RSchema::Monotype(RType::Scalar(
                        BaseType::Int,
                        Formula::VAL_INT.eq(Formula::IntLit(i)),
                    )))
                } else {
                    self.all_symbols().get(name).cloned()
                }
            }
        }
        // TODO - `let Some` chain
        else if a == 1 && UN_OP_TOKENS.contains_right(name) {
            let op = UN_OP_TOKENS.get_by_right(name).unwrap();
            Some(RSchema::un_op_type(op))
        } else {
            let is_binary = a == 2 && BIN_OP_TOKENS.contains_right(name);

            if is_binary {
                if has_set {
                    let ops = BIN_OP_TOKENS
                        .iter()
                        .filter(|(_, v)| *v == name)
                        .map(|(k, _)| k);
                    let op = ops.clone().next().unwrap();

                    Some(RSchema::bin_op_type(match ops.skip(1).next() {
                        Some(op) => op,
                        None => op,
                    }))
                } else {
                    let op = BIN_OP_TOKENS.get_by_right(name).unwrap();
                    Some(RSchema::bin_op_type(op))
                }
            } else {
                self.all_symbols().get(name).cloned()
            }
        }
    }

    // symbolAsFormula :: Environment -> Id -> RType -> Formula
    // symbolAsFormula _ name t | arity t > 0
    //                       = error $ unwords ["symbolAsFormula: not a scalar symbol", name]
    // symbolAsFormula env name t
    //   | name == "True"    = BoolLit True
    //   | name == "False"   = BoolLit False
    //   | isJust asInt      = IntLit (fromJust asInt)
    //   | isConstructor     = Cons sort name []
    //   | otherwise         = Var sort name
    //   where
    //     isConstructor = isJust (lookupConstructor name env)
    //     sort = toSort (baseTypeOf t)
    //     asInt = asInteger name

    pub fn symbol_as_formula(&self, name: Id, t: RType) -> Formula {
        if t.arity() > 0 {
            panic!("not a scalar symbol {name}")
        }

        if name.as_str() == "True" {
            Formula::BoolLit(true)
        } else if name.as_str() == "False" {
            Formula::BoolLit(false)
        } else if let Some(i) = name.as_str().parse::<BigInt>().ok() {
            Formula::IntLit(i)
        } else {
            let is_constructor = self.lookup_constructor(&name).is_some();
            let sort = t.base_type().to_sort();

            if is_constructor {
                Formula::Cons(sort, name, vec![])
            } else {
                Formula::Var(sort, name)
            }
        }
    }

    // -- | Is @name@ a constant in @env@ including built-in constants)?
    // isConstant name env = (name `elem` ["True", "False"]) ||
    //                       isJust (asInteger name) ||
    //                       (name `elem` Map.elems unOpTokens) ||
    //                       (name `elem` Map.elems binOpTokens) ||
    //                       (name `Set.member` (env ^. constants))

    /// Is `name` a constant in `env` including built-in constants?
    pub fn is_constant(&self, name: &Id) -> bool {
        name.as_str() == "True"
            || name.as_str() == "False"
            || name.as_str().parse::<BigInt>().is_ok()
            || UN_OP_TOKENS.contains_right(name)
            || BIN_OP_TOKENS.contains_right(name)
            || self.constants.contains(name)
    }

    // -- | 'isBound' @tv env@: is type variable @tv@ bound in @env@?
    // isBound :: Environment -> Id -> Bool
    // isBound env tv = tv `elem` env ^. boundTypeVars

    /// Is type variable `tv` bound in `env`?
    pub fn is_bound(&self, tv: &Id) -> bool {
        self.bound_type_vars.contains(tv)
    }

    // addVariable :: Id -> RType -> Environment -> Environment
    // addVariable name t = addPolyVariable name (Monotype t)

    pub fn add_variable(&mut self, name: Id, t: RType) {
        self.add_poly_variable(name, RSchema::Monotype(t));
    }

    // addPolyVariable :: Id -> RSchema -> Environment -> Environment
    // addPolyVariable name sch e =  let n = arity (toMonotype sch) in (symbols %~ Map.insertWith Map.union n (Map.singleton name sch)) e
    //   where
    //     syms = unwords $ Map.keys $ allSymbols e
    //     en = Map.keys $ allSymbols e
    //     n = arity (toMonotype sch)
    //     en' = Map.keys $ allSymbols ((symbols %~ Map.insertWith Map.union n (Map.singleton name sch)) e)

    pub fn add_poly_variable(&mut self, name: Id, sch: RSchema) {
        let n = sch.to_monotype().arity();
        self.symbols.entry(n).or_default().insert(name, sch);
    }

    // -- | 'addConstant' @name t env@ : add type binding @name@ :: Monotype @t@ to @env@
    // addConstant :: Id -> RType -> Environment -> Environment
    // addConstant name t = addPolyConstant name (Monotype t)

    /// Add type binding `name` :: `t` to `env`
    pub fn add_constant(&mut self, name: Id, t: RType) {
        self.add_poly_constant(name, RSchema::Monotype(t));
    }

    // -- | 'addPolyConstant' @name sch env@ : add type binding @name@ :: @sch@ to @env@
    // addPolyConstant :: Id -> RSchema -> Environment -> Environment
    // addPolyConstant name sch = addPolyVariable name sch . (constants %~ Set.insert name)

    /// Add type binding `name` :: `sch` to `env`
    pub fn add_poly_constant(&mut self, name: Id, sch: RSchema) {
        self.add_poly_variable(name.clone(), sch);
        self.constants.insert(name);
    }

    // addLetBound :: Id -> RType -> Environment -> Environment
    // addLetBound name t = addVariable name t . (letBound %~ Set.insert name)

    /// Add let-bound variable `name` :: `t` to `env`
    pub fn add_let_bound(&mut self, name: Id, t: RType) {
        self.add_variable(name.clone(), t);
        self.let_bound.insert(name);
    }

    // addUnresolvedConstant :: Id -> RSchema -> Environment -> Environment
    // addUnresolvedConstant name sch = unresolvedConstants %~ Map.insert name sch

    /// Add unresolved constant `name` :: `sch` to `env`
    pub fn add_unresolved_constant(&mut self, name: Id, sch: RSchema) {
        self.unresolved_constants.insert(name, sch);
    }

    // removeVariable :: Id -> Environment -> Environment
    // removeVariable name env = case Map.lookup name (allSymbols env) of
    //   Nothing -> env
    //   Just sch -> over symbols (Map.insertWith (flip Map.difference) (arity $ toMonotype sch) (Map.singleton name sch)) . over constants (Set.delete name) $ env

    pub fn remove_variable(&mut self, name: &Id) {
        if let Some(sch) = self.all_symbols().get(name) {
            let n = sch.to_monotype().arity();
            self.symbols.entry(n).and_modify(|m| {
                m.remove(name);
            });
            self.constants.remove(name);
        }
    }

    // embedContext :: Environment -> RType -> (Environment, RType)
    // embedContext env (LetT x tDef tBody) =
    //   let
    //     (env', tDef') = embedContext (removeVariable x env) tDef
    //     (env'', tBody') = embedContext env' tBody
    //   in (addLetBound x tDef' env'', tBody')
    // -- TODO: function?
    // embedContext env t = (env, t)

    pub fn embed_context(&mut self, t: RType) -> RType {
        match t {
            RType::Let(x, t_def, t_body) => {
                let t_def = self.embed_context(*t_def);
                let t_body = self.embed_context(*t_body);
                self.add_let_bound(x.clone(), t_def.clone());
                RType::Let(x, Box::new(t_def), Box::new(t_body))
            }
            RType::Function { .. } => todo!("function?"),
            _ => t,
        }
    }

    // unfoldAllVariables env = over unfoldedVars (Set.union (Map.keysSet (symbolsOfArity 0 env) Set.\\ (env ^. constants))) env

    pub fn unfold_all_variables(&mut self) {
        let vars = self
            .symbols_of_arity(0)
            .keys()
            .cloned()
            .collect::<HashSet<_>>()
            .difference(&self.constants)
            .cloned()
            .collect::<HashSet<_>>();
        self.unfolded_vars.extend(vars);
    }

    // addMeasure :: Id -> MeasureDef -> Environment -> Environment
    // addMeasure measureName m = over measures (Map.insert measureName m)

    pub fn add_measure(&mut self, measure_name: Id, m: MeasureDef) {
        self.measures.insert(measure_name, m);
    }

    // addBoundPredicate :: PredSig -> Environment -> Environment
    // addBoundPredicate sig = over boundPredicates (sig :)

    pub fn add_bound_predicate(&mut self, sig: PredSig) {
        self.bound_predicates.push(sig);
    }

    // addGlobalPredicate :: Id -> Sort -> [Sort] -> Environment -> Environment
    // addGlobalPredicate predName resSort argSorts = over globalPredicates (Map.insert predName (resSort : argSorts))

    pub fn add_global_predicate(&mut self, pred_name: Id, res_sort: Sort, arg_sorts: Vec<Sort>) {
        self.global_predicates
            .insert(pred_name, iter::once(res_sort).chain(arg_sorts).collect());
    }

    // addTypeSynonym :: Id -> [Id] -> RType -> Environment -> Environment
    // addTypeSynonym name tvs t = over typeSynonyms (Map.insert name (tvs, t))

    pub fn add_type_synonym(&mut self, name: Id, tvs: BTreeSet<Id>, t: RType) {
        self.type_synonyms.insert(name, (tvs, t));
    }

    // -- | 'addDatatype' @name env@ : add datatype @name@ to the environment
    // addDatatype :: Id -> DatatypeDef -> Environment -> Environment
    // addDatatype name dt = over datatypes (Map.insert name dt)

    /// Add datatype `name` to the environment
    pub fn add_datatype(&mut self, name: Id, dt: DatatypeDef) {
        self.datatypes.insert(name, dt);
    }

    // -- | 'lookupConstructor' @ctor env@ : the name of the datatype for which @ctor@ is registered as a constructor in @env@, if any
    // lookupConstructor :: Id -> Environment -> Maybe Id
    // lookupConstructor ctor env = let m = Map.filter (\dt -> ctor `elem` dt ^. constructors) (env ^. datatypes)
    //   in if Map.null m
    //       then Nothing
    //       else Just $ fst $ Map.findMin m

    pub fn lookup_constructor(&self, ctor: &Id) -> Option<Id> {
        let m = self
            .datatypes
            .iter()
            .filter(|(_, dt)| dt.constructors.contains(ctor))
            .collect::<HashMap<_, _>>();

        if m.is_empty() {
            None
        } else {
            Some((*m.keys().next().unwrap()).clone())
        }
    }

    // -- | 'addTypeVar' @a@ : Add bound type variable @a@ to the environment
    // addTypeVar :: Id -> Environment -> Environment
    // addTypeVar a = over boundTypeVars (a :)

    /// Add bound type variable `a` to the environment
    pub fn add_type_var(&mut self, a: Id) {
        self.bound_type_vars.insert(a);
    }

    // -- | 'addAssumption' @f env@ : @env@ with extra assumption @f@
    // addAssumption :: Formula -> Environment -> Environment
    // addAssumption f = assumptions %~ Set.insert f

    /// Add extra assumption `f` to the environment
    pub fn add_assumption(&mut self, f: Formula) {
        self.assumptions.insert(f);
    }

    // -- | 'addScrutinee' @p env@ : @env@ with @p@ marked as having been scrutinized already
    // addScrutinee :: RProgram -> Environment -> Environment
    // addScrutinee p = usedScrutinees %~ (p :)

    /// Mark `p` as having been scrutinized already
    pub fn add_scrutinee(&mut self, p: RProgram) {
        self.used_scrutinees.push(p);
    }

    // allPredicates env = Map.fromList (map (\(PredSig pName argSorts resSort) -> (pName, resSort:argSorts)) (env ^. boundPredicates)) `Map.union` (env ^. globalPredicates)

    pub fn all_predicates(&self) -> HashMap<Id, Vec<Sort>> {
        let mut predicates =
            HashMap::with_capacity(self.bound_predicates.len() + self.global_predicates.len());

        for predicate in &self.bound_predicates {
            let PredSig {
                name,
                arg_sorts,
                res_sort,
            } = predicate;

            predicates.insert(
                name.clone(),
                iter::once(res_sort.clone())
                    .chain(arg_sorts.clone())
                    .collect(),
            );
        }

        predicates.extend(
            self.global_predicates
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())),
        );

        predicates
    }

    // -- | 'allMeasuresOf' @dtName env@ : all measure of datatype with name @dtName@ in @env@
    // allMeasuresOf dtName env = Map.filter (\(MeasureDef (DataS sName _) _ _ _ _) -> dtName == sName) $ env ^. measures

    pub fn all_measures_of(&self, dt_name: &Id) -> HashMap<Id, MeasureDef> {
        self.measures
            .iter()
            .filter(|(_, m)| match &m.in_sort {
                Sort::Data(name, _) => name == dt_name,
                _ => todo!("return false?"),
            })
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect()
    }

    // -- | 'allMeasurePostconditions' @baseT env@ : all nontrivial postconditions of measures of @baseT@ in case it is a datatype
    // allMeasurePostconditions includeQuanitifed baseT@(DatatypeT dtName tArgs _) env =
    //     let
    //       allMeasures = Map.toList $ allMeasuresOf dtName env
    //       isAbstract = null $ ((env ^. datatypes) Map.! dtName) ^. constructors
    //     in catMaybes $ map extractPost allMeasures ++
    //                    if isAbstract then map contentProperties allMeasures else [] ++
    //                    if includeQuanitifed then map elemProperties allMeasures else []
    //   where
    //     extractPost (mName, MeasureDef _ outSort _ _ fml) =
    //       if fml == ftrue
    //         then Nothing
    //         else Just $ substitute (Map.singleton valueVarName (Pred outSort mName [Var (toSort baseT) valueVarName])) fml

    //     contentProperties (mName, MeasureDef (DataS _ vars) a _ _ _) = case elemIndex a vars of
    //       Nothing -> Nothing
    //       Just i -> let (ScalarT elemT fml) = tArgs !! i -- @mName@ "returns" one of datatype's parameters: transfer the refinement onto the value of the measure
    //                 in let
    //                     elemSort = toSort elemT
    //                     measureApp = Pred elemSort mName [Var (toSort baseT) valueVarName]
    //                    in Just $ substitute (Map.singleton valueVarName measureApp) fml
    //     contentProperties (mName, MeasureDef {}) = Nothing

    //     elemProperties (mName, MeasureDef (DataS _ vars) (SetS a) _ _ _) = case elemIndex a vars of
    //       Nothing -> Nothing
    //       Just i -> let (ScalarT elemT fml) = tArgs !! i -- @mName@ is a set of datatype "elements": add an axiom that every element of the set has that property
    //                 in if fml == ftrue || fml == ffalse || not (Set.null $ unknownsOf fml)
    //                     then Nothing
    //                     else  let
    //                             elemSort = toSort elemT
    //                             scopedVar = Var elemSort "_x"
    //                             setVal = Pred (SetS elemSort) mName [Var (toSort baseT) valueVarName]
    //                           in Just $ All scopedVar (fin scopedVar setVal |=>| substitute (Map.singleton valueVarName scopedVar) fml)
    //     elemProperties (mName, MeasureDef {}) = Nothing

    // allMeasurePostconditions _ _ _ = []

    /// All nontrivial postconditions of measures of `base_t` in case it is a datatype
    pub fn all_measure_postconditions(
        &self,
        include_quantified: bool,
        base_t: &BaseType<Formula>,
    ) -> Vec<Formula> {
        if let BaseType::Datatype(dt_name, t_args, _) = base_t {
            let all_measures = self.all_measures_of(dt_name);
            let is_abstract = self
                .datatypes
                .get(dt_name)
                .map_or(false, |dt| dt.constructors.is_empty());

            let mut predicates = all_measures
                .iter()
                .filter_map(|(k, v)| self.extract_post(k, v, base_t))
                .collect::<Vec<_>>();

            if is_abstract {
                predicates.extend(
                    all_measures
                        .iter()
                        .filter_map(|(k, v)| self.content_properties(k, v, t_args, base_t)),
                )
            }

            if include_quantified {
                predicates.extend(
                    all_measures
                        .iter()
                        .filter_map(|(k, v)| self.elem_properties(k, v, t_args, base_t)),
                )
            }

            predicates
        } else {
            Vec::new()
        }
    }

    fn extract_post(
        &self,
        m_name: &Id,
        m: &MeasureDef,
        base_t: &BaseType<Formula>,
    ) -> Option<Formula> {
        if m.postcondition == Formula::TRUE {
            None
        } else {
            let out_sort = m.out_sort.clone();
            let measure_app = Formula::Pred(
                out_sort,
                m_name.clone(),
                vec![Formula::Var(base_t.to_sort(), VALUE_VAR_NAME)],
            );

            Some(
                m.postcondition
                    .clone()
                    .substitute(&Substitution::new(BTreeMap::from_iter([(
                        VALUE_VAR_NAME,
                        measure_app,
                    )]))),
            )
        }
    }

    fn content_properties(
        &self,
        m_name: &Id,
        m: &MeasureDef,
        t_args: &[RType],
        base_t: &BaseType<Formula>,
    ) -> Option<Formula> {
        if let Sort::Data(_, vars) = &m.in_sort {
            if let Some(i) = vars.iter().position(|t| *t == m.out_sort) {
                let TypeSkeleton::Scalar(elem_t, fml) = &t_args[i] else {
                    unreachable!()
                };
                let elem_sort = elem_t.to_sort();
                let measure_app = Formula::Pred(
                    elem_sort,
                    m_name.clone(),
                    vec![Formula::Var(base_t.to_sort(), VALUE_VAR_NAME)],
                );

                Some(
                    fml.clone()
                        .substitute(&Substitution::new(BTreeMap::from_iter([(
                            VALUE_VAR_NAME,
                            measure_app,
                        )]))),
                )
            } else {
                None
            }
        } else {
            None
        }
    }

    fn elem_properties(
        &self,
        m_name: &Id,
        m: &MeasureDef,
        t_args: &[RType],
        base_t: &BaseType<Formula>,
    ) -> Option<Formula> {
        if let Sort::Data(_, vars) = &m.in_sort {
            if let Some(i) = vars
                .iter()
                .position(|t| *t == Sort::Set(Box::new(m.out_sort.clone())))
            {
                let TypeSkeleton::Scalar(elem_t, fml) = &t_args[i] else {
                    unreachable!()
                };
                let elem_sort = elem_t.to_sort();
                let scoped_var = Formula::Var(elem_sort.clone(), Id::Builtin("_x"));
                let set_val = Formula::Pred(
                    Sort::Set(Box::new(elem_sort)),
                    m_name.clone(),
                    vec![Formula::Var(base_t.to_sort(), VALUE_VAR_NAME)],
                );

                if *fml == Formula::TRUE || *fml == Formula::FALSE || !fml.unknowns().is_empty() {
                    None
                } else {
                    Some(Formula::All(
                        Box::new(scoped_var.clone()),
                        Box::new(
                            scoped_var.clone().member(set_val.clone()).implies(
                                fml.clone()
                                    .substitute(&Substitution::new(BTreeMap::from_iter([(
                                        VALUE_VAR_NAME,
                                        scoped_var.clone(),
                                    )]))),
                            ),
                        ),
                    ))
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    // typeSubstituteEnv :: TypeSubstitution -> Environment -> Environment
    // typeSubstituteEnv tass = over symbols (Map.map (Map.map (schemaSubstitute tass)))

    pub fn type_substitute_env(&self, tass: TypeSubstitution) -> Environment {
        let symbols = self
            .symbols
            .iter()
            .map(|(k, m)| {
                (
                    *k,
                    m.iter()
                        .map(|(id, schema)| (id.clone(), tass.schema_substitute(schema.clone())))
                        .collect(),
                )
            })
            .collect();

        Environment {
            symbols,
            ..self.clone()
        }
    }

    // -- | Insert weakest refinement
    // refineTop :: Environment -> SType -> RType
    // refineTop env (ScalarT (DatatypeT name tArgs pArgs) _) =
    //   let variances = env ^. (datatypes . to (Map.! name) . predVariances) in
    //   ScalarT (DatatypeT name (map (refineTop env) tArgs) (map (BoolLit . not) variances)) ftrue
    // refineTop _ (ScalarT IntT _) = ScalarT IntT ftrue
    // refineTop _ (ScalarT BoolT _) = ScalarT BoolT ftrue
    // refineTop _ (ScalarT (TypeVarT vSubst a) _) = ScalarT (TypeVarT vSubst a) ftrue
    // refineTop env (FunctionT x tArg tFun) = FunctionT x (refineBot env tArg) (refineTop env tFun)

    pub fn refine_top(&self, t: SType) -> RType {
        match t {
            SType::Scalar(BaseType::Datatype(name, t_args, p_args), _) => {
                let variances = self
                    .datatypes
                    .get(&name)
                    .map_or_else(|| Vec::new(), |dt| dt.pred_variances.clone());

                RType::Scalar(
                    BaseType::Datatype(
                        name,
                        t_args.iter().map(|t| self.refine_top(t.clone())).collect(),
                        p_args.iter().map(|_| Formula::BoolLit(false)).collect(),
                    ),
                    Formula::TRUE,
                )
            }
            SType::Scalar(BaseType::Int, _) => RType::Scalar(BaseType::Int, Formula::TRUE),
            SType::Scalar(BaseType::Bool, _) => RType::Scalar(BaseType::Bool, Formula::TRUE),
            SType::Scalar(BaseType::TypeVar(v_subst, a), _) => {
                RType::Scalar(BaseType::TypeVar(v_subst, a), Formula::TRUE)
            }
            SType::Function { x, t_arg, t_res } => RType::Function {
                x,
                t_arg: Box::new(self.refine_bot(*t_arg)),
                t_res: Box::new(self.refine_top(*t_res)),
            },
            _ => unreachable!(),
        }
    }

    // -- | Insert strongest refinement
    // refineBot :: Environment -> SType -> RType
    // refineBot env (ScalarT (DatatypeT name tArgs pArgs) _) =
    //   let variances = env ^. (datatypes . to (Map.! name) . predVariances) in
    //   ScalarT (DatatypeT name (map (refineBot env) tArgs) (map BoolLit variances)) ffalse
    // refineBot _ (ScalarT IntT _) = ScalarT IntT ffalse
    // refineBot _ (ScalarT BoolT _) = ScalarT BoolT ffalse
    // refineBot _ (ScalarT (TypeVarT vSubst a) _) = ScalarT (TypeVarT vSubst a) ffalse
    // refineBot env (FunctionT x tArg tFun) = FunctionT x (refineTop env tArg) (refineBot env tFun)

    /// Insert strongest refinement
    pub fn refine_bot(&self, t: SType) -> RType {
        match t {
            SType::Scalar(BaseType::Datatype(name, t_args, p_args), _) => {
                let variances = self
                    .datatypes
                    .get(&name)
                    .map_or_else(|| Vec::new(), |dt| dt.pred_variances.clone());

                RType::Scalar(
                    BaseType::Datatype(
                        name,
                        t_args.iter().map(|t| self.refine_bot(t.clone())).collect(),
                        p_args.iter().map(|_| Formula::FALSE).collect(),
                    ),
                    Formula::FALSE,
                )
            }
            SType::Scalar(BaseType::Int, _) => RType::Scalar(BaseType::Int, Formula::FALSE),
            SType::Scalar(BaseType::Bool, _) => RType::Scalar(BaseType::Bool, Formula::FALSE),
            SType::Scalar(BaseType::TypeVar(v_subst, a), _) => {
                RType::Scalar(BaseType::TypeVar(v_subst, a), Formula::FALSE)
            }
            SType::Function { x, t_arg, t_res } => RType::Function {
                x,
                t_arg: Box::new(self.refine_top(*t_arg)),
                t_res: Box::new(self.refine_bot(*t_res)),
            },
            _ => unreachable!(),
        }
    }
}

impl PartialEq for Environment {
    fn eq(&self, other: &Self) -> bool {
        self.symbols == other.symbols && self.assumptions == other.assumptions
    }
}

impl Eq for Environment {}

impl PartialOrd for Environment {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match self.symbols.partial_cmp(&other.symbols) {
            Some(core::cmp::Ordering::Equal) => self
                .unresolved_constants
                .partial_cmp(&other.unresolved_constants),
            ord => ord,
        }
    }
}

impl Ord for Environment {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl fmt::Display for Environment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}",
            util::remove_domain(&self.constants, &self.all_symbols())
                .keys()
                .format(", "),
            self.assumptions.iter().format(", ")
        )
    }
}

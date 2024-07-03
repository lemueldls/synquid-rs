use std::{cell::RefCell, collections::BTreeMap, iter, rc::Rc};

use crate::{
    logic::{self, Formula, Sort},
    program::{DatatypeDef, Environment},
    r#type::{RSchema, TypeSkeleton},
    util::{self, Id},
};
use bimap::BiHashMap;
use hashbrown::{HashMap, HashSet};
use itertools::Itertools;
// use parking_lot::RwLock;
use slotmap::{new_key_type, SlotMap};
use z3::ast;

new_key_type! {
    pub struct FormulaId;
    pub struct Z3AstId;
    // pub struct Z3SortId;
}

#[derive(Debug)]
#[doc(alias = "Z3Data")]
pub struct Z3State<'ctx> {
    /// Z3 environment for the main solver
    pub env: &'ctx Z3Env<'ctx>,
    /// Mapping from Synquid sorts to Z3 sorts
    pub sorts: HashMap<Sort, z3::Sort<'ctx>>,
    /// AST nodes for scalar variables
    pub vars: HashMap<Id, ast::Dynamic<'ctx>>,
    /// Function declarations for measures, predicates, and constructors
    pub functions: HashMap<Id, Rc<z3::FuncDecl<'ctx>>>,
    /// Datatypes mapped directly to Z3 datatypes (monomorphic only)
    pub stored_datatypes: HashSet<Id>,
    /// Control literals for computing UNSAT cores
    pub control_literals: BiHashMap<Formula, ast::Dynamic<'ctx>>,
    /// Z3 environment for the auxiliary solver
    pub aux_env: &'ctx Z3Env<'ctx>,
    /// Boolean sort in the auxiliary solver
    pub bool_sort_aux: Option<z3::Sort<'ctx>>,
    /// Control literals for computing UNSAT cores in the auxiliary solver
    pub control_literals_aux: BiHashMap<Formula, ast::Dynamic<'ctx>>,
}

//   initSolver env = do
//     -- Disable MBQI:
//     params <- mkParams
//     symb <- mkStringSymbol "mbqi"
//     paramsSetBool params symb False
//     solverSetParams params

//     convertDatatypes (allSymbols env) (Map.toList $ env ^. datatypes)

//     boolAux <- withAuxSolver mkBoolSort
//     boolSortAux .= Just boolAux

pub fn init_solver(env: Environment, state: &mut Z3State) {
    let mut params = z3::Params::new(&state.env.context);
    let symb = z3::Symbol::String("mbqi".to_string());
    params.set_bool(symb, false);

    state.env.solver.set_params(&params);

    state.convert_datatypes(&env.all_symbols(), Vec::from_iter(env.datatypes));

    let bool_aux = z3::Sort::bool(&state.aux_env.context);
    state.bool_sort_aux = Some(bool_aux);
}

impl<'ctx> Z3State<'ctx> {
    pub fn new(env: &'ctx Z3Env) -> Self {
        Self {
            env,
            sorts: HashMap::new(),
            vars: HashMap::new(),
            functions: HashMap::new(),
            stored_datatypes: HashSet::new(),
            control_literals: BiHashMap::new(),
            aux_env: env,
            bool_sort_aux: None,
            control_literals_aux: BiHashMap::new(),
        }
    }

    pub fn ctx(&self) -> &'ctx z3::Context {
        &self.env.context
    }

    pub fn aux_ctx(&self) -> &'ctx z3::Context {
        &self.aux_env.context
    }

    pub fn register_z3_ast(&mut self, z3_ast: &dyn ast::Ast<'ctx>) -> ast::Dynamic<'ctx> {
        ast::Dynamic::from_ast(z3_ast)
    }

    // pub fn register_z3_ast(&mut self, z3_ast: &dyn ast::Ast<'ctx>) -> Z3AstId {
    //     self.z3_ast_map.insert(ast::Dynamic::from_ast(z3_ast))
    // }

    // pub fn get_z3_ast(&self, id: Z3AstId) -> &ast::Dynamic<'ctx> {
    //     self.z3_ast_map.get(id).unwrap()
    // }

    // pub fn register_z3_sort(&mut self, z3_sort: z3::Sort<'ctx>) -> Z3SortId {
    //     self.z3_sort_map.insert(z3_sort)
    // }

    // pub fn get_z3_sort(&self, id: Z3SortId) -> &z3::Sort<'ctx> {
    //     self.z3_sort_map.get(id).unwrap()
    // }

    //   isSat fml = do
    //       res <- local $ (fmlToAST >=> assert) fml >> check

    //       case res of
    //         Unsat -> debug 2 (text "SMT CHECK" <+> pretty fml <+> text "UNSAT") $ return False
    //         Sat -> debug 2 (text "SMT CHECK" <+> pretty fml <+> text "SAT") $ return True
    //         -- _ -> error $ unwords ["isValid: Z3 returned Unknown for", show fml]
    //         _ -> debug 2 (text "SMT CHECK" <+> pretty fml <+> text "UNKNOWN treating as SAT") $ return True

    pub fn is_sat(&mut self, fml: &Formula) -> bool {
        fml.clone().to_ast(self);
        let res = self.env.solver.check();

        match res {
            z3::SatResult::Unsat => {
                log::debug!("SMT CHECK {fml} UNSAT");

                false
            }
            z3::SatResult::Sat => {
                log::debug!("SMT CHECK {fml} SAT");

                true
            }
            z3::SatResult::Unknown => {
                log::debug!("SMT CHECK {fml} UNKNOWN treating as SAT");

                true
            }
        }
    }

    // convertDatatypes :: Map Id RSchema -> [(Id, DatatypeDef)] -> Z3State ()
    // convertDatatypes _ [] = return ()
    // convertDatatypes symbols ((dtName, DatatypeDef [] _ _ ctors@(_:_) _):rest) = do
    //   ifM (uses storedDatatypes (Set.member dtName))
    //     (return ()) -- This datatype has already been processed as a dependency
    //     (do
    //       dtSymb <- mkStringSymbol dtName
    //       z3ctors <- mapM convertCtor ctors
    //       z3dt <- mkDatatype dtSymb z3ctors
    //       sorts %= Map.insert dataSort z3dt
    //       storedDatatypes %= Set.insert dtName)
    //   convertDatatypes symbols rest
    //   where
    //     dataSort = DataS dtName []

    //     convertCtor cName = do
    //       z3CName <- mkStringSymbol cName
    //       recognizerName <- mkStringSymbol ("is" ++ cName)
    //       let args = allArgs $ toMonotype $ symbols Map.! cName
    //       z3Args <- mapM convertField args
    //       mkConstructor z3CName recognizerName z3Args

    //     convertField (Var fSort fName) = do
    //       z3FName <- mkStringSymbol fName
    //       z3FSort <- case fSort of
    //                     DataS dtName' [] ->
    //                       if dtName' == dtName
    //                         then return Nothing -- Recursive sort is denoted with Nothing
    //                         else case lookup dtName' rest of
    //                               Nothing -> Just <$> toZ3Sort fSort -- Datatype dtName' should have already been processed
    //                               Just dtDef -> do -- It is an eligible datatype yet to process; process it now instead
    //                                               convertDatatypes symbols [(dtName', dtDef)]
    //                                               Just <$> toZ3Sort fSort
    //                     _ -> Just <$> toZ3Sort fSort
    //       return (z3FName, z3FSort, 0)

    // convertDatatypes symbols (_:rest) = convertDatatypes symbols rest -- Polymorphic datatype, do not convert

    pub fn convert_datatypes(
        &mut self,
        symbols: &HashMap<Id, RSchema>,
        mut datatypes: Vec<(Id, DatatypeDef)>,
    ) {
        if datatypes.is_empty() {
            return;
        }

        let (
            dt_name,
            DatatypeDef {
                constructors: ctors,
                ..
            },
        ) = datatypes.remove(0);

        if self.stored_datatypes.contains(&dt_name) {
            return;
        }

        let dt_symb = z3::Symbol::String(dt_name.to_string());
        let mut z3_dt = z3::DatatypeBuilder::new(self.ctx(), dt_symb);
        // let z3_ctors = ctors
        //     .iter()
        //     .map(|ctor| self.convert_ctor(symbols, &dt_name, &datatypes, ctor.clone()))
        //     .collect();
        for ctor in ctors {
            let (name, args) = self.convert_ctor(symbols, &dt_name, &datatypes, ctor);
            z3_dt = z3_dt.variant(name, args);
        }

        let z3_dt = z3_dt.finish();

        self.sorts
            .insert(Sort::Data(dt_name.clone(), vec![]), z3_dt.sort);
        self.stored_datatypes.insert(dt_name);
    }

    fn convert_ctor(
        &mut self,
        symbols: &HashMap<Id, RSchema>,
        dt_name: &Id,
        rest: &[(Id, DatatypeDef)],
        ctor: Id,
    ) -> (&'ctx str, Vec<(&'ctx str, z3::DatatypeAccessor<'ctx>)>) {
        // let z3_cname = z3::Symbol::String(ctor.to_string());
        let args = symbols.get(&ctor).unwrap().to_monotype().clone().all_args();
        let z3_args = args
            .into_iter()
            .map(|arg| self.convert_field(symbols, dt_name, rest, arg))
            .collect::<Vec<_>>();

        (ctor.into_static_str(), z3_args)
    }

    fn convert_field(
        &mut self,
        symbols: &HashMap<Id, RSchema>,
        dt_name: &Id,
        rest: &[(Id, DatatypeDef)],
        field: Formula,
    ) -> (&'ctx str, z3::DatatypeAccessor<'ctx>) {
        match field {
            Formula::Var(f_sort, f_name) => {
                // let z3_fname = z3::Symbol::String(f_name.to_string());
                let z3_fsort = match f_sort {
                    Sort::Data(ref dt_name_prime, ref xs) if xs.is_empty() => {
                        if dt_name_prime == dt_name {
                            None
                        } else {
                            match rest
                                .iter()
                                .find(|(dt_name_prime, _)| dt_name_prime == dt_name)
                            {
                                None => Some(f_sort.to_z3_sort(self)),
                                Some((_, dt_def)) => {
                                    self.convert_datatypes(
                                        symbols,
                                        vec![(dt_name_prime.clone(), dt_def.clone())],
                                    );

                                    Some(f_sort.to_z3_sort(self))
                                }
                            }
                        }
                    }
                    _ => Some(f_sort.to_z3_sort(self)),
                };

                (
                    f_name.into_static_str(),
                    z3::DatatypeAccessor::Sort(z3_fsort.unwrap()),
                )
            }
            _ => panic!("Expected a variable, found {field}"),
        }
    }

    // -- | Get the literal in the auxiliary solver that corresponds to a given literal in the main solver
    // litToAux :: AST -> Z3State AST
    // litToAux lit = do
    //   fml <- uses controlLiterals (Bimap.!> lit)
    //   uses controlLiteralsAux (Bimap.! fml)

    /// Get the interal in the auxiliary solver that corresponds to a given literal in the main solver
    pub fn lit_to_aux(&self, lit: &ast::Dynamic<'ctx>) -> &ast::Dynamic<'ctx> {
        let fml = self.control_literals.get_by_right(lit).unwrap();

        self.control_literals_aux.get_by_left(fml).unwrap()
    }

    // -- | Get the literal in the main solver that corresponds to a given literal in the auxiliary solver
    // litFromAux :: AST -> Z3State AST
    // litFromAux lit = do
    //   fml <- uses controlLiteralsAux (Bimap.!> lit)
    //   uses controlLiterals (Bimap.! fml)

    /// Get the literal in the main solver that corresponds to a given literal in the auxiliary solver
    pub fn lit_from_aux(&self, lit: &ast::Dynamic<'ctx>) -> &ast::Dynamic<'ctx> {
        let fml = self.control_literals_aux.get_by_right(lit).unwrap();

        self.control_literals.get_by_left(fml).unwrap()
    }

    // -- | 'getAllMUSs' @assumption mustHave fmls@ : find all minimal unsatisfiable subsets of @fmls@ with @mustHave@, which contain @mustHave@, assuming @assumption@
    // -- (implements Marco algorithm by Mark H. Liffiton et al.)
    // getAllMUSs :: Formula -> Formula -> [Formula] -> Z3State [[Formula]]
    // getAllMUSs assumption mustHave fmls = do
    //   push
    //   withAuxSolver push

    //   let allFmls = mustHave : fmls
    //   (controlLits, controlLitsAux) <- unzip <$> mapM getControlLits allFmls

    //   -- traceShow (text "getAllMUSs" $+$ text "assumption:" <+> pretty assumption $+$ text "must have:" <+> pretty mustHave $+$ text "fmls:" <+> pretty fmls) $ return ()
    //   fmlToAST assumption >>= assert
    //   condAssumptions <- mapM fmlToAST allFmls >>= zipWithM mkImplies controlLits
    //   mapM_ assert $ condAssumptions
    //   withAuxSolver $ assert $ head controlLitsAux

    //   res <- getAllMUSs' controlLitsAux (head controlLits) []
    //   withAuxSolver $ pop 1
    //   pop 1
    //   return res

    //   where
    //     getControlLits fml = do
    //       litMb <- uses controlLiterals (Bimap.lookup fml)
    //       case litMb of
    //         Just lit -> do
    //           litAux <- uses controlLiteralsAux (Bimap.! fml)
    //           return (lit, litAux)
    //         Nothing -> do
    //           bool <- toZ3Sort BoolS
    //           boolAux <- fromJust <$> use boolSortAux
    //           name <- ((++ "lit") . show . Bimap.size) <$> use controlLiterals
    //           lit <- mkStringSymbol name >>= flip mkConst bool
    //           litAux <- withAuxSolver $ mkStringSymbol name >>= flip mkConst boolAux
    //           controlLiterals %= Bimap.insert fml lit
    //           controlLiteralsAux %= Bimap.insert fml litAux
    //           return (lit, litAux)

    // getAllMUSs' controlLitsAux mustHave cores = do
    //   seedMb <- getNextSeed
    //   case seedMb of
    //     Nothing -> return cores -- No uncovered subsets left, return the cores accumulated so far
    //     Just s -> do
    //       (seed, rest) <- bothM (mapM litFromAux) s
    //       mapM litToFml seed >>= debugOutput "Seed"
    //       res <- checkAssumptions seed  -- Check if seed is satisfiable
    //       case res of
    //         Unsat -> do                 -- Unsatisfiable: extract MUS
    //           mus <- getUnsatCore >>= minimize
    //           blockUp mus
    //           unsatFmls <- mapM litToFml (delete mustHave mus)
    //           if mustHave `elem` mus
    //             then do
    //                   debugOutput "MUS" unsatFmls
    //                   getAllMUSs' controlLitsAux mustHave (unsatFmls : cores)
    //             else do
    //                   debugOutput "MUSeless" unsatFmls
    //                   getAllMUSs' controlLitsAux mustHave cores
    //         _ -> do
    //           mss <- maximize seed rest  -- Satisfiable: expand to MSS
    //           blockDown mss
    //           mapM litToFml mss >>= debugOutput "MSS"
    //           getAllMUSs' controlLitsAux mustHave cores
    //         -- _ -> do
    //           -- fmls <- mapM litToFml seed
    //           -- error $ unwords $ ["getAllMUSs: Z3 returned Unknown for"] ++ map show fmls

    //   where
    //     -- | Get the formula mapped to a given control literal in the main solver
    //     litToFml = uses controlLiterals . flip (Bimap.!>)

    //     -- | Get an unexplored subset of control literals inside the auxiliary solver
    //     getNextSeed = withAuxSolver $ do
    //       (res, modelMb) <- getModel
    //       case res of
    //         Unsat -> return Nothing -- No unexplored subsets left
    //         Sat -> Just <$> partitionM (getCtrlLitModel True (fromJust modelMb)) controlLitsAux -- Found unexplored subset: partition @controlLitsAux@ according to the model

    //     -- | Extract the Boolean value for literal @lit@ from the model @m@ with default @bias@
    //     getCtrlLitModel bias m lit = do
    //       resMb <- fromJust <$> eval m lit >>= getBoolValue
    //       case resMb of
    //         Nothing -> return bias
    //         Just b -> return b

    //     -- | Mark all supersets of @mus@ explored
    //     blockUp mus = withAuxSolver $ mapM (litToAux >=> mkNot) mus >>= mkOr >>= assert

    //     -- | Mark all subsets of @mss@ explored
    //     blockDown mss = withAuxSolver $ do
    //       mss' <- mapM litToAux mss
    //       let rest = controlLitsAux \\ mss'
    //       (if null rest then mkFalse else mkOr rest) >>= assert

    //     -- | Shrink unsatisfiable set @lits@ to some MUS
    //     minimize lits = local $ minimize' [] lits
    //     minimize' checked [] = return checked
    //     minimize' checked (lit:lits) = do
    //       res <- checkAssumptions lits
    //       case res of
    //         Unsat -> minimize' checked lits -- lit can be omitted
    //         _ -> assert lit >> minimize' (lit:checked) lits -- lit required for UNSAT: leave it in the minimal core

    //     -- | Grow satisfiable set @checked@ with literals from @rest@ to some MSS
    //     maximize checked rest = local $ mapM_ assert checked >> maximize' checked rest
    //     maximize' checked [] = return checked -- checked includes all literals and thus must be maximal
    //     maximize' checked rest = do
    //       mkOr rest >>= assert
    //       (res, modelMb) <- getModel
    //       case res of
    //         Unsat -> return checked -- cannot add any literals, checked is maximal
    //         _ -> do -- found some literals to add; fix them and continue
    //           (setRest, unsetRest) <- partitionM (getCtrlLitModel True (fromJust modelMb)) rest
    //           mapM_ assert setRest
    //           maximize' (checked ++ setRest) unsetRest

    //     debugOutput label fmls = debug 2 (text label <+> pretty fmls) $ return ()

    /// Find all minimal unsatisfiable subsets of `fmls` with `must_have`, which contain `must_have`, assuming `assumption`
    /// (implements Marco algorithm by Mark H. Liffiton et al.)
    pub fn get_all_muss(
        &mut self,
        assumption: Formula,
        must_have: Formula,
        fmls: Vec<Formula>,
    ) -> Vec<Vec<Formula>> {
        self.env.solver.push();
        self.aux_env.solver.push();

        let all_fmls = iter::once(must_have.clone()).chain(fmls).collect_vec();
        let (control_lits, control_lits_aux): (Vec<_>, Vec<_>) = all_fmls
            .iter()
            .map(|fml| self.get_control_lits(fml))
            .unzip();

        self.env
            .solver
            .assert(&assumption.to_ast(self).as_bool().unwrap());

        let cond_assumptions = all_fmls
            .into_iter()
            .map(|fml| fml.to_ast(self))
            .zip(control_lits.iter())
            .map(|(fml, lit)| fml.as_bool().unwrap().implies(&lit.as_bool().unwrap()))
            .collect::<Vec<_>>();

        for assumption in cond_assumptions {
            self.env.solver.assert(&assumption);
        }

        self.aux_env
            .solver
            .assert(&control_lits_aux[0].as_bool().unwrap());

        let res = self.get_all_muss_(control_lits_aux, control_lits[0].clone(), vec![]);

        self.aux_env.solver.pop(1);
        self.env.solver.pop(1);

        res
    }

    fn get_control_lits(&mut self, fml: &Formula) -> (ast::Dynamic<'ctx>, ast::Dynamic<'ctx>) {
        let lit_mb = self.control_literals.get_by_left(&fml);

        match lit_mb {
            Some(lit) => {
                let lit_aux = self.control_literals_aux.get_by_left(&fml).unwrap();

                (lit.clone(), lit_aux.clone())
            }
            None => {
                let name = z3::Symbol::String(format!("lit{}", self.control_literals.len()));
                let lit =
                    z3::ast::Dynamic::from(z3::ast::Bool::new_const(self.ctx(), name.clone()));
                let lit_aux =
                    z3::ast::Dynamic::from(z3::ast::Bool::new_const(self.aux_ctx(), name));

                self.control_literals.insert(fml.clone(), lit.clone());
                self.control_literals_aux
                    .insert(fml.clone(), lit_aux.clone());

                (lit, lit_aux)
            }
        }
    }

    fn get_all_muss_(
        &self,
        control_lits_aux: Vec<z3::ast::Dynamic<'ctx>>,
        must_have: z3::ast::Dynamic<'ctx>,
        cores: Vec<Vec<Formula>>,
    ) -> Vec<Vec<Formula>> {
        let seed_mb = self.get_next_seed(&control_lits_aux);

        match seed_mb {
            None => cores,
            Some((seed, rest)) => {
                let (seed, rest) = (
                    seed.iter().map(|lit| self.lit_from_aux(lit)).collect_vec(),
                    rest.iter().map(|lit| self.lit_from_aux(lit)).collect_vec(),
                );

                self.debug_output(
                    "Seed",
                    seed.iter().map(|lit| self.lit_to_fml(lit)).collect(),
                );

                let res = self.env.solver.check_assumptions(
                    &seed
                        .iter()
                        .map(|s| s.as_bool().unwrap())
                        .collect::<Box<[_]>>(),
                );

                match res {
                    z3::SatResult::Unsat => {
                        let mus = self.minimize(self.env.solver.get_unsat_core());
                        self.block_up(&mus);

                        let unsat_fmls = mus
                            .iter()
                            .filter(|lit| **lit != must_have)
                            .map(|lit| self.lit_to_fml(lit))
                            .collect_vec();

                        if mus.contains(&must_have) {
                            self.debug_output("MUS", unsat_fmls.clone());

                            self.get_all_muss_(control_lits_aux, must_have, vec![unsat_fmls])
                        } else {
                            self.debug_output("MUSeless", unsat_fmls.clone());

                            self.get_all_muss_(control_lits_aux, must_have, cores)
                        }
                    }
                    _ => {
                        let mss = self.maximize(seed, rest);
                        self.block_down(&mss);

                        let mss_fmls = mss
                            .iter()
                            .map(|lit| self.lit_to_fml(lit))
                            .collect::<Vec<_>>();
                        self.debug_output("MSS", mss_fmls);

                        self.get_all_muss_(control_lits_aux, must_have, cores)
                    }
                }
            }
        }
    }

    /// Get the formula mapped to a given control literal in the main solver
    fn lit_to_fml(&self, lit: &z3::ast::Dynamic<'ctx>) -> Formula {
        self.control_literals.get_by_right(lit).unwrap().clone()
    }

    /// Get an unexplored subset of control literals inside the auxiliary solver
    fn get_next_seed<'a>(
        &self,
        control_lits_aux: &'a Vec<z3::ast::Dynamic<'ctx>>,
    ) -> Option<(
        Vec<&'a z3::ast::Dynamic<'ctx>>,
        Vec<&'a z3::ast::Dynamic<'ctx>>,
    )> {
        let res = self.aux_env.solver.check();

        match res {
            z3::SatResult::Unsat => None,
            z3::SatResult::Sat => {
                let model_mb = self.aux_env.solver.get_model().unwrap();

                Some(
                    control_lits_aux
                        .iter()
                        .partition(|lit| self.get_ctrl_lit_model(true, &model_mb, lit)),
                )
            }
            _ => panic!("getAllMUSs: Z3 returned Unknown for"),
        }
    }

    /// Extract the Boolean value for literal `lit` from the model `m` with default `bias`
    fn get_ctrl_lit_model(
        &self,
        bias: bool,
        m: &z3::Model<'ctx>,
        lit: &z3::ast::Dynamic<'ctx>,
    ) -> bool {
        let res_mb = m.eval(lit, true).unwrap().as_bool();

        match res_mb {
            None => bias,
            Some(b) => b.as_bool().unwrap(),
        }
    }

    /// Mark all supersets of `mus` explored
    fn block_up(&self, mus: &[z3::ast::Dynamic<'ctx>]) {
        self.env.solver.assert(&z3::ast::Bool::or(
            self.aux_ctx(),
            &mus.iter()
                .map(|lit| lit.as_bool().unwrap().not())
                .collect::<Box<[_]>>()
                .iter() // ..
                .collect::<Box<[_]>>(),
        ));
    }

    /// Mark all subsets of `mss` explored
    fn block_down(&self, mss: &[&z3::ast::Dynamic<'ctx>]) {
        let mss = mss
            .iter()
            .map(|lit| self.lit_to_aux(lit))
            .collect::<Vec<_>>();

        let rest = self
            .control_literals_aux
            .right_values()
            .filter(|lit| !mss.contains(lit))
            .collect::<Vec<_>>();

        if rest.is_empty() {
            self.aux_env
                .solver
                .assert(&z3::ast::Bool::from_bool(self.ctx(), false));
        } else {
            self.aux_env.solver.assert(&z3::ast::Bool::or(
                self.aux_ctx(),
                &rest
                    .iter()
                    .map(|lit| lit.as_bool().unwrap())
                    .collect::<Box<[_]>>()
                    .iter()
                    .collect::<Box<[_]>>(),
            ));
        }
    }

    /// Shrink unsatisfiable set `lits` to some MUS
    fn minimize(&self, lits: Vec<z3::ast::Bool<'ctx>>) -> Vec<z3::ast::Dynamic<'ctx>> {
        self.minimize_(vec![], lits)
    }

    fn minimize_(
        &self,
        checked: Vec<z3::ast::Dynamic<'ctx>>,
        lits: Vec<z3::ast::Bool<'ctx>>,
    ) -> Vec<z3::ast::Dynamic<'ctx>> {
        if lits.is_empty() {
            return checked;
        }

        let lit = &lits[0];
        let rest = lits[1..].to_vec();

        match self.env.solver.check_assumptions(&rest) {
            z3::SatResult::Unsat => self.minimize_(checked, rest),
            _ => {
                self.env.solver.assert(lit);
                self.minimize_(checked, rest)
            }
        }
    }

    /// Grow satisfiable set `checked` with literals from `rest` to some MSS
    fn maximize<'a>(
        &self,
        checked: Vec<&'a z3::ast::Dynamic<'ctx>>,
        rest: Vec<&'a z3::ast::Dynamic<'ctx>>,
    ) -> Vec<&'a z3::ast::Dynamic<'ctx>> {
        let mss = self.maximize_(checked, rest);

        for lit in &mss {
            self.env.solver.assert(&lit.as_bool().unwrap());
        }

        mss
    }

    fn maximize_<'a>(
        &self,
        mut checked: Vec<&'a z3::ast::Dynamic<'ctx>>,
        rest: Vec<&'a z3::ast::Dynamic<'ctx>>,
    ) -> Vec<&'a z3::ast::Dynamic<'ctx>> {
        if rest.is_empty() {
            return checked;
        }

        self.env.solver.assert(&z3::ast::Bool::or(
            self.ctx(),
            &rest
                .iter()
                .map(|lit| lit.as_bool().unwrap())
                .collect::<Box<[_]>>()
                .iter()
                .collect::<Box<[_]>>(),
        ));

        match self.env.solver.check() {
            z3::SatResult::Unsat => checked,
            _ => {
                let model = self.env.solver.get_model().unwrap();

                let (set_rest, unset_rest): (Vec<_>, Vec<_>) = rest
                    .into_iter()
                    .partition(|lit| self.get_ctrl_lit_model(true, &model, lit));

                for lit in &set_rest {
                    self.env.solver.assert(&lit.as_bool().unwrap());
                }

                checked.extend(set_rest);

                self.maximize_(checked, unset_rest)
            }
        }
    }

    pub fn debug_output(&self, label: &str, fmls: Vec<Formula>) {
        log::debug!("{label} {fmls:?}");
    }
}

#[derive(Debug)]
pub struct Z3Env<'ctx> {
    pub solver: z3::Solver<'ctx>,
    pub context: z3::Context,
}

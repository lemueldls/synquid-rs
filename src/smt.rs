//! Z3 backend (mirror of `Synquid.Z3`).
//!
//! The Haskell reference threads a `StateT Z3Data IO` monad with two Z3
//! environments (main and auxiliary solver, each with its own context). The
//! `z3` crate (0.20.2) instead uses one implicit thread-local context shared
//! by all objects, so this module holds two `Solver`s in that single context.
//! This is equivalent for the control-literals scheme: main and auxiliary
//! solvers never exchange ASTs; only *formula* identities travel across,
//! through `ControlMap` (`Bimap<Formula, u64>`), which is context-independent.
//!
//! Scope semantics mirror the reference exactly:
//! - `isSat` uses `local` = `push`/`pop` around `assert >> check`,
//!   so the assertion does **not** persist across calls.
//! - `getAllMUSs` wraps the whole MARCO loop in one `push`/`pop`
//!   per solver; `minimize`/`maximize` each run inside their
//!   own `local`.
//! - The `vars`/`functions`/`sorts` caches and control-literal tables are
//!   persistent (never rolled back), matching the reference's `Z3Data` maps.
//!
//! TODO (M9): error reporting should route through `ErrorMessage`; Z3 calls are
//! currently infallible (mirroring the reference's `error` on `Unknown`).

use std::collections::{BTreeMap, BTreeSet, HashMap};

use bimap::BiBTreeMap;

/// Backwards-compatible alias keeping the plan's naming (`BiMap`).
type BiMap<L, R> = BiBTreeMap<L, R>;
use z3::{
    ast::{self, Ast, Set},
    DatatypeAccessor, DatatypeBuilder, FuncDecl, Model, SatResult, Solver, Sort as ZSort,
};

use crate::{
    logic::{and_clean, fnot, implies, BinOp, Formula, Sort, UnOp},
    program::{all_symbols, DatatypeDef, Environment},
    types::{all_args, to_monotype, RSchema},
    util::Id,
};

/// Z3 AST in a generic (sort-erased) form; the reference uses a single `AST`.
type ZAst = ast::Dynamic;

/// Split `xs` according to a predicate, preserving order (mirrors
/// `Data.List.partition` used by `partitionM` in the reference).
fn partition<T>(xs: &[T], keep: impl Fn(&T) -> bool) -> (Vec<T>, Vec<T>)
where
    T: Clone,
{
    let mut yes = Vec::new();
    let mut no = Vec::new();
    for x in xs {
        if keep(x) {
            yes.push(x.clone());
        } else {
            no.push(x.clone());
        }
    }
    (yes, no)
}

/// Control literals for MARCO. The reference stores `Bimap Formula AST` for
/// each of the two solvers; the crate's ASTs are not hashable, so numeric
/// ids (`u64`) cross-reference `Bimap<Formula, u64>` with
/// `HashMap<u64, Bool>`. Main and auxiliary literals share the same id.
#[derive(Default)]
struct ControlMap {
    main: BiMap<Formula, u64>,
    aux: BiMap<Formula, u64>,
    main_asts: HashMap<u64, ast::Bool>,
    aux_asts: HashMap<u64, ast::Bool>,
    count: u64,
}

impl ControlMap {
    fn insert(&mut self, fml: Formula, main_lit: ast::Bool, aux_lit: ast::Bool) -> u64 {
        let id = self.count;
        self.count += 1;
        self.main.insert(fml.clone(), id);
        self.aux.insert(fml, id);
        self.main_asts.insert(id, main_lit);
        self.aux_asts.insert(id, aux_lit);
        id
    }
}

/// SMT runtime: two Z3 solvers plus the reference's `Z3Data` tables.
pub struct Z3Runtime {
    main_solver: Solver,
    aux_solver: Solver,
    /// Mapping from Synquid sorts to Z3 sorts.
    sorts: BTreeMap<Sort, ZSort>,
    /// AST nodes for scalar variables.
    vars: HashMap<String, ZAst>,
    /// Function declarations for measures, predicates, and constructors.
    functions: HashMap<String, FuncDecl>,
    /// Constructors of datatypes stored as Z3 datatypes: datatype name →
    /// constructor name → declaration.
    datatype_constructors: HashMap<Id, HashMap<Id, FuncDecl>>,
    /// Datatypes mapped directly to Z3 datatypes (monomorphic only).
    stored_datatypes: BTreeSet<Id>,
    /// Control literals for computing unsat cores.
    controls: ControlMap,
    /// Cumulative time spent inside Z3 calls, in microseconds.
    total_us: u128,
    /// Number of `is_sat` calls.
    sat_calls: u64,
    /// Number of `get_all_mus` calls.
    mus_calls: u64,
}

impl Z3Runtime {
    /// Cumulative time spent inside Z3 calls, in microseconds.
    #[must_use]
    pub fn total_us(&self) -> u128 {
        self.total_us
    }
    /// Number of `is_sat` calls.
    #[must_use]
    pub fn sat_calls(&self) -> u64 {
        self.sat_calls
    }
    /// Number of `get_all_mus` calls.
    #[must_use]
    pub fn mus_calls(&self) -> u64 {
        self.mus_calls
    }
    /// Create a runtime and populate it with the definitions of `env`.
    ///
    /// Mirrors `MonadSMT.initSolver`: disables MBQI on the main
    /// solver, then converts all monomorphic datatypes.
    #[must_use]
    pub fn new(env: &Environment) -> Self {
        let mut params = z3::Params::new();
        params.set_bool("mbqi", false);
        let main_solver = Solver::new();
        main_solver.set_params(&params);
        let aux_solver = Solver::new();

        let mut runtime = Z3Runtime {
            main_solver,
            aux_solver,
            sorts: BTreeMap::new(),
            vars: HashMap::new(),
            functions: HashMap::new(),
            datatype_constructors: HashMap::new(),
            stored_datatypes: BTreeSet::new(),
            controls: ControlMap::default(),
            total_us: 0,
            sat_calls: 0,
            mus_calls: 0,
        };
        runtime.convert_datatypes(&all_symbols(env), &env.datatypes);
        runtime
    }

    /// `isSat`: is `fml` satisfiable? `Unknown` counts as `Sat`.
    pub fn is_sat(&mut self, fml: &Formula) -> bool {
        self.sat_calls += 1;
        let t = std::time::Instant::now();
        let ast = self.fml_to_ast_bool(fml);
        self.main_solver.push();
        self.main_solver.assert(&ast);
        let res = self.main_solver.check();
        self.main_solver.pop(1);
        self.total_us += t.elapsed().as_micros();
        res != SatResult::Unsat
    }

    /// `getAllMUSs`: all minimal unsatisfiable subsets of
    /// `fmls` that contain `must_have`, assuming `assumption`.
    ///
    /// Note: the returned cores are in discovery order and contain the
    /// *formulas* of `fmls` (excluding `must_have`), like the reference.
    pub fn get_all_mus(
        &mut self,
        assumption: &Formula,
        must_have: &Formula,
        fmls: &[Formula],
    ) -> Vec<Vec<Formula>> {
        self.mus_calls += 1;
        let t = std::time::Instant::now();
        self.main_solver.push();
        self.aux_solver.push();

        let mut all_fmls = vec![must_have.clone()];
        all_fmls.extend_from_slice(fmls);
        let control_lits: Vec<u64> = all_fmls
            .iter()
            .map(|fml| self.get_control_lit(fml.clone()))
            .collect();
        let must_have_lit = control_lits[0];

        let assumption_ast = self.fml_to_ast_bool(assumption);
        self.main_solver.assert(&assumption_ast);
        for (&lit, fml) in control_lits.iter().zip(&all_fmls) {
            let fml_ast = self.fml_to_ast_bool(fml);
            let assert = self.control_lit_main(lit).implies(&fml_ast);
            self.main_solver.assert(&assert);
        }
        self.aux_solver.assert(self.control_lit_aux(must_have_lit));

        let result = self.get_all_mus_loop(&control_lits, must_have_lit, Vec::new());

        self.aux_solver.pop(1);
        self.main_solver.pop(1);
        self.total_us += t.elapsed().as_micros();
        result
    }

    /// `getAllMUSs'`: the MARCO main loop.
    fn get_all_mus_loop(
        &self,
        control_lits_aux: &[u64],
        must_have: u64,
        mut cores: Vec<Vec<Formula>>,
    ) -> Vec<Vec<Formula>> {
        loop {
            let Some((seed, rest)) = self.get_next_seed(control_lits_aux) else {
                return cores;
            };
            let seed_asts: Vec<ast::Bool> = seed
                .iter()
                .map(|&lit| self.control_lit_main(lit).clone())
                .collect();
            if self.main_solver.check_assumptions(&seed_asts) == SatResult::Unsat {
                let mus = self.minimize(&self.main_solver.get_unsat_core());
                self.block_up(&mus);
                let unsat_fmls: Vec<Formula> = mus
                    .iter()
                    .filter(|&&lit| lit != must_have)
                    .map(|&lit| self.lit_to_fml(lit))
                    .collect();
                if mus.contains(&must_have) {
                    cores.push(unsat_fmls);
                }
            } else {
                let mss = self.maximize(&seed, &rest);
                self.block_down(&mss, control_lits_aux);
            }
        }
    }

    /// `getNextSeed`: an unexplored subset of the control
    /// literals, from a model of the auxiliary solver; `None` means the
    /// search space is exhausted. Returns the (seed, rest) split (literals
    /// selected true / false by the model, biased towards true).
    fn get_next_seed(&self, control_lits_aux: &[u64]) -> Option<(Vec<u64>, Vec<u64>)> {
        let (res, model_mb) = (self.aux_solver.check(), self.aux_solver.get_model());
        match res {
            SatResult::Unsat => None,
            SatResult::Sat => {
                let model = model_mb.expect("getNextSeed: sat but no model");
                let (seed, rest) = partition(control_lits_aux, |&lit| {
                    self.get_ctrl_lit_model(true, &model, lit)
                });
                Some((seed, rest))
            }
            SatResult::Unknown => panic!("getNextSeed: Z3 returned Unknown"),
        }
    }

    /// `getCtrlLitModel`: the value of auxiliary literal `lit`
    /// in `model`, defaulting to `bias` when unconstrained.
    fn get_ctrl_lit_model(&self, bias: bool, model: &Model, lit: u64) -> bool {
        let value = model
            .eval(self.control_lit_aux(lit), true)
            .and_then(|b| b.as_bool());
        value.unwrap_or(bias)
    }

    /// `blockUp`: mark all supersets of the core as explored by
    /// asserting in the auxiliary solver that not all of its literals hold.
    fn block_up(&self, mus: &[u64]) {
        let nots: Vec<ast::Bool> = mus
            .iter()
            .map(|&lit| self.control_lit_aux(lit).not())
            .collect();
        self.aux_solver.assert(ast::Bool::or(&nots));
    }

    /// `blockDown`: mark all subsets of the MSS as explored by
    /// asserting in the auxiliary solver that some literal outside it holds
    /// (or `false` when nothing is left outside).
    fn block_down(&self, mss: &[u64], control_lits_aux: &[u64]) {
        let mss_set: BTreeSet<u64> = mss.iter().copied().collect();
        let rest: Vec<ast::Bool> = control_lits_aux
            .iter()
            .filter(|lit| !mss_set.contains(lit))
            .map(|&lit| self.control_lit_aux(lit).clone())
            .collect();
        if rest.is_empty() {
            self.aux_solver.assert(ast::Bool::from_bool(false));
        } else {
            self.aux_solver.assert(ast::Bool::or(&rest));
        }
    }

    /// `minimize`: greedily shrink an unsat set to a minimal
    /// unsat subset, inside its own `local` (push/pop): the required
    /// literals are asserted within that scope only.
    fn minimize(&self, unsat_core: &[ast::Bool]) -> Vec<u64> {
        self.main_solver.push();
        let mut rest: Vec<u64> = unsat_core.iter().map(|lit| self.lit_id_of(lit)).collect();
        let mut checked: Vec<u64> = Vec::new();
        while let Some(lit) = rest.first().copied() {
            rest.remove(0);
            let assumptions: Vec<ast::Bool> = rest
                .iter()
                .map(|&id| self.control_lit_main(id).clone())
                .collect();
            if self.main_solver.check_assumptions(&assumptions) == SatResult::Unsat {
                // lit can be omitted: drop it.
            } else {
                self.main_solver.assert(self.control_lit_main(lit));
                checked.push(lit);
            }
        }
        self.main_solver.pop(1);
        checked
    }

    /// `maximize`: grow a satisfiable seed to a maximal
    /// satisfiable subset, inside its own `local` (push/pop).
    fn maximize(&self, checked0: &[u64], rest0: &[u64]) -> Vec<u64> {
        self.main_solver.push();
        let mut checked: Vec<u64> = checked0.to_vec();
        let mut rest: Vec<u64> = rest0.to_vec();
        for &lit in &checked {
            self.main_solver.assert(self.control_lit_main(lit));
        }
        loop {
            if rest.is_empty() {
                break;
            }
            let or_rest: Vec<ast::Bool> = rest
                .iter()
                .map(|&id| self.control_lit_main(id).clone())
                .collect();
            self.main_solver.assert(ast::Bool::or(&or_rest));
            let (res, model_mb) = (self.main_solver.check(), self.main_solver.get_model());
            if res == SatResult::Unsat {
                break; // checked is maximal
            }
            let model = model_mb.expect("maximize: sat but no model");
            let (set_rest, unset_rest): (Vec<u64>, Vec<u64>) =
                partition(&rest, |&lit| self.get_main_lit_model(true, &model, lit));
            for &lit in &set_rest {
                self.main_solver.assert(self.control_lit_main(lit));
            }
            checked.extend(&set_rest);
            rest = unset_rest;
        }
        self.main_solver.pop(1);
        checked
    }

    /// Model value of a *main*-solver control literal (used by `maximize`).
    fn get_main_lit_model(&self, bias: bool, model: &Model, lit: u64) -> bool {
        let value = model
            .eval(self.control_lit_main(lit), true)
            .and_then(|b| b.as_bool());
        value.unwrap_or(bias)
    }

    /// `getControlLits`: the control literal for a formula,
    /// creating (and caching) it on first use.
    fn get_control_lit(&mut self, fml: Formula) -> u64 {
        if let Some(id) = self.controls.main.get_by_left(&fml).copied() {
            return id;
        }
        let name = format!("{}lit", self.controls.count);
        let main_lit = ast::Bool::new_const(name.as_str());
        let aux_lit = ast::Bool::new_const(name.as_str());
        self.controls.insert(fml, main_lit, aux_lit)
    }

    /// `litToFml`: the formula mapped to a control literal.
    fn lit_to_fml(&self, lit: u64) -> Formula {
        self.controls
            .main
            .get_by_right(&lit)
            .cloned()
            .unwrap_or_else(|| panic!("litToFml: no formula for literal {lit}"))
    }

    /// The main-solver AST for a control literal.
    fn control_lit_main(&self, lit: u64) -> &ast::Bool {
        &self.controls.main_asts[&lit]
    }

    /// The auxiliary-solver AST for a control literal.
    fn control_lit_aux(&self, lit: u64) -> &ast::Bool {
        &self.controls.aux_asts[&lit]
    }

    /// The id of a main-solver literal AST (as returned by `get_unsat_core`).
    fn lit_id_of(&self, lit: &ast::Bool) -> u64 {
        self.controls
            .main_asts
            .iter()
            .find_map(|(&id, ast)| ast.ast_eq(lit).then_some(id))
            .expect("litIdOf: literal not found in control map")
    }

    /// `convertDatatypes`: build Z3 datatypes for monomorphic
    /// `DatatypeDef`s, in sorted (by name) order like `Map.toList`.
    fn convert_datatypes(
        &mut self,
        symbols: &BTreeMap<Id, RSchema>,
        datatypes: &BTreeMap<Id, DatatypeDef>,
    ) {
        for (dt_name, dt_def) in datatypes {
            if dt_def.type_params.is_empty() && !dt_def.constructors.is_empty() {
                self.convert_datatype(dt_name, dt_def, symbols, datatypes);
            }
        }
    }

    /// Convert a single monomorphic datatype, unless already stored
    /// (it may have been processed earlier as a dependency).
    fn convert_datatype(
        &mut self,
        dt_name: &Id,
        dt_def: &DatatypeDef,
        symbols: &BTreeMap<Id, RSchema>,
        datatypes: &BTreeMap<Id, DatatypeDef>,
    ) {
        if self.stored_datatypes.contains(dt_name) {
            return;
        }
        let mut builder = DatatypeBuilder::new(dt_name.clone());
        for ctor_name in &dt_def.constructors {
            let field_sorts: Vec<(Id, Sort)> = all_args(&to_monotype(&symbols[ctor_name]))
                .into_iter()
                .map(|arg| match arg {
                    Formula::Var(s, name) => (name, *s),
                    _ => panic!("convertCtor: constructor argument is not a variable"),
                })
                .collect();
            let mut fields: Vec<(&str, DatatypeAccessor)> = Vec::with_capacity(field_sorts.len());
            for (name, sort) in &field_sorts {
                let accessor = self.convert_field(sort, name, dt_name, symbols, datatypes);
                fields.push((name.as_str(), accessor));
            }
            builder = builder.variant(ctor_name, fields);
        }
        let datatype_sort = builder.finish();
        self.sorts
            .insert(Sort::DataS(dt_name.clone(), Vec::new()), datatype_sort.sort);
        let constructors = datatype_sort
            .variants
            .into_iter()
            .map(|variant| (variant.constructor.name(), variant.constructor))
            .collect();
        self.datatype_constructors
            .insert(dt_name.clone(), constructors);
        self.stored_datatypes.insert(dt_name.clone());
    }

    /// `convertField`: a constructor field's accessor
    /// description. Recursive references to `dt_name` use the builder's
    /// index; an eligible not-yet-converted dependency is converted first;
    /// everything else is a plain Z3 sort reference (polymorphic datatypes
    /// stay `Int`).
    fn convert_field(
        &mut self,
        f_sort: &Sort,
        _f_name: &Id,
        dt_name: &Id,
        symbols: &BTreeMap<Id, RSchema>,
        datatypes: &BTreeMap<Id, DatatypeDef>,
    ) -> DatatypeAccessor {
        match f_sort {
            Sort::DataS(dt_name2, args) if args.is_empty() => {
                if dt_name2 == dt_name {
                    return DatatypeAccessor::datatype(dt_name.clone());
                }
                if !self.stored_datatypes.contains(dt_name2)
                    && let Some(dt_def) = datatypes.get(dt_name2)
                {
                    self.convert_datatype(dt_name2, dt_def, symbols, datatypes);
                }
                DatatypeAccessor::sort(self.z3_sort_of(f_sort))
            }
            _ => DatatypeAccessor::sort(self.z3_sort_of(f_sort)),
        }
    }

    /// `toZ3Sort`: Z3 sort for a Synquid sort, cached in
    /// `sorts`. Variables and polymorphic datatypes become `Int`;
    /// monomorphic datatypes already converted are looked up in the cache.
    fn z3_sort_of(&mut self, s: &Sort) -> ZSort {
        if let Some(z3s) = self.sorts.get(s) {
            return z3s.clone();
        }
        let sorted = match s {
            Sort::BoolS => ZSort::bool(),
            Sort::IntS => ZSort::int(),
            Sort::VarS(_) => ZSort::int(),
            Sort::DataS(..) => ZSort::int(),
            Sort::SetS(el) => ZSort::set(&self.z3_sort_of(el)),
            Sort::AnyS => ZSort::int(),
        };
        self.sorts.insert(s.clone(), sorted.clone());
        sorted
    }

    /// `asZ3Sort`: the sort as Z3 sees it (used for name
    /// mangling only).
    fn as_z3_sort(s: &Sort) -> Sort {
        match s {
            Sort::VarS(_) => Sort::IntS,
            Sort::DataS(_, args) if !args.is_empty() => Sort::IntS,
            Sort::SetS(el) => Sort::SetS(Box::new(Self::as_z3_sort(el))),
            s => s.clone(),
        }
    }

    /// `fmlToAST`: formula to Z3 AST, after `simplify`.
    pub fn fml_to_ast_bool(&mut self, fml: &Formula) -> ast::Bool {
        let ast = self.z3_ast_of(&Self::simplify(fml));
        ast.as_bool()
            .unwrap_or_else(|| panic!("fmlToAST: expected a boolean AST, got {fml:?}"))
    }

    /// `simplify`, mirroring its sort-based rewriting of
    /// comparisons on booleans.
    #[must_use]
    fn simplify(expr: &Formula) -> Formula {
        match expr {
            Formula::SetLit(el, xs) => {
                Formula::SetLit(el.clone(), xs.iter().map(Self::simplify).collect())
            }
            Formula::Unary(op, e) => Formula::Unary(*op, Box::new(Self::simplify(e))),
            Formula::Binary(op, e1, e2) => {
                let e1s = Self::simplify(e1);
                let e2s = Self::simplify(e2);
                if crate::logic::sort_of(&e1s) == Sort::BoolS {
                    match op {
                        BinOp::Le => implies(e1s, e2s),
                        BinOp::Ge => implies(e2s, e1s),
                        BinOp::Lt => and_clean(fnot(e1s), e2s),
                        BinOp::Gt => and_clean(fnot(e2s), e1s),
                        _ => Formula::Binary(*op, Box::new(e1s), Box::new(e2s)),
                    }
                } else {
                    Formula::Binary(*op, Box::new(e1s), Box::new(e2s))
                }
            }
            Formula::Ite(e0, e1, e2) => Formula::Ite(
                Box::new(Self::simplify(e0)),
                Box::new(Self::simplify(e1)),
                Box::new(Self::simplify(e2)),
            ),
            Formula::Pred(s, name, args) => Formula::Pred(
                s.clone(),
                name.clone(),
                args.iter().map(Self::simplify).collect(),
            ),
            Formula::Cons(s, name, args) => Formula::Cons(
                s.clone(),
                name.clone(),
                args.iter().map(Self::simplify).collect(),
            ),
            Formula::All(v, e) => {
                Formula::All(Box::new(Self::simplify(v)), Box::new(Self::simplify(e)))
            }
            _ => expr.clone(),
        }
    }

    /// `toAST`: formula to Z3 AST.
    fn z3_ast_of(&mut self, expr: &Formula) -> ZAst {
        match expr {
            Formula::BoolLit(b) => ZAst::from_ast(&ast::Bool::from_bool(*b)),
            Formula::IntLit(i) => ZAst::from_ast(&ast::Int::from_i64(*i)),
            Formula::SetLit(el, xs) => self.set_literal(el, xs),
            Formula::Var(s, name) => self.var(s, name),
            Formula::Unknown(_, name) => {
                panic!("toAST: encountered a second-order unknown {name}")
            }
            Formula::Unary(op, e) => {
                let e_ast = self.z3_ast_of(e);
                Self::un_op(*op, &e_ast)
            }
            Formula::Binary(op, e1, e2) => {
                let e1_ast = self.z3_ast_of(e1);
                let e2_ast = self.z3_ast_of(e2);
                if matches!(op, BinOp::And | BinOp::Or | BinOp::Implies | BinOp::Iff)
                    && (e1_ast.as_bool().is_none() || e2_ast.as_bool().is_none())
                {
                    panic!("toAST: non-bool operand in {op:?} ({e1:?}, {e2:?})");
                }
                let res = Self::bin_op(*op, &e1_ast, &e2_ast);
                if matches!(
                    op,
                    BinOp::And | BinOp::Or | BinOp::Implies | BinOp::Iff | BinOp::Eq | BinOp::Neq
                ) && res.as_bool().is_none()
                {
                    panic!("toAST: bad boolean formula {expr:?}");
                }
                res
            }
            Formula::Ite(e0, e1, e2) => {
                let e0 = self.z3_ast_of(e0);
                let e0 = e0.as_bool().expect("toAST: ite condition is not a boolean");
                let then = self.z3_ast_of(e1);
                let els = self.z3_ast_of(e2);
                let ite = e0.ite(&then, &els);
                ZAst::from_ast(&ite)
            }
            Formula::Pred(s, name, args) => {
                let arg_sorts: Vec<Sort> = args.iter().map(crate::logic::sort_of).collect();
                let arg_asts: Vec<ZAst> = args.iter().map(|a| self.z3_ast_of(a)).collect();
                let decl = self.function(s, name, &arg_sorts);
                let arg_refs: Vec<&dyn Ast> = arg_asts.iter().map(|a| a as &dyn Ast).collect();
                decl.apply(&arg_refs)
            }
            Formula::Cons(s, name, args) => {
                let arg_sorts: Vec<Sort> = args.iter().map(crate::logic::sort_of).collect();
                let arg_asts: Vec<ZAst> = args.iter().map(|a| self.z3_ast_of(a)).collect();
                let decl = self.constructor(s, name, &arg_sorts);
                let arg_refs: Vec<&dyn Ast> = arg_asts.iter().map(|a| a as &dyn Ast).collect();
                decl.apply(&arg_refs)
            }
            Formula::All(v, e) => self.accum_all(&[(**v).clone()], e),
        }
    }

    /// `setLiteral`: `{x1, ..., xn}` as set addition.
    fn set_literal(&mut self, el: &Sort, xs: &[Formula]) -> ZAst {
        let el_sort = self.z3_sort_of(el);
        let mut set = Set::empty(&el_sort);
        for x in xs {
            set = set.add(&self.z3_ast_of(x));
        }
        ZAst::from_ast(&set)
    }

    /// `accumAll`: collect consecutive `All` binders and
    /// quantify with `mkForallConst []` (no patterns).
    fn accum_all(&mut self, xs: &[Formula], e: &Formula) -> ZAst {
        if let Formula::All(y, e) = e {
            let mut xs = xs.to_vec();
            xs.push((**y).clone());
            self.accum_all(&xs, e)
        } else {
            let bound_asts: Vec<ZAst> = xs.iter().map(|x| self.z3_ast_of(x)).collect();
            let bound_refs: Vec<&dyn Ast> = bound_asts.iter().map(|a| a as &dyn Ast).collect();
            let body = self.z3_ast_of(e);
            let body = body
                .as_bool()
                .expect("toAST: quantified body is not a boolean");
            let forall = ast::forall_const(&bound_refs, &[], &body);
            ZAst::from_ast(&forall)
        }
    }

    /// `unOp`.
    fn un_op(op: UnOp, e: &ZAst) -> ZAst {
        match op {
            UnOp::Neg => ZAst::from_ast(
                &e.as_int()
                    .expect("toAST: negating a non-integer")
                    .unary_minus(),
            ),
            UnOp::Not => ZAst::from_ast(&e.as_bool().expect("toAST: negating a non-boolean").not()),
        }
    }

    /// `binOp`.
    fn bin_op(op: BinOp, e1: &ZAst, e2: &ZAst) -> ZAst {
        match op {
            BinOp::Eq => ZAst::from_ast(&e1.eq(e2)),
            BinOp::Neq => ZAst::from_ast(&z3::ast::Dynamic::distinct(&[e1, e2])),
            BinOp::Gt => ZAst::from_ast(&Self::int_of(e1).gt(Self::int_of(e2))),
            BinOp::Lt => ZAst::from_ast(&Self::int_of(e1).lt(Self::int_of(e2))),
            BinOp::Le => ZAst::from_ast(&Self::int_of(e1).le(Self::int_of(e2))),
            BinOp::Ge => ZAst::from_ast(&Self::int_of(e1).ge(Self::int_of(e2))),
            BinOp::Times => ZAst::from_ast(&ast::Int::mul(&[Self::int_of(e1), Self::int_of(e2)])),
            BinOp::Plus => ZAst::from_ast(&ast::Int::add(&[Self::int_of(e1), Self::int_of(e2)])),
            BinOp::Minus => ZAst::from_ast(&ast::Int::sub(&[Self::int_of(e1), Self::int_of(e2)])),
            BinOp::And => ZAst::from_ast(&ast::Bool::and(&[Self::bool_of(e1), Self::bool_of(e2)])),
            BinOp::Or => ZAst::from_ast(&ast::Bool::or(&[Self::bool_of(e1), Self::bool_of(e2)])),
            BinOp::Implies => ZAst::from_ast(&Self::bool_of(e1).implies(Self::bool_of(e2))),
            BinOp::Iff => ZAst::from_ast(&Self::bool_of(e1).iff(Self::bool_of(e2))),
            BinOp::Union => {
                ZAst::from_ast(&ast::Set::set_union(&[Self::set_of(e1), Self::set_of(e2)]))
            }
            BinOp::Intersect => {
                ZAst::from_ast(&ast::Set::intersect(&[Self::set_of(e1), Self::set_of(e2)]))
            }
            BinOp::Diff => ZAst::from_ast(&Self::set_of(e1).difference(Self::set_of(e2))),
            BinOp::Member => ZAst::from_ast(&Self::set_of(e2).member(e1)),
            BinOp::Subset => ZAst::from_ast(&Self::set_of(e1).set_subset(Self::set_of(e2))),
        }
    }

    /// Downcast helper for integer operands.
    fn int_of(e: &ZAst) -> ast::Int {
        e.as_int().expect("toAST: expected an integer operand")
    }

    /// Downcast helper for boolean operands.
    fn bool_of(e: &ZAst) -> ast::Bool {
        e.as_bool().expect("toAST: expected a boolean operand")
    }

    /// Downcast helper for set operands.
    fn set_of(e: &ZAst) -> Set {
        Set::try_from(e.clone()).expect("toAST: expected a set operand")
    }

    /// `var`: lookup or create a variable with the mangled
    /// name `ident ++ show (asZ3Sort s)`.
    fn var(&mut self, s: &Sort, ident: &Id) -> ZAst {
        let name = format!("{ident}{}", Self::show_sort(&Self::as_z3_sort(s)));
        if let Some(v) = self.vars.get(&name) {
            return v.clone();
        }
        let z3s = self.z3_sort_of(s);
        let v = ZAst::new_const(name.as_str(), &z3s);
        self.vars.insert(name, v.clone());
        v
    }

    /// `function`: lookup or create a function declaration
    /// with the mangled name `name ++ concatMap (show . asZ3Sort) (resT :
    /// argTypes)`.
    fn function(&mut self, res_t: &Sort, name: &Id, arg_types: &[Sort]) -> &FuncDecl {
        let mut mangled = name.clone();
        mangled.push_str(&Self::show_sort(&Self::as_z3_sort(res_t)));
        for t in arg_types {
            mangled.push_str(&Self::show_sort(&Self::as_z3_sort(t)));
        }
        if !self.functions.contains_key(&mangled) {
            let arg_refs: Vec<ZSort> = arg_types.iter().map(|t| self.z3_sort_of(t)).collect();
            let arg_refs: Vec<&ZSort> = arg_refs.iter().collect();
            let res_sort = self.z3_sort_of(res_t);
            let decl = FuncDecl::new(mangled.as_str(), &arg_refs, &res_sort);
            self.functions.insert(mangled.clone(), decl);
        }
        &self.functions[&mangled]
    }

    /// `constructor`: the datatype constructor when the result
    /// sort is a stored monomorphic datatype, otherwise `function`.
    fn constructor(&mut self, res_t: &Sort, c_name: &Id, arg_types: &[Sort]) -> &FuncDecl {
        match res_t {
            Sort::DataS(dt_name, args) if args.is_empty() => {
                if self.stored_datatypes.contains(dt_name) {
                    return self.datatype_constructors[dt_name]
                        .get(c_name)
                        .unwrap_or_else(|| panic!("constructor: no constructor {c_name}"));
                }
                self.function(res_t, c_name, arg_types)
            }
            _ => self.function(res_t, c_name, arg_types),
        }
    }

    /// Haskell's derived `Show` for `Sort`, used by name mangling.
    fn show_sort(s: &Sort) -> String {
        match s {
            Sort::BoolS => "BoolS".to_string(),
            Sort::IntS => "IntS".to_string(),
            Sort::VarS(name) => format!("VarS \"{name}\""),
            Sort::DataS(name, args) => {
                format!(
                    "DataS \"{name}\" [{}]",
                    args.iter()
                        .map(Self::show_sort)
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            Sort::SetS(el) => format!("SetS {}", Self::show_sort(el)),
            Sort::AnyS => "AnyS".to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Z3Runtime;
    use crate::{
        logic::{
            and, and_clean, bool_var, eq, ffalse, fnot, ftrue, ge, int_lit, int_var, le, lt,
            Formula, Sort,
        },
        program::{add_constant, add_datatype, empty_env, DatatypeDef, Environment},
        types::{int, BaseType, TypeSkeleton},
    };

    fn cons(sort: Sort, name: &str, args: Vec<Formula>) -> Formula {
        Formula::Cons(Box::new(sort), name.to_string(), args)
    }

    fn int_list_env() -> Environment {
        let mut env = empty_env();
        let nil_name = "Nil".to_string();
        let cons_name = "Cons".to_string();
        let list_name = "IntList".to_string();
        env = add_datatype(
            &list_name,
            DatatypeDef {
                type_params: vec![],
                pred_params: vec![],
                pred_variances: vec![],
                constructors: vec![nil_name.clone(), cons_name.clone()],
                wf_metric: None,
            },
            &env,
        );
        let list_t = TypeSkeleton::ScalarT(BaseType::DatatypeT(list_name, vec![], vec![]), ftrue());
        env = add_constant(&nil_name, &list_t, &env);
        let cons_t = TypeSkeleton::FunctionT(
            "head".to_string(),
            Box::new(int(ftrue())),
            Box::new(TypeSkeleton::FunctionT(
                "tail".to_string(),
                Box::new(list_t.clone()),
                Box::new(list_t),
            )),
        );
        add_constant(&cons_name, &cons_t, &env)
    }

    fn list_sort() -> Sort {
        Sort::DataS("IntList".to_string(), vec![])
    }

    #[test]
    fn is_sat_basic() {
        let mut z3 = Z3Runtime::new(&empty_env());
        assert!(z3.is_sat(&ftrue()));
        assert!(!z3.is_sat(&ffalse()));
        assert!(z3.is_sat(&eq(int_var("x"), int_lit(0))));
        assert!(!z3.is_sat(&and(
            eq(int_var("x"), int_lit(0)),
            eq(int_var("x"), int_lit(1))
        )));
        assert!(z3.is_sat(&bool_var("b")));
        assert!(!z3.is_sat(&and(bool_var("b"), fnot(bool_var("b")))));
    }

    #[test]
    fn is_sat_quantified() {
        let mut z3 = Z3Runtime::new(&empty_env());
        let all_pos = Formula::All(
            Box::new(int_var("n")),
            Box::new(ge(int_var("n"), int_lit(0))),
        );
        assert!(z3.is_sat(&all_pos));
        let none_pos_neg = Formula::All(
            Box::new(int_var("n")),
            Box::new(and(
                ge(int_var("n"), int_lit(0)),
                lt(int_var("n"), int_lit(0)),
            )),
        );
        assert!(!z3.is_sat(&none_pos_neg));
    }

    #[test]
    fn simplify_bool_comparisons() {
        let a = bool_var("a");
        let b = bool_var("b");
        let x = int_var("x");
        let y = int_var("y");
        assert_eq!(
            Z3Runtime::simplify(&le(a.clone(), b.clone())),
            crate::logic::implies(a.clone(), b.clone())
        );
        assert_eq!(
            Z3Runtime::simplify(&ge(a.clone(), b.clone())),
            crate::logic::implies(b.clone(), a.clone())
        );
        assert_eq!(
            Z3Runtime::simplify(&lt(a.clone(), b.clone())),
            and_clean(fnot(a.clone()), b.clone())
        );
        assert_eq!(
            Z3Runtime::simplify(&crate::logic::gt(a.clone(), b.clone())),
            and_clean(fnot(b), a)
        );
        assert_eq!(Z3Runtime::simplify(&le(x.clone(), y.clone())), le(x, y));
    }

    #[test]
    fn is_sat_bool_comparison() {
        let mut z3 = Z3Runtime::new(&empty_env());
        let a = bool_var("a");
        let b = bool_var("b");
        assert!(z3.is_sat(&le(a.clone(), b.clone())));
        assert!(!z3.is_sat(&and(le(a.clone(), b.clone()), and(a, fnot(b)))));
    }

    #[test]
    fn datatype_conversion() {
        let mut z3 = Z3Runtime::new(&int_list_env());
        let sort = list_sort();
        let nil = cons(sort.clone(), "Nil", vec![]);
        let cons0 = cons(sort.clone(), "Cons", vec![int_lit(0), nil.clone()]);
        let cons1 = cons(sort.clone(), "Cons", vec![int_lit(1), nil.clone()]);
        assert!(z3.is_sat(&eq(nil.clone(), nil.clone())));
        assert!(z3.is_sat(&eq(cons0.clone(), cons0.clone())));
        assert!(!z3.is_sat(&eq(nil, cons0.clone())));
        assert!(!z3.is_sat(&eq(cons0, cons1)));
        assert!(z3.is_sat(&eq(
            cons(
                sort.clone(),
                "Cons",
                vec![
                    int_lit(0),
                    cons(
                        sort.clone(),
                        "Cons",
                        vec![int_lit(1), cons(sort, "Nil", vec![])]
                    )
                ],
            ),
            cons(
                Sort::DataS("IntList".to_string(), vec![]),
                "Cons",
                vec![
                    int_lit(0),
                    cons(
                        Sort::DataS("IntList".to_string(), vec![]),
                        "Cons",
                        vec![
                            int_lit(1),
                            cons(Sort::DataS("IntList".to_string(), vec![]), "Nil", vec![])
                        ]
                    )
                ],
            )
        )));
    }

    #[test]
    fn datatype_satisfies_constructor() {
        let mut z3 = Z3Runtime::new(&int_list_env());
        let sort = list_sort();
        let x = int_var("x");
        let nil = cons(sort.clone(), "Nil", vec![]);
        assert!(z3.is_sat(&and(
            eq(x.clone(), int_lit(0)),
            eq(
                cons(sort, "Cons", vec![x, nil]),
                cons(
                    list_sort(),
                    "Cons",
                    vec![int_lit(0), cons(list_sort(), "Nil", vec![])]
                )
            )
        )));
    }

    #[test]
    fn mus_with_must_have() {
        let mut z3 = Z3Runtime::new(&empty_env());
        let x = int_var("x");
        let x0 = eq(x.clone(), int_lit(0));
        let x1 = eq(x.clone(), int_lit(1));
        let x2 = eq(x, int_lit(2));
        let mut cores = z3.get_all_mus(&ftrue(), &x0, &[x1.clone(), x2.clone()]);
        cores.sort();
        assert_eq!(cores, vec![vec![x1], vec![x2]]);
    }

    #[test]
    fn mus_inconsistent_assumption() {
        let mut z3 = Z3Runtime::new(&empty_env());
        let x = int_var("x");
        let assumption = eq(x.clone(), int_lit(0));
        let must_have = eq(x.clone(), int_lit(3));
        let cores = z3.get_all_mus(
            &assumption,
            &must_have,
            &[eq(x.clone(), int_lit(1)), eq(x, int_lit(2))],
        );
        assert_eq!(cores, vec![vec![]]);
    }
}

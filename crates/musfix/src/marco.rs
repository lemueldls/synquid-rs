//! `MARCO` enumeration of minimal unsatisfiable subsets (the "`MUSfix`"
//! solver).
//!
//! This is the straight port of the MARCO machinery formerly embedded in
//! `synquid::smt` (`Z3Runtime::getAllMUSs` and helpers), made generic over a
//! minimal SMT engine so the crate stays independent of Synquid's formula
//! vocabulary. See the crate-level docs for the preserved semantics.

use std::collections::BTreeSet;

/// Result of a satisfiability query, distinguishing `Unknown` (which the
/// reference handles differently per site: panic in `getNextSeed`, treat as
/// sat in `minimize`/`maximize`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CheckResult {
    Sat,
    Unsat,
    Unknown,
}

/// The SMT services the MARCO loop needs, supplied by the host solver.
///
/// `Fml` is the host's formula type (`synquid::logic::Formula`); `Lit` is
/// the boolean AST type of the underlying SMT backend; `Model` is the
/// backend's model type, opaque here.
pub trait SmtEngine {
    type Fml: Clone;
    type Lit: Clone;
    type Model;

    /// Translate a formula to a boolean AST (used for assumptions and the
    /// `controlLit ⇒ fml` implications).
    fn fml_to_ast(&mut self, fml: &Self::Fml) -> Self::Lit;

    /// Control literal for `fml`, creating (and caching) it on first use.
    /// Literal ids are shared between the main and auxiliary solvers.
    fn get_control_lit(&mut self, fml: Self::Fml) -> u64;

    /// The main-solver AST for a control literal.
    fn main_lit(&self, id: u64) -> &Self::Lit;
    /// The auxiliary-solver AST for a control literal.
    fn aux_lit(&self, id: u64) -> &Self::Lit;
    /// The formula mapped to a control literal.
    fn lit_to_fml(&self, id: u64) -> Self::Fml;
    /// The id of a main-solver literal AST (as returned by `unsat_core`).
    fn lit_id_of(&self, lit: &Self::Lit) -> u64;

    /// Solver scope management.
    fn push_main(&mut self);
    fn pop_main(&mut self, n: u32);
    fn push_aux(&mut self);
    fn pop_aux(&mut self, n: u32);

    /// Assert a boolean AST into the given solver.
    fn assert_main(&mut self, lit: &Self::Lit);
    fn assert_aux(&mut self, lit: &Self::Lit);

    /// Satisfiability queries.
    fn check_main(&mut self) -> CheckResult;
    fn check_aux(&mut self) -> CheckResult;
    fn check_main_assumptions(&mut self, lits: &[Self::Lit]) -> CheckResult;

    /// Model access and evaluation of a control literal against a model
    /// (falling back to `bias` when the literal is unconstrained).
    fn main_model(&self) -> Option<Self::Model>;
    fn aux_model(&self) -> Option<Self::Model>;
    fn eval_main_lit(&self, model: &Self::Model, id: u64, bias: bool) -> bool;
    fn eval_aux_lit(&self, model: &Self::Model, id: u64, bias: bool) -> bool;
    fn unsat_core(&self) -> Vec<Self::Lit>;

    /// Boolean composition (only what the MARCO loop needs).
    fn lit_not(&self, lit: &Self::Lit) -> Self::Lit;
    fn lit_or(&self, lits: &[Self::Lit]) -> Self::Lit;
    fn lit_implies(&self, lhs: &Self::Lit, rhs: &Self::Lit) -> Self::Lit;
    fn lit_false(&self) -> Self::Lit;
}

/// `getAllMUSs`: all minimal unsatisfiable subsets of `fmls` that contain
/// `must_have`, assuming `assumption`.
///
/// The returned cores are in discovery order and contain the *formulas* of
/// `fmls` (excluding `must_have`).
pub fn get_all_mus<E: SmtEngine>(
    engine: &mut E,
    assumption: &E::Fml,
    must_have: &E::Fml,
    fmls: &[E::Fml],
) -> Vec<Vec<E::Fml>> {
    engine.push_main();
    engine.push_aux();

    let mut all_fmls = vec![must_have.clone()];
    all_fmls.extend_from_slice(fmls);
    let control_lits: Vec<u64> = all_fmls
        .iter()
        .cloned()
        .map(|fml| engine.get_control_lit(fml))
        .collect();
    let must_have_lit = control_lits[0];

    let assumption_ast = engine.fml_to_ast(assumption);
    engine.assert_main(&assumption_ast);
    for (&lit, fml) in control_lits.iter().zip(&all_fmls) {
        let fml_ast = engine.fml_to_ast(fml);
        let assert = engine.lit_implies(engine.main_lit(lit), &fml_ast);
        engine.assert_main(&assert);
    }
    let must_have_ast = engine.aux_lit(must_have_lit).clone();
    engine.assert_aux(&must_have_ast);

    let result = get_all_mus_loop(engine, &control_lits, must_have_lit, Vec::new());

    engine.pop_aux(1);
    engine.pop_main(1);
    result
}

/// `getAllMUSs'`: the MARCO main loop.
fn get_all_mus_loop<E: SmtEngine>(
    engine: &mut E,
    control_lits_aux: &[u64],
    must_have: u64,
    mut cores: Vec<Vec<E::Fml>>,
) -> Vec<Vec<E::Fml>> {
    loop {
        let Some((seed, rest)) = get_next_seed(engine, control_lits_aux) else {
            return cores;
        };
        let seed_asts: Vec<E::Lit> = seed
            .iter()
            .map(|&lit| engine.main_lit(lit).clone())
            .collect();
        if engine.check_main_assumptions(&seed_asts) == CheckResult::Unsat {
            let unsat_core = engine.unsat_core();
            let mus = minimize(engine, &unsat_core);
            block_up(engine, &mus);
            let unsat_fmls: Vec<E::Fml> = mus
                .iter()
                .filter(|&&lit| lit != must_have)
                .map(|&lit| engine.lit_to_fml(lit))
                .collect();
            if mus.contains(&must_have) {
                cores.push(unsat_fmls);
            }
        } else {
            let mss = maximize(engine, &seed, &rest);
            block_down(engine, &mss, control_lits_aux);
        }
    }
}

/// `getNextSeed`: an unexplored subset of the control literals, from a model
/// of the auxiliary solver; `None` means the search space is exhausted.
/// Returns the (seed, rest) split (literals selected true / false by the
/// model, biased towards true).
fn get_next_seed<E: SmtEngine>(
    engine: &mut E,
    control_lits_aux: &[u64],
) -> Option<(Vec<u64>, Vec<u64>)> {
    match engine.check_aux() {
        CheckResult::Unsat => None,
        CheckResult::Sat => {
            let model = engine.aux_model().expect("getNextSeed: sat but no model");
            let (seed, rest) = partition(control_lits_aux, |&lit| {
                engine.eval_aux_lit(&model, lit, true)
            });
            Some((seed, rest))
        }
        CheckResult::Unknown => panic!("getNextSeed: Z3 returned Unknown"),
    }
}

/// `blockUp`: mark all supersets of the core as explored by asserting in the
/// auxiliary solver that not all of its literals hold.
fn block_up<E: SmtEngine>(engine: &mut E, mus: &[u64]) {
    let nots: Vec<E::Lit> = mus
        .iter()
        .map(|&lit| engine.lit_not(engine.aux_lit(lit)))
        .collect();
    let or = engine.lit_or(&nots);
    engine.assert_aux(&or);
}

/// `blockDown`: mark all subsets of the MSS as explored by asserting in the
/// auxiliary solver that some literal outside it holds (or `false` when
/// nothing is left outside).
fn block_down<E: SmtEngine>(engine: &mut E, mss: &[u64], control_lits_aux: &[u64]) {
    let mss_set: BTreeSet<u64> = mss.iter().copied().collect();
    let rest: Vec<E::Lit> = control_lits_aux
        .iter()
        .filter(|lit| !mss_set.contains(lit))
        .map(|&lit| engine.aux_lit(lit).clone())
        .collect();
    if rest.is_empty() {
        let f = engine.lit_false();
        engine.assert_aux(&f);
    } else {
        let or = engine.lit_or(&rest);
        engine.assert_aux(&or);
    }
}

/// `minimize`: greedily shrink an unsat set to a minimal unsat subset, inside
/// its own `local` (push/pop): the required literals are asserted within that
/// scope only.
fn minimize<E: SmtEngine>(engine: &mut E, unsat_core: &[E::Lit]) -> Vec<u64> {
    engine.push_main();
    let mut rest: Vec<u64> = unsat_core.iter().map(|lit| engine.lit_id_of(lit)).collect();
    let mut checked: Vec<u64> = Vec::new();
    while let Some(lit) = rest.first().copied() {
        rest.remove(0);
        let assumptions: Vec<E::Lit> = rest.iter().map(|&id| engine.main_lit(id).clone()).collect();
        if engine.check_main_assumptions(&assumptions) == CheckResult::Unsat {
            // lit can be omitted: drop it.
        } else {
            let lit_ast = engine.main_lit(lit).clone();
            engine.assert_main(&lit_ast);
            checked.push(lit);
        }
    }
    engine.pop_main(1);
    checked
}

/// `maximize`: grow a satisfiable seed to a maximal satisfiable subset,
/// inside its own `local` (push/pop).
fn maximize<E: SmtEngine>(engine: &mut E, checked0: &[u64], rest0: &[u64]) -> Vec<u64> {
    engine.push_main();
    let mut checked: Vec<u64> = checked0.to_vec();
    let mut rest: Vec<u64> = rest0.to_vec();
    for &lit in &checked {
        let lit_ast = engine.main_lit(lit).clone();
        engine.assert_main(&lit_ast);
    }
    loop {
        if rest.is_empty() {
            break;
        }
        let or_rest: Vec<E::Lit> = rest.iter().map(|&id| engine.main_lit(id).clone()).collect();
        let or = engine.lit_or(&or_rest);
        engine.assert_main(&or);
        if engine.check_main() == CheckResult::Unsat {
            break; // checked is maximal
        }
        let model = engine.main_model().expect("maximize: sat but no model");
        let (set_rest, unset_rest): (Vec<u64>, Vec<u64>) =
            partition(&rest, |&lit| engine.eval_main_lit(&model, lit, true));
        for &lit in &set_rest {
            let lit_ast = engine.main_lit(lit).clone();
            engine.assert_main(&lit_ast);
        }
        checked.extend(&set_rest);
        rest = unset_rest;
    }
    engine.pop_main(1);
    checked
}

/// Split `xs` according to a predicate, preserving order (mirrors
/// `Data.List.partition` used by `partitionM` in the reference).
fn partition<T>(xs: &[T], keep: impl Fn(&T) -> bool) -> (Vec<T>, Vec<T>)
where T: Clone {
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

#[cfg(test)]
mod tests {
    use z3::{
        Model, SatResult, Solver,
        ast::{Bool, Int},
    };

    use super::{CheckResult, SmtEngine, get_all_mus, partition};

    fn to_check_result(r: SatResult) -> CheckResult {
        match r {
            SatResult::Sat => CheckResult::Sat,
            SatResult::Unsat => CheckResult::Unsat,
            SatResult::Unknown => CheckResult::Unknown,
        }
    }

    /// `SmtEngine` over real `z3::Solver`s, with formulas being bare boolean
    /// ASTs. The control-literal cache is a linear scan (z3 ASTs are not
    /// ordered); the main solver is exposed so tests can inject background
    /// theory when needed.
    struct MockEngine {
        main: Solver,
        aux: Solver,
        lits: Vec<(Bool, Bool)>,
        fmls: Vec<Bool>,
        count: u64,
    }

    impl MockEngine {
        fn new() -> Self {
            Self {
                main: Solver::new(),
                aux: Solver::new(),
                lits: Vec::new(),
                fmls: Vec::new(),
                count: 0,
            }
        }
    }

    impl SmtEngine for MockEngine {
        type Fml = Bool;
        type Lit = Bool;
        type Model = Model;

        fn fml_to_ast(&mut self, fml: &Self::Fml) -> Self::Lit {
            fml.clone()
        }

        fn get_control_lit(&mut self, fml: Self::Fml) -> u64 {
            if let Some(id) = self.fmls.iter().position(|f| *f == fml) {
                return id as u64;
            }
            let id = self.count;
            self.count += 1;
            let name = format!("{}lit", id);
            let main_lit = Bool::new_const(name.as_str());
            let aux_lit = Bool::new_const(name.as_str());
            self.fmls.push(fml);
            self.lits.push((main_lit, aux_lit));
            id
        }

        fn main_lit(&self, id: u64) -> &Self::Lit {
            &self.lits[id as usize].0
        }

        fn aux_lit(&self, id: u64) -> &Self::Lit {
            &self.lits[id as usize].1
        }

        fn lit_to_fml(&self, id: u64) -> Self::Fml {
            self.fmls[id as usize].clone()
        }

        fn lit_id_of(&self, lit: &Self::Lit) -> u64 {
            self.lits
                .iter()
                .position(|(main, _)| main.ast_eq(lit))
                .map(|i| i as u64)
                .expect("litIdOf: literal not found in control map")
        }

        fn push_main(&mut self) {
            self.main.push();
        }

        fn pop_main(&mut self, n: u32) {
            self.main.pop(n);
        }

        fn push_aux(&mut self) {
            self.aux.push();
        }

        fn pop_aux(&mut self, n: u32) {
            self.aux.pop(n);
        }

        fn assert_main(&mut self, lit: &Self::Lit) {
            self.main.assert(lit);
        }

        fn assert_aux(&mut self, lit: &Self::Lit) {
            self.aux.assert(lit);
        }

        fn check_main(&mut self) -> CheckResult {
            to_check_result(self.main.check())
        }

        fn check_aux(&mut self) -> CheckResult {
            to_check_result(self.aux.check())
        }

        fn check_main_assumptions(&mut self, lits: &[Self::Lit]) -> CheckResult {
            to_check_result(self.main.check_assumptions(lits))
        }

        fn main_model(&self) -> Option<Self::Model> {
            self.main.get_model()
        }

        fn aux_model(&self) -> Option<Self::Model> {
            self.aux.get_model()
        }

        fn eval_main_lit(&self, model: &Self::Model, id: u64, bias: bool) -> bool {
            model
                .eval(self.main_lit(id), true)
                .and_then(|b| b.as_bool())
                .unwrap_or(bias)
        }

        fn eval_aux_lit(&self, model: &Self::Model, id: u64, bias: bool) -> bool {
            model
                .eval(self.aux_lit(id), true)
                .and_then(|b| b.as_bool())
                .unwrap_or(bias)
        }

        fn unsat_core(&self) -> Vec<Self::Lit> {
            self.main.get_unsat_core()
        }

        fn lit_not(&self, lit: &Self::Lit) -> Self::Lit {
            lit.not()
        }

        fn lit_or(&self, lits: &[Self::Lit]) -> Self::Lit {
            Bool::or(lits)
        }

        fn lit_implies(&self, lhs: &Self::Lit, rhs: &Self::Lit) -> Self::Lit {
            lhs.implies(rhs)
        }

        fn lit_false(&self) -> Self::Lit {
            Bool::from_bool(false)
        }
    }

    fn int(name: &str) -> Int {
        Int::new_const(name)
    }

    fn int_eq(x: Int, v: i64) -> Bool {
        x.eq(Int::from_i64(v))
    }

    #[test]
    fn mus_with_must_have() {
        let mut engine = MockEngine::new();
        let x = int("x");
        let must_have = int_eq(x.clone(), 0);
        let f1 = int_eq(x.clone(), 1);
        let f2 = int_eq(x, 2);
        let true_ast = Bool::from_bool(true);
        let cores = get_all_mus(&mut engine, &true_ast, &must_have, &[
            f1.clone(),
            f2.clone(),
        ]);
        assert_eq!(cores.len(), 2);
        assert!(
            cores
                .iter()
                .any(|core| core.len() == 1 && core[0].ast_eq(&f1))
        );
        assert!(
            cores
                .iter()
                .any(|core| core.len() == 1 && core[0].ast_eq(&f2))
        );
    }

    #[test]
    fn inconsistent_assumption_makes_single_empty_core() {
        let mut engine = MockEngine::new();
        let x = int("x");
        let assumption = int_eq(x.clone(), 0);
        let must_have = int_eq(x.clone(), 3);
        let cores = get_all_mus(&mut engine, &assumption, &must_have, &[
            int_eq(x.clone(), 1),
            int_eq(x, 2),
        ]);
        assert_eq!(cores, vec![Vec::<Bool>::new()]);
    }

    #[test]
    fn core_is_minimal() {
        let mut engine = MockEngine::new();
        let x = int("x");
        let z = int("z");
        let must_have = int_eq(x.clone(), 0);
        let f1 = int_eq(x, 1);
        let f2 = int_eq(z, 42);
        let true_ast = Bool::from_bool(true);
        let cores = get_all_mus(&mut engine, &true_ast, &must_have, &[
            f1.clone(),
            f2.clone(),
        ]);
        assert_eq!(cores, vec![vec![f1]]);
    }

    #[test]
    fn must_have_required_but_excluded_from_cores() {
        let mut engine = MockEngine::new();
        let x = int("x");
        let must_have = int_eq(x.clone(), 0);
        let cores = get_all_mus(&mut engine, &Bool::from_bool(true), &must_have, &[
            int_eq(x.clone(), 1),
            int_eq(x.clone(), 2),
        ]);
        assert_eq!(cores.len(), 2);
        for core in &cores {
            assert_eq!(core.len(), 1);
            assert!(!core[0].ast_eq(&must_have));
        }
    }

    #[test]
    fn control_lit_cache_persists_across_calls() {
        let mut engine = MockEngine::new();
        let x = int("x");
        let must_have = int_eq(x.clone(), 0);
        let f1 = int_eq(x.clone(), 1);
        let true_ast = Bool::from_bool(true);
        let cores1 = get_all_mus(&mut engine, &true_ast, &must_have, &[f1.clone()]);
        assert_eq!(cores1, vec![vec![f1.clone()]]);
        let first_count = engine.count;
        assert_eq!(first_count, 2);
        let f2 = int_eq(x, 2);
        let cores2 = get_all_mus(&mut engine, &true_ast, &must_have, &[
            f1.clone(),
            f2.clone(),
        ]);
        assert_eq!(cores2.len(), 2);
        assert!(
            cores2
                .iter()
                .any(|core| core.len() == 1 && core[0].ast_eq(&f1))
        );
        assert!(
            cores2
                .iter()
                .any(|core| core.len() == 1 && core[0].ast_eq(&f2))
        );
        assert_eq!(engine.count, first_count + 1, "cache did not persist");
    }

    #[test]
    fn partition_splits_by_predicate() {
        let (yes, no) = partition(&[1, 2, 3, 4], |&x| x % 2 == 0);
        assert_eq!(yes, vec![2, 4]);
        assert_eq!(no, vec![1, 3]);
    }
}

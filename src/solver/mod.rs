use crate::{logic::Formula, program::Environment};

pub mod fixpoint;
pub mod horn;

pub trait MonadSMT {
    fn init_solver(env: Environment);
    fn is_sat(formula: Formula) -> bool;
    fn all_unsat_cores(a: Formula, b: Formula, c: Vec<Formula>) -> Vec<Vec<Formula>>;
}

pub trait MonadHorn {
    // fn init_horn_solver(env: Environment) -> Candiate
}

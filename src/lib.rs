pub mod data;
pub mod error;
pub mod explorer;
pub mod logic;
pub mod parser;
pub mod pretty;
pub mod program;
pub mod resolver;
pub mod smt;
pub mod solver;
pub mod synthesizer;
pub mod tokens;
pub mod r#type;
pub mod type_constraint_solver;
pub mod util;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Doc(String);

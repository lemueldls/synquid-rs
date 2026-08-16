//! Synquid: a program synthesizer using liquid type refinement (Rust port of
//! the Haskell implementation in `specs/src/Synquid`).

pub mod cli;
pub mod error;
pub mod explorer;
pub mod horn_solver;
pub mod html;
pub mod logic;
pub mod parser;
pub mod pretty;
pub mod program;
pub mod resolver;
pub mod smt;
pub mod synthesizer;
pub mod tc_solver;
pub mod tokens;
pub mod type_checker;
pub mod types;
pub mod util;

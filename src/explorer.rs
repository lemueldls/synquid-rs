use core::fmt;
use std::collections::BTreeMap;

use itertools::Itertools;

use crate::{
    error::SourcePos,
    program::{Environment, Goal, RProgram, UProgram},
    r#type::{RType, SType},
    type_constraint_solver::TypingState,
    util::Id,
};

/// Choices for the type of terminating fixpoint operator
pub enum FixpointStrategy {
    /// Do not use fixpoint
    DisableFixpoint,
    /// Fixpoint decreases the first well-founded argument
    FirstArgument,
    /// Fixpoint decreases the lexicographical tuple of all well-founded argument in declaration order
    AllArguments,
    /// Fixpoint without termination check
    Nonterminating,
}

/// Choices for the order of e-term enumeration
pub enum PickSymbolStrategy {
    PickDepthFirst,
    PickInterleave,
}

/// Parameters of program exploration
pub struct ExplorerParams {
    /// Maximum depth of application trees
    e_guess_depth: i32,
    /// Maximum depth of application trees inside match scrutinees
    scrutinee_depth: i32,
    /// Maximum nesting level of matches
    match_depth: i32,
    /// Maximum nesting level of auxiliary functions (lambdas used as arguments)
    aux_depth: i32,
    /// How to generate terminating fixpoints
    fix_strategy: FixpointStrategy,
    /// Enable polymorphic recursion?
    poly_recursion: bool,
    /// Enable recursion polymorphic in abstract predicates?
    pred_poly_recursion: bool,
    /// Should we match eagerly on all unfolded variables?
    abduce_scrutinees: bool,
    /// Unfold binders introduced by matching (to use them in match abduction)?
    unfold_locals: bool,
    /// Should implementations that only cover part of the input space be accepted?
    partial_solution: bool,
    /// Solve subtyping constraints during the bottom-up phase
    incremental_checking: bool,
    /// Check consistency of function's type with the goal before exploring arguments?
    consistency_checking: bool,
    /// Split subtyping constraints between datatypes into constraints over each measure
    split_measures: bool,
    /// Context in which subterm is currently being generated (used only for logging and symmetry reduction)
    context: Box<dyn Fn(RProgram) -> RProgram>,
    /// Should enumerated terms be memoized?
    use_memoization: bool,
    /// Should partial applications be memoized to check for redundancy?
    symmetry_reduction: bool,
    /// Source position of the current goal
    source_pos: SourcePos,
    /// How verbose logging is
    explorer_log_level: i32,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Requirements(BTreeMap<Id, Vec<RType>>);

/// State of program exploration
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ExplorerState {
    /// Type-checking state
    typing_state: TypingState,
    /// Subterms to be synthesized independently
    aux_goals: Vec<Goal>,
    /// Synthesized auxiliary goals, to be inserted into the main program
    solved_aux_goals: BTreeMap<Id, RProgram>,
    /// Local bindings to be checked upon use (in type checking mode)
    lambda_lets: BTreeMap<Id, (Environment, UProgram)>,
    /// All types that a variable is required to comply to (in repair mode)
    required_types: Requirements,
    /// Number of times each symbol has been used in the program so far
    symbol_use_count: BTreeMap<Id, usize>,
}

/// Key in the memoization store
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MemoKey {
    key_type_arity: usize,
    key_last_shape: SType,
    key_state: ExplorerState,
    key_depth: usize,
}

impl fmt::Display for MemoKey {
    // -- pretty (MemoKey arity t d st) = pretty env <+> text "|-" <+> hsep (replicate arity (text "? ->")) <+> pretty t <+> text "AT" <+> pretty d
    // pretty (MemoKey arity t st d) = hsep (replicate arity (text "? ->")) <+> pretty t <+> text "AT" <+> pretty d <+> parens (pretty (st ^. typingState . candidates))
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} -> {} AT {} ({})",
            "? -> ".repeat(self.key_type_arity as usize),
            self.key_last_shape,
            self.key_depth,
            // REVIEW: correctness of implementation
            self.key_state.typing_state.candidates.iter().format(", ")
        )
    }
}

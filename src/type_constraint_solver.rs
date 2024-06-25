use std::collections::BTreeMap;

use hashbrown::{HashMap, HashSet};

use crate::{
    error::SourcePos,
    logic::{Candidate, Formula, QMap, QSpace, Substitution},
    program::{Constraint, Environment},
    r#type::TypeSubstitution,
    util::{self, Id},
    Doc,
};

/// Parameters of type constraint solving
pub struct TypingParams {
    /// Qualifier generator for conditionals
    cond_quals_gen: Box<dyn Fn(Environment, Vec<Formula>) -> QSpace>,
    /// Qualifier generator for match scrutinees
    match_quals_gen: Box<dyn Fn(Environment, Vec<Formula>) -> QSpace>,
    /// Qualifier generator for types
    type_quals_gen: Box<dyn Fn(Environment, Formula, Vec<Formula>) -> QSpace>,
    /// Qualifier generator for bound predicates
    pred_quals_gen: Box<dyn Fn(Environment, Vec<Formula>, Vec<Formula>) -> QSpace>,
    tc_solver_split_measures: bool,
    /// How verbose logging is
    tc_solver_log_level: u8,
}

/// State of type constraint solving
#[derive(Debug)]
pub struct TypingState {
    // Persistent state:
    /// Typing constraints yet to be converted to horn clauses
    pub typing_constraints: Vec<Constraint>,
    /// Current assignment to free type variables
    pub type_assignment: TypeSubstitution,
    /// Current assignment to free predicate variables  _qualifierMap :: QMap,
    pub pred_assignment: Substitution,
    /// Current state space for predicate unknowns
    pub qualifier_map: QMap,
    /// Current set of candidate liquid assignments to unknowns
    pub candidates: Vec<Candidate>,
    /// Initial environment
    pub init_env: Environment,
    /// Number of unique identifiers issued so far
    pub id_count: BTreeMap<Id, i32>,
    /// Has the entire program been seen?
    pub is_final: bool,
    // Temporary state:
    /// Typing constraints that cannot be simplified anymore and can be converted to horn clauses or qualifier maps
    pub simple_constraints: Vec<Constraint>,
    /// Horn clauses generated from subtyping constraints
    pub horn_clauses: Vec<(Formula, Id)>,
    /// Formulas generated from type consistency constraints
    pub consistency_checks: Vec<Formula>,
    /// Information to be added to all type errors
    pub error_context: (SourcePos, Doc),
}

impl PartialEq for TypingState {
    fn eq(&self, other: &Self) -> bool {
        // REVIEW: what do "a" and "u" mean?
        let set = HashSet::from_iter([Id::Builtin("a"), Id::Builtin("u")]);

        let self_id_count = util::restrict_domain(&set, &self.id_count);
        let other_id_count = util::restrict_domain(&set, &other.id_count);

        self_id_count == other_id_count
            && self.type_assignment == other.type_assignment
            && self.candidates == other.candidates
    }
}

impl Eq for TypingState {}

impl PartialOrd for TypingState {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        // REVIEW: what do "a" and "u" mean?
        let set = HashSet::from_iter([Id::Builtin("a"), Id::Builtin("u")]);

        let self_id_count = util::restrict_domain(&set, &self.id_count);
        let other_id_count = util::restrict_domain(&set, &other.id_count);

        match self_id_count.partial_cmp(&other_id_count) {
            Some(std::cmp::Ordering::Equal) => {
                match self.type_assignment.partial_cmp(&other.type_assignment) {
                    Some(std::cmp::Ordering::Equal) => {
                        self.candidates.partial_cmp(&other.candidates)
                    }
                    other => other,
                }
            }
            other => other,
        }
    }
}

impl Ord for TypingState {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

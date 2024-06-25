use core::fmt;
use std::collections::{BTreeMap, BTreeSet};

use hashbrown::{HashMap, HashSet};
use itertools::Itertools;

use super::Formula;
use crate::util::Id;

#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct QSpace {
    /// Qualifiers
    pub qualifiers: Vec<Formula>,
    /// Maximum number of qualifiers in a valuation
    pub max_count: usize,
}

#[repr(transparent)]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct QMap(BTreeMap<Id, QSpace>);

impl QMap {
    /// Get `g` component of the search space for unknown `u` in `qmap`
    pub fn lookup_quals<A>(&self, g: fn(&QSpace) -> A, u: &Formula) -> A {
        match u {
            Formula::Unknown(_, u) => match self.0.get(u) {
                Some(qs) => g(qs),
                None => panic!("missing qualifiers for unknown"),
            },
            _ => panic!("expected unknown"),
        }
    }

    pub fn lookup_quals_subst(&self, u: &Formula) -> Vec<Formula> {
        match u {
            Formula::Unknown(s, _) => {
                let mut qs: Vec<Formula> = self
                    .lookup_quals(|q_space| q_space.qualifiers.clone(), u)
                    .into_iter()
                    .map(|fml| fml.substitute(s))
                    .collect();

                let gos = qs.iter().flat_map(|u| self.go(u)).collect::<Vec<_>>();
                qs.extend(gos);

                qs
            }
            _ => panic!("expected unknown"),
        }
    }

    fn go(&self, u: &Formula) -> Vec<Formula> {
        match u {
            u @ Formula::Unknown(..) => self.lookup_quals_subst(u),
            fml => vec![fml.clone()],
        }
    }

    /// Top of the solution lattice (maps every unknown in the domain of `self` to the empty set of qualifiers)
    pub fn top_solution(&self) -> Solution {
        let solution = self
            .0
            .keys()
            .map(|u| (u.clone(), Valuation::default()))
            .collect();

        Solution(solution)
    }

    /// Bottom of the solution lattice (maps every unknown in the domain of `self` to all its qualifiers)
    pub fn bot_solution(&self) -> Solution {
        let solution = self
            .0
            .iter()
            .map(|(u, q_space)| {
                let quals = q_space.qualifiers.iter().cloned().collect();

                (u.clone(), Valuation(quals))
            })
            .collect();

        Solution(solution)
    }
}

#[repr(transparent)]
#[derive(derive_more::Constructor, Debug)]
pub struct ExtractAssumptions(fn(Formula) -> HashSet<Formula>);

/// Valuation of a predicate unknown as a set of qualifiers
#[repr(transparent)]
#[derive(
    derive_more::Into,
    derive_more::IntoIterator,
    derive_more::AsRef,
    derive_more::AsMut,
    derive_more::Constructor,
    Debug,
    Clone,
    Default,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
)]
pub struct Valuation(BTreeSet<Formula>);

impl fmt::Display for Valuation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{{}}}", self.as_ref().iter().format(", "))
    }
}

/// Mapping from predicate unknowns to their valuations
#[repr(transparent)]
#[derive(
    derive_more::AsRef,
    derive_more::AsMut,
    derive_more::Constructor,
    Debug,
    Clone,
    Default,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
)]
pub struct Solution(BTreeMap<Id, Valuation>);

impl Solution {
    /// valuation of `u` in `self`
    pub fn valuation(&self, u: &Formula) -> Valuation {
        match u {
            Formula::Unknown(s, u) => match self.0.get(u) {
                Some(quals) => Valuation(
                    quals
                        .0
                        .iter()
                        .cloned()
                        .map(|fml| fml.substitute(s))
                        .collect(),
                ),
                None => panic!("valuation: no value for unknown"),
            },
            _ => panic!("expected unknown"),
        }
    }

    /// Element-wise conjunction of `self` and `other`
    pub fn merge(&self, other: &Solution) -> Solution {
        let mut solution = self.0.clone();

        for (u, quals) in other.0.iter() {
            match solution.get_mut(u) {
                Some(quals1) => {
                    quals1.0.extend(quals.0.iter().cloned());
                }
                None => {
                    solution.insert(u.clone(), quals.clone());
                }
            }
        }

        Solution(solution)
    }
}

impl fmt::Display for Solution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[{}]",
            self.as_ref()
                .iter()
                .format_with(", ", |(key, val), f| f(&format_args!("{key} -> {val}")))
        )
    }
}

#[derive(Debug, Clone)]
pub struct Candidate {
    pub solution: Solution,
    pub valid_constraints: BTreeSet<Formula>,
    pub invalid_constraints: BTreeSet<Formula>,
    pub label: String,
}

impl Default for Candidate {
    fn default() -> Self {
        Candidate {
            solution: Solution(BTreeMap::new()),
            valid_constraints: BTreeSet::new(),
            invalid_constraints: BTreeSet::new(),
            label: String::from("0"),
        }
    }
}

impl fmt::Display for Candidate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}: {} ({} {})",
            self.label,
            self.solution,
            self.valid_constraints.len(),
            self.invalid_constraints.len()
        )
    }
}

impl PartialEq for Candidate {
    fn eq(&self, other: &Self) -> bool {
        self.solution
            .0
            .iter()
            .filter(|(_, v)| !v.0.is_empty())
            .collect::<BTreeMap<_, _>>()
            == other
                .solution
                .0
                .iter()
                .filter(|(_, v)| !v.0.is_empty())
                .collect::<BTreeMap<_, _>>()
            && self.valid_constraints == other.valid_constraints
            && self.invalid_constraints == other.invalid_constraints
    }
}

impl Eq for Candidate {}

impl PartialOrd for Candidate {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        let cmp = self
            .solution
            .0
            .iter()
            .filter(|(_, v)| !v.0.is_empty())
            .collect::<BTreeMap<_, _>>()
            .cmp(
                &other
                    .solution
                    .0
                    .iter()
                    .filter(|(_, v)| !v.0.is_empty())
                    .collect::<BTreeMap<_, _>>(),
            );

        if cmp != std::cmp::Ordering::Equal {
            return Some(cmp);
        }

        let cmp = self.valid_constraints.cmp(&other.valid_constraints);
        if cmp != std::cmp::Ordering::Equal {
            return Some(cmp);
        }

        self.invalid_constraints
            .partial_cmp(&other.invalid_constraints)
    }
}

impl Ord for Candidate {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

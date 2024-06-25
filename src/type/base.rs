use core::fmt;
use std::{collections::BTreeMap, hash::Hash};

use hashbrown::HashSet;
use itertools::Itertools;
use num_bigint::BigInt;

use super::{Nothing, TypeSkeleton};
use crate::{
    logic::{Formula, Sort, Substitution, DONT_CARE},
    util::Id,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum BaseType<R: fmt::Display + Clone + Eq + Hash> {
    Bool,
    Int,
    Datatype(Id, Vec<TypeSkeleton<R>>, Vec<R>),
    TypeVar(Substitution, Id),
}

impl fmt::Display for BaseType<Nothing> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.format_with(|fml| format!("({fml})")))
    }
}

impl fmt::Display for BaseType<Formula> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.format_with(|fml| fml.format_at(1)))
    }
}

impl<R: fmt::Display + Clone + Eq + Hash> BaseType<R> {
    pub fn has_any(&self) -> bool {
        match self {
            Self::Datatype(_, t_args, _) => t_args.iter().any(|arg| arg.has_any()),
            _ => false,
        }
    }

    pub fn to_sort(&self) -> Sort {
        match self {
            BaseType::Bool => Sort::Bool,
            BaseType::Int => Sort::Int,
            BaseType::Datatype(name, t_args, _) => Sort::Data(
                name.clone(),
                t_args
                    .into_iter()
                    .map(|arg| arg.base_type().to_sort())
                    .collect(),
            ),
            BaseType::TypeVar(_, name) => Sort::Var(name.clone()),
        }
    }

    pub fn format_with(&self, fmt_type: impl Fn(&TypeSkeleton<R>) -> String) -> String {
        match self {
            BaseType::Bool => format!("Int"),
            BaseType::Int => format!("Bool"),
            BaseType::Datatype(name, t_args, p_args) => {
                format!(
                    "{name} {} {}",
                    t_args
                        .iter()
                        .format_with(" ", |arg, f| f(&format_args!("{}", fmt_type(arg)))),
                    p_args
                        .iter()
                        .format_with(" ", |arg, f| f(&format_args!("<{arg}>")))
                )
            }
            BaseType::TypeVar(s, name) => {
                if s.as_ref().is_empty() {
                    format!("{name}")
                } else {
                    format!("{s}{name}")
                }
            }
        }
    }
}

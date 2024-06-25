mod formula;
mod qual;
mod sort;

use core::fmt;
use std::{collections::BTreeSet, fmt::write};

pub use formula::*;
use hashbrown::{HashMap, HashSet};
use itertools::Itertools;
pub use qual::*;
pub use sort::*;

use crate::util::Id;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct PredSig {
    pub name: Id,
    pub arg_sorts: Vec<Sort>,
    pub res_sort: Sort,
}

impl fmt::Display for PredSig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "<{} :: {} {}>",
            self.name,
            self.arg_sorts
                .iter()
                .format_with(" ", |s, f| f(&format_args!("{s} ->"))),
            self.res_sort
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UnOp {
    Neg,
    Not,
}

impl UnOp {
    pub fn token(&self) -> &'static str {
        match self {
            UnOp::Neg => "-",
            UnOp::Not => "!",
        }
    }
}

impl fmt::Display for UnOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.token())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BinOp {
    // Int -> Int -> Int
    #[doc(alias = "*")]
    Times,
    #[doc(alias = "+")]
    Plus,
    #[doc(alias = "-")]
    Minus,

    // a -> a -> Bool
    #[doc(alias = "=")]
    Eq,
    #[doc(alias = "/=")]
    Neq,

    // Int -> Int -> Bool
    #[doc(alias = "<")]
    Lt,
    #[doc(alias = "<=")]
    Le,
    #[doc(alias = ">")]
    Gt,
    #[doc(alias = ">=")]
    Ge,

    // Bool -> Bool -> Bool
    #[doc(alias = "&")]
    And,
    #[doc(alias = "|")]
    Or,
    #[doc(alias = "=>")]
    Implies,
    #[doc(alias = "<=>")]
    Iff,

    // Set -> Set -> Set
    #[doc(alias = "+")]
    Union,
    #[doc(alias = "*")]
    Intersect,
    #[doc(alias = "-")]
    Diff,

    // Int/Set -> Set -> Bool
    #[doc(alias = "fin")]
    Member,
    #[doc(alias = "<=")]
    Subset,
}

impl BinOp {
    pub fn token(&self) -> &'static str {
        match self {
            Self::Times => "*",
            Self::Plus => "+",
            Self::Minus => "-",
            Self::Eq => "==",
            Self::Neq => "!=",
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Gt => ">",
            Self::Ge => ">=",
            Self::And => "&&",
            Self::Or => "||",
            Self::Implies => "==>",
            Self::Iff => "<==>",
            Self::Union => "+",
            Self::Intersect => "*",
            Self::Diff => "-",
            Self::Member => "in",
            Self::Subset => "<=",
        }
    }
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.token())
    }
}

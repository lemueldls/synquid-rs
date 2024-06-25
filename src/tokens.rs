use crate::{
    logic::{BinOp, UnOp},
    util::Id,
};
use bimap::BiHashMap;
use lazy_static::lazy_static;

pub const KEYWORDS: [&str; 21] = [
    "Bool",
    "data",
    "else",
    "error",
    "False",
    "if",
    "in",
    "inline",
    "Int",
    "let",
    "match",
    "measure",
    "predicate",
    "qualifier",
    "Set",
    "termination",
    "then",
    "True",
    "type",
    "with",
    "where",
];

lazy_static! {
    pub static ref UN_OP_TOKENS: BiHashMap<UnOp, Id> =
        BiHashMap::from_iter([(UnOp::Neg, Id::Builtin("-")), (UnOp::Not, Id::Builtin("!")),]);
    pub static ref BIN_OP_TOKENS: BiHashMap<BinOp, Id> = BiHashMap::from_iter([
        (BinOp::Times, Id::Builtin("*")),
        (BinOp::Plus, Id::Builtin("+")),
        (BinOp::Minus, Id::Builtin("-")),
        (BinOp::Eq, Id::Builtin("==")),
        (BinOp::Neq, Id::Builtin("!=")),
        (BinOp::Lt, Id::Builtin("<")),
        (BinOp::Le, Id::Builtin("<=")),
        (BinOp::Gt, Id::Builtin(">")),
        (BinOp::Ge, Id::Builtin(">=")),
        (BinOp::And, Id::Builtin("&&")),
        (BinOp::Or, Id::Builtin("||")),
        (BinOp::Implies, Id::Builtin("==>")),
        (BinOp::Iff, Id::Builtin("<==>")),
        (BinOp::Union, Id::Builtin("+")),
        (BinOp::Intersect, Id::Builtin("*")),
        (BinOp::Diff, Id::Builtin("-")),
        (BinOp::Member, Id::Builtin("in")),
        (BinOp::Subset, Id::Builtin("<=")),
    ]);
}

pub const OTHER_OPS: [&str; 7] = ["::", ":", "->", "|", "=", "??", ","];

pub const IDENTIFIER_CHARS: &str = "_'";
pub const COMMENT_START: &str = "{-";
pub const COMMENT_END: &str = "-}";
pub const COMMENT_LINE: &str = "--";

/// Is string `str` a literal of a primitive type?
pub fn is_literal(str: &str) -> bool {
    str.parse::<i64>().is_ok() || str == "True" || str == "False"
}

pub fn is_type_name(str: &str) -> bool {
    str.chars().next().unwrap().is_uppercase()
}

pub fn is_identifier(str: &str) -> bool {
    str.chars().next().unwrap().is_lowercase()
}

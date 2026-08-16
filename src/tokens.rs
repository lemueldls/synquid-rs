//! Lexemes of the Synquid language (mirror of `Synquid.Tokens`).

use crate::{
    logic::{BinOp, UnOp},
    util::{Id, as_integer},
};

/// Keywords of the language.
#[must_use]
pub fn keywords() -> Vec<&'static str> {
    vec![
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
    ]
}

/// Names of unary operators.
#[must_use]
pub fn un_op_tokens() -> Vec<(UnOp, &'static str)> {
    vec![(UnOp::Neg, "-"), (UnOp::Not, "!")]
}

/// Names of binary operators.
#[must_use]
pub fn bin_op_tokens() -> Vec<(BinOp, &'static str)> {
    vec![
        (BinOp::Times, "*"),
        (BinOp::Plus, "+"),
        (BinOp::Minus, "-"),
        (BinOp::Eq, "=="),
        (BinOp::Neq, "!="),
        (BinOp::Lt, "<"),
        (BinOp::Le, "<="),
        (BinOp::Gt, ">"),
        (BinOp::Ge, ">="),
        (BinOp::And, "&&"),
        (BinOp::Or, "||"),
        (BinOp::Implies, "==>"),
        (BinOp::Iff, "<==>"),
        (BinOp::Union, "+"),
        (BinOp::Intersect, "*"),
        (BinOp::Diff, "-"),
        (BinOp::Member, "in"),
        (BinOp::Subset, "<="),
    ]
}

/// Other operators.
#[must_use]
pub fn other_ops() -> Vec<&'static str> {
    vec!["::", ":", "->", "|", "=", "??", ",", ".", "\\"]
}

/// Characters allowed in identifiers (in addition to letters and digits).
pub const IDENTIFIER_CHARS: &str = "_'";
/// Start of a multi-line comment.
pub const COMMENT_START: &str = "{-";
/// End of a multi-line comment.
pub const COMMENT_END: &str = "-}";
/// Start of a single-line comment.
pub const COMMENT_LINE: &str = "--";

/// Is `str` a literal of a primitive type?
#[must_use]
pub fn is_literal(str: &str) -> bool {
    as_integer(str).is_some() || str == "True" || str == "False"
}

#[must_use]
pub fn is_type_name(str: &str) -> bool {
    str.chars().next().is_some_and(|c| c.is_uppercase())
}

#[must_use]
pub fn is_identifier(str: &str) -> bool {
    str.chars().next().is_some_and(|c| c.is_lowercase())
}

/// Token string for a unary operator (Haskell `unOpTokens Map.! op`).
#[must_use]
pub fn un_op_token_str(op: UnOp) -> Id {
    un_op_tokens()
        .into_iter()
        .find(|(o, _)| *o == op)
        .map(|(_, s)| s.to_string())
        .expect("unOpTokens: missing token")
}

/// All unary operators with the given token string (in the token map's key
/// order).
#[must_use]
pub fn un_ops_for_token(token: &str) -> Vec<UnOp> {
    un_op_tokens()
        .into_iter()
        .filter(|(_, t)| *t == token)
        .map(|(o, _)| o)
        .collect()
}

/// Token string for a binary operator (Haskell `binOpTokens Map.! op`).
#[must_use]
pub fn bin_op_token_str(op: BinOp) -> Id {
    bin_op_tokens()
        .into_iter()
        .find(|(o, _)| *o == op)
        .map(|(_, s)| s.to_string())
        .expect("binOpTokens: missing token")
}

/// All binary operators with the given token string, in key order.
#[must_use]
pub fn bin_ops_for_token(token: &str) -> Vec<BinOp> {
    bin_op_tokens()
        .into_iter()
        .filter(|(_, t)| *t == token)
        .map(|(o, _)| o)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::logic::BinOp;

    #[test]
    fn test_tokens() {
        assert_eq!(bin_ops_for_token("+"), vec![BinOp::Plus, BinOp::Union]);
        assert_eq!(bin_ops_for_token("*"), vec![BinOp::Times, BinOp::Intersect]);
        assert_eq!(bin_ops_for_token("-"), vec![BinOp::Minus, BinOp::Diff]);
        assert_eq!(bin_ops_for_token("=="), vec![BinOp::Eq]);
        assert_eq!(bin_op_token_str(BinOp::Subset), "<=");
        assert_eq!(un_op_token_str(crate::logic::UnOp::Not), "!");
    }

    #[test]
    fn test_literals() {
        assert!(is_literal("42"));
        assert!(is_literal("True"));
        assert!(!is_literal("x"));
    }
}

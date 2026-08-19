//! Source positions and error kinds (mirror of `Synquid.Error`).

use crate::{
    pretty::{Doc, show_doc},
    util::Id,
};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourcePos {
    pub source_name: Id,
    pub line: usize,
    pub column: usize,
}

impl SourcePos {
    #[must_use]
    pub const fn source_line(&self) -> usize {
        self.line
    }

    #[must_use]
    pub const fn source_column(&self) -> usize {
        self.column
    }

    #[must_use]
    pub const fn source_name(&self) -> &Id {
        &self.source_name
    }
}

/// Dummy source position.
#[must_use]
pub fn no_pos() -> SourcePos {
    SourcePos {
        source_name: "<no file name>".to_string(),
        line: 1,
        column: 1,
    }
}

/// Anything with a source position attached.
#[derive(Clone, Debug, PartialOrd, Ord, Hash)]
pub struct Pos<A> {
    pub position: SourcePos,
    pub node: A,
}

impl<A: PartialEq> PartialEq for Pos<A> {
    fn eq(&self, other: &Self) -> bool {
        self.node == other.node
    }
}

impl<A: Eq> Eq for Pos<A> {}

impl<A> Pos<A> {
    pub const fn new(position: SourcePos, node: A) -> Self {
        Pos { position, node }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ErrorKind {
    ParseError,
    ResolutionError,
    TypeError,
    SynthesisError,
}

#[derive(Clone)]
pub struct ErrorMessage {
    pub kind: ErrorKind,
    pub position: SourcePos,
    pub description: Doc,
}

impl std::fmt::Debug for ErrorMessage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ErrorMessage")
            .field("kind", &self.kind)
            .field("position", &self.position)
            .field("description", &show_doc(&self.description))
            .finish()
    }
}

impl ErrorMessage {
    #[must_use]
    pub const fn new(kind: ErrorKind, position: SourcePos, description: Doc) -> Self {
        ErrorMessage {
            kind,
            position,
            description,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pos_eq_compares_node_only() {
        let p1 = Pos::new(no_pos(), 1);
        let p2 = Pos::new(
            SourcePos {
                source_name: "different".to_string(),
                line: 2,
                column: 3,
            },
            1,
        );
        assert_eq!(p1, p2);
        let p3 = Pos::new(no_pos(), 2);
        assert_ne!(p1, p3);
    }
}

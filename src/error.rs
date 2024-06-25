use core::fmt;
use std::{borrow::Cow, fmt::Debug, ops};

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SourcePos(Cow<'static, str>);

pub const NO_POS: SourcePos = SourcePos(Cow::Borrowed(""));

impl PartialOrd for SourcePos {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        // TODO: Test if correct
        // self.0.start.partial_cmp(&other.0.start)
        Some(self.0.cmp(&other.0))
    }
}

impl Ord for SourcePos {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

pub struct Pos<A> {
    pub position: SourcePos,
    pub node: A,
}

impl<A: PartialEq> PartialEq for Pos<A> {
    fn eq(&self, other: &Self) -> bool {
        self.position == other.position && self.node == other.node
    }
}

impl<A: Eq> Eq for Pos<A> {}

impl<A: Debug> fmt::Debug for Pos<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Pos")
            .field("position", &self.position)
            .field("node", &self.node)
            .finish()
    }
}

impl<A: Clone> Clone for Pos<A> {
    fn clone(&self) -> Self {
        Self {
            position: self.position.clone(),
            node: self.node.clone(),
        }
    }
}

pub enum ErrorKind {
    ParseError,
    ResolutionError,
    TypeError,
    SynthesisError,
}

pub struct ErrorMessage {
    pub kind: ErrorKind,
    pub position: SourcePos,
    pub description: String,
}

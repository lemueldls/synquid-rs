use core::fmt;
use std::{
    cmp,
    collections::BTreeMap,
    hash::{self, Hash, Hasher},
};

use hashbrown::{HashMap, HashSet};
use owo_colors::OwoColorize;

use crate::{
    data::{Either, Left, Right},
    logic::VALUE_VAR_NAME,
    r#type::RType,
};

#[derive(Debug, Clone)]
pub enum Id {
    Builtin(&'static str),
    Local(Box<str>),
}

impl Id {
    pub fn as_str(&self) -> &str {
        match self {
            Id::Builtin(s) => s,
            Id::Local(s) => s,
        }
    }
}

impl fmt::Display for Id {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if *self == VALUE_VAR_NAME {
            write!(f, "{}", self.bold())
        } else {
            write!(f, "{self}")
        }
    }
}

impl PartialEq for Id {
    fn eq(&self, other: &Self) -> bool {
        self.as_str() == other.as_str()
    }
}

impl Eq for Id {}

impl PartialOrd for Id {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.as_str().partial_cmp(other.as_str())
    }
}

impl Ord for Id {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl Hash for Id {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

impl phf::PhfHash for Id {
    fn phf_hash<H: Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

pub fn uncurry3<A, B, C, D, F: Fn(A) -> FF, FF: Fn(B) -> FFF, FFF: Fn(C) -> D>(
    f: F,
) -> impl Fn(A, B, C) -> D {
    move |a, b, c| f(a)(b)(c)
}

pub fn from_right<T>(x: Right<T>) -> T {
    x.0
}

pub fn from_left<T>(x: Left<T>) -> T {
    x.0
}

pub fn map_left<A, B, C>(f: impl Fn(A) -> B) -> impl Fn(Either<A, C>) -> Either<B, C> {
    move |e| match e {
        Either::Left(a) => Either::Left(Left(f(from_left(a)))),
        Either::Right(c) => Either::Right(c),
    }
}

pub fn map_right<A, B, C>(f: impl Fn(A) -> B) -> impl Fn(Either<C, A>) -> Either<C, B> {
    move |e| match e {
        Either::Left(c) => Either::Left(c),
        Either::Right(a) => Either::Right(Right(f(from_right(a)))),
    }
}

pub fn mapped_compare<A, B: Ord>(f: impl Fn(A) -> B) -> impl Fn(A, A) -> cmp::Ordering {
    move |x, y| f(x).cmp(&f(y))
}

pub fn both<A, B>(f: impl Fn(A) -> B) -> impl Fn(A, A) -> (B, B) {
    move |x1, x2| (f(x1), f(x2))
}

// pub fn both2<A, B, C, F: Fn(A) -> FF, FF: Fn(B) -> C, FFFF: Fn(B, B) -> (C, C)>(
//     f: F,
// ) -> impl Fn(A, A) -> FFFF {
//     // move |x1, x2| move |y1, y2| ((f(x1))(y1), (f(x2))(y2))
//     move |x1, x2| move |y1, y2| todo!()
// }

/// Map `m` restricted on the set of keys `keys`
pub fn restrict_domain<K: Eq + Ord + Hash + Clone, V: Clone>(
    keys: &HashSet<K>,
    m: &BTreeMap<K, V>,
) -> BTreeMap<K, V> {
    m.clone()
        .into_iter()
        .filter(|(k, _)| keys.contains(k))
        .collect()
}

/// Map `m` with the set of keys `keys` removed from its domain
pub fn remove_domain<K: Eq + Hash + Clone, V: Clone>(
    keys: &HashSet<K>,
    m: &HashMap<K, V>,
) -> HashMap<K, V> {
    m.clone()
        .into_iter()
        .filter(|(k, _)| !keys.contains(k))
        .collect()
}

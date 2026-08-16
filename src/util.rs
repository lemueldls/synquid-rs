//! Common types and helper functions (mirror of `Synquid.Util`).

use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet},
};

pub type Id = String;

pub fn uncurry3<A, B, C, D>(f: impl Fn(A, B, C) -> D, (x, y, z): (A, B, C)) -> D {
    f(x, y, z)
}

pub fn from_right<T, E>(r: Result<T, E>) -> T {
    match r {
        Ok(x) => x,
        Err(_) => panic!("from_right: expected Right"),
    }
}

pub fn from_left<T, E>(l: Result<T, E>) -> E {
    match l {
        Err(e) => e,
        Ok(_) => panic!("from_left: expected Left"),
    }
}

pub fn map_left<A, B, C>(f: impl Fn(A) -> B, r: Result<C, A>) -> Result<C, B> {
    match r {
        Ok(x) => Ok(x),
        Err(a) => Err(f(a)),
    }
}

pub fn map_right<A, B, C>(f: impl Fn(A) -> B, r: Result<A, C>) -> Result<B, C> {
    match r {
        Ok(a) => Ok(f(a)),
        Err(c) => Err(c),
    }
}

pub fn mapped_compare<T, K: Ord + ?Sized>(f: impl Fn(&T) -> &K, x: &T, y: &T) -> Ordering {
    f(x).cmp(f(y))
}

pub fn both<A, B>(f: impl Fn(A) -> B, (x1, x2): (A, A)) -> (B, B) {
    (f(x1), f(x2))
}

pub fn both_map<A, B, C>(f: impl Fn(A, B) -> C, (x1, x2): (A, A), (y1, y2): (B, B)) -> (C, C) {
    (f(x1, y1), f(x2, y2))
}

pub fn both_m<A, B, E>(f: impl Fn(A) -> Result<B, E>, (x1, x2): (A, A)) -> Result<(B, B), E> {
    Ok((f(x1)?, f(x2)?))
}

/// Compare two sets: first by size, then element-wise (Haskell `Set` Ord).
#[must_use]
pub fn set_compare<T: Ord>(x: &BTreeSet<T>, y: &BTreeSet<T>) -> Ordering {
    match x.len().cmp(&y.len()) {
        Ordering::Equal => x.iter().cmp(y.iter()),
        res => res,
    }
}

#[must_use]
pub fn disjoint<T: Ord>(s1: &BTreeSet<T>, s2: &BTreeSet<T>) -> bool {
    s1.intersection(s2).next().is_none()
}

#[must_use]
pub fn restrict_domain<K: Ord + Clone, V: Clone>(
    keys: &BTreeSet<K>,
    m: &BTreeMap<K, V>,
) -> BTreeMap<K, V> {
    partition_domain(keys, m).0
}

#[must_use]
pub fn remove_domain<K: Ord + Clone, V: Clone>(
    keys: &BTreeSet<K>,
    m: &BTreeMap<K, V>,
) -> BTreeMap<K, V> {
    partition_domain(keys, m).1
}

#[must_use]
pub fn partition_domain<K: Ord + Clone, V: Clone>(
    keys: &BTreeSet<K>,
    m: &BTreeMap<K, V>,
) -> (BTreeMap<K, V>, BTreeMap<K, V>) {
    let mut restrict = BTreeMap::new();
    let mut remove = BTreeMap::new();
    for (k, v) in m {
        if keys.contains(k) {
            restrict.insert(k.clone(), v.clone());
        } else {
            remove.insert(k.clone(), v.clone());
        }
    }
    (restrict, remove)
}

pub fn const_map<K: Ord + Clone, V: Clone>(keys: &BTreeSet<K>, val: V) -> BTreeMap<K, V> {
    keys.iter().cloned().map(|k| (k, val.clone())).collect()
}

pub fn set_concat_map<A: Ord, B: Ord>(
    f: impl Fn(&A) -> BTreeSet<B>,
    s: &BTreeSet<A>,
) -> BTreeSet<B> {
    let mut res = BTreeSet::new();
    for a in s {
        for b in f(a) {
            res.insert(b);
        }
    }
    res
}

/// All subsets of `s` of sizes no greater than `n`.
#[must_use]
pub fn bounded_subsets<T: Ord + Clone>(n: usize, s: &BTreeSet<T>) -> BTreeSet<BTreeSet<T>> {
    fn go<T: Ord + Clone>(
        n: usize,
        elems: &[T],
        cur: BTreeSet<T>,
        acc: &mut BTreeSet<BTreeSet<T>>,
    ) {
        acc.insert(cur.clone());
        if n == 0 {
            return;
        }
        for (i, e) in elems.iter().enumerate() {
            let mut c = cur.clone();
            c.insert(e.clone());
            go(n - 1, &elems[i + 1..], c, acc);
        }
    }
    let mut acc = BTreeSet::new();
    go(
        n,
        &s.iter().cloned().collect::<Vec<_>>(),
        BTreeSet::new(),
        &mut acc,
    );
    acc
}

/// Partition a set-valued map into sub-maps where non-disjoint value sets are
/// grouped together.
#[must_use]
pub fn to_disjoint_groups<K: Ord + Clone, V: Ord + Clone>(
    m: &BTreeMap<K, BTreeSet<V>>,
) -> Vec<(BTreeSet<K>, BTreeSet<V>)> {
    fn close<K: Ord + Clone, V: Ord + Clone>(
        keys: &mut BTreeSet<K>,
        vals: &mut BTreeSet<V>,
        m: &BTreeMap<K, BTreeSet<V>>,
    ) {
        let m_disj: BTreeMap<K, BTreeSet<V>> = m
            .iter()
            .filter(|(_, v)| disjoint(v, vals))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        let m_non_disj: Vec<(K, BTreeSet<V>)> = m
            .iter()
            .filter(|(_, v)| !disjoint(v, vals))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        if m_non_disj.is_empty() {
            return;
        }
        for (k, v) in m_non_disj {
            keys.insert(k);
            vals.extend(v);
        }
        close(keys, vals, &m_disj);
    }

    let mut m = m.clone();
    let mut acc = Vec::new();
    while let Some((key, vals)) = m.iter().next().map(|(k, v)| (k.clone(), v.clone())) {
        let mut keys = BTreeSet::new();
        keys.insert(key.clone());
        let mut vals = vals;
        close(&mut keys, &mut vals, &m);
        for k in &keys {
            m.remove(k);
        }
        acc.push((keys, vals));
    }
    acc
}

pub fn partition_m<T: Clone, E>(
    f: impl Fn(&T) -> Result<bool, E>,
    xs: &[T],
) -> Result<(Vec<T>, Vec<T>), E> {
    let mut ys = Vec::new();
    let mut zs = Vec::new();
    for x in xs {
        if f(x)? {
            ys.push(x.clone());
        } else {
            zs.push(x.clone());
        }
    }
    Ok((ys, zs))
}

pub fn find_m<T: Clone, E>(f: impl Fn(&T) -> Result<bool, E>, xs: &[T]) -> Result<Option<T>, E> {
    for x in xs {
        if f(x)? {
            return Ok(Some(x.clone()));
        }
    }
    Ok(None)
}

pub fn any_m<T, E>(f: impl Fn(&T) -> Result<bool, E>, xs: &[T]) -> Result<bool, E> {
    for x in xs {
        if f(x)? {
            return Ok(true);
        }
    }
    Ok(false)
}

pub fn all_m<T, E>(f: impl Fn(&T) -> Result<bool, E>, xs: &[T]) -> Result<bool, E> {
    for x in xs {
        if !f(x)? {
            return Ok(false);
        }
    }
    Ok(true)
}

pub fn find_just_m<T, U: Clone, E>(
    f: impl Fn(&T) -> Result<Option<U>, E>,
    xs: &[T],
) -> Result<Option<U>, E> {
    for x in xs {
        if let Some(res) = f(x)? {
            return Ok(Some(res));
        }
    }
    Ok(None)
}

pub fn if_m<E>(
    cond: Result<bool, E>,
    t: impl FnOnce() -> Result<(), E>,
    e: impl FnOnce() -> Result<(), E>,
) -> Result<(), E> {
    if cond? { t() } else { e() }
}

pub fn set_partition_m<T: Ord + Clone, E>(
    f: impl Fn(&T) -> Result<bool, E>,
    s: &BTreeSet<T>,
) -> Result<(BTreeSet<T>, BTreeSet<T>), E> {
    let (ys, zs) = partition_m(f, &s.iter().cloned().collect::<Vec<_>>())?;
    Ok((ys.into_iter().collect(), zs.into_iter().collect()))
}

#[must_use]
pub fn as_integer(s: &str) -> Option<i64> {
    if !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()) {
        s.parse().ok()
    } else {
        None
    }
}

// Debug output level: above which debug output is ignored.
pub const DEBUG_OUT_LEVEL: usize = 1;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_set_compare() {
        let mut a = BTreeSet::new();
        a.insert(1);
        let mut b = BTreeSet::new();
        b.insert(2);
        b.insert(3);
        assert_eq!(set_compare(&a, &b), Ordering::Less);
        assert_eq!(set_compare(&a, &a), Ordering::Equal);
    }

    #[test]
    fn test_to_disjoint_groups() {
        let mut m = BTreeMap::new();
        m.insert(0, BTreeSet::from([1, 2]));
        m.insert(1, BTreeSet::from([2, 3]));
        m.insert(2, BTreeSet::from([5]));
        let groups = to_disjoint_groups(&m);
        assert_eq!(groups.len(), 2);
    }

    #[test]
    fn test_bounded_subsets() {
        let s = BTreeSet::from([1, 2, 3]);
        let subs = bounded_subsets(2, &s);
        assert_eq!(subs.len(), 7); // of size <= 2
        assert!(!subs.contains(&BTreeSet::from([1, 2, 3])));
    }

    #[test]
    fn test_as_integer() {
        assert_eq!(as_integer("42"), Some(42));
        assert_eq!(as_integer("-3"), None);
        assert_eq!(as_integer("abc"), None);
    }
}

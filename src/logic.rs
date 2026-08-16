//! Formulas of the refinement logic (mirror of `Synquid.Logic`).

use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet},
};

use crate::util::Id;

/// Wildcard/placeholder bound variable name (Haskell `_`).
pub const DONT_CARE: &str = "_";
/// Name of the special value variable.
pub const VALUE_VAR_NAME: &str = "_v";

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Sort {
    BoolS,
    IntS,
    VarS(Id),
    DataS(Id, Vec<Sort>),
    SetS(Box<Sort>),
    AnyS,
}

impl std::fmt::Display for Sort {
    /// Mirrors the `Pretty` instance from `Synquid.Pretty`.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sort::IntS => write!(f, "Int"),
            Sort::BoolS => write!(f, "Bool"),
            Sort::SetS(el) => write!(f, "Set {el}"),
            Sort::VarS(name) => write!(f, "{name}"),
            Sort::DataS(name, args) => {
                write!(f, "{name}")?;
                for arg in args {
                    write!(f, " ({arg})")?;
                }
                Ok(())
            }
            Sort::AnyS => write!(f, "?"),
        }
    }
}

#[must_use]
pub const fn is_set_s(s: &Sort) -> bool {
    matches!(s, Sort::SetS(_))
}

#[must_use]
pub fn elem_sort(s: &Sort) -> Sort {
    match s {
        Sort::SetS(x) => *x.clone(),
        _ => panic!("elemSort: not a set sort"),
    }
}

#[must_use]
pub const fn is_data(s: &Sort) -> bool {
    matches!(s, Sort::DataS(_, _))
}

#[must_use]
pub fn sort_args_of(s: &Sort) -> Vec<Sort> {
    match s {
        Sort::DataS(_, s_args) => s_args.clone(),
        _ => panic!("sortArgsOf: not a datatype sort"),
    }
}

#[must_use]
pub fn var_sort_name(s: &Sort) -> &Id {
    match s {
        Sort::VarS(name) => name,
        _ => panic!("varSortName: not a type variable sort"),
    }
}

/// All type variables in a sort.
#[must_use]
pub fn type_vars_of_sort(s: &Sort) -> BTreeSet<Id> {
    match s {
        Sort::VarS(name) => BTreeSet::from([name.clone()]),
        Sort::DataS(_, s_args) => {
            let mut acc = BTreeSet::new();
            for a in s_args {
                acc.extend(type_vars_of_sort(a));
            }
            acc
        }
        Sort::SetS(s) => type_vars_of_sort(s),
        _ => BTreeSet::new(),
    }
}

/// Mapping from type variables to sorts.
pub type SortSubstitution = BTreeMap<Id, Sort>;

#[must_use]
pub fn sort_substitute(subst: &SortSubstitution, s: Sort) -> Sort {
    match s {
        Sort::VarS(a) => {
            match subst.get(&a) {
                Some(s2) => sort_substitute(subst, s2.clone()),
                None => Sort::VarS(a),
            }
        }
        Sort::DataS(name, args) => {
            Sort::DataS(
                name,
                args.into_iter()
                    .map(|a| sort_substitute(subst, a))
                    .collect(),
            )
        }
        Sort::SetS(el) => Sort::SetS(Box::new(sort_substitute(subst, *el))),
        s => s,
    }
}

/// Fresh type variables "A0", "A1", ...
#[must_use]
pub fn distinct_type_vars(n: usize) -> Vec<Id> {
    (0..n).map(|i| format!("A{i}")).collect()
}

#[must_use]
pub fn noncapture_sort_subst(s_vars: &[Id], s_args: &[Sort], s: &Sort) -> Sort {
    let distinct = distinct_type_vars(s_vars.len());
    let subst1: SortSubstitution = s_vars
        .iter()
        .zip(distinct.iter())
        .map(|(v, d)| (v.clone(), Sort::VarS(d.clone())))
        .collect();
    let s_fresh = sort_substitute(&subst1, s.clone());
    let subst2: SortSubstitution = distinct
        .iter()
        .zip(s_args.iter())
        .map(|(d, a)| (d.clone(), a.clone()))
        .collect();
    sort_substitute(&subst2, s_fresh)
}

/// Unify two lists of sorts, respecting bound type variables.
pub fn unify_sorts(
    bound_tvs: &BTreeSet<Id>,
    xs: &[Sort],
    ys: &[Sort],
) -> Result<SortSubstitution, (Sort, Sort)> {
    fn go(
        subst: SortSubstitution,
        xs: &[Sort],
        ys: &[Sort],
        bound: &BTreeSet<Id>,
    ) -> Result<SortSubstitution, (Sort, Sort)> {
        match (xs.split_first(), ys.split_first()) {
            (None, None) => Ok(subst),
            (Some((x, xsr)), Some((y, ysr))) if x == y => go(subst, xsr, ysr, bound),
            (Some((x, xsr)), Some((y, ysr))) => {
                match (x, y) {
                    (Sort::SetS(sx), Sort::SetS(sy)) => {
                        let mut nx = Vec::from(xsr);
                        nx.insert(0, *sx.clone());
                        let mut ny = Vec::from(ysr);
                        ny.insert(0, *sy.clone());
                        go(subst, &nx, &ny, bound)
                    }
                    (Sort::DataS(name, args), Sort::DataS(name2, args2)) if name == name2 => {
                        let mut nx = Vec::from(xsr);
                        nx.splice(0..0, args.iter().cloned());
                        let mut ny = Vec::from(ysr);
                        ny.splice(0..0, args2.iter().cloned());
                        go(subst, &nx, &ny, bound)
                    }
                    (Sort::DataS(name, _), Sort::DataS(name2, _)) => {
                        Err((
                            Sort::DataS(name.clone(), vec![]),
                            Sort::DataS(name2.clone(), vec![]),
                        ))
                    }
                    (Sort::AnyS, _) => go(subst, xsr, ysr, bound),
                    (_, Sort::AnyS) => go(subst, xsr, ysr, bound),
                    (Sort::VarS(x), y) if !bound.contains(x) => {
                        match subst.get(x) {
                            Some(s) => {
                                let mut nx = Vec::from(xsr);
                                nx.insert(0, s.clone());
                                let mut ny = Vec::from(ysr);
                                ny.insert(0, y.clone());
                                go(subst, &nx, &ny, bound)
                            }
                            None => {
                                if type_vars_of_sort(y).contains(x) {
                                    Err((Sort::VarS(x.clone()), y.clone()))
                                } else {
                                    let mut subst2 = subst;
                                    subst2.insert(x.clone(), y.clone());
                                    go(subst2, xsr, ysr, bound)
                                }
                            }
                        }
                    }
                    (x, Sort::VarS(y)) if !bound.contains(y) => {
                        let mut ny = Vec::from(ysr);
                        ny.insert(0, Sort::VarS(y.clone()));
                        let mut nx = Vec::from(xsr);
                        nx.insert(0, x.clone());
                        go(subst, &ny, &nx, bound)
                    }
                    (x, y) => Err((x.clone(), y.clone())),
                }
            }
            _ => unreachable!(),
        }
    }
    go(SortSubstitution::new(), xs, ys, bound_tvs)
}

/// Constraints generated during formula resolution.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SortConstraint {
    SameSort(Sort, Sort),
    IsOrd(Sort),
}

/// Signature of a logic function / predicate: name and argument sorts.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PredSig {
    pub pred_sig_name: Id,
    pub pred_sig_arg_sorts: Vec<Sort>,
    pub pred_sig_res_sort: Sort,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UnOp {
    Neg,
    Not,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BinOp {
    Times,
    Plus,
    Minus,
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    Implies,
    Iff,
    Union,
    Intersect,
    Diff,
    Member,
    Subset,
}

/// Variable substitution (formula-level).
pub type Substitution = BTreeMap<Id, Formula>;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Formula {
    BoolLit(bool),
    IntLit(i64),
    SetLit(Box<Sort>, Vec<Formula>),
    Var(Box<Sort>, Id),
    Unknown(Substitution, Id),
    Unary(UnOp, Box<Formula>),
    Binary(BinOp, Box<Formula>, Box<Formula>),
    Ite(Box<Formula>, Box<Formula>, Box<Formula>),
    Pred(Box<Sort>, Id, Vec<Formula>),
    Cons(Box<Sort>, Id, Vec<Formula>),
    All(Box<Formula>, Box<Formula>),
}

#[must_use]
pub fn unknown_name(f: &Formula) -> &Id {
    match f {
        Formula::Unknown(_, name) => name,
        _ => panic!("unknownName: not an unknown"),
    }
}

#[must_use]
pub fn var_name(f: &Formula) -> &Id {
    match f {
        Formula::Var(_, name) => name,
        _ => panic!("varName: not a variable"),
    }
}

#[must_use]
pub fn var_type(f: &Formula) -> &Sort {
    match f {
        Formula::Var(s, _) => s,
        _ => panic!("varType: not a variable"),
    }
}

#[must_use]
pub const fn is_var(f: &Formula) -> bool {
    matches!(f, Formula::Var(_, _))
}

#[must_use]
pub const fn is_cons(f: &Formula) -> bool {
    matches!(f, Formula::Cons(_, _, _))
}

#[must_use]
pub const fn ftrue() -> Formula {
    Formula::BoolLit(true)
}

#[must_use]
pub const fn ffalse() -> Formula {
    Formula::BoolLit(false)
}

#[must_use]
pub const fn bool_lit(b: bool) -> Formula {
    Formula::BoolLit(b)
}

#[must_use]
pub const fn int_lit(i: i64) -> Formula {
    Formula::IntLit(i)
}

#[must_use]
pub fn bool_var(x: &str) -> Formula {
    Formula::Var(Box::new(Sort::BoolS), x.to_string())
}

#[must_use]
pub fn val_bool() -> Formula {
    bool_var(VALUE_VAR_NAME)
}

#[must_use]
pub fn int_var(x: &str) -> Formula {
    Formula::Var(Box::new(Sort::IntS), x.to_string())
}

#[must_use]
pub fn val_int() -> Formula {
    int_var(VALUE_VAR_NAME)
}

#[must_use]
pub fn vart_var(n: &str) -> Formula {
    Formula::Var(
        Box::new(Sort::VarS(n.to_string())),
        VALUE_VAR_NAME.to_string(),
    )
}

#[must_use]
pub fn val_vart(n: &str) -> Formula {
    vart_var(n)
}

#[must_use]
pub fn set_var(s: &str) -> Formula {
    Formula::Var(
        Box::new(Sort::SetS(Box::new(Sort::VarS(s.to_string())))),
        VALUE_VAR_NAME.to_string(),
    )
}

#[must_use]
pub fn val_set(s: &str) -> Formula {
    set_var(s)
}

#[must_use]
pub fn fneg(e: Formula) -> Formula {
    Formula::Unary(UnOp::Neg, Box::new(e))
}

#[must_use]
pub fn fnot(e: Formula) -> Formula {
    Formula::Unary(UnOp::Not, Box::new(e))
}

#[must_use]
pub fn times(l: Formula, r: Formula) -> Formula {
    Formula::Binary(BinOp::Times, Box::new(l), Box::new(r))
}
#[must_use]
pub fn plus(l: Formula, r: Formula) -> Formula {
    Formula::Binary(BinOp::Plus, Box::new(l), Box::new(r))
}
#[must_use]
pub fn minus(l: Formula, r: Formula) -> Formula {
    Formula::Binary(BinOp::Minus, Box::new(l), Box::new(r))
}
#[must_use]
pub fn eq(l: Formula, r: Formula) -> Formula {
    Formula::Binary(BinOp::Eq, Box::new(l), Box::new(r))
}
#[must_use]
pub fn neq(l: Formula, r: Formula) -> Formula {
    Formula::Binary(BinOp::Neq, Box::new(l), Box::new(r))
}
#[must_use]
pub fn le(l: Formula, r: Formula) -> Formula {
    Formula::Binary(BinOp::Le, Box::new(l), Box::new(r))
}
#[must_use]
pub fn lt(l: Formula, r: Formula) -> Formula {
    Formula::Binary(BinOp::Lt, Box::new(l), Box::new(r))
}
#[must_use]
pub fn gt(l: Formula, r: Formula) -> Formula {
    Formula::Binary(BinOp::Gt, Box::new(l), Box::new(r))
}
#[must_use]
pub fn ge(l: Formula, r: Formula) -> Formula {
    Formula::Binary(BinOp::Ge, Box::new(l), Box::new(r))
}
#[must_use]
pub fn and(l: Formula, r: Formula) -> Formula {
    Formula::Binary(BinOp::And, Box::new(l), Box::new(r))
}
#[must_use]
pub fn or(l: Formula, r: Formula) -> Formula {
    Formula::Binary(BinOp::Or, Box::new(l), Box::new(r))
}
#[must_use]
pub fn implies(l: Formula, r: Formula) -> Formula {
    Formula::Binary(BinOp::Implies, Box::new(l), Box::new(r))
}
#[must_use]
pub fn iff(l: Formula, r: Formula) -> Formula {
    Formula::Binary(BinOp::Iff, Box::new(l), Box::new(r))
}
#[must_use]
pub fn union_op(l: Formula, r: Formula) -> Formula {
    Formula::Binary(BinOp::Union, Box::new(l), Box::new(r))
}
#[must_use]
pub fn intersect(l: Formula, r: Formula) -> Formula {
    Formula::Binary(BinOp::Intersect, Box::new(l), Box::new(r))
}
#[must_use]
pub fn diff(l: Formula, r: Formula) -> Formula {
    Formula::Binary(BinOp::Diff, Box::new(l), Box::new(r))
}
#[must_use]
pub fn member(l: Formula, r: Formula) -> Formula {
    Formula::Binary(BinOp::Member, Box::new(l), Box::new(r))
}
#[must_use]
pub fn subset(l: Formula, r: Formula) -> Formula {
    Formula::Binary(BinOp::Subset, Box::new(l), Box::new(r))
}

#[must_use]
pub fn and_clean(l: Formula, r: Formula) -> Formula {
    if l == ftrue() {
        r
    } else if r == ftrue() {
        l
    } else if l == ffalse() || r == ffalse() {
        ffalse()
    } else {
        and(l, r)
    }
}

#[must_use]
pub fn or_clean(l: Formula, r: Formula) -> Formula {
    if l == ffalse() {
        r
    } else if r == ffalse() {
        l
    } else if l == ftrue() || r == ftrue() {
        ftrue()
    } else {
        or(l, r)
    }
}

/// Conjunction of a set of formulas (right-folded, as in Haskell `foldr`).
#[must_use]
pub fn conjunction(fmls: &BTreeSet<Formula>) -> Formula {
    fmls.iter()
        .rev()
        .fold(ftrue(), |acc, f| and_clean(f.clone(), acc))
}

/// Disjunction of a set of formulas (right-folded, as in Haskell `foldr`).
#[must_use]
pub fn disjunction(fmls: &BTreeSet<Formula>) -> Formula {
    fmls.iter()
        .rev()
        .fold(ffalse(), |acc, f| or_clean(f.clone(), acc))
}

/// Set of all input variables in `fml`.
#[must_use]
pub fn vars_of(fml: &Formula) -> BTreeSet<Formula> {
    match fml {
        Formula::SetLit(_, elems) => set_vars(elems),
        v @ Formula::Var(..) => BTreeSet::from([v.clone()]),
        Formula::Unary(_, e) => vars_of(e),
        Formula::Binary(_, e1, e2) => {
            let mut acc = vars_of(e1);
            acc.extend(vars_of(e2));
            acc
        }
        Formula::Ite(e0, e1, e2) => {
            let mut acc = vars_of(e0);
            acc.extend(vars_of(e1));
            acc.extend(vars_of(e2));
            acc
        }
        Formula::Pred(_, _, es) => set_vars(es),
        Formula::Cons(_, _, es) => set_vars(es),
        Formula::All(x, e) => {
            let mut acc = vars_of(e);
            acc.remove(&**x);
            acc
        }
        _ => BTreeSet::new(),
    }
}

fn set_vars(fmles: &[Formula]) -> BTreeSet<Formula> {
    let mut acc = BTreeSet::new();
    for f in fmles {
        acc.extend(vars_of(f));
    }
    acc
}

/// All predicate unknowns of `fml`.
#[must_use]
pub fn unknowns_of(fml: &Formula) -> BTreeSet<Formula> {
    match fml {
        u @ Formula::Unknown(..) => BTreeSet::from([u.clone()]),
        Formula::Unary(_, e) => unknowns_of(e),
        Formula::Binary(_, e1, e2) => {
            let mut acc = unknowns_of(e1);
            acc.extend(unknowns_of(e2));
            acc
        }
        Formula::Ite(e0, e1, e2) => {
            let mut acc = unknowns_of(e0);
            acc.extend(unknowns_of(e1));
            acc.extend(unknowns_of(e2));
            acc
        }
        Formula::Pred(_, _, es) => set_unknowns(es),
        Formula::Cons(_, _, es) => set_unknowns(es),
        Formula::All(_, e) => unknowns_of(e),
        _ => BTreeSet::new(),
    }
}

fn set_unknowns(fmles: &[Formula]) -> BTreeSet<Formula> {
    let mut acc = BTreeSet::new();
    for f in fmles {
        acc.extend(unknowns_of(f));
    }
    acc
}

/// Sets of positive and negative predicate unknowns in `fml`.
#[must_use]
pub fn pos_neg_unknowns(fml: &Formula) -> (BTreeSet<Id>, BTreeSet<Id>) {
    match fml {
        Formula::Unknown(_, u) => (BTreeSet::from([u.clone()]), BTreeSet::new()),
        Formula::Unary(UnOp::Not, e) => {
            let (p, n) = pos_neg_unknowns(e);
            (n, p)
        }
        Formula::Binary(BinOp::Implies, e1, e2) => {
            let (p1, n1) = pos_neg_unknowns(e1);
            let (p2, n2) = pos_neg_unknowns(e2);
            (
                n1.union(&p2).cloned().collect(),
                p1.union(&n2).cloned().collect(),
            )
        }
        Formula::Binary(BinOp::Iff, e1, e2) => {
            let (p, n) = pos_neg_unknowns(&implies((**e1).clone(), (**e2).clone()));
            let (p2, n2) = pos_neg_unknowns(&implies((**e2).clone(), (**e1).clone()));
            (
                p.union(&p2).cloned().collect(),
                n.union(&n2).cloned().collect(),
            )
        }
        Formula::Binary(_, e1, e2) => {
            let (p1, n1) = pos_neg_unknowns(e1);
            let (p2, n2) = pos_neg_unknowns(e2);
            (
                p1.union(&p2).cloned().collect(),
                n1.union(&n2).cloned().collect(),
            )
        }
        Formula::Ite(e, e1, e2) => {
            let (p, n) = pos_neg_unknowns(&implies((**e).clone(), (**e1).clone()));
            let (p2, n2) = pos_neg_unknowns(&implies(fnot((**e).clone()), (**e2).clone()));
            (
                p.union(&p2).cloned().collect(),
                n.union(&n2).cloned().collect(),
            )
        }
        _ => (BTreeSet::new(), BTreeSet::new()),
    }
}

#[must_use]
pub fn pos_unknowns(fml: &Formula) -> BTreeSet<Id> {
    pos_neg_unknowns(fml).0
}

#[must_use]
pub fn neg_unknowns(fml: &Formula) -> BTreeSet<Id> {
    pos_neg_unknowns(fml).1
}

/// Sets of positive and negative predicate identifiers in `fml`.
#[must_use]
pub fn pos_neg_preds(fml: &Formula) -> (BTreeSet<Id>, BTreeSet<Id>) {
    match fml {
        Formula::Pred(s, p, _) if **s == Sort::BoolS => {
            (BTreeSet::from([p.clone()]), BTreeSet::new())
        }
        Formula::Unary(UnOp::Not, e) => {
            let (p, n) = pos_neg_preds(e);
            (n, p)
        }
        Formula::Binary(BinOp::Implies, e1, e2) => {
            let (p1, n1) = pos_neg_preds(e1);
            let (p2, n2) = pos_neg_preds(e2);
            (
                n1.union(&p2).cloned().collect(),
                p1.union(&n2).cloned().collect(),
            )
        }
        Formula::Binary(BinOp::Iff, e1, e2) => {
            let (p, n) = pos_neg_preds(&implies((**e1).clone(), (**e2).clone()));
            let (p2, n2) = pos_neg_preds(&implies((**e2).clone(), (**e1).clone()));
            (
                p.union(&p2).cloned().collect(),
                n.union(&n2).cloned().collect(),
            )
        }
        Formula::Binary(_, e1, e2) => {
            let (p1, n1) = pos_neg_preds(e1);
            let (p2, n2) = pos_neg_preds(e2);
            (
                p1.union(&p2).cloned().collect(),
                n1.union(&n2).cloned().collect(),
            )
        }
        Formula::Ite(e, e1, e2) => {
            let (p, n) = pos_neg_preds(&implies((**e).clone(), (**e1).clone()));
            let (p2, n2) = pos_neg_preds(&implies(fnot((**e).clone()), (**e2).clone()));
            (
                p.union(&p2).cloned().collect(),
                n.union(&n2).cloned().collect(),
            )
        }
        _ => (BTreeSet::new(), BTreeSet::new()),
    }
}

#[must_use]
pub fn pos_preds(fml: &Formula) -> BTreeSet<Id> {
    pos_neg_preds(fml).0
}

#[must_use]
pub fn neg_preds(fml: &Formula) -> BTreeSet<Id> {
    pos_neg_preds(fml).1
}

/// All predicate identifiers in `fml`.
#[must_use]
pub fn preds_of(fml: &Formula) -> BTreeSet<Id> {
    match fml {
        Formula::Pred(_, p, es) => {
            let mut acc = BTreeSet::from([p.clone()]);
            for e in es {
                acc.extend(preds_of(e));
            }
            acc
        }
        Formula::SetLit(_, elems) => set_preds(elems),
        Formula::Unary(_, e) => preds_of(e),
        Formula::Binary(_, e1, e2) => {
            let mut acc = preds_of(e1);
            acc.extend(preds_of(e2));
            acc
        }
        Formula::Ite(e0, e1, e2) => {
            let mut acc = preds_of(e0);
            acc.extend(preds_of(e1));
            acc.extend(preds_of(e2));
            acc
        }
        Formula::All(_, e) => preds_of(e),
        _ => BTreeSet::new(),
    }
}

fn set_preds(fmles: &[Formula]) -> BTreeSet<Id> {
    let mut acc = BTreeSet::new();
    for e in fmles {
        acc.extend(preds_of(e));
    }
    acc
}

/// Left-hand side of a binary expression.
#[must_use]
pub fn left_hand_side(fml: &Formula) -> Formula {
    match fml {
        Formula::Binary(_, l, _) => *l.clone(),
        _ => panic!("leftHandSide: not a binary formula"),
    }
}

/// Right-hand side of a binary expression.
#[must_use]
pub fn right_hand_side(fml: &Formula) -> Formula {
    match fml {
        Formula::Binary(_, _, r) => *r.clone(),
        _ => panic!("rightHandSide: not a binary formula"),
    }
}

#[must_use]
pub fn conjuncts_of(fml: &Formula) -> BTreeSet<Formula> {
    match fml {
        Formula::Binary(BinOp::And, l, r) => {
            let mut acc = conjuncts_of(l);
            acc.extend(conjuncts_of(r));
            acc
        }
        f => BTreeSet::from([f.clone()]),
    }
}

/// Base sort of a term in the refinement logic.
#[must_use]
pub fn sort_of(fml: &Formula) -> Sort {
    match fml {
        Formula::BoolLit(_) => Sort::BoolS,
        Formula::IntLit(_) => Sort::IntS,
        Formula::SetLit(s, _) => Sort::SetS(Box::new((**s).clone())),
        Formula::Var(s, _) => (**s).clone(),
        Formula::Unknown(..) => Sort::BoolS,
        Formula::Unary(op, _) => {
            if *op == UnOp::Neg {
                Sort::IntS
            } else {
                Sort::BoolS
            }
        }
        Formula::Binary(op, e1, _) => {
            match op {
                BinOp::Times | BinOp::Plus | BinOp::Minus => Sort::IntS,
                BinOp::Union | BinOp::Intersect | BinOp::Diff => sort_of(e1),
                _ => Sort::BoolS,
            }
        }
        Formula::Ite(_, e1, _) => sort_of(e1),
        Formula::Pred(s, ..) => (**s).clone(),
        Formula::Cons(s, ..) => (**s).clone(),
        Formula::All(..) => Sort::BoolS,
    }
}

#[must_use]
pub fn is_executable(fml: &Formula) -> bool {
    match fml {
        Formula::SetLit(..) => false,
        Formula::Unary(_, e) => is_executable(e),
        Formula::Binary(_, e1, e2) => is_executable(e1) && is_executable(e2),
        Formula::Ite(..) => false,
        Formula::Pred(..) => false,
        Formula::All(..) => false,
        _ => true,
    }
}

/// Replace first-order variables in `fml` according to `subst`.
#[must_use]
pub fn substitute(subst: &Substitution, fml: Formula) -> Formula {
    match fml {
        Formula::SetLit(b, elems) => {
            Formula::SetLit(b, elems.into_iter().map(|e| substitute(subst, e)).collect())
        }
        Formula::Var(s, name) => {
            match subst.get(&name) {
                Some(f) => f.clone(),
                None => Formula::Var(s, name),
            }
        }
        Formula::Unknown(s, name) => Formula::Unknown(compose_substitutions(&s, subst), name),
        Formula::Unary(op, e) => Formula::Unary(op, Box::new(substitute(subst, *e))),
        Formula::Binary(op, e1, e2) => {
            Formula::Binary(
                op,
                Box::new(substitute(subst, *e1)),
                Box::new(substitute(subst, *e2)),
            )
        }
        Formula::Ite(e0, e1, e2) => {
            Formula::Ite(
                Box::new(substitute(subst, *e0)),
                Box::new(substitute(subst, *e1)),
                Box::new(substitute(subst, *e2)),
            )
        }
        Formula::Pred(b, name, args) => {
            Formula::Pred(
                b,
                name,
                args.into_iter().map(|a| substitute(subst, a)).collect(),
            )
        }
        Formula::Cons(b, name, args) => {
            Formula::Cons(
                b,
                name,
                args.into_iter().map(|a| substitute(subst, a)).collect(),
            )
        }
        Formula::All(v, e) => {
            if let Formula::Var(s, x) = *v {
                assert!(
                    !subst.contains_key(&x),
                    "substitute: scoped variable clashes with substitution variable {x}"
                );
                Formula::All(
                    Box::new(Formula::Var(s, x)),
                    Box::new(substitute(subst, *e)),
                )
            } else {
                panic!("substitute: quantifier bound is not a variable");
            }
        }
        f => f,
    }
}

/// Compose substitutions (the new one is applied after the old one's values are
/// substituted).
#[must_use]
pub fn compose_substitutions(old: &Substitution, new: &Substitution) -> Substitution {
    let new2 = remove_id(new);
    let mut res: Substitution = old
        .iter()
        .map(|(x, f)| (x.clone(), substitute(&new2, f.clone())))
        .collect();
    for (x, f) in new2 {
        res.insert(x, f);
    }
    res
}

/// Remove identity substitutions.
fn remove_id(subst: &Substitution) -> Substitution {
    subst
        .iter()
        .filter(|(x, fml)| !(is_var(fml) && var_name(fml) == *x))
        .map(|(x, fml)| (x.clone(), fml.clone()))
        .collect()
}

/// Fresh variables indexed by de Bruijn (Haskell `deBrujns`).
#[must_use]
pub fn de_brujns(n: usize) -> Vec<Id> {
    (0..n).map(|i| format!("{DONT_CARE}{i}")).collect()
}

#[must_use]
pub fn sort_substitute_fml(subst: &SortSubstitution, fml: &Formula) -> Formula {
    match fml {
        Formula::SetLit(el, es) => {
            Formula::SetLit(
                Box::new(sort_substitute(subst, (**el).clone())),
                es.iter().map(|e| sort_substitute_fml(subst, e)).collect(),
            )
        }
        Formula::Var(s, name) => {
            Formula::Var(
                Box::new(sort_substitute(subst, (**s).clone())),
                name.clone(),
            )
        }
        Formula::Unknown(s, name) => {
            Formula::Unknown(
                s.iter()
                    .map(|(k, v)| (k.clone(), sort_substitute_fml(subst, v)))
                    .collect(),
                name.clone(),
            )
        }
        Formula::Unary(op, e) => Formula::Unary(*op, Box::new(sort_substitute_fml(subst, e))),
        Formula::Binary(op, l, r) => {
            Formula::Binary(
                *op,
                Box::new(sort_substitute_fml(subst, l)),
                Box::new(sort_substitute_fml(subst, r)),
            )
        }
        Formula::Ite(c, l, r) => {
            Formula::Ite(
                Box::new(sort_substitute_fml(subst, c)),
                Box::new(sort_substitute_fml(subst, l)),
                Box::new(sort_substitute_fml(subst, r)),
            )
        }
        Formula::Pred(s, name, es) => {
            Formula::Pred(
                Box::new(sort_substitute(subst, (**s).clone())),
                name.clone(),
                es.iter().map(|e| sort_substitute_fml(subst, e)).collect(),
            )
        }
        Formula::Cons(s, name, es) => {
            Formula::Cons(
                Box::new(sort_substitute(subst, (**s).clone())),
                name.clone(),
                es.iter().map(|e| sort_substitute_fml(subst, e)).collect(),
            )
        }
        Formula::All(x, e) => {
            Formula::All(
                Box::new(sort_substitute_fml(subst, x)),
                Box::new(sort_substitute_fml(subst, e)),
            )
        }
        f => f.clone(),
    }
}

#[must_use]
pub fn noncapture_sort_subst_fml(s_vars: &[Id], s_args: &[Sort], fml: &Formula) -> Formula {
    let distinct = distinct_type_vars(s_vars.len());
    let subst1: SortSubstitution = s_vars
        .iter()
        .zip(distinct.iter())
        .map(|(v, d)| (v.clone(), Sort::VarS(d.clone())))
        .collect();
    let fml_fresh = sort_substitute_fml(&subst1, fml);
    let subst2: SortSubstitution = distinct
        .iter()
        .zip(s_args.iter())
        .map(|(d, a)| (d.clone(), a.clone()))
        .collect();
    sort_substitute_fml(&subst2, &fml_fresh)
}

#[must_use]
pub fn substitute_predicate(p_subst: &Substitution, fml: &Formula) -> Formula {
    match fml {
        Formula::Pred(b, name, args) => {
            match p_subst.get(name) {
                None => {
                    Formula::Pred(
                        b.clone(),
                        name.clone(),
                        args.iter()
                            .map(|a| substitute_predicate(p_subst, a))
                            .collect(),
                    )
                }
                Some(value) => {
                    let subst: Substitution = de_brujns(args.len())
                        .into_iter()
                        .zip(args.iter().cloned())
                        .collect();
                    substitute(&subst, substitute_predicate(p_subst, value))
                }
            }
        }
        Formula::Unary(op, e) => Formula::Unary(*op, Box::new(substitute_predicate(p_subst, e))),
        Formula::Binary(op, e1, e2) => {
            Formula::Binary(
                *op,
                Box::new(substitute_predicate(p_subst, e1)),
                Box::new(substitute_predicate(p_subst, e2)),
            )
        }
        Formula::Ite(e0, e1, e2) => {
            Formula::Ite(
                Box::new(substitute_predicate(p_subst, e0)),
                Box::new(substitute_predicate(p_subst, e1)),
                Box::new(substitute_predicate(p_subst, e2)),
            )
        }
        Formula::All(v, e) => Formula::All(v.clone(), Box::new(substitute_predicate(p_subst, e))),
        f => f.clone(),
    }
}

/// Negation normal form: no negation above boolean connectives, only && and ||.
#[must_use]
pub fn negation_nnf(fml: &Formula) -> Formula {
    match fml {
        Formula::Unary(UnOp::Not, e) => {
            match &**e {
                Formula::Unary(UnOp::Not, e2) => negation_nnf(e2),
                Formula::Binary(BinOp::And, e1, e2) => {
                    or(
                        negation_nnf(&fnot((**e1).clone())),
                        negation_nnf(&fnot((**e2).clone())),
                    )
                }
                Formula::Binary(BinOp::Or, e1, e2) => {
                    and(
                        negation_nnf(&fnot((**e1).clone())),
                        negation_nnf(&fnot((**e2).clone())),
                    )
                }
                Formula::Binary(BinOp::Implies, e1, e2) => {
                    and(negation_nnf(e1), negation_nnf(&fnot((**e2).clone())))
                }
                Formula::Binary(BinOp::Iff, e1, e2) => {
                    or(
                        and(negation_nnf(e1), negation_nnf(&fnot((**e2).clone()))),
                        and(negation_nnf(&fnot((**e1).clone())), negation_nnf(e2)),
                    )
                }
                _ => fml.clone(),
            }
        }
        Formula::Binary(BinOp::Implies, e1, e2) => {
            or(negation_nnf(&fnot((**e1).clone())), negation_nnf(e2))
        }
        Formula::Binary(BinOp::Iff, e1, e2) => {
            or(
                and(negation_nnf(e1), negation_nnf(e2)),
                and(
                    negation_nnf(&fnot((**e1).clone())),
                    negation_nnf(&fnot((**e2).clone())),
                ),
            )
        }
        Formula::Binary(op, e1, e2) if *op == BinOp::And || *op == BinOp::Or => {
            Formula::Binary(*op, Box::new(negation_nnf(e1)), Box::new(negation_nnf(e2)))
        }
        Formula::Ite(cond, e1, e2) => {
            or(
                and(negation_nnf(cond), negation_nnf(e1)),
                and(negation_nnf(&fnot(*cond.clone())), negation_nnf(e2)),
            )
        }
        f => f.clone(),
    }
}

/// Disjunctive normal form for unknowns (known predicates treated as atoms).
#[must_use]
pub fn u_dnf(fml: &Formula) -> Vec<Formula> {
    dnf(&negation_nnf(fml))
}

fn dnf(e: &Formula) -> Vec<Formula> {
    match e {
        Formula::Binary(BinOp::Or, e1, e2) => {
            if unknowns_of(e1).is_empty() && unknowns_of(e2).is_empty() {
                vec![e.clone()]
            } else {
                let mut v = dnf(e1);
                v.extend(dnf(e2));
                v
            }
        }
        Formula::Binary(BinOp::And, e1, e2) => {
            let l = dnf(e1);
            let r = dnf(e2);
            let mut v = Vec::new();
            for lc in &l {
                for rc in &r {
                    v.push(and(lc.clone(), rc.clone()));
                }
            }
            v
        }
        f => vec![f.clone()],
    }
}

#[must_use]
pub fn atoms_of(fml: &Formula) -> BTreeSet<Formula> {
    let mut acc = BTreeSet::new();
    atoms_of_iter(&negation_nnf(fml), &mut acc);
    acc
}

fn atoms_of_iter(fml: &Formula, acc: &mut BTreeSet<Formula>) {
    match fml {
        Formula::Binary(BinOp::And | BinOp::Or, l, r) => {
            atoms_of_iter(l, acc);
            atoms_of_iter(r, acc);
        }
        f => {
            acc.insert(f.clone());
        }
    }
}

/// Split formulas by a predicate argument: group formulas that contain a
/// one-argument predicate application whose only argument is `arg`.
#[must_use]
pub fn split_by_predicate(
    preds: &BTreeSet<Id>,
    arg: &Formula,
    fmls: &[Formula],
) -> Option<BTreeMap<Id, BTreeSet<Formula>>> {
    fn check(
        whole: &Formula,
        m: &mut BTreeMap<Id, BTreeSet<Formula>>,
        fml: &Formula,
        arg: &Formula,
        preds: &BTreeSet<Id>,
    ) -> Option<()> {
        if fml == arg {
            return None;
        }
        match fml {
            Formula::Pred(_, name, args) => {
                if preds.contains(name) && args.len() == 1 && args[0] == *arg {
                    m.entry(name.clone()).or_default().insert(whole.clone());
                    Some(())
                } else {
                    for a in args {
                        check(whole, m, a, arg, preds)?;
                    }
                    Some(())
                }
            }
            Formula::SetLit(_, args) => {
                for a in args {
                    check(whole, m, a, arg, preds)?;
                }
                Some(())
            }
            Formula::Unary(_, f) => check(whole, m, f, arg, preds),
            Formula::Binary(_, l, r) => {
                check(whole, m, l, arg, preds)?;
                check(whole, m, r, arg, preds)
            }
            Formula::Ite(c, t, e) => {
                check(whole, m, c, arg, preds)?;
                check(whole, m, t, arg, preds)?;
                check(whole, m, e, arg, preds)
            }
            Formula::Cons(_, _, args) => {
                for a in args {
                    check(whole, m, a, arg, preds)?;
                }
                Some(())
            }
            _ => Some(()),
        }
    }

    let mut m = BTreeMap::new();
    for fml in fmls {
        check(fml, &mut m, fml, arg, preds)?;
    }
    Some(m)
}

/// Predicate equivalent to `x in s` that does not contain comprehensions.
#[must_use]
pub fn set_to_predicate(x: Formula, s: &Formula) -> Formula {
    match s {
        Formula::Binary(BinOp::Union, sl, sr) => {
            or(set_to_predicate(x.clone(), sl), set_to_predicate(x, sr))
        }
        Formula::Binary(BinOp::Intersect, sl, sr) => {
            and(set_to_predicate(x.clone(), sl), set_to_predicate(x, sr))
        }
        Formula::Binary(BinOp::Diff, sl, sr) => {
            and(
                set_to_predicate(x.clone(), sl),
                fnot(set_to_predicate(x, sr)),
            )
        }
        Formula::Ite(c, t, e) => {
            Formula::Ite(
                c.clone(),
                Box::new(set_to_predicate(x.clone(), t)),
                Box::new(set_to_predicate(x, e)),
            )
        }
        s => member(x, s.clone()),
    }
}

/// Search space for valuations of a single unknown.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct QSpace {
    pub qualifiers: Vec<Formula>,
    /// Maximum number of qualifiers in a valuation.
    pub max_count: usize,
}

#[must_use]
pub const fn empty_qspace() -> QSpace {
    QSpace {
        qualifiers: Vec::new(),
        max_count: 0,
    }
}

#[must_use]
pub fn to_space(mb_n: Option<usize>, quals: Vec<Formula>) -> QSpace {
    let mut seen = BTreeSet::new();
    let mut quals_nub = Vec::new();
    for q in quals {
        if seen.insert(q.clone()) {
            quals_nub.push(q);
        }
    }
    let n = quals_nub.len();
    QSpace {
        qualifiers: quals_nub,
        max_count: mb_n.unwrap_or(n),
    }
}

/// Mapping from unknowns to their search spaces.
pub type QMap = BTreeMap<Id, QSpace>;

#[must_use]
pub fn lookup_quals<'a>(qmap: &'a QMap, fml: &Formula) -> &'a [Formula] {
    match fml {
        Formula::Unknown(_, u) => {
            match qmap.get(u) {
                Some(qs) => &qs.qualifiers,
                None => panic!("lookupQuals: missing qualifiers for unknown {u}"),
            }
        }
        _ => panic!("lookupQuals: not an unknown"),
    }
}

#[must_use]
pub fn lookup_max_count(qmap: &QMap, fml: &Formula) -> usize {
    match fml {
        Formula::Unknown(_, u) => {
            match qmap.get(u) {
                Some(qs) => qs.max_count,
                None => panic!("lookupMaxCount: missing qualifiers for unknown {u}"),
            }
        }
        _ => panic!("lookupMaxCount: not an unknown"),
    }
}

#[must_use]
pub fn lookup_quals_subst(qmap: &QMap, u: &Formula) -> Vec<Formula> {
    let subst = match u {
        Formula::Unknown(s, _) => s.clone(),
        _ => panic!("lookupQualsSubst: not an unknown"),
    };
    let mut res = Vec::new();
    for q in lookup_quals(qmap, u).to_vec() {
        let fml = substitute(&subst, q);
        match fml {
            Formula::Unknown(..) => res.extend(lookup_quals_subst(qmap, &fml)),
            _ => res.push(fml),
        }
    }
    res
}

/// Function extracting the assumptions from a formula (as in the Haskell type
/// alias). Boxed so implementations may capture an environment.
pub type ExtractAssumptions = Box<dyn Fn(&Formula) -> BTreeSet<Formula>>;

/// Valuation of a predicate unknown as a set of qualifiers.
pub type Valuation = BTreeSet<Formula>;

/// Mapping from predicate unknowns to their valuations.
pub type Solution = BTreeMap<Id, Valuation>;

/// Top of the solution lattice (maps every unknown in the domain of `qmap` to
/// the empty set).
#[must_use]
pub fn top_solution(qmap: &QMap) -> Solution {
    qmap.keys().cloned().map(|k| (k, BTreeSet::new())).collect()
}

/// Bottom of the solution lattice (maps every unknown to all its qualifiers).
#[must_use]
pub fn bot_solution(qmap: &QMap) -> Solution {
    qmap.iter()
        .map(|(k, qs)| (k.clone(), qs.qualifiers.iter().cloned().collect()))
        .collect()
}

/// Valuation of `u` in `sol`.
#[must_use]
pub fn valuation(sol: &Solution, u: &Formula) -> Valuation {
    match u {
        Formula::Unknown(s, ident) => {
            match sol.get(ident) {
                Some(quals) => quals.iter().map(|q| substitute(s, q.clone())).collect(),
                None => panic!("valuation: no value for unknown {ident}"),
            }
        }
        _ => panic!("valuation: not an unknown"),
    }
}

/// Substitute solutions from `sol` for all predicate variables in `fml`.
#[must_use]
pub fn apply_solution(sol: &Solution, fml: &Formula) -> Formula {
    match fml {
        Formula::Unknown(s, ident) => {
            match sol.get(ident) {
                Some(quals) => substitute(s, conjunction(quals)),
                None => fml.clone(),
            }
        }
        Formula::Unary(op, e) => Formula::Unary(*op, Box::new(apply_solution(sol, e))),
        Formula::Binary(op, e1, e2) => {
            Formula::Binary(
                *op,
                Box::new(apply_solution(sol, e1)),
                Box::new(apply_solution(sol, e2)),
            )
        }
        Formula::Ite(e0, e1, e2) => {
            Formula::Ite(
                Box::new(apply_solution(sol, e0)),
                Box::new(apply_solution(sol, e1)),
                Box::new(apply_solution(sol, e2)),
            )
        }
        Formula::All(x, e) => Formula::All(x.clone(), Box::new(apply_solution(sol, e))),
        f => f.clone(),
    }
}

/// Element-wise union of two solutions.
#[must_use]
pub fn merge(sol: &Solution, sol2: &Solution) -> Solution {
    let mut res = sol.clone();
    for (k, v) in sol2 {
        res.entry(k.clone()).or_default().extend(v.iter().cloned());
    }
    res
}

/// A solution candidate (mirror of `Candidate`).
#[derive(Clone, Debug)]
pub struct Candidate {
    pub solution: Solution,
    pub valid_constraints: BTreeSet<Formula>,
    pub invalid_constraints: BTreeSet<Formula>,
    pub label: String,
}

#[must_use]
pub fn initial_candidate() -> Candidate {
    Candidate {
        solution: Solution::new(),
        valid_constraints: BTreeSet::new(),
        invalid_constraints: BTreeSet::new(),
        label: "0".to_string(),
    }
}

/// The solution with all empty valuations removed.
fn filtered_solution(sol: &Solution) -> Solution {
    sol.iter()
        .filter(|(_, v)| !v.is_empty())
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect()
}

/// Lexicographic comparison of solutions (keys, then valuations element-wise).
fn solution_cmp(a: &Solution, b: &Solution) -> Ordering {
    let mut ia = a.iter();
    let mut ib = b.iter();
    loop {
        match (ia.next(), ib.next()) {
            (None, None) => return Ordering::Equal,
            (None, Some(_)) => return Ordering::Less,
            (Some(_), None) => return Ordering::Greater,
            (Some((ka, va)), Some((kb, vb))) => {
                match ka.cmp(kb) {
                    Ordering::Equal => {
                        match va.iter().cmp(vb.iter()) {
                            Ordering::Equal => continue,
                            o => return o,
                        }
                    }
                    o => return o,
                }
            }
        }
    }
}

/// Partial equality for `Candidate` (mirror of the Haskell `Eq` instance).
impl PartialEq for Candidate {
    fn eq(&self, other: &Self) -> bool {
        filtered_solution(&self.solution) == filtered_solution(&other.solution)
            && self.valid_constraints == other.valid_constraints
            && self.invalid_constraints == other.invalid_constraints
    }
}

impl Eq for Candidate {}

/// Total ordering for `Candidate` (mirror of the Haskell `Ord` instance).
impl PartialOrd for Candidate {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Candidate {
    fn cmp(&self, other: &Self) -> Ordering {
        solution_cmp(
            &filtered_solution(&self.solution),
            &filtered_solution(&other.solution),
        )
        .then_with(|| {
            self.valid_constraints
                .iter()
                .cmp(other.valid_constraints.iter())
        })
        .then_with(|| {
            self.invalid_constraints
                .iter()
                .cmp(other.invalid_constraints.iter())
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sort_substitute() {
        let mut subst = SortSubstitution::new();
        subst.insert("a".to_string(), Sort::IntS);
        assert_eq!(
            sort_substitute(&subst, Sort::VarS("a".to_string())),
            Sort::IntS
        );
        assert_eq!(
            sort_substitute(&subst, Sort::VarS("b".to_string())),
            Sort::VarS("b".to_string())
        );
    }

    #[test]
    fn test_unify_sorts() {
        let bound = BTreeSet::new();
        assert!(unify_sorts(&bound, &[], &[]).is_ok());
        assert!(unify_sorts(&bound, &[Sort::IntS], &[Sort::IntS]).is_ok());
        let subst = unify_sorts(&bound, &[Sort::VarS("a".to_string())], &[Sort::IntS]).unwrap();
        assert_eq!(subst.get("a"), Some(&Sort::IntS));
        assert!(unify_sorts(&bound, &[Sort::IntS], &[Sort::BoolS]).is_err());
    }

    #[test]
    fn test_and_clean() {
        assert_eq!(and_clean(ftrue(), int_var("x")), int_var("x"));
        assert_eq!(and_clean(ffalse(), int_var("x")), ffalse());
    }

    #[test]
    fn test_vars_of() {
        let f = and(int_var("x"), eq(val_int(), int_var("y")));
        let vs = vars_of(&f);
        assert_eq!(vs.len(), 3);
    }

    #[test]
    fn test_negation_nnf() {
        // !(x && y) == (!x || !y)
        let f = fnot(and(bool_var("x"), bool_var("y")));
        assert_eq!(
            negation_nnf(&f),
            or(fnot(bool_var("x")), fnot(bool_var("y")))
        );
        // x ==> y  ==  (!x || y)
        let g = implies(bool_var("x"), bool_var("y"));
        assert_eq!(negation_nnf(&g), or(fnot(bool_var("x")), bool_var("y")));
    }

    #[test]
    fn test_substitute() {
        let mut subst = Substitution::new();
        subst.insert("x".to_string(), int_var("z"));
        assert_eq!(substitute(&subst, int_var("x")), int_var("z"));
        let f = and(int_var("x"), int_var("y"));
        assert_eq!(substitute(&subst, f), and(int_var("z"), int_var("y")));
    }

    #[test]
    fn test_candidate_ord() {
        let mut c1 = initial_candidate();
        c1.solution
            .insert("u".to_string(), BTreeSet::from([int_var("x")]));
        let c2 = initial_candidate();
        assert!(c2 < c1);
        assert_eq!(c1, c1.clone());
    }

    #[test]
    fn test_valuation() {
        let mut sol = Solution::new();
        sol.insert(
            "u".to_string(),
            BTreeSet::from([eq(int_var("_v"), int_var("x"))]),
        );
        let u = Formula::Unknown(Substitution::new(), "u".to_string());
        assert_eq!(valuation(&sol, &u).len(), 1);
    }
}

use core::fmt;
use std::{cell::RefCell, collections::BTreeMap};

use hashbrown::{
    hash_map::{self, Entry},
    HashMap, HashSet,
};
use itertools::Itertools;

use super::{Formula, Substitution};
// use parking_lot::{MappedRwLockReadGuard, RwLockReadGuard};
use crate::{
    r#type::{BaseType, TypeSkeleton},
    smt::Z3State,
    util::Id,
};

#[derive(derive_more::IsVariant, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Sort {
    Bool,
    Int,
    Var(Id),
    Data(Id, Vec<Sort>),
    Set(Box<Sort>),
    Any,
}

impl Sort {
    /// All type variables in `s`
    pub fn type_vars(&self) -> HashSet<Id> {
        match self {
            Sort::Var(name) => {
                let mut set = HashSet::new();
                set.insert(name.clone());
                set
            }
            Sort::Data(_, s_args) => s_args.iter().flat_map(Sort::type_vars).collect(),
            Sort::Set(s) => s.type_vars(),
            _ => HashSet::new(),
        }
    }

    pub fn elem_sort(&self) -> &Self {
        match self {
            Self::Set(sort) => sort,
            _ => self,
        }
    }

    pub fn sort_args_of(&self) -> &Vec<Self> {
        match self {
            Self::Data(_id, sort) => sort,
            _ => todo!(),
        }
    }

    pub fn var_sort_name(&self) -> Option<&Id> {
        match self {
            Self::Var(id) => Some(id),
            _ => None,
        }
    }

    // REVIEW: Test if [`crate::logic::Sort`] is safe to clone. I might have to use slot maps in case hashes don't matter.
    // REVIEW: Test if [`z3::Sort`] is safe to clone. I am currently treating them as [`core::rc::Rc`] wrapped.
    pub fn to_z3_sort<'ctx>(&self, state: &mut Z3State<'ctx>) -> z3::Sort<'ctx> {
        let ctx = state.ctx();

        if let Some(sort) = state.sorts.get(self) {
            sort.clone()
        } else {
            let sort = match self {
                Sort::Bool => z3::Sort::bool(ctx),
                Sort::Int => z3::Sort::int(ctx),
                Sort::Var(name) => z3::Sort::int(ctx),
                Sort::Data(name, args) => z3::Sort::int(ctx),
                Sort::Set(el) => el.to_z3_sort(state).clone(),
                Sort::Any => z3::Sort::int(ctx),
            };

            state.sorts.insert(self.clone(), sort.clone());

            sort
        }
    }

    pub fn refine(self, f: Formula) -> TypeSkeleton<Formula> {
        match self {
            Sort::Bool => TypeSkeleton::Scalar(BaseType::Bool, f),
            Sort::Int => TypeSkeleton::Scalar(BaseType::Int, f),
            Sort::Var(name) => {
                TypeSkeleton::Scalar(BaseType::TypeVar(Substitution::default(), name), f)
            }
            Sort::Data(name, s_args) => TypeSkeleton::Scalar(
                BaseType::Datatype(
                    name,
                    s_args.iter().map(TypeSkeleton::from_sort).collect(),
                    Vec::new(),
                ),
                f,
            ),
            Sort::Set(s) => TypeSkeleton::Scalar(
                BaseType::Datatype(
                    SET_TYPE_NAME,
                    vec![TypeSkeleton::from_sort(&*s)],
                    Vec::new(),
                ),
                f,
            ),
            Sort::Any => TypeSkeleton::Any,
        }
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sort::Bool => write!(f, "Bool"),
            Sort::Int => write!(f, "Int"),
            Sort::Var(name) => write!(f, "{name}"),
            Sort::Data(name, args) => write!(
                f,
                "{name} {}",
                args.iter()
                    .format_with(" ", |a, f| f(&format_args!("({a})")))
            ),
            Sort::Set(el) => write!(f, "Set {el}"),
            Sort::Any => write!(f, "?"),
        }
    }
}

#[repr(transparent)]
#[derive(
    derive_more::IntoIterator, derive_more::AsMut, derive_more::Constructor, Debug, Default,
)]
pub struct SortSubstitution(HashMap<Id, Sort>);

impl SortSubstitution {
    pub fn sort_substitute(&self, sort: Sort) -> Sort {
        match sort {
            Sort::Var(ref a) => match self.0.get(a) {
                Some(b) => b.clone(),
                None => sort,
            },
            Sort::Data(name, args) => Sort::Data(
                name.clone(),
                args.into_iter().map(|a| self.sort_substitute(a)).collect(),
            ),
            Sort::Set(s) => Sort::Set(Box::new(self.sort_substitute(*s))),
            s => s,
        }
    }

    pub fn sort_substitute_fml(&self, fml: Formula) -> Formula {
        match fml {
            Formula::SetLit(el, es) => Formula::SetLit(
                self.sort_substitute(el),
                es.into_iter()
                    .map(|e| self.sort_substitute_fml(e))
                    .collect(),
            ),
            Formula::Var(s, name) => Formula::Var(self.sort_substitute(s), name),
            Formula::Unknown(s, name) => Formula::Unknown(
                Substitution::new(
                    s.into_iter()
                        .map(|(k, v)| (k, self.sort_substitute_fml(v)))
                        .collect(),
                ),
                name,
            ),
            Formula::Unary(op, e) => Formula::Unary(op, Box::new(self.sort_substitute_fml(*e))),
            Formula::Binary(op, l, r) => Formula::Binary(
                op,
                Box::new(self.sort_substitute_fml(*l)),
                Box::new(self.sort_substitute_fml(*r)),
            ),
            Formula::Ite(c, l, r) => Formula::Ite(
                Box::new(self.sort_substitute_fml(*c)),
                Box::new(self.sort_substitute_fml(*l)),
                Box::new(self.sort_substitute_fml(*r)),
            ),
            Formula::Pred(s, name, es) => Formula::Pred(
                self.sort_substitute(s),
                name,
                es.into_iter()
                    .map(|e| self.sort_substitute_fml(e))
                    .collect(),
            ),
            Formula::Cons(s, name, es) => Formula::Cons(
                self.sort_substitute(s),
                name,
                es.into_iter()
                    .map(|e| self.sort_substitute_fml(e))
                    .collect(),
            ),
            Formula::All(x, e) => Formula::All(
                Box::new(self.sort_substitute_fml(*x)),
                Box::new(self.sort_substitute_fml(*e)),
            ),
            _ => fml,
        }
    }
}

pub fn distinct_type_vars(ds: &[impl fmt::Display]) -> Vec<Id> {
    ds.into_iter()
        .map(|d| Id::Local(format!("A{d}").into_boxed_str()))
        .collect()
}

pub fn noncapture_sort_subst(s_vars: Vec<Id>, s_args: Vec<Sort>, s: Sort) -> Sort {
    let distinct_type_vars = distinct_type_vars(&s_vars);
    let s_fresh = SortSubstitution::new(
        s_vars
            .into_iter()
            .zip(distinct_type_vars.clone().into_iter().map(Sort::Var))
            .collect(),
    )
    .sort_substitute(s);

    SortSubstitution::new(distinct_type_vars.clone().into_iter().zip(s_args).collect())
        .sort_substitute(s_fresh)
}

pub fn unify_sorts(
    bound_tvs: &HashSet<Id>,
    mut xs: Vec<Sort>,
    mut ys: Vec<Sort>,
) -> Result<SortSubstitution, (Sort, Sort)> {
    let mut subst = SortSubstitution::default();

    while !xs.is_empty() && !ys.is_empty() {
        let x = xs.remove(0);
        let y = ys.remove(0);

        match (x, y) {
            (x, y) if x == y => continue,
            (Sort::Set(x), Sort::Set(y)) => {
                xs.insert(0, *x);
                ys.insert(0, *y);
            }
            (Sort::Data(name, args), Sort::Data(name_, args_)) => {
                if name == name_ {
                    xs.extend(args);
                    ys.extend(args_);
                } else {
                    return Err((Sort::Data(name, vec![]), Sort::Data(name_, vec![])));
                }
            }
            (Sort::Any, _) => {
                xs.remove(0);
            }
            (_, Sort::Any) => {
                ys.remove(0);
            }
            (Sort::Var(x), y) if !bound_tvs.contains(&x) => match subst.0.entry(x.clone()) {
                Entry::Occupied(entry) => {
                    xs.insert(0, entry.get().clone());
                    ys.insert(0, y);
                }
                Entry::Vacant(entry) => {
                    if y.var_sort_name().map_or(false, |y| bound_tvs.contains(y)) {
                        return Err((Sort::Var(x), y));
                    } else {
                        entry.insert(y);
                    }
                }
            },
            (x, Sort::Var(y)) if !bound_tvs.contains(&y) => {
                xs.insert(0, Sort::Var(y));
                ys.insert(0, x);
            }
            (x, y) => {
                return Err((x, y));
            }
        }
    }

    Ok(subst)
}

#[derive(Debug)]
pub enum SortConstraint {
    SameSort(Sort, Sort),
    IsOrd(Sort),
}

pub fn noncapture_sort_subst_fml(s_vars: Vec<Id>, s_args: Vec<Sort>, fml: Formula) -> Formula {
    let distinct_type_vars = distinct_type_vars(&s_vars);
    let s_fresh = SortSubstitution::new(
        s_vars
            .into_iter()
            .zip(distinct_type_vars.clone().into_iter().map(Sort::Var))
            .collect(),
    )
    .sort_substitute_fml(fml);

    SortSubstitution::new(distinct_type_vars.clone().into_iter().zip(s_args).collect())
        .sort_substitute_fml(s_fresh)
}

pub const EMPTY_SET_CTOR: Id = Id::Builtin("Emptyset");
pub const SINGLETON_CTOR: Id = Id::Builtin("Singleton");
pub const INSERT_SET_CTOR: Id = Id::Builtin("Insert");
pub const SET_TYPE_NAME: Id = Id::Builtin("DSet");
pub const SET_TYPE_VAR: Id = Id::Builtin("setTypeVar");
pub const SET_CONSTRUCTORS: [Id; 3] = [EMPTY_SET_CTOR, SINGLETON_CTOR, INSERT_SET_CTOR];

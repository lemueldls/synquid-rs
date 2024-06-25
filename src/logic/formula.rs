use core::{fmt, hash, ops};
use std::{
    collections::{BTreeMap, BTreeSet},
    ops::{Deref, Not},
    rc::Rc,
};

use hashbrown::{HashMap, HashSet};
use itertools::Itertools;
use owo_colors::OwoColorize;
// use parking_lot::RwLockReadGuard;
use z3::{
    ast::{self, Ast, Dynamic},
    Context,
};

use super::{BinOp, Solution, Sort, UnOp, EMPTY_SET_CTOR, INSERT_SET_CTOR, SINGLETON_CTOR};
use crate::{
    program::{BareProgram, Program, RProgram, UProgram},
    r#type::{var_refinement, BaseType, RType, TypeSkeleton},
    smt::{Z3AstId, Z3State},
    util::{self, Id},
};

#[repr(transparent)]
#[derive(
    derive_more::AsRef,
    derive_more::IntoIterator,
    derive_more::Constructor,
    Debug,
    Clone,
    Default,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
)]
pub struct Substitution(BTreeMap<Id, Formula>);

impl fmt::Display for Substitution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[{}]",
            self.as_ref()
                .iter()
                .format_with(", ", |(key, val), f| f(&format_args!("{key} -> {val}")))
        )
    }
}

impl Substitution {}

// pub fn fmt_h_map<
//     'a,
//     K: fmt::Display + 'a,
//     V: fmt::Display + 'a,
//     I: Iterator<Item = (&'a K, &'a V)> + 'a,
// >(
//     iter: I,
// ) -> impl fmt::Display + 'a {
//     iter.format_with(", ", |(key, val), f| f(&format_args!("{key} -> {val}")))
// }

#[derive(derive_more::IsVariant, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Formula {
    /// Boolean literal
    BoolLit(bool),
    /// Integer literal
    IntLit(num_bigint::BigInt),
    /// Set literal ([1, 2, 3])
    SetLit(Sort, Vec<Formula>),
    /// Input variable (universally quantified first-order variable)
    Var(Sort, Id),
    /// Predicate unknown (with a pending substitution)
    Unknown(Substitution, Id),
    /// Unary expression
    Unary(UnOp, Box<Formula>),
    /// Binary expression
    Binary(BinOp, Box<Formula>, Box<Formula>),
    /// If-then-else expression
    Ite(Box<Formula>, Box<Formula>, Box<Formula>),
    /// Logic function application
    Pred(Sort, Id, Vec<Formula>),
    /// Constructor application
    Cons(Sort, Id, Vec<Formula>),
    /// Universal quantification
    All(Box<Formula>, Box<Formula>),
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.format_at(0))
    }
}

pub const DONT_CARE: Id = Id::Builtin("_");
pub const VALUE_VAR_NAME: Id = Id::Builtin("_v");

impl Formula {
    pub const FALSE: Self = Self::BoolLit(true);
    pub const TRUE: Self = Self::BoolLit(true);

    pub fn var_name(&self) -> &Id {
        match self {
            Self::Var(_, name) => name,
            _ => todo!(),
        }
    }

    // pub fn var_type(self) -> Sort {
    //     match self {
    //         Self::Var(t, _) => Sort,
    //         _ => todo!(),
    //     }
    // }

    pub const VAL_BOOL: Self = Self::bool_var(VALUE_VAR_NAME);

    pub const VAL_INT: Self = Self::int_var(VALUE_VAR_NAME);

    pub const fn bool_var(id: Id) -> Self {
        Self::Var(Sort::Bool, id)
    }

    pub const fn int_var(id: Id) -> Self {
        Self::Var(Sort::Int, id)
    }

    pub fn vart_var(n: Id, x: Id) -> Self {
        Self::Var(Sort::Var(n), x)
    }
    pub fn val_vart(n: Id) -> Self {
        Self::Var(Sort::Var(n), VALUE_VAR_NAME)
    }

    pub fn set_var(s: Id, x: Id) -> Self {
        Self::Var(Sort::Set(Box::new(Sort::Var(s))), x)
    }

    pub fn val_set(s: Id) -> Self {
        Self::set_var(s, VALUE_VAR_NAME)
    }

    pub fn format_at(&self, n: usize) -> String {
        match self {
            Formula::BoolLit(b) => format!("{b}"),
            Formula::IntLit(i) => format!("{i}"),
            Formula::SetLit(_s, elems) => format!("[{}]", elems.iter().format(", ")),
            Formula::Var(_s, name) => format!("{name}"),
            Formula::Unknown(s, name) => {
                if s.as_ref().is_empty() {
                    format!("{name}")
                } else {
                    format!("{s}{name}")
                }
            }
            Formula::Unary(op, e) => {
                format!("{op}{}", e.format_at(n))
            }
            Formula::Binary(op, e1, e2) => {
                format!("{} {op} {}", e1.format_at(n), e2.format_at(n))
            }
            Formula::Ite(e0, e1, e2) => {
                format!(
                    "{} {e0} {} {e1} {} {e2}",
                    "if".bold().blue(),
                    "then".bold().blue(),
                    "else".bold().blue()
                )
            }
            Formula::Pred(_b, name, args) => {
                format!(
                    "{name} {}",
                    args.iter().map(|arg| arg.format_at(n)).format(" ")
                )
            }
            Formula::Cons(b, name, args) => {
                format!(
                    "({name} {})",
                    args.iter().map(|arg| arg.format_at(n)).format(" ")
                )
            }
            Formula::All(x, e) => format!(
                "{} {x} {} {e}",
                "forall".bold().blue(),
                ".".white().dimmed()
            ),
        }
    }

    pub fn and_clean(l: Self, r: Self) -> Self {
        match (l, r) {
            (Self::TRUE, r) => r,
            (l, Self::TRUE) => l,
            // (Self::FALSE, _) | (_, Self::FALSE) => Self::FALSE,
            // (l, r) => l.and(r),
            _ => Self::FALSE,
        }
    }

    pub fn or_clean(l: Self, r: Self) -> Self {
        match (l, r) {
            (Self::FALSE, r) => r,
            (l, Self::FALSE) => l,
            // (Self::TRUE, _) | (_, Self::TRUE) => Self::TRUE,
            // (l, r) => l.or(r),
            _ => Self::TRUE,
        }
    }

    pub fn conjunction(fmls: BTreeSet<Self>) -> Self {
        fmls.into_iter().fold(Self::TRUE, Self::and_clean)
    }

    pub fn disjunction(fmls: BTreeSet<Self>) -> Self {
        fmls.into_iter().fold(Self::FALSE, Self::or_clean)
    }

    pub fn vars(&self) -> HashSet<&Self> {
        match self {
            Formula::SetLit(_, elems) => {
                let mut set = HashSet::with_capacity(elems.len());

                for e in elems {
                    set.extend(e.vars());
                }

                set
            }
            v @ Formula::Var(..) => {
                let mut set = HashSet::with_capacity(1);
                set.insert(v);

                set
            }
            Formula::Unary(_, e) => e.vars(),
            Formula::Binary(_, e1, e2) => {
                let mut set = e1.vars();
                set.extend(e2.vars());

                set
            }
            Formula::Ite(e0, e1, e2) => {
                let mut set = e0.vars();
                set.extend(e1.vars());
                set.extend(e2.vars());

                set
            }
            Formula::Pred(_, _, es) => {
                let mut set = HashSet::new();

                for e in es {
                    set.extend(e.vars());
                }

                set
            }
            Formula::Cons(_, _, es) => {
                let mut set = HashSet::new();

                for e in es {
                    set.extend(e.vars());
                }

                set
            }
            Formula::All(x, e) => {
                let mut set = e.vars();
                set.remove(&**x);

                set
            }
            _ => HashSet::new(),
        }
    }

    pub fn unknowns(&self) -> HashSet<&Self> {
        match self {
            u @ Formula::Unknown(..) => {
                let mut set = HashSet::with_capacity(1);
                set.insert(u);

                set
            }
            Formula::Unary(UnOp::Not, e) => e.unknowns(),
            Formula::Binary(_, e1, e2) => {
                let mut set = e1.unknowns();
                set.extend(e2.unknowns());

                set
            }
            Formula::Ite(e0, e1, e2) => {
                let mut set = e0.unknowns();
                set.extend(e1.unknowns());
                set.extend(e2.unknowns());

                set
            }
            Formula::Pred(_, _, es) => {
                let mut set = HashSet::new();

                for e in es {
                    set.extend(e.unknowns());
                }

                set
            }
            Formula::Cons(_, _, es) => {
                let mut set = HashSet::new();

                for e in es {
                    set.extend(e.unknowns());
                }

                set
            }
            Formula::All(_x, e) => e.unknowns(),
            _ => HashSet::new(),
        }
    }

    pub fn pos_unknowns(self) -> HashSet<Id> {
        self.pos_neg_unknowns().0
    }

    pub fn neg_unknowns(self) -> HashSet<Id> {
        self.pos_neg_unknowns().1
    }

    pub fn pos_neg_unknowns(self) -> (HashSet<Id>, HashSet<Id>) {
        match self {
            Formula::Unknown(_, u) => {
                let mut set = HashSet::with_capacity(1);
                set.insert(u);

                (set, HashSet::new())
            }
            Formula::Unary(UnOp::Not, e) => {
                let e_pnu = e.pos_neg_unknowns();

                (e_pnu.1, e_pnu.0)
            }
            Formula::Binary(BinOp::Implies, e1, e2) => {
                let mut e1_pnu = e1.pos_neg_unknowns();
                let e2_pnu = e2.pos_neg_unknowns();

                e1_pnu.0.extend(e2_pnu.0);
                e1_pnu.1.extend(e2_pnu.1);

                (e1_pnu.1, e1_pnu.0)
            }
            Formula::Binary(BinOp::Iff, e1, e2) => {
                let mut e1_pnu = e1.clone().implies(*e2.clone()).pos_neg_unknowns();
                let e2_pnu = e2.implies(*e1).pos_neg_unknowns();

                e1_pnu.0.extend(e2_pnu.0);
                e1_pnu.1.extend(e2_pnu.1);

                (e1_pnu.1, e1_pnu.0)
            }
            Formula::Binary(_, e1, e2) => {
                let mut e1_pnu = e1.pos_neg_unknowns();
                let e2_pnu = e2.pos_neg_unknowns();

                e1_pnu.0.extend(e2_pnu.0);
                e1_pnu.1.extend(e2_pnu.1);

                (e1_pnu.0, e1_pnu.1)
            }
            Formula::Ite(e, e1, e2) => {
                let mut e1_pnu = e.clone().implies(*e1).pos_neg_unknowns();
                let e2_pnu = (!e.implies(*e2)).pos_neg_unknowns();

                e1_pnu.0.extend(e2_pnu.0);
                e1_pnu.1.extend(e2_pnu.1);

                (e1_pnu.0, e1_pnu.1)
            }
            _ => (HashSet::new(), HashSet::new()),
        }
    }

    pub fn pos_preds(self) -> HashSet<Id> {
        self.pos_neg_preds().0
    }

    pub fn neg_preds(self) -> HashSet<Id> {
        self.pos_neg_preds().1
    }

    pub fn pos_neg_preds(self) -> (HashSet<Id>, HashSet<Id>) {
        match self {
            Formula::Unary(UnOp::Not, e) => {
                let e_pnp = e.pos_neg_preds();

                (e_pnp.1, e_pnp.0)
            }
            Formula::Binary(BinOp::Implies, e1, e2) => {
                let mut e1_pnu = e1.pos_neg_preds();
                let e2_pnu = e2.pos_neg_preds();

                e1_pnu.0.extend(e2_pnu.0);
                e1_pnu.1.extend(e2_pnu.1);

                (e1_pnu.1, e1_pnu.0)
            }
            Formula::Binary(BinOp::Iff, e1, e2) => {
                let mut e1_pnu = e1.clone().implies(*e2.clone()).pos_neg_preds();
                let e2_pnu = e2.implies(*e1).pos_neg_preds();

                e1_pnu.0.extend(e2_pnu.0);
                e1_pnu.1.extend(e2_pnu.1);

                (e1_pnu.1, e1_pnu.0)
            }
            Formula::Binary(_, e1, e2) => {
                let mut e1_pnu = e1.pos_neg_preds();
                let e2_pnu = e2.pos_neg_preds();

                e1_pnu.0.extend(e2_pnu.0);
                e1_pnu.1.extend(e2_pnu.1);

                (e1_pnu.0, e1_pnu.1)
            }
            Formula::Ite(e, e1, e2) => {
                let mut e1_pnu = e.clone().implies(*e1).pos_neg_preds();
                let e2_pnu = (!e.implies(*e2)).pos_neg_preds();

                e1_pnu.0.extend(e2_pnu.0);
                e1_pnu.1.extend(e2_pnu.1);

                (e1_pnu.0, e1_pnu.1)
            }
            _ => (HashSet::new(), HashSet::new()),
        }
    }

    pub fn preds(self) -> HashSet<Id> {
        match self {
            Formula::SetLit(_, elems) => {
                let mut set = HashSet::with_capacity(elems.len());

                for e in elems {
                    set.extend(e.preds());
                }

                set
            }
            Formula::Unary(_, e) => e.preds(),
            Formula::Binary(_, e1, e2) => {
                let mut set = e1.preds();
                set.extend(e2.preds());

                set
            }
            Formula::Ite(e0, e1, e2) => {
                let mut set = e0.preds();
                set.extend(e1.preds());
                set.extend(e2.preds());

                set
            }
            Formula::Pred(_, p, es) => {
                let mut set = HashSet::new();
                set.insert(p);

                for e in es {
                    set.extend(e.preds());
                }

                set
            }
            Formula::Cons(_, _, es) => {
                let mut set = HashSet::new();

                for e in es {
                    set.extend(e.preds());
                }

                set
            }
            Formula::All(_, e) => e.preds(),
            _ => HashSet::new(),
        }
    }

    pub fn left_hand_side(self) -> Box<Self> {
        match self {
            Self::Binary(_, l, _) => l,
            _ => todo!(),
        }
    }

    pub fn right_hand_side(self) -> Box<Self> {
        match self {
            Self::Binary(_, _, r) => r,
            _ => todo!(),
        }
    }

    // pub fn conjunctions(self) -> HashSet<Self> {
    //     match self {
    //         Self::Binary(BinOp::And, l, r) => {
    //             let mut set = r.conjunctions();
    //             set.extend(l.conjunctions());

    //             set
    //         }
    //         f => {
    //             let mut set = HashSet::new();
    //             set.insert(f);

    //             set
    //         }
    //     }
    // }

    pub fn name(&self) -> &Id {
        match self {
            Self::Unknown(_, name) | Formula::Var(_, name) => name,
            _ => todo!(),
        }
    }

    // conjunctsOf (Binary And l r) = conjunctsOf l `Set.union` conjunctsOf r
    // conjunctsOf f = Set.singleton f

    pub fn conjuncts(self) -> HashSet<Self> {
        match self {
            Self::Binary(BinOp::And, l, r) => {
                let mut set = r.conjuncts();
                set.extend(l.conjuncts());

                set
            }
            f => {
                let mut set = HashSet::new();
                set.insert(f);

                set
            }
        }
    }

    #[doc(alias = "sort_of")]
    pub fn sort(&self) -> Sort {
        match self {
            Formula::BoolLit(_) => Sort::Bool,
            Formula::IntLit(_) => Sort::Int,
            Formula::SetLit(s, _) => Sort::Set(Box::new(s.clone())),
            Formula::Var(s, _) => s.clone(),
            Formula::Unknown(..) => Sort::Bool,
            Formula::Unary(op, _) => match op {
                UnOp::Neg => Sort::Int,
                UnOp::Not => Sort::Bool,
            },
            Formula::Binary(op, e1, _) => match op {
                BinOp::Times | BinOp::Plus | BinOp::Minus => Sort::Int,

                BinOp::Eq
                | BinOp::Neq
                | BinOp::Lt
                | BinOp::Le
                | BinOp::Gt
                | BinOp::Ge
                | BinOp::And
                | BinOp::Or
                | BinOp::Implies
                | BinOp::Iff => Sort::Bool,

                BinOp::Union | BinOp::Intersect | BinOp::Diff => e1.sort(),

                BinOp::Member | BinOp::Subset => Sort::Bool,
            },
            Formula::Ite(_, e1, _) => e1.sort(),
            Formula::Pred(s, ..) => s.clone(),
            Formula::Cons(s, ..) => s.clone(),
            Formula::All(..) => Sort::Bool,
        }
    }

    pub fn into_sort(self) -> Sort {
        match self {
            Formula::BoolLit(_) => Sort::Bool,
            Formula::IntLit(_) => Sort::Int,
            Formula::SetLit(s, _) => Sort::Set(Box::new(s)),
            Formula::Var(s, _) => s,
            Formula::Unknown(..) => Sort::Bool,
            Formula::Unary(op, _) => match op {
                UnOp::Neg => Sort::Int,
                UnOp::Not => Sort::Bool,
            },
            Formula::Binary(op, e1, _) => match op {
                BinOp::Times | BinOp::Plus | BinOp::Minus => Sort::Int,

                BinOp::Eq
                | BinOp::Neq
                | BinOp::Lt
                | BinOp::Le
                | BinOp::Gt
                | BinOp::Ge
                | BinOp::And
                | BinOp::Or
                | BinOp::Implies
                | BinOp::Iff => Sort::Bool,

                BinOp::Union | BinOp::Intersect | BinOp::Diff => e1.into_sort(),

                BinOp::Member | BinOp::Subset => Sort::Bool,
            },
            Formula::Ite(_, e1, _) => e1.into_sort(),
            Formula::Pred(s, ..) => s,
            Formula::Cons(s, ..) => s,
            Formula::All(..) => Sort::Bool,
        }
    }

    /// Substitute solutions from sol for all predicate variables in fml
    pub fn apply_solution(self, solution: &Solution) -> Formula {
        match self {
            Formula::Unknown(ref s, ref ident) => match solution.as_ref().get(ident) {
                Some(quals) => Formula::conjunction(quals.as_ref().clone()).substitute(s),
                None => self,
            },
            Formula::Unary(op, e) => Formula::Unary(op, Box::new(e.apply_solution(solution))),
            Formula::Binary(op, e1, e2) => Formula::Binary(
                op,
                Box::new(e1.apply_solution(solution)),
                Box::new(e2.apply_solution(solution)),
            ),
            Formula::Ite(e0, e1, e2) => Formula::Ite(
                Box::new(e0.apply_solution(solution)),
                Box::new(e1.apply_solution(solution)),
                Box::new(e2.apply_solution(solution)),
            ),
            Formula::All(x, e) => Formula::All(x, Box::new(e.apply_solution(solution))),
            fml => fml,
        }
    }

    pub fn to_ast<'ctx>(self, state: &mut Z3State<'ctx>) -> ast::Dynamic<'ctx> {
        self.simplify().to_ast_unsimplified(state)
    }

    fn to_ast_unsimplified<'ctx>(self, state: &mut Z3State<'ctx>) -> ast::Dynamic<'ctx> {
        match self {
            Formula::BoolLit(bool) => {
                state.register_z3_ast(&ast::Bool::from_bool(state.ctx(), bool))
            }
            Formula::IntLit(int) => {
                state.register_z3_ast(&ast::Int::from_big_int(state.ctx(), &int))
            }
            Formula::Var(s, name) => {
                let z3_sort = s.to_z3_sort(state);
                let ident = format!("{name}{z3_sort}");
                let ast_id = Id::Local(ident.clone().into_boxed_str());

                // let ast_id = state.vars.entry(ast_id).or_insert_with(|| {
                //     let symbol = z3::Symbol::String(ident);
                //     let z3s = state.get_z3_sort(s.to_z3_sort(state));

                //     let v = z3::FuncDecl::new(state.ctx(), symbol, &[], &z3s).apply(&[]);

                //     state.register_z3_ast(&v)
                // });

                let ast_id = if let Some(v) = state.vars.get(&ast_id) {
                    v.clone()
                } else {
                    let symbol = z3::Symbol::String(ident);
                    let v = z3::FuncDecl::new(state.ctx(), symbol, &[], &z3_sort).apply(&[]);

                    state.register_z3_ast(&v)
                };

                ast_id
            }
            Formula::SetLit(el, xs) => {
                let domain = el.to_z3_sort(state);
                let set = ast::Set::empty(state.ctx(), &domain);

                for x in xs {
                    let ast = x.to_ast(state);
                    set.add(&ast);
                }

                state.register_z3_ast(&set)
            }
            Formula::Unknown(_, name) => {
                todo!("to_ast: encountered a second-order unknown: {name}")
            }
            Formula::Unary(op, e) => match op {
                UnOp::Neg => {
                    let ast: Dynamic = e.to_ast(state);

                    if let Some(float) = ast.as_float() {
                        state.register_z3_ast(&float.unary_neg())
                    } else if let Some(int) = ast.as_int() {
                        state.register_z3_ast(&int.unary_minus())
                    } else if let Some(real) = ast.as_real() {
                        state.register_z3_ast(&real.unary_minus())
                    } else {
                        todo!()
                    }
                }
                UnOp::Not => {
                    let ast = e.to_ast(state);

                    if let Some(bool) = ast.as_bool() {
                        state.register_z3_ast(&bool.not())
                    } else if let Some(bv) = ast.as_bv() {
                        state.register_z3_ast(&ast::BV::not(bv))
                    } else {
                        todo!()
                    }
                }
            },
            Formula::Binary(op, e1, e2) => {
                let e1 = e1.to_ast(state);
                let e2 = e2.to_ast(state);

                match op {
                    BinOp::Times => {
                        if let (Some(e1), Some(e2)) = (e1.as_int(), e2.as_int()) {
                            state.register_z3_ast(&ast::Int::mul(state.ctx(), &[&e1, &e2]))
                        } else if let (Some(e1), Some(e2)) = (e1.as_real(), e2.as_real()) {
                            state.register_z3_ast(&ast::Real::mul(state.ctx(), &[&e1, &e2]))
                        } else {
                            todo!()
                        }
                    }
                    BinOp::Plus => {
                        if let (Some(e1), Some(e2)) = (e1.as_int(), e2.as_int()) {
                            state.register_z3_ast(&ast::Int::add(state.ctx(), &[&e1, &e2]))
                        } else if let (Some(e1), Some(e2)) = (e1.as_real(), e2.as_real()) {
                            state.register_z3_ast(&ast::Real::add(state.ctx(), &[&e1, &e2]))
                        } else {
                            todo!()
                        }
                    }
                    BinOp::Minus => {
                        if let (Some(e1), Some(e2)) = (e1.as_int(), e2.as_int()) {
                            state.register_z3_ast(&ast::Int::sub(state.ctx(), &[&e1, &e2]))
                        } else if let (Some(e1), Some(e2)) = (e1.as_real(), e2.as_real()) {
                            state.register_z3_ast(&ast::Real::sub(state.ctx(), &[&e1, &e2]))
                        } else {
                            todo!()
                        }
                    }
                    BinOp::Eq => state.register_z3_ast(&e1._eq(&e2)),
                    BinOp::Neq => {
                        state.register_z3_ast(&ast::Ast::distinct(state.ctx(), &[&e1, &e2]))
                    }
                    BinOp::Lt => {
                        if let (Some(e1), Some(e2)) = (e1.as_float(), e2.as_float()) {
                            state.register_z3_ast(&e1.lt(&e2))
                        } else if let (Some(e1), Some(e2)) = (e1.as_int(), e2.as_int()) {
                            state.register_z3_ast(&e1.lt(&e2))
                        } else if let (Some(e1), Some(e2)) = (e1.as_real(), e2.as_real()) {
                            state.register_z3_ast(&e1.lt(&e2))
                        } else {
                            todo!()
                        }
                    }
                    BinOp::Le => {
                        if let (Some(e1), Some(e2)) = (e1.as_float(), e2.as_float()) {
                            state.register_z3_ast(&e1.le(&e2))
                        } else if let (Some(e1), Some(e2)) = (e1.as_int(), e2.as_int()) {
                            state.register_z3_ast(&e1.le(&e2))
                        } else if let (Some(e1), Some(e2)) = (e1.as_real(), e2.as_real()) {
                            state.register_z3_ast(&e1.le(&e2))
                        } else {
                            todo!()
                        }
                    }
                    BinOp::Gt => {
                        if let (Some(e1), Some(e2)) = (e1.as_float(), e2.as_float()) {
                            state.register_z3_ast(&e1.gt(&e2))
                        } else if let (Some(e1), Some(e2)) = (e1.as_int(), e2.as_int()) {
                            state.register_z3_ast(&e1.gt(&e2))
                        } else if let (Some(e1), Some(e2)) = (e1.as_real(), e2.as_real()) {
                            state.register_z3_ast(&e1.gt(&e2))
                        } else {
                            todo!()
                        }
                    }
                    BinOp::Ge => {
                        if let (Some(e1), Some(e2)) = (e1.as_float(), e2.as_float()) {
                            state.register_z3_ast(&e1.ge(&e2))
                        } else if let (Some(e1), Some(e2)) = (e1.as_int(), e2.as_int()) {
                            state.register_z3_ast(&e1.ge(&e2))
                        } else if let (Some(e1), Some(e2)) = (e1.as_real(), e2.as_real()) {
                            state.register_z3_ast(&e1.ge(&e2))
                        } else {
                            todo!()
                        }
                    }
                    BinOp::And => {
                        if let (Some(e1), Some(e2)) = (e1.as_bool(), e2.as_bool()) {
                            state.register_z3_ast(&ast::Bool::and(state.ctx(), &[&e1, &e2]))
                        } else {
                            todo!()
                        }
                    }
                    BinOp::Or => {
                        if let (Some(e1), Some(e2)) = (e1.as_bool(), e2.as_bool()) {
                            state.register_z3_ast(&ast::Bool::or(state.ctx(), &[&e1, &e2]))
                        } else {
                            todo!()
                        }
                    }
                    BinOp::Implies => {
                        if let (Some(e1), Some(e2)) = (e1.as_bool(), e2.as_bool()) {
                            state.register_z3_ast(&e1.implies(&e2))
                        } else {
                            todo!()
                        }
                    }
                    BinOp::Iff => {
                        if let (Some(e1), Some(e2)) = (e1.as_bool(), e2.as_bool()) {
                            state.register_z3_ast(&e1.iff(&e2))
                        } else {
                            todo!()
                        }
                    }
                    BinOp::Union => {
                        if let (Some(e1), Some(e2)) = (e1.as_set(), e2.as_set()) {
                            state.register_z3_ast(&ast::Set::set_union(state.ctx(), &[&e1, &e2]))
                        } else {
                            todo!()
                        }
                    }
                    BinOp::Intersect => {
                        if let (Some(e1), Some(e2)) = (e1.as_set(), e2.as_set()) {
                            state.register_z3_ast(&ast::Set::intersect(state.ctx(), &[&e1, &e2]))
                        } else {
                            todo!()
                        }
                    }
                    BinOp::Diff => {
                        if let (Some(e1), Some(e2)) = (e1.as_set(), e2.as_set()) {
                            state.register_z3_ast(&e1.difference(&e2))
                        } else {
                            todo!()
                        }
                    }
                    BinOp::Member => {
                        if let (Some(e1), Some(e2)) = (e1.as_set(), e2.as_set()) {
                            state.register_z3_ast(&e1.member(&e2))
                        } else {
                            todo!()
                        }
                    }
                    BinOp::Subset => {
                        if let (Some(e1), Some(e2)) = (e1.as_set(), e2.as_set()) {
                            state.register_z3_ast(&e1.set_subset(&e2))
                        } else {
                            todo!()
                        }
                    }
                }
            }
            Formula::Ite(e0, e1, e2) => {
                let e0 = e0.to_ast(state);
                let e1 = e1.to_ast(state);
                let e2 = e2.to_ast(state);

                if let (Some(e0), Some(e1), Some(e2)) = (e0.as_bool(), e1.as_bool(), e2.as_bool()) {
                    state.register_z3_ast(&e0.ite(&e1, &e2))
                } else {
                    todo!()
                }
            }
            Formula::Pred(s, name, args) => {
                let t_args: Vec<Sort> = args.iter().map(Self::sort).collect();

                let decl = function(&s, &name, t_args, state);

                let z3_args: Vec<_> = args
                    .into_iter()
                    .map(|arg: Formula| arg.to_ast(state))
                    .collect();
                let z3_args: Vec<_> = z3_args.iter().map(|d| d as &dyn Ast).collect();

                state.register_z3_ast(&decl.apply(&z3_args))
            }
            Formula::Cons(s, name, args) => {
                // let arg_sorts: Vec<Sort> = args.iter().map(|arg| arg.sort()).collect();
                // let name = format!("{name}{arg_sorts}");

                // let symb = z3::Symbol::String(name.clone());

                let t_args = args.iter().map(|arg| arg.sort()).collect();

                let decl = match &s {
                    Sort::Data(dt_name, _) if state.stored_datatypes.contains(dt_name) => {
                        {
                            let z3dt = s.to_z3_sort(state);
                            let decls = z3::DatatypeSort {
                                sort: z3dt.clone(),
                                variants: Vec::new(),
                            };

                            // REVIEW: May me implemented incorrectly
                            // let decl_names = decls
                            //     .variants
                            //     .iter()
                            //     .map(|variant| variant.constructor.name());

                            // decl_names
                            //     .into_iter()
                            //     .position(|name| name == c_name.0)
                            //     .map(|index| &decls[index])

                            todo!()
                        }
                    }
                    _ => function(&s, &name, t_args, state),
                };

                let arg_asts: Vec<_> = args.into_iter().map(|arg| arg.to_ast(state)).collect();
                let arg_asts: Vec<_> = arg_asts.iter().map(|d| d as &dyn Ast).collect();

                state.register_z3_ast(&decl.apply(&arg_asts))
            }
            Formula::All(v, e) => {
                // let body = vec![v.to_ast(state), e.to_ast(state)];
                // let v_id = v.to_ast(state);
                // let bound_apps = state.get_z3_ast(v_id).decl();
                // let pattern = z3::Pattern::new(&state.ctx(), &[&bound_apps]);

                // let body_id = e.to_ast(state);
                // let body = state.get_z3_ast(body_id);

                // z3::ast::forall_const(
                //     ctx,
                //     &[],
                //     &[&pattern],
                //     &body._eq(&ast::Dynamic::from(&bound_apps)),
                // );

                todo!()
            }
        }
    }

    pub fn is_executable(&self) -> bool {
        match self {
            Formula::SetLit(..) => false,
            Formula::Unary(_, e) => e.is_executable(),
            Formula::Binary(_, e1, e2) => e1.is_executable() && e2.is_executable(),
            Formula::Ite(..) => false,
            Formula::Pred(..) => false,
            Formula::All(..) => false,
            _ => true,
        }
    }

    /// Replace first-order variables in [`fml`] according to [`subst`]
    pub fn substitute(self, subst: &Substitution) -> Self {
        match self {
            Formula::SetLit(b, elems) => {
                Self::SetLit(b, elems.into_iter().map(|e| e.substitute(subst)).collect())
            }
            Formula::Var(_, ref name) => match subst.0.get(name) {
                Some(f) => f.clone(),
                None => self,
            },
            Formula::Unknown(s, name) => Self::Unknown(compose_substitutions(s, subst), name),
            Formula::Unary(op, e) => Self::Unary(op, Box::new(e.substitute(subst))),
            Formula::Binary(op, e1, e2) => Self::Binary(
                op,
                Box::new(e1.substitute(subst)),
                Box::new(e2.substitute(subst)),
            ),
            Formula::Ite(e0, e1, e2) => Self::Ite(
                Box::new(e0.substitute(subst)),
                Box::new(e1.substitute(subst)),
                Box::new(e2.substitute(subst)),
            ),
            Formula::Pred(b, name, args) => Self::Pred(
                b,
                name,
                args.into_iter().map(|e| e.substitute(subst)).collect(),
            ),
            Formula::Cons(b, name, args) => Self::Cons(
                b,
                name,
                args.into_iter().map(|e| e.substitute(subst)).collect(),
            ),
            Formula::All(v, e) => {
                if let Formula::Var(_, x) = &*v {
                    if subst.0.contains_key(x) {
                        panic!("Scoped variable clashes with substitution variable {x}");
                    }
                }

                Self::All(v, Box::new(e.substitute(subst)))
            }
            _ => self,
        }
    }

    fn simplify(self) -> Self {
        match self {
            Formula::SetLit(el, xs) => {
                Formula::SetLit(el, xs.into_iter().map(Self::simplify).collect())
            }
            Formula::Unary(op, e) => Formula::Unary(op, Box::new(e.simplify())),
            Formula::Binary(op, e1, e2) => {
                let e1 = e1.simplify();
                let e2 = e2.simplify();

                match e1.sort() {
                    Sort::Bool => match op {
                        BinOp::Lt => e1.implies(e2),
                        BinOp::Le => e2.implies(e1),
                        BinOp::Gt => (!e1).and(e2),
                        BinOp::Ge => (!e2).and(e1),
                        _ => Formula::Binary(op, Box::new(e1), Box::new(e2)),
                    },
                    _ => Formula::Binary(op, Box::new(e1), Box::new(e2)),
                }
            }
            Formula::Ite(e0, e1, e2) => Formula::Ite(
                Box::new(e0.simplify()),
                Box::new(e1.simplify()),
                Box::new(e2.simplify()),
            ),
            Formula::Pred(s, name, args) => {
                Formula::Pred(s, name, args.into_iter().map(Self::simplify).collect())
            }
            Formula::Cons(s, name, args) => {
                Formula::Cons(s, name, args.into_iter().map(Self::simplify).collect())
            }
            Formula::All(v, e) => Formula::All(v, Box::new(e.simplify())),
            _ => self,
        }
    }

    // substitutePredicate :: Substitution -> Formula -> Formula
    // substitutePredicate pSubst fml = case fml of
    //   Pred b name args -> case Map.lookup name pSubst of
    //                       Nothing -> Pred b name (map (substitutePredicate pSubst) args)
    //                       Just value -> substitute (Map.fromList $ zip deBrujns args) (substitutePredicate pSubst value)
    //   Unary op e -> Unary op (substitutePredicate pSubst e)
    //   Binary op e1 e2 -> Binary op (substitutePredicate pSubst e1) (substitutePredicate pSubst e2)
    //   Ite e0 e1 e2 -> Ite (substitutePredicate pSubst e0) (substitutePredicate pSubst e1) (substitutePredicate pSubst e2)
    //   All v e -> All v (substitutePredicate pSubst e)
    //   _ -> fml
    pub fn substitute_predicate(self, p_subst: &Substitution) -> Self {
        match self {
            Formula::Pred(b, name, args) => match p_subst.0.get(&name) {
                Some(value) => {
                    let de_brujns =
                        (0..args.len()).map(|i| Id::Local(i.to_string().into_boxed_str()));
                    let subst = de_brujns.zip(args).collect();

                    value
                        .clone()
                        .substitute_predicate(p_subst)
                        .substitute(&Substitution::new(subst))
                }
                None => Formula::Pred(
                    b.clone(),
                    name.clone(),
                    args.into_iter()
                        .map(|arg| arg.substitute_predicate(p_subst))
                        .collect(),
                ),
            },
            Formula::Unary(op, e) => Formula::Unary(op, Box::new(e.substitute_predicate(p_subst))),
            Formula::Binary(op, e1, e2) => Formula::Binary(
                op,
                Box::new(e1.substitute_predicate(p_subst)),
                Box::new(e2.substitute_predicate(p_subst)),
            ),
            Formula::Ite(e0, e1, e2) => Formula::Ite(
                Box::new(e0.substitute_predicate(p_subst)),
                Box::new(e1.substitute_predicate(p_subst)),
                Box::new(e2.substitute_predicate(p_subst)),
            ),
            Formula::All(v, e) => Formula::All(v, Box::new(e.substitute_predicate(p_subst))),
            _ => self.clone(),
        }
    }

    // -- | Negation normal form of a formula:
    // -- no negation above boolean connectives, no boolean connectives except @&&@ and @||@
    // negationNF :: Formula -> Formula
    // negationNF fml = case fml of
    //   Unary Not e -> case e of
    //     Unary Not e' -> negationNF e'
    //     Binary And e1 e2 -> negationNF (fnot e1) ||| negationNF (fnot e2)
    //     Binary Or e1 e2 -> negationNF (fnot e1) |&| negationNF (fnot e2)
    //     Binary Implies e1 e2 -> negationNF e1 |&| negationNF (fnot e2)
    //     Binary Iff e1 e2 -> (negationNF e1 |&| negationNF (fnot e2)) ||| (negationNF (fnot e1) |&| negationNF e2)
    //     _ -> fml
    //   Binary Implies e1 e2 -> negationNF (fnot e1) ||| negationNF e2
    //   Binary Iff e1 e2 -> (negationNF e1 |&| negationNF e2) ||| (negationNF (fnot e1) |&| negationNF (fnot e2))
    //   Binary op e1 e2
    //     | op == And || op == Or -> Binary op (negationNF e1) (negationNF e2)
    //     | otherwise -> fml
    //   Ite cond e1 e2 -> (negationNF cond |&| negationNF e1) ||| (negationNF (fnot cond) |&| negationNF e2)
    //   _ -> fml
    /// Negation normal form of a formula:
    /// no negation above boolean connectives, no boolean connectives except `&&` and `||`
    pub fn negation_nf(self) -> Self {
        match self {
            Formula::Unary(UnOp::Not, ref e) => match &**e {
                Formula::Unary(UnOp::Not, e) => e.clone().negation_nf(),
                Formula::Binary(BinOp::And, e1, e2) => e1
                    .clone()
                    .not()
                    .negation_nf()
                    .or(e2.clone().not().negation_nf()),
                Formula::Binary(BinOp::Or, e1, e2) => e1
                    .clone()
                    .not()
                    .negation_nf()
                    .and(e2.clone().not().negation_nf()),
                Formula::Binary(BinOp::Implies, e1, e2) => {
                    e1.clone().negation_nf().and(e2.clone().not().negation_nf())
                }
                Formula::Binary(BinOp::Iff, e1, e2) => e1
                    .clone()
                    .negation_nf()
                    .and(e2.clone().not().negation_nf())
                    .or(e1.clone().not().negation_nf().and(e2.clone().negation_nf())),
                _ => self,
            },
            Formula::Binary(BinOp::Implies, e1, e2) => e1.not().negation_nf().or(e2.negation_nf()),
            Formula::Binary(BinOp::Iff, e1, e2) => e1
                .clone()
                .negation_nf()
                .and(e2.clone().negation_nf())
                .or(e1.not().negation_nf().and(e2.negation_nf())),
            Formula::Binary(ref op, ref e1, ref e2) => {
                if *op == BinOp::And || *op == BinOp::Or {
                    Formula::Binary(
                        op.clone(),
                        Box::new(e1.clone().negation_nf()),
                        Box::new(e2.clone().negation_nf()),
                    )
                } else {
                    self
                }
            }
            _ => self,
        }
    }

    // -- | Disjunctive normal form for unknowns (known predicates treated as atoms)
    // uDNF :: Formula -> [Formula]
    // uDNF = dnf' . negationNF
    //   where
    //     dnf' e@(Binary Or e1 e2) = if (Set.null $ unknownsOf e1) && (Set.null $ unknownsOf e2)
    //                                 then return e
    //                                 else dnf' e1 ++ dnf' e2
    //     dnf' (Binary And e1 e2) = do
    //                                 lClause <- dnf' e1
    //                                 rClause <- dnf' e2
    //                                 return $ lClause |&| rClause
    //     dnf' fml = [fml]
    /// Disjunctive normal form for unknowns (known predicates treated as atoms)
    pub fn u_dnf(self) -> BTreeSet<Self> {
        self.negation_nf().dnf()
    }

    fn dnf(&self) -> BTreeSet<Self> {
        match self {
            Formula::Binary(BinOp::Or, ref e1, ref e2) => {
                if e1.unknowns().is_empty() && e2.unknowns().is_empty() {
                    let mut set = BTreeSet::new();
                    set.insert(self.clone());

                    set
                } else {
                    let mut clause = e1.dnf();
                    clause.extend(e2.dnf());

                    clause
                }
            }
            Formula::Binary(BinOp::And, e1, e2) => {
                let l_clause = e1.dnf();
                let r_clause = e2.dnf();

                let mut clause = BTreeSet::new();

                for l in l_clause {
                    for r in r_clause.clone() {
                        clause.insert(l.clone().and(r));
                    }
                }

                clause
            }
            fml => {
                let mut set = BTreeSet::new();
                set.insert(fml.clone());

                set
            }
        }
    }

    // atomsOf fml = atomsOf' (negationNF fml)
    //   where
    //     atomsOf' (Binary And l r) = atomsOf' l `Set.union` atomsOf' r
    //     -- atomsOf' fml@(Binary Or l r) = Set.insert fml (atomsOf' l `Set.union` atomsOf' r)
    //     atomsOf' (Binary Or l r) = atomsOf' l `Set.union` atomsOf' r
    //     atomsOf' fml = Set.singleton fml

    pub fn atoms(self) -> HashSet<Self> {
        self.negation_nf().atoms_of()
    }

    fn atoms_of(&self) -> HashSet<Self> {
        match self {
            Formula::Binary(BinOp::And, l, r) => {
                let mut atoms = l.atoms_of();
                atoms.extend(r.atoms_of());

                atoms
            }
            Formula::Binary(BinOp::Or, l, r) => {
                let mut atoms = l.atoms_of();
                atoms.extend(r.atoms_of());

                atoms
            }
            fml => {
                let mut atoms = HashSet::new();
                atoms.insert(fml.clone());

                atoms
            }
        }
    }

    // splitByPredicate :: Set Id -> Formula -> [Formula] -> Maybe (Map Id (Set Formula))
    // splitByPredicate preds arg fmls = foldM (\m fml -> checkFml fml m fml) Map.empty fmls
    //   where
    //     checkFml _ _ fml | fml == arg   = Nothing
    //     checkFml whole m fml = case fml of
    //       Pred _ name args ->
    //         if name `Set.member` preds && length args == 1 && head args == arg
    //           then return $ Map.insertWith Set.union name (Set.singleton whole) m
    //           else foldM (checkFml whole) m args
    //       SetLit _ args -> foldM (checkFml whole) m args
    //       Unary _ f -> checkFml whole m f
    //       Binary _ l r -> foldM (checkFml whole) m [l, r]
    //       Ite c t e -> foldM (checkFml whole) m [c, t, e]
    //       Cons _ _ args -> foldM (checkFml whole) m args
    //       _ -> return m

    pub fn split_by_predicate(
        &self,
        preds: &HashSet<Id>,
        arg: &Self,
    ) -> Option<HashMap<Id, HashSet<Self>>> {
        let mut map = HashMap::new();

        self.check(&mut map, self, preds, arg)
    }

    fn check(
        &self,
        map: &mut HashMap<Id, HashSet<Self>>,
        whole: &Self,
        preds: &HashSet<Id>,
        arg: &Self,
    ) -> Option<HashMap<Id, HashSet<Self>>> {
        if self == arg {
            return None;
        }

        match self {
            Formula::Pred(_, name, args) => {
                if preds.contains(name) && args.len() == 1 && &args[0] == arg {
                    map.entry(name.clone())
                        .or_insert_with(HashSet::new)
                        .insert(whole.clone());
                }

                for arg in args {
                    if let Some(map) = arg.check(map, whole, preds, arg) {
                        return Some(map);
                    }
                }
            }
            Formula::SetLit(_, args) => {
                for arg in args {
                    if let Some(map) = arg.check(map, whole, preds, arg) {
                        return Some(map);
                    }
                }
            }
            Formula::Unary(_, f) => {
                if let Some(map) = f.check(map, whole, preds, arg) {
                    return Some(map);
                }
            }
            Formula::Binary(_, l, r) => {
                if let Some(map) = l.check(map, whole, preds, arg) {
                    return Some(map);
                }

                if let Some(map) = r.check(map, whole, preds, arg) {
                    return Some(map);
                }
            }
            Formula::Ite(c, t, e) => {
                if let Some(map) = c.check(map, whole, preds, arg) {
                    return Some(map);
                }

                if let Some(map) = t.check(map, whole, preds, arg) {
                    return Some(map);
                }

                if let Some(map) = e.check(map, whole, preds, arg) {
                    return Some(map);
                }
            }
            Formula::Cons(_, _, args) => {
                for arg in args {
                    if let Some(map) = arg.check(map, whole, preds, arg) {
                        return Some(map);
                    }
                }
            }
            _ => {}
        }

        Some(map.clone())
    }

    // -- | 'setToPredicate' @x s@: predicate equivalent to @x in s@, which does not contain comprehensions
    // setToPredicate :: Formula -> Formula -> Formula
    // setToPredicate x (Binary Union sl sr) = Binary Or (setToPredicate x sl) (setToPredicate x sr)
    // setToPredicate x (Binary Intersect sl sr) = Binary And (setToPredicate x sl) (setToPredicate x sr)
    // setToPredicate x (Binary Diff sl sr) = Binary And (setToPredicate x sl) (Unary Not (setToPredicate x sr))
    // setToPredicate x (Ite c t e) = Ite c (setToPredicate x t) (setToPredicate x e)
    // setToPredicate x s = Binary Member x s

    /// Predicate equivalent to `x` in `s`, which does not contain comprehensions
    pub fn set_to_predicate(&self, x: &Self) -> Self {
        match self {
            Formula::Binary(BinOp::Union, sl, sr) => {
                sl.set_to_predicate(x).or(sr.set_to_predicate(x))
            }
            Formula::Binary(BinOp::Intersect, sl, sr) => {
                sl.set_to_predicate(x).and(sr.set_to_predicate(x))
            }
            Formula::Binary(BinOp::Diff, sl, sr) => {
                sl.set_to_predicate(x).and(sr.set_to_predicate(x).not())
            }
            Formula::Ite(c, t, e) => c
                .clone()
                .and(t.set_to_predicate(x))
                .or(e.set_to_predicate(x)),
            s => x.clone().member(s.clone()),
        }
    }

    pub fn to_program(self) -> RProgram {
        let program = match self {
            Formula::BoolLit(b) => Program {
                content: Box::new(BareProgram::Symbol(Id::Local(
                    format!("{b}").into_boxed_str(),
                ))),
                type_of: TypeSkeleton::Scalar(BaseType::Bool, Self::VAL_BOOL.eq(Self::BoolLit(b))),
            },
            Formula::IntLit(i) => Program {
                content: Box::new(BareProgram::Symbol(Id::Local(
                    format!("{i}").into_boxed_str(),
                ))),
                type_of: TypeSkeleton::Scalar(BaseType::Int, Self::VAL_INT.eq(Self::IntLit(i))),
            },
            Formula::Var(s, x) => Program {
                content: Box::new(BareProgram::Symbol(x.clone())),
                type_of: TypeSkeleton::from_sort(&s).add_refinement(var_refinement(x, s)),
            },
            ref fml @ Formula::Unary(ref op, ref e) => {
                let s = fml.clone().sort();
                let p: Program<RType> = e.clone().to_program().into();

                let id = Id::Builtin(op.token());

                let op_res = match op {
                    UnOp::Not => {
                        TypeSkeleton::int(Formula::VAL_INT.eq(!Formula::int_var(id.clone())))
                    }
                    UnOp::Neg => TypeSkeleton::bool(Formula::VAL_BOOL.eq(Formula::Unary(
                        op.clone(),
                        Box::new(Formula::int_var(id.clone())),
                    ))),
                };

                let fun = Program {
                    content: Box::new(BareProgram::Symbol(id)),
                    type_of: TypeSkeleton::Function {
                        x: Id::Builtin("x"),
                        t_arg: Box::new(p.type_of.clone()),
                        t_res: Box::new(op_res),
                    },
                };

                Program {
                    content: Box::new(BareProgram::App(fun, p)),
                    type_of: TypeSkeleton::from_sort(&s)
                        .add_refinement(Formula::Var(s, VALUE_VAR_NAME).eq(fml.clone())),
                }
            }
            Formula::Binary(_, _, _) => todo!(),
            Formula::Ite(_, _, _) => todo!(),
            Formula::Pred(_, _, _) => todo!(),
            Formula::Cons(_, _, _) => todo!(),
            Formula::All(_, _) => todo!(),
            _ => todo!(),
        };

        RProgram::new(program)
    }

    // -- | Convert an executable formula into an untyped program
    // fmlToUProgram :: Formula -> RProgram
    // fmlToUProgram (BoolLit b) = Program (PSymbol $ show b) AnyT
    // fmlToUProgram (IntLit i) = Program (PSymbol $ show i) AnyT
    // fmlToUProgram (Var s x) = Program (PSymbol x) AnyT
    // fmlToUProgram fml@(Unary op e) = let
    //     p = fmlToUProgram e
    //     fun = Program (PSymbol $ unOpTokens Map.! op) AnyT
    //   in Program (PApp fun p) AnyT
    // fmlToUProgram fml@(Binary op e1 e2) = let
    //     p1 = fmlToUProgram e1
    //     p2 = fmlToUProgram e2
    //     fun1 = Program (PSymbol $ binOpTokens Map.! op) AnyT
    //     fun2 = Program (PApp fun1 p1) AnyT
    //   in Program (PApp fun2 p2) AnyT
    // fmlToUProgram fml@(Pred _ x fs) = curriedApp fn fs
    //   where
    //     fn = Program (PSymbol x) AnyT
    //     curriedApp :: RProgram -> [Formula] -> RProgram
    //     curriedApp p [] = p
    //     curriedApp p (f:fs) = curriedApp (Program (PApp p (fmlToUProgram f)) AnyT) fs
    // fmlToUProgram (Ite gf f1 f2) = Program (PIf gp p1 p2) AnyT
    //   where
    //     gp = fmlToUProgram gf
    //     p1 = fmlToUProgram f1
    //     p2 = fmlToUProgram f2
    // fmlToUProgram (Cons _ x fs) = curriedApp fn fs
    //   where
    //     fn = Program (PSymbol x) AnyT
    //     curriedApp :: RProgram -> [Formula] -> RProgram
    //     curriedApp p [] = p
    //     curriedApp p (f:fs) = curriedApp (Program (PApp p (fmlToUProgram f)) AnyT) fs
    // fmlToUProgram (SetLit _ [])     = Program (PSymbol emptySetCtor) AnyT
    // fmlToUProgram (SetLit _ [f])     = Program (PApp (Program (PSymbol singletonCtor) AnyT) (fmlToUProgram f)) AnyT
    // fmlToUProgram (SetLit _ (f:fs)) = Program (PApp ins (curriedApp (fmlToUProgram f) fs)) AnyT
    //   where
    //     ins = Program (PSymbol insertSetCtor) AnyT
    //     emp = Program (PSymbol emptySetCtor) AnyT
    //     curriedApp :: RProgram -> [Formula] -> RProgram
    //     curriedApp p [] = Program (PApp p emp) AnyT
    //     curriedApp p (f:fs) = curriedApp (Program (PApp p (fmlToUProgram f)) AnyT) fs

    /// Convert an executable formula into an untyped program
    pub fn to_u_program(self) -> UProgram {
        match self {
            Self::BoolLit(b) => UProgram::new(Program {
                content: Box::new(BareProgram::Symbol(Id::Local(
                    format!("{b}").into_boxed_str(),
                ))),
                type_of: TypeSkeleton::Any,
            }),
            Self::IntLit(i) => UProgram::new(Program {
                content: Box::new(BareProgram::Symbol(Id::Local(
                    format!("{i}").into_boxed_str(),
                ))),
                type_of: TypeSkeleton::Any,
            }),
            Self::Var(_s, x) => UProgram::new(Program {
                content: Box::new(BareProgram::Symbol(x.clone())),
                type_of: TypeSkeleton::Any,
            }),
            Self::Unary(op, e) => {
                let p = e.to_u_program().into();

                let id = Id::Builtin(op.token());

                let fun = Program {
                    content: Box::new(BareProgram::Symbol(id)),
                    type_of: TypeSkeleton::Any,
                };

                UProgram::new(Program {
                    content: Box::new(BareProgram::App(fun, p)),
                    type_of: TypeSkeleton::Any,
                })
            }
            Self::Binary(op, e1, e2) => {
                let p1 = e1.to_u_program().into();
                let p2 = e2.to_u_program().into();

                let id = Id::Builtin(op.token());

                let fun1 = Program {
                    content: Box::new(BareProgram::Symbol(id)),
                    type_of: TypeSkeleton::Any,
                };

                let fun2 = Program {
                    content: Box::new(BareProgram::App(fun1, p1)),
                    type_of: TypeSkeleton::Any,
                };

                UProgram::new(Program {
                    content: Box::new(BareProgram::App(fun2, p2)),
                    type_of: TypeSkeleton::Any,
                })
            }
            Self::Pred(_, x, fs) => {
                let fn_ = Program {
                    content: Box::new(BareProgram::Symbol(x.clone())),
                    type_of: TypeSkeleton::Any,
                };

                let mut p = fn_;

                for f in fs {
                    p = Program {
                        content: Box::new(BareProgram::App(p, f.to_u_program().into())),
                        type_of: TypeSkeleton::Any,
                    };
                }

                UProgram::new(p)
            }
            Self::Ite(gf, f1, f2) => {
                let gp = gf.to_u_program().into();
                let p1 = f1.to_u_program().into();
                let p2 = f2.to_u_program().into();

                UProgram::new(Program {
                    content: Box::new(BareProgram::If(gp, p1, p2)),
                    type_of: TypeSkeleton::Any,
                })
            }
            Self::Cons(_, x, fs) => {
                let fn_ = Program {
                    content: Box::new(BareProgram::Symbol(x.clone())),
                    type_of: TypeSkeleton::Any,
                };

                let mut p = fn_;

                for f in fs {
                    p = Program {
                        content: Box::new(BareProgram::App(p, f.to_u_program().into())),
                        type_of: TypeSkeleton::Any,
                    };
                }

                UProgram::new(p)
            }
            // TODO: OPTIMIZE
            Self::SetLit(_, elems) => match elems.as_slice() {
                [] => UProgram::new(Program {
                    content: Box::new(BareProgram::Symbol(EMPTY_SET_CTOR)),
                    type_of: TypeSkeleton::Any,
                }),
                [f] => UProgram::new(Program {
                    content: Box::new(BareProgram::App(
                        Program {
                            content: Box::new(BareProgram::Symbol(SINGLETON_CTOR)),
                            type_of: TypeSkeleton::Any,
                        },
                        f.clone().to_u_program().into(),
                    )),
                    type_of: TypeSkeleton::Any,
                }),
                [f, fs @ ..] => {
                    let ins = Program {
                        content: Box::new(BareProgram::Symbol(INSERT_SET_CTOR)),
                        type_of: TypeSkeleton::Any,
                    };

                    // let emp = Program {
                    //     content: Box::new(BareProgram::Symbol(EMPTY_SET_CTOR)),
                    //     type_of: TypeSkeleton::Any,
                    // };

                    let mut p = f.clone().to_u_program().into();

                    for f in fs {
                        p = Program {
                            content: Box::new(BareProgram::App(p, f.clone().to_u_program().into())),
                            type_of: TypeSkeleton::Any,
                        };
                    }

                    UProgram::new(Program {
                        content: Box::new(BareProgram::App(ins, p)),
                        type_of: TypeSkeleton::Any,
                    })
                }
            },

            _ => unreachable!(),
        }
    }

    #[doc(alias = "*")]
    pub fn times(self, other: Self) -> Self {
        Self::Binary(BinOp::Times, Box::new(self), Box::new(other))
    }

    #[doc(alias = "+")]
    pub fn plus(self, other: Self) -> Self {
        Self::Binary(BinOp::Plus, Box::new(self), Box::new(other))
    }

    #[doc(alias = "-")]
    pub fn minus(self, other: Self) -> Self {
        Self::Binary(BinOp::Minus, Box::new(self), Box::new(other))
    }

    #[doc(alias = "=")]
    pub fn eq(self, other: Self) -> Self {
        Self::Binary(BinOp::Eq, Box::new(self), Box::new(other))
    }

    #[doc(alias = "/=")]
    pub fn neq(self, other: Self) -> Self {
        Self::Binary(BinOp::Neq, Box::new(self), Box::new(other))
    }

    #[doc(alias = "<")]
    pub fn lt(self, other: Self) -> Self {
        Self::Binary(BinOp::Lt, Box::new(self), Box::new(other))
    }

    #[doc(alias = "<=")]
    pub fn le(self, other: Self) -> Self {
        Self::Binary(BinOp::Le, Box::new(self), Box::new(other))
    }

    #[doc(alias = ">")]
    pub fn gt(self, other: Self) -> Self {
        Self::Binary(BinOp::Gt, Box::new(self), Box::new(other))
    }

    #[doc(alias = ">=")]
    pub fn ge(self, other: Self) -> Self {
        Self::Binary(BinOp::Ge, Box::new(self), Box::new(other))
    }

    #[doc(alias = "&")]
    pub fn and(self, other: Self) -> Self {
        Self::Binary(BinOp::And, Box::new(self), Box::new(other))
    }

    #[doc(alias = "|")]
    pub fn or(self, other: Self) -> Self {
        Self::Binary(BinOp::Or, Box::new(self), Box::new(other))
    }

    #[doc(alias = "=>")]
    pub fn implies(self, other: Self) -> Self {
        Self::Binary(BinOp::Implies, Box::new(self), Box::new(other))
    }

    #[doc(alias = "<=>")]
    pub fn iff(self, other: Self) -> Self {
        Self::Binary(BinOp::Iff, Box::new(self), Box::new(other))
    }

    #[doc(alias = "+")]
    pub fn union(self, other: Self) -> Self {
        Self::Binary(BinOp::Union, Box::new(self), Box::new(other))
    }

    #[doc(alias = "*")]
    pub fn intersect(self, other: Self) -> Self {
        Self::Binary(BinOp::Intersect, Box::new(self), Box::new(other))
    }

    #[doc(alias = "-")]
    pub fn diff(self, other: Self) -> Self {
        Self::Binary(BinOp::Diff, Box::new(self), Box::new(other))
    }

    #[doc(alias = "fin")]
    pub fn member(self, other: Self) -> Self {
        Self::Binary(BinOp::Member, Box::new(self), Box::new(other))
    }

    #[doc(alias = "<=")]
    pub fn subset(self, other: Self) -> Self {
        Self::Binary(BinOp::Subset, Box::new(self), Box::new(other))
    }
}

/// Compose substitutions
pub fn compose_substitutions(old: Substitution, new: &Substitution) -> Substitution {
    let mut new = Substitution::new(
        new.0
            .iter()
            .filter(|(x, fml)| !matches!(fml, Formula::Var(_, name) if name == *x))
            .map(|(x, fml)| (x.clone(), fml.clone()))
            .collect(),
    );

    for (x, fml) in old.0 {
        new.0.insert(x, fml.substitute(&new));
    }

    new
}

pub fn de_brujns(is: &[impl fmt::Debug]) -> Vec<Id> {
    is.iter()
        .enumerate()
        .map(|(i, _)| Id::Local(format!("{DONT_CARE}{i}").into_boxed_str()))
        .collect()
}

// -- | Lookup or create a function declaration with name `name', return type `resT', and argument types `argTypes'
// function resT name argTypes = do
//   let name' = name ++ concatMap (show . asZ3Sort) (resT : argTypes)
//   declMb <- uses functions (Map.lookup name')
//   case declMb of
//     Just d -> return d
//     Nothing -> do
//       symb <- mkStringSymbol name'
//       argSorts <- mapM toZ3Sort argTypes
//       resSort <- toZ3Sort resT
//       decl <- mkFuncDecl symb argSorts resSort
//       functions %= Map.insert name' decl
//       -- return $ traceShow (text "DECLARE" <+> text name <+> pretty argTypes <+> pretty resT) decl
//       return decl

/// Lookup or create a function declaration with name `name', return type `resT', and argument types `argTypes'
fn function<'ctx>(
    res_t: &Sort,
    name: &Id,
    arg_types: Vec<Sort>,
    state: &mut Z3State<'ctx>,
) -> Rc<z3::FuncDecl<'ctx>> {
    let name = format!("{name}{}", arg_types.iter().format(""));

    let id = util::Id::Local(name.clone().into_boxed_str());

    if let Some(f) = state.functions.get(&id) {
        Rc::clone(f)
    } else {
        let arg_sorts: Vec<_> = arg_types
            .into_iter()
            .map(|arg| arg.to_z3_sort(state))
            .collect();
        let arg_sorts: Vec<_> = arg_sorts.iter().collect();

        let symb: z3::Symbol = z3::Symbol::String(name);
        let res_sort = res_t.to_z3_sort(state);
        let decl = z3::FuncDecl::new(state.ctx(), symb, &arg_sorts, &res_sort);

        // String::new().pop

        Rc::new(decl)
    }
}

impl ops::Neg for Formula {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::Unary(UnOp::Neg, Box::new(self))
    }
}

impl ops::Not for Formula {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self::Unary(UnOp::Not, Box::new(self))
    }
}

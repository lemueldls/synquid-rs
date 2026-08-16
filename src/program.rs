//! Executable program terms, declarations, and the typing environment
//! (mirror of `Synquid.Program`).

use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

use crate::{
    error::{Pos, SourcePos},
    logic::{
        BinOp, Formula, PredSig, Sort, Substitution, UnOp, and, bool_lit, bool_var,
        diff as set_diff, eq, ffalse, fneg, fnot, ftrue, ge, gt, iff, implies, int_lit, int_var,
        intersect, le, lt, member, minus, neq, or, plus, sort_of, subset, substitute, times,
        union_op, unknowns_of, val_bool, val_int, val_set,
    },
    tokens::{bin_op_token_str, bin_op_tokens, un_op_token_str, un_op_tokens},
    types::{
        BaseType, RSchema, RType, SET_TYPE_NAME, SType, SchemaSkeleton, TypeSkeleton,
        add_refinement, arity, base_type_of, bool as bool_type, bool_all, from_sort,
        int as int_type, int_all, schema_substitute, set_all, substitute_in_type, to_monotype,
        to_sort, var_refinement, vart_all,
    },
    util::{Id, as_integer},
};

// Program terms

/// One case inside a pattern match expression.
#[derive(Clone, Debug)]
pub struct Case<T> {
    /// Constructor name.
    pub constructor: Id,
    /// Bindings for constructor arguments.
    pub arg_names: Vec<Id>,
    /// Result of the match in this case.
    pub expr: Program<T>,
}

/// Program skeletons parametrized by information stored in symbols,
/// conditionals, and by node types.
#[derive(Clone, Debug)]
pub enum BareProgram<T> {
    /// Symbol (variable or constant).
    PSymbol(Id),
    /// Function application.
    PApp(Box<Program<T>>, Box<Program<T>>),
    /// Lambda abstraction.
    PFun(Id, Box<Program<T>>),
    /// Conditional.
    PIf(Box<Program<T>>, Box<Program<T>>, Box<Program<T>>),
    /// Pattern match on datatypes.
    PMatch(Box<Program<T>>, Vec<Case<T>>),
    /// Fixpoint.
    PFix(Vec<Id>, Box<Program<T>>),
    /// Let binding.
    PLet(Id, Box<Program<T>>, Box<Program<T>>),
    /// Hole (program to fill in).
    PHole,
    /// Error.
    PErr,
}

/// Programs annotated with types.
#[derive(Clone, Debug)]
pub struct Program<T> {
    pub content: BareProgram<T>,
    pub type_of: T,
}

// Structural comparisons that ignore type annotations (as in the reference).

fn cmp_case<T>(a: &Case<T>, b: &Case<T>) -> Ordering {
    let o1 = a.constructor.cmp(&b.constructor);
    if o1 == Ordering::Equal {
        let o2 = a.arg_names.cmp(&b.arg_names);
        if o2 == Ordering::Equal {
            cmp_pgm(&a.expr, &b.expr)
        } else {
            o2
        }
    } else {
        o1
    }
}

fn cmp_pgm<T>(a: &Program<T>, b: &Program<T>) -> Ordering {
    cmp_bare(&a.content, &b.content)
}

fn cmp_cases<T>(a: &[Case<T>], b: &[Case<T>]) -> Ordering {
    let o = a.len().cmp(&b.len());
    if o != Ordering::Equal {
        return o;
    }
    for (x, y) in a.iter().zip(b.iter()) {
        let o = cmp_case(x, y);
        if o != Ordering::Equal {
            return o;
        }
    }
    Ordering::Equal
}

fn cmp_bare<T>(a: &BareProgram<T>, b: &BareProgram<T>) -> Ordering {
    const fn ctor_index<T>(p: &BareProgram<T>) -> usize {
        use BareProgram::{PApp, PErr, PFix, PFun, PHole, PIf, PLet, PMatch, PSymbol};
        match p {
            PSymbol(..) => 0,
            PApp(..) => 1,
            PFun(..) => 2,
            PIf(..) => 3,
            PMatch(..) => 4,
            PFix(..) => 5,
            PLet(..) => 6,
            PHole => 7,
            PErr => 8,
        }
    }
    let (ia, ib) = (ctor_index(a), ctor_index(b));
    if ia != ib {
        return ia.cmp(&ib);
    }
    use BareProgram::{PApp, PErr, PFix, PFun, PHole, PIf, PLet, PMatch, PSymbol};
    match (a, b) {
        (PSymbol(x), PSymbol(y)) => x.cmp(y),
        (PApp(f1, x1), PApp(f2, x2)) => {
            let o = cmp_pgm(f1, f2);
            if o == Ordering::Equal {
                cmp_pgm(x1, x2)
            } else {
                o
            }
        }
        (PFun(x1, e1), PFun(x2, e2)) => {
            let o = x1.cmp(x2);
            if o == Ordering::Equal {
                cmp_pgm(e1, e2)
            } else {
                o
            }
        }
        (PIf(c1, t1, e1), PIf(c2, t2, e2)) => {
            let o = cmp_pgm(c1, c2);
            if o == Ordering::Equal {
                let o = cmp_pgm(t1, t2);
                if o == Ordering::Equal {
                    cmp_pgm(e1, e2)
                } else {
                    o
                }
            } else {
                o
            }
        }
        (PMatch(s1, cs1), PMatch(s2, cs2)) => {
            let o = cmp_cases(cs1, cs2);
            if o == Ordering::Equal {
                cmp_pgm(s1, s2)
            } else {
                o
            }
        }
        (PFix(xs1, e1), PFix(xs2, e2)) => {
            let o = xs1.cmp(xs2);
            if o == Ordering::Equal {
                cmp_pgm(e1, e2)
            } else {
                o
            }
        }
        (PLet(x1, d1, b1), PLet(x2, d2, b2)) => {
            let o = x1.cmp(x2);
            if o == Ordering::Equal {
                let o = cmp_pgm(d1, d2);
                if o == Ordering::Equal {
                    cmp_pgm(b1, b2)
                } else {
                    o
                }
            } else {
                o
            }
        }
        (PHole, PHole) | (PErr, PErr) => Ordering::Equal,
        _ => unreachable!("cmpBare: same constructor index mismatch"),
    }
}

impl<T> PartialEq for Case<T> {
    fn eq(&self, other: &Self) -> bool {
        cmp_case(self, other) == Ordering::Equal
    }
}

impl<T> Eq for Case<T> {}

impl<T> PartialOrd for Case<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for Case<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        cmp_case(self, other)
    }
}

impl<T> PartialEq for BareProgram<T> {
    fn eq(&self, other: &Self) -> bool {
        cmp_bare(self, other) == Ordering::Equal
    }
}

impl<T> Eq for BareProgram<T> {}

impl<T> PartialOrd for BareProgram<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for BareProgram<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        cmp_bare(self, other)
    }
}

impl<T> PartialEq for Program<T> {
    fn eq(&self, other: &Self) -> bool {
        cmp_pgm(self, other) == Ordering::Equal
    }
}

impl<T> Eq for Program<T> {}

impl<T> PartialOrd for Program<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for Program<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        cmp_pgm(self, other)
    }
}

/// Untyped programs.
pub type UProgram = Program<RType>;
/// Refinement-typed programs.
pub type RProgram = Program<RType>;

/// Program with no information annotated.
#[must_use]
pub const fn untyped(c: BareProgram<RType>) -> RProgram {
    Program {
        content: c,
        type_of: TypeSkeleton::AnyT,
    }
}

/// Hole.
#[must_use]
pub const fn u_hole() -> RProgram {
    untyped(BareProgram::PHole)
}

#[must_use]
pub const fn is_hole(p: &RProgram) -> bool {
    matches!(p.content, BareProgram::PHole)
}

/// Map the annotations of all nodes (and the top-level annotation).
pub fn map_type<T: Clone, U: Clone>(p: &Program<T>, f: &impl Fn(&T) -> U) -> Program<U> {
    let content = match &p.content {
        BareProgram::PSymbol(name) => BareProgram::PSymbol(name.clone()),
        BareProgram::PApp(fun, arg) => {
            BareProgram::PApp(Box::new(map_type(fun, f)), Box::new(map_type(arg, f)))
        }
        BareProgram::PFun(x, body) => BareProgram::PFun(x.clone(), Box::new(map_type(body, f))),
        BareProgram::PIf(c, t, e) => {
            BareProgram::PIf(
                Box::new(map_type(c, f)),
                Box::new(map_type(t, f)),
                Box::new(map_type(e, f)),
            )
        }
        BareProgram::PMatch(scr, cases) => {
            BareProgram::PMatch(
                Box::new(map_type(scr, f)),
                cases
                    .iter()
                    .map(|case| {
                        Case {
                            constructor: case.constructor.clone(),
                            arg_names: case.arg_names.clone(),
                            expr: map_type(&case.expr, f),
                        }
                    })
                    .collect(),
            )
        }
        BareProgram::PFix(args, body) => {
            BareProgram::PFix(args.clone(), Box::new(map_type(body, f)))
        }
        BareProgram::PLet(x, def, body) => {
            BareProgram::PLet(
                x.clone(),
                Box::new(map_type(def, f)),
                Box::new(map_type(body, f)),
            )
        }
        BareProgram::PHole => BareProgram::PHole,
        BareProgram::PErr => BareProgram::PErr,
    };
    Program {
        content,
        type_of: f(&p.type_of),
    }
}

/// Erase all type annotations.
#[must_use]
pub fn erase_types(p: &RProgram) -> RProgram {
    map_type(p, &|_| TypeSkeleton::AnyT)
}

#[must_use]
pub fn symbol_name(p: &RProgram) -> Id {
    match &p.content {
        BareProgram::PSymbol(name) => name.clone(),
        _ => panic!("symbolName: not a symbol"),
    }
}

#[must_use]
pub fn symbol_list(p: &RProgram) -> Vec<Id> {
    match &p.content {
        BareProgram::PSymbol(name) => vec![name.clone()],
        BareProgram::PApp(fun, arg) => {
            let mut names = symbol_list(fun);
            names.extend(symbol_list(arg));
            names
        }
        _ => vec![],
    }
}

/// All symbol names appearing in a program.
#[must_use]
pub fn symbols_of(p: &RProgram) -> BTreeSet<Id> {
    match &p.content {
        BareProgram::PSymbol(name) => [name.clone()].into_iter().collect(),
        BareProgram::PApp(fun, arg) => {
            let mut s = symbols_of(fun);
            s.extend(symbols_of(arg));
            s
        }
        BareProgram::PFun(_, body) => symbols_of(body),
        BareProgram::PIf(c, t, e) => {
            let mut s = symbols_of(c);
            s.extend(symbols_of(t));
            s.extend(symbols_of(e));
            s
        }
        BareProgram::PMatch(scr, cases) => {
            let mut s = symbols_of(scr);
            for case in cases {
                s.extend(symbols_of(&case.expr));
            }
            s
        }
        BareProgram::PFix(_, body) => symbols_of(body),
        BareProgram::PLet(_, def, body) => {
            let mut s = symbols_of(def);
            s.extend(symbols_of(body));
            s
        }
        _ => BTreeSet::new(),
    }
}

#[must_use]
pub fn error_program() -> RProgram {
    Program {
        content: BareProgram::PErr,
        type_of: vart(crate::logic::DONT_CARE, ftrue()),
    }
}

#[must_use]
pub const fn is_error(p: &RProgram) -> bool {
    matches!(p.content, BareProgram::PErr)
}

/// Variable type `t` with refinement `fml` (Haskell `vart a fml`).
fn vart(a: &str, fml: Formula) -> RType {
    TypeSkeleton::ScalarT(BaseType::TypeVarT(Substitution::new(), a.to_string()), fml)
}

/// Substitute a symbol for a subterm in a program.
#[must_use]
pub fn program_substitute_symbol(name: &Id, subterm: &RProgram, p: &RProgram) -> RProgram {
    let pss = |q: &RProgram| program_substitute_symbol(name, subterm, q);
    let content = match &p.content {
        BareProgram::PSymbol(x) => {
            if x == name {
                subterm.content.clone()
            } else {
                p.content.clone()
            }
        }
        BareProgram::PApp(fun, arg) => BareProgram::PApp(Box::new(pss(fun)), Box::new(pss(arg))),
        BareProgram::PFun(x, body) => BareProgram::PFun(x.clone(), Box::new(pss(body))),
        BareProgram::PIf(c, t, e) => {
            BareProgram::PIf(Box::new(pss(c)), Box::new(pss(t)), Box::new(pss(e)))
        }
        BareProgram::PMatch(scr, cases) => {
            BareProgram::PMatch(
                Box::new(pss(scr)),
                cases
                    .iter()
                    .map(|case| {
                        Case {
                            constructor: case.constructor.clone(),
                            arg_names: case.arg_names.clone(),
                            expr: pss(&case.expr),
                        }
                    })
                    .collect(),
            )
        }
        BareProgram::PFix(args, body) => BareProgram::PFix(args.clone(), Box::new(pss(body))),
        BareProgram::PLet(x, def, body) => {
            BareProgram::PLet(x.clone(), Box::new(pss(def)), Box::new(pss(body)))
        }
        other => other.clone(),
    };
    Program {
        content,
        type_of: p.type_of.clone(),
    }
}

// Convert an executable formula into a program

#[must_use]
pub fn fml_to_program(fml: &Formula) -> RProgram {
    match fml {
        Formula::BoolLit(b) => {
            Program {
                // The reference's `show b` for `Bool` yields the capitalized
                // constructor name (`show True == "True"`), which is the
                // poly constant in scope.
                content: BareProgram::PSymbol(if *b { "True" } else { "False" }.to_string()),
                type_of: bool_type(eq(val_bool(), bool_lit(*b))),
            }
        }
        Formula::IntLit(i) => {
            Program {
                content: BareProgram::PSymbol(i.to_string()),
                type_of: int_type(eq(val_int(), int_lit(*i))),
            }
        }
        Formula::Var(s, x) => {
            Program {
                content: BareProgram::PSymbol(x.clone()),
                type_of: add_refinement(from_sort(s), &var_refinement(x, s)),
            }
        }
        Formula::Unary(op, e) => {
            let s = sort_of(fml);
            let p = fml_to_program(e);
            let op_res = if *op == UnOp::Not {
                bool_type(eq(val_bool(), fnot(int_var("x"))))
            } else {
                int_type(eq(val_int(), Formula::Unary(*op, Box::new(int_var("x")))))
            };
            let fun = Program {
                content: BareProgram::PSymbol(un_op_token_str(*op)),
                type_of: TypeSkeleton::FunctionT(
                    "x".to_string(),
                    Box::new(p.type_of.clone()),
                    Box::new(op_res),
                ),
            };
            Program {
                content: BareProgram::PApp(Box::new(fun), Box::new(p)),
                type_of: add_refinement(
                    from_sort(&s),
                    &eq(
                        Formula::Var(Box::new(s), crate::logic::VALUE_VAR_NAME.to_string()),
                        fml.clone(),
                    ),
                ),
            }
        }
        Formula::Binary(op, e1, e2) => {
            let s = sort_of(fml);
            let p1 = fml_to_program(e1);
            let p2 = fml_to_program(e2);
            let op_res = if *op == BinOp::Times {
                int_type(eq(
                    val_int(),
                    Formula::Binary(*op, Box::new(int_var("x")), Box::new(int_var("y"))),
                ))
            } else {
                bool_type(eq(
                    val_bool(),
                    Formula::Binary(*op, Box::new(int_var("x")), Box::new(int_var("y"))),
                ))
            };
            let fun1 = Program {
                content: BareProgram::PSymbol(bin_op_token_str(*op)),
                type_of: TypeSkeleton::FunctionT(
                    "x".to_string(),
                    Box::new(p1.type_of.clone()),
                    Box::new(TypeSkeleton::FunctionT(
                        "y".to_string(),
                        Box::new(p2.type_of.clone()),
                        Box::new(op_res.clone()),
                    )),
                ),
            };
            let fun2 = Program {
                content: BareProgram::PApp(Box::new(fun1), Box::new(p1)),
                type_of: TypeSkeleton::FunctionT(
                    "y".to_string(),
                    Box::new(p2.type_of.clone()),
                    Box::new(op_res),
                ),
            };
            Program {
                content: BareProgram::PApp(Box::new(fun2), Box::new(p2)),
                type_of: add_refinement(
                    from_sort(&s),
                    &eq(
                        Formula::Var(Box::new(s), crate::logic::VALUE_VAR_NAME.to_string()),
                        fml.clone(),
                    ),
                ),
            }
        }
        Formula::Pred(_, x, fs) => {
            let mut cur = Program {
                content: BareProgram::PSymbol(x.clone()),
                type_of: TypeSkeleton::FunctionT(
                    x.clone(),
                    Box::new(TypeSkeleton::AnyT),
                    Box::new(TypeSkeleton::AnyT),
                ),
            };
            for f in fs {
                cur = Program {
                    content: BareProgram::PApp(Box::new(cur), Box::new(fml_to_program(f))),
                    type_of: TypeSkeleton::AnyT,
                };
            }
            cur
        }
        other => panic!("fmlToProgram: cannot convert {other:?}"),
    }
}

// Convert an executable formula into an untyped program

#[must_use]
pub fn fml_to_u_program(fml: &Formula) -> UProgram {
    match fml {
        Formula::BoolLit(b) => {
            Program {
                content: BareProgram::PSymbol(if *b { "True" } else { "False" }.to_string()),
                type_of: TypeSkeleton::AnyT,
            }
        }
        Formula::IntLit(i) => {
            Program {
                content: BareProgram::PSymbol(i.to_string()),
                type_of: TypeSkeleton::AnyT,
            }
        }
        Formula::Var(_, x) => {
            Program {
                content: BareProgram::PSymbol(x.clone()),
                type_of: TypeSkeleton::AnyT,
            }
        }
        Formula::Unary(op, e) => {
            let p = fml_to_u_program(e);
            let fun = Program {
                content: BareProgram::PSymbol(un_op_token_str(*op)),
                type_of: TypeSkeleton::AnyT,
            };
            Program {
                content: BareProgram::PApp(Box::new(fun), Box::new(p)),
                type_of: TypeSkeleton::AnyT,
            }
        }
        Formula::Binary(op, e1, e2) => {
            let p1 = fml_to_u_program(e1);
            let p2 = fml_to_u_program(e2);
            let fun1 = Program {
                content: BareProgram::PSymbol(bin_op_token_str(*op)),
                type_of: TypeSkeleton::AnyT,
            };
            let fun2 = Program {
                content: BareProgram::PApp(Box::new(fun1), Box::new(p1)),
                type_of: TypeSkeleton::AnyT,
            };
            Program {
                content: BareProgram::PApp(Box::new(fun2), Box::new(p2)),
                type_of: TypeSkeleton::AnyT,
            }
        }
        Formula::Pred(_, x, fs) | Formula::Cons(_, x, fs) => {
            let mut cur = Program {
                content: BareProgram::PSymbol(x.clone()),
                type_of: TypeSkeleton::AnyT,
            };
            for f in fs {
                cur = Program {
                    content: BareProgram::PApp(Box::new(cur), Box::new(fml_to_u_program(f))),
                    type_of: TypeSkeleton::AnyT,
                };
            }
            cur
        }
        Formula::Ite(gf, f1, f2) => {
            Program {
                content: BareProgram::PIf(
                    Box::new(fml_to_u_program(gf)),
                    Box::new(fml_to_u_program(f1)),
                    Box::new(fml_to_u_program(f2)),
                ),
                type_of: TypeSkeleton::AnyT,
            }
        }
        Formula::SetLit(_, fs) => {
            let empty = || {
                Program {
                    content: BareProgram::PSymbol(crate::types::EMPTY_SET_CTOR.to_string()),
                    type_of: TypeSkeleton::AnyT,
                }
            };
            let singleton = || {
                Program {
                    content: BareProgram::PSymbol(crate::types::SINGLETON_CTOR.to_string()),
                    type_of: TypeSkeleton::AnyT,
                }
            };
            let insert = || {
                Program {
                    content: BareProgram::PSymbol(crate::types::INSERT_SET_CTOR.to_string()),
                    type_of: TypeSkeleton::AnyT,
                }
            };
            if fs.is_empty() {
                empty()
            } else if fs.len() == 1 {
                Program {
                    content: BareProgram::PApp(
                        Box::new(singleton()),
                        Box::new(fml_to_u_program(&fs[0])),
                    ),
                    type_of: TypeSkeleton::AnyT,
                }
            } else {
                let mut cur = fml_to_u_program(&fs[0]);
                for f in &fs[1..] {
                    cur = Program {
                        content: BareProgram::PApp(Box::new(cur), Box::new(fml_to_u_program(f))),
                        type_of: TypeSkeleton::AnyT,
                    };
                }
                let cur = Program {
                    content: BareProgram::PApp(Box::new(cur), Box::new(empty())),
                    type_of: TypeSkeleton::AnyT,
                };
                Program {
                    content: BareProgram::PApp(Box::new(insert()), Box::new(cur)),
                    type_of: TypeSkeleton::AnyT,
                }
            }
        }
        other => panic!("fmlToUProgram: cannot convert {other:?}"),
    }
}

/// Change argument names in function type `t` to be the same as in the
/// abstraction `p`.
pub fn rename_as_impl(is_bound: &impl Fn(&Id) -> bool, p: &UProgram, t: &RType) -> RType {
    rename_as_impl_inner(is_bound, &Substitution::new(), p, t)
}
fn rename_as_impl_inner(
    is_bound: &impl Fn(&Id) -> bool,
    subst: &Substitution,
    p: &UProgram,
    t: &RType,
) -> RType {
    match (&p.content, t) {
        (BareProgram::PFun(y, p_res), TypeSkeleton::FunctionT(x, t_arg, t_res)) => {
            let t_arg_sub = substitute_in_type(is_bound, subst, t_arg);
            let subst2 = match &**t_arg {
                TypeSkeleton::ScalarT(base_t, _) => {
                    let mut subst2 = subst.clone();
                    subst2.insert(
                        x.clone(),
                        Formula::Var(Box::new(to_sort(base_t)), y.clone()),
                    );
                    subst2
                }
                _ => subst.clone(),
            };
            TypeSkeleton::FunctionT(
                y.clone(),
                Box::new(t_arg_sub),
                Box::new(rename_as_impl_inner(is_bound, &subst2, p_res, t_res)),
            )
        }
        _ => substitute_in_type(is_bound, subst, t),
    }
}

// Top-level definitions

/// User-defined datatype representation.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct DatatypeDef {
    /// Type parameters.
    pub type_params: Vec<Id>,
    /// Signatures of predicate parameters.
    pub pred_params: Vec<PredSig>,
    /// For each predicate parameter, whether it is contravariant.
    pub pred_variances: Vec<bool>,
    /// Constructor names.
    pub constructors: Vec<Id>,
    /// Name of the measure that serves as well founded termination metric.
    pub wf_metric: Option<Id>,
}

/// One case in a measure definition: constructor name, arguments, and body.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MeasureCase {
    pub constructor: Id,
    pub arg_names: Vec<Id>,
    pub body: Formula,
}

/// Defaults for constant arguments of measures.
pub type MeasureDefaults = Vec<(Id, Sort)>;

/// User-defined measure function representation.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MeasureDef {
    pub in_sort: Sort,
    pub out_sort: Sort,
    pub definitions: Vec<MeasureCase>,
    pub constant_args: MeasureDefaults,
    pub postcondition: Formula,
}

/// All possible constant arguments of measures with multiple arguments.
pub type ArgMap = BTreeMap<Id, BTreeSet<Formula>>;

// Evaluation environment

/// Typing environment.
#[derive(Clone, Debug)]
pub struct Environment {
    /// Variables and constants (with their refinement types), indexed by arity.
    pub symbols: BTreeMap<usize, BTreeMap<Id, RSchema>>,
    /// Bound type variables.
    pub bound_type_vars: Vec<Id>,
    /// Argument sorts of bound abstract refinements.
    pub bound_predicates: Vec<PredSig>,
    /// Unknown assumptions.
    pub assumptions: BTreeSet<Formula>,
    /// For polymorphic recursive calls, the shape their types must have.
    pub shape_constraints: BTreeMap<Id, SType>,
    /// Program terms that have already been scrutinized.
    pub used_scrutinees: Vec<RProgram>,
    /// In eager match mode, datatype variables that can be scrutinized.
    pub unfolded_vars: BTreeSet<Id>,
    /// Subset of symbols that are let-bound.
    pub let_bound: BTreeSet<Id>,
    /// Subset of symbols that are constants.
    pub constants: BTreeSet<Id>,
    /// Datatype definitions.
    pub datatypes: BTreeMap<Id, DatatypeDef>,
    /// Signatures (resSort:argSorts) of module-level logic functions.
    pub global_predicates: BTreeMap<Id, Vec<Sort>>,
    /// Measure definitions.
    pub measures: BTreeMap<Id, MeasureDef>,
    /// Type synonym definitions.
    pub type_synonyms: BTreeMap<Id, (Vec<Id>, RType)>,
    /// Unresolved types of components.
    pub unresolved_constants: BTreeMap<Id, RSchema>,
}

/// Environments are compared by their logical content only.
fn env_cmp(a: &Environment, b: &Environment) -> Ordering {
    let o = a.symbols.cmp(&b.symbols);
    if o == Ordering::Equal {
        a.assumptions.cmp(&b.assumptions)
    } else {
        o
    }
}

impl PartialEq for Environment {
    fn eq(&self, other: &Self) -> bool {
        env_cmp(self, other) == Ordering::Equal
    }
}

impl Eq for Environment {}

impl PartialOrd for Environment {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Environment {
    fn cmp(&self, other: &Self) -> Ordering {
        env_cmp(self, other)
    }
}

/// Empty environment.
#[must_use]
pub const fn empty_env() -> Environment {
    Environment {
        symbols: BTreeMap::new(),
        bound_type_vars: vec![],
        bound_predicates: vec![],
        assumptions: BTreeSet::new(),
        shape_constraints: BTreeMap::new(),
        used_scrutinees: vec![],
        unfolded_vars: BTreeSet::new(),
        let_bound: BTreeSet::new(),
        constants: BTreeSet::new(),
        global_predicates: BTreeMap::new(),
        datatypes: BTreeMap::new(),
        measures: BTreeMap::new(),
        type_synonyms: BTreeMap::new(),
        unresolved_constants: BTreeMap::new(),
    }
}

/// All symbols of arity `n` in `env`.
#[must_use]
pub fn symbols_of_arity(n: usize, env: &Environment) -> BTreeMap<Id, RSchema> {
    env.symbols.get(&n).cloned().unwrap_or_default()
}

/// All symbols in an environment.
#[must_use]
pub fn all_symbols(env: &Environment) -> BTreeMap<Id, RSchema> {
    let mut all = BTreeMap::new();
    for inner in env.symbols.values() {
        all.extend(inner.clone());
    }
    all
}

/// Type of symbol `name` in `env`, including built-in constants.
#[must_use]
pub fn lookup_symbol(name: &Id, arity: usize, has_set: bool, env: &Environment) -> Option<RSchema> {
    let is_binary = arity == 2 && bin_op_tokens().iter().any(|(_, t)| *t == name);
    let as_int = as_integer(name);
    if arity == 0 && name == "True" {
        Some(SchemaSkeleton::Monotype(bool_type(eq(
            val_bool(),
            bool_lit(true),
        ))))
    } else if arity == 0 && name == "False" {
        Some(SchemaSkeleton::Monotype(bool_type(fnot(val_bool()))))
    } else if arity == 0 && as_int.is_some() {
        Some(SchemaSkeleton::Monotype(int_type(eq(
            val_int(),
            int_lit(as_int.unwrap()),
        ))))
    } else if arity == 1 && un_op_tokens().iter().any(|(_, t)| *t == name) {
        let op = un_op_tokens().iter().find(|(_, t)| *t == name).unwrap().0;
        Some(un_op_type(op))
    } else if is_binary && has_set {
        let ops: Vec<BinOp> = bin_op_tokens()
            .iter()
            .filter(|(_, t)| *t == name)
            .map(|(op, _)| *op)
            .collect();
        let op = match ops.as_slice() {
            [] => unreachable!("lookupSymbol: no operator for {name}"),
            [single] => *single,
            _ => ops[1],
        };
        Some(bin_op_type(op))
    } else if is_binary {
        let op = bin_op_tokens().iter().find(|(_, t)| *t == name).unwrap().0;
        Some(bin_op_type(op))
    } else {
        all_symbols(env).get(name).cloned()
    }
}

#[must_use]
pub fn symbol_as_formula(env: &Environment, name: &Id, t: &RType) -> Formula {
    assert!(arity(t) == 0, "symbolAsFormula: not a scalar symbol {name}");
    let as_int = as_integer(name);
    if name == "True" {
        Formula::BoolLit(true)
    } else if name == "False" {
        Formula::BoolLit(false)
    } else if as_int.is_some() {
        Formula::IntLit(as_int.unwrap())
    } else if lookup_constructor(name, env).is_some() {
        Formula::Cons(Box::new(to_sort(&base_type_of(t))), name.clone(), vec![])
    } else {
        Formula::Var(Box::new(to_sort(&base_type_of(t))), name.clone())
    }
}

fn un_op_type(op: UnOp) -> RSchema {
    match op {
        UnOp::Neg => {
            SchemaSkeleton::Monotype(TypeSkeleton::FunctionT(
                "x".to_string(),
                Box::new(int_all()),
                Box::new(int_type(eq(val_int(), fneg(int_var("x"))))),
            ))
        }
        UnOp::Not => {
            SchemaSkeleton::Monotype(TypeSkeleton::FunctionT(
                "x".to_string(),
                Box::new(bool_all()),
                Box::new(bool_type(eq(val_bool(), fnot(bool_var("x"))))),
            ))
        }
    }
}

fn vart_var(a: &str, x: &str) -> Formula {
    Formula::Var(Box::new(Sort::VarS(a.to_string())), x.to_string())
}

fn set_var(a: &str, x: &str) -> Formula {
    Formula::Var(
        Box::new(Sort::SetS(Box::new(Sort::VarS(a.to_string())))),
        x.to_string(),
    )
}

/// Set type `set a fml`.
fn set_type(a: &str, fml: Formula) -> RType {
    TypeSkeleton::ScalarT(
        BaseType::DatatypeT(SET_TYPE_NAME.to_string(), vec![vart_all(a)], vec![]),
        fml,
    )
}

fn forall_a(body: RType) -> RSchema {
    SchemaSkeleton::ForallT("a".to_string(), Box::new(SchemaSkeleton::Monotype(body)))
}

#[must_use]
pub fn bin_op_type(op: BinOp) -> RSchema {
    let two_sorted = |x_t: RType, y_t: RType, res: RType| {
        TypeSkeleton::FunctionT(
            "x".to_string(),
            Box::new(x_t),
            Box::new(TypeSkeleton::FunctionT(
                "y".to_string(),
                Box::new(y_t),
                Box::new(res),
            )),
        )
    };
    let bool_res = |fml: Formula| bool_type(eq(val_bool(), fml));
    match op {
        BinOp::Times => {
            SchemaSkeleton::Monotype(two_sorted(
                int_all(),
                int_all(),
                int_type(eq(val_int(), times(int_var("x"), int_var("y")))),
            ))
        }
        BinOp::Plus => {
            SchemaSkeleton::Monotype(two_sorted(
                int_all(),
                int_all(),
                int_type(eq(val_int(), plus(int_var("x"), int_var("y")))),
            ))
        }
        BinOp::Minus => {
            SchemaSkeleton::Monotype(two_sorted(
                int_all(),
                int_all(),
                int_type(eq(val_int(), minus(int_var("x"), int_var("y")))),
            ))
        }
        BinOp::Eq => {
            forall_a(two_sorted(
                vart_all("a"),
                vart_all("a"),
                bool_res(eq(vart_var("a", "x"), vart_var("a", "y"))),
            ))
        }
        BinOp::Neq => {
            forall_a(two_sorted(
                vart_all("a"),
                vart_all("a"),
                bool_res(neq(vart_var("a", "x"), vart_var("a", "y"))),
            ))
        }
        BinOp::Lt => {
            forall_a(two_sorted(
                vart_all("a"),
                vart_all("a"),
                bool_res(lt(vart_var("a", "x"), vart_var("a", "y"))),
            ))
        }
        BinOp::Le => {
            forall_a(two_sorted(
                vart_all("a"),
                vart_all("a"),
                bool_res(le(vart_var("a", "x"), vart_var("a", "y"))),
            ))
        }
        BinOp::Gt => {
            forall_a(two_sorted(
                vart_all("a"),
                vart_all("a"),
                bool_res(gt(vart_var("a", "x"), vart_var("a", "y"))),
            ))
        }
        BinOp::Ge => {
            forall_a(two_sorted(
                vart_all("a"),
                vart_all("a"),
                bool_res(ge(vart_var("a", "x"), vart_var("a", "y"))),
            ))
        }
        BinOp::And => {
            SchemaSkeleton::Monotype(two_sorted(
                bool_all(),
                bool_all(),
                bool_res(and(bool_var("x"), bool_var("y"))),
            ))
        }
        BinOp::Or => {
            SchemaSkeleton::Monotype(two_sorted(
                bool_all(),
                bool_all(),
                bool_res(or(bool_var("x"), bool_var("y"))),
            ))
        }
        BinOp::Implies => {
            SchemaSkeleton::Monotype(two_sorted(
                bool_all(),
                bool_all(),
                bool_res(implies(bool_var("x"), bool_var("y"))),
            ))
        }
        BinOp::Iff => {
            SchemaSkeleton::Monotype(two_sorted(
                bool_all(),
                bool_all(),
                bool_res(iff(bool_var("x"), bool_var("y"))),
            ))
        }
        BinOp::Union => {
            forall_a(two_sorted(
                set_all("a"),
                set_all("a"),
                set_type(
                    "a",
                    eq(val_set("a"), union_op(set_var("a", "x"), set_var("a", "y"))),
                ),
            ))
        }
        BinOp::Intersect => {
            forall_a(two_sorted(
                set_all("a"),
                set_all("a"),
                set_type(
                    "a",
                    eq(
                        val_set("a"),
                        intersect(set_var("a", "x"), set_var("a", "y")),
                    ),
                ),
            ))
        }
        BinOp::Diff => {
            forall_a(two_sorted(
                set_all("a"),
                set_all("a"),
                set_type(
                    "a",
                    eq(val_set("a"), set_diff(set_var("a", "x"), set_var("a", "y"))),
                ),
            ))
        }
        BinOp::Member => {
            forall_a(two_sorted(
                vart_all("a"),
                set_all("a"),
                bool_res(member(vart_var("a", "x"), set_var("a", "y"))),
            ))
        }
        BinOp::Subset => {
            forall_a(two_sorted(
                set_all("a"),
                set_all("a"),
                bool_res(subset(set_var("a", "x"), set_var("a", "y"))),
            ))
        }
    }
}

/// Is `name` a constant in `env` (including built-in constants)?
#[must_use]
pub fn is_constant(name: &Id, env: &Environment) -> bool {
    name == "True"
        || name == "False"
        || as_integer(name).is_some()
        || un_op_tokens().iter().any(|(_, t)| *t == name)
        || bin_op_tokens().iter().any(|(_, t)| *t == name)
        || env.constants.contains(name)
}

/// Is type variable `tv` bound in `env`?
#[must_use]
pub fn is_bound(env: &Environment, tv: &Id) -> bool {
    env.bound_type_vars.contains(tv)
}

#[must_use]
pub fn add_variable(name: &Id, t: &RType, env: &Environment) -> Environment {
    add_poly_variable(name, SchemaSkeleton::Monotype(t.clone()), env)
}

#[must_use]
pub fn add_poly_variable(name: &Id, sch: RSchema, env: &Environment) -> Environment {
    let mut env = env.clone();
    let n = arity(&to_monotype(&sch));
    env.symbols.entry(n).or_default().insert(name.clone(), sch);
    env
}

#[must_use]
pub fn add_constant(name: &Id, t: &RType, env: &Environment) -> Environment {
    add_poly_constant(name, SchemaSkeleton::Monotype(t.clone()), env)
}

#[must_use]
pub fn add_poly_constant(name: &Id, sch: RSchema, env: &Environment) -> Environment {
    let mut env = add_poly_variable(name, sch, env);
    env.constants.insert(name.clone());
    env
}

#[must_use]
pub fn add_let_bound(name: &Id, t: &RType, env: &Environment) -> Environment {
    let mut env = add_variable(name, t, env);
    env.let_bound.insert(name.clone());
    env
}

#[must_use]
pub fn add_unresolved_constant(name: &Id, sch: RSchema, env: &Environment) -> Environment {
    let mut env = env.clone();
    env.unresolved_constants.insert(name.clone(), sch);
    env
}

#[must_use]
pub fn remove_variable(name: &Id, env: &Environment) -> Environment {
    let mut env = env.clone();
    if let Some(sch) = all_symbols(&env).get(name) {
        let n = arity(&to_monotype(sch));
        if let Some(inner) = env.symbols.get_mut(&n) {
            inner.remove(name);
        }
        env.constants.remove(name);
    }
    env
}

#[must_use]
pub fn embed_context(env: &Environment, t: &RType) -> (Environment, RType) {
    match t {
        TypeSkeleton::LetT(x, t_def, t_body) => {
            let (env1, t_def1) = embed_context(&remove_variable(x, env), t_def);
            let (env2, t_body1) = embed_context(&env1, t_body);
            (add_let_bound(x, &t_def1, &env2), t_body1)
        }
        _ => (env.clone(), t.clone()),
    }
}

#[must_use]
pub fn unfold_all_variables(env: &Environment) -> Environment {
    let mut env = env.clone();
    let sym0: BTreeSet<Id> = symbols_of_arity(0, &env).into_keys().collect();
    let fresh: BTreeSet<Id> = sym0.difference(&env.constants).cloned().collect();
    env.unfolded_vars = env.unfolded_vars.union(&fresh).cloned().collect();
    env
}

#[must_use]
pub fn add_measure(measure_name: &Id, m: MeasureDef, env: &Environment) -> Environment {
    let mut env = env.clone();
    env.measures.insert(measure_name.clone(), m);
    env
}

#[must_use]
pub fn add_bound_predicate(sig: PredSig, env: &Environment) -> Environment {
    let mut env = env.clone();
    env.bound_predicates.push(sig);
    env
}

#[must_use]
pub fn add_global_predicate(
    pred_name: &Id,
    res_sort: Sort,
    arg_sorts: Vec<Sort>,
    env: &Environment,
) -> Environment {
    let mut env = env.clone();
    let mut sorts = vec![res_sort];
    sorts.extend(arg_sorts);
    env.global_predicates.insert(pred_name.clone(), sorts);
    env
}

#[must_use]
pub fn add_type_synonym(name: &Id, tvs: Vec<Id>, t: RType, env: &Environment) -> Environment {
    let mut env = env.clone();
    env.type_synonyms.insert(name.clone(), (tvs, t));
    env
}

#[must_use]
pub fn add_datatype(name: &Id, dt: DatatypeDef, env: &Environment) -> Environment {
    let mut env = env.clone();
    env.datatypes.insert(name.clone(), dt);
    env
}

/// The name of the datatype for which `ctor` is registered as a constructor
/// in `env`, if any.
#[must_use]
pub fn lookup_constructor(ctor: &Id, env: &Environment) -> Option<Id> {
    env.datatypes
        .iter()
        .find(|(_, dt)| dt.constructors.contains(ctor))
        .map(|(name, _)| name.clone())
}

#[must_use]
pub fn add_type_var(a: &Id, env: &Environment) -> Environment {
    let mut env = env.clone();
    env.bound_type_vars.push(a.clone());
    env
}

#[must_use]
pub fn add_assumption(f: Formula, env: &Environment) -> Environment {
    let mut env = env.clone();
    env.assumptions.insert(f);
    env
}

/// Env with `p` marked as having been scrutinized already.
#[must_use]
pub fn add_scrutinee(p: RProgram, env: &Environment) -> Environment {
    let mut env = env.clone();
    env.used_scrutinees.push(p);
    env
}

/// All predicates, module-level and bound.
#[must_use]
pub fn all_predicates(env: &Environment) -> BTreeMap<Id, Vec<Sort>> {
    let mut m: BTreeMap<Id, Vec<Sort>> = env
        .bound_predicates
        .iter()
        .map(|sig| {
            let mut sorts = vec![sig.pred_sig_res_sort.clone()];
            sorts.extend(sig.pred_sig_arg_sorts.clone());
            (sig.pred_sig_name.clone(), sorts)
        })
        .collect();
    for (name, sorts) in &env.global_predicates {
        m.insert(name.clone(), sorts.clone());
    }
    m
}

/// All measures of datatype with name `dt_name` in `env`.
#[must_use]
pub fn all_measures_of(dt_name: &Id, env: &Environment) -> BTreeMap<Id, MeasureDef> {
    env.measures
        .iter()
        .filter(|(_, m)| matches!(&m.in_sort, Sort::DataS(s_name, _) if s_name == dt_name))
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect()
}

/// All nontrivial postconditions of measures of `base_t` in case it is a
/// datatype.
#[must_use]
pub fn all_measure_postconditions(
    include_quantified: bool,
    base_t: &BaseType<Formula>,
    env: &Environment,
) -> Vec<Formula> {
    match base_t {
        BaseType::DatatypeT(dt_name, t_args, _) => {
            let all_measures: Vec<(Id, MeasureDef)> =
                all_measures_of(dt_name, env).into_iter().collect();
            let is_abstract = env.datatypes[dt_name].constructors.is_empty();
            let base_sort = to_sort(base_t);
            let mut posts = Vec::new();
            for (m_name, m) in &all_measures {
                if let Some(fml) = extract_post(m_name, m, &base_sort) {
                    posts.push(fml);
                }
            }
            if is_abstract {
                for (m_name, m) in &all_measures {
                    if let Some(fml) = content_properties(m_name, m, base_t, t_args) {
                        posts.push(fml);
                    }
                }
            }
            if include_quantified {
                for (m_name, m) in &all_measures {
                    if let Some(fml) = elem_properties(m_name, m, base_t, t_args) {
                        posts.push(fml);
                    }
                }
            }
            posts
        }
        _ => vec![],
    }
}

fn extract_post(m_name: &Id, m: &MeasureDef, base_sort: &Sort) -> Option<Formula> {
    if m.postcondition == ftrue() {
        return None;
    }
    let app = Formula::Pred(Box::new(m.out_sort.clone()), m_name.clone(), vec![
        Formula::Var(
            Box::new(base_sort.clone()),
            crate::logic::VALUE_VAR_NAME.to_string(),
        ),
    ]);
    Some(substitute(
        &Substitution::from([(crate::logic::VALUE_VAR_NAME.to_string(), app)]),
        m.postcondition.clone(),
    ))
}

/// If the measure "returns" one of the datatype's parameters, transfer the
/// refinement onto the value of the measure.
fn content_properties(
    m_name: &Id,
    m: &MeasureDef,
    base_t: &BaseType<Formula>,
    t_args: &[RType],
) -> Option<Formula> {
    let MeasureDef {
        in_sort,
        out_sort,
        definitions: _,
        constant_args: _,
        postcondition: fml,
    } = m;
    match in_sort {
        Sort::DataS(_, vars) => {
            let i = vars.iter().position(|v| v == out_sort)?;
            let elem_t = match &t_args[i] {
                TypeSkeleton::ScalarT(elem_t, _) => elem_t,
                _ => return None,
            };
            let elem_sort = to_sort(elem_t);
            let measure_app =
                Formula::Pred(Box::new(elem_sort), m_name.clone(), vec![Formula::Var(
                    Box::new(to_sort(base_t)),
                    crate::logic::VALUE_VAR_NAME.to_string(),
                )]);
            Some(substitute(
                &Substitution::from([(crate::logic::VALUE_VAR_NAME.to_string(), measure_app)]),
                fml.clone(),
            ))
        }
        _ => None,
    }
}

/// If the measure is a set of datatype elements, add an axiom that every
/// element of the set has that property.
fn elem_properties(
    m_name: &Id,
    m: &MeasureDef,
    base_t: &BaseType<Formula>,
    t_args: &[RType],
) -> Option<Formula> {
    let MeasureDef {
        in_sort,
        out_sort,
        definitions: _,
        constant_args: _,
        postcondition: _,
    } = m;
    match (in_sort, out_sort) {
        (Sort::DataS(_, vars), Sort::SetS(a)) => {
            let i = vars.iter().position(|v| v == a.as_ref())?;
            // The axiom carries the refinement of the datatype's element type
            // (the reference: `let (ScalarT elemT fml) = tArgs !! i`), NOT
            // the measure's postcondition.
            let (elem_t, fml) = match &t_args[i] {
                TypeSkeleton::ScalarT(elem_t, fml) => (elem_t, fml),
                _ => return None,
            };
            if *fml == ftrue() || *fml == ffalse() || !unknowns_of(fml).is_empty() {
                return None;
            }
            let elem_sort = to_sort(elem_t);
            let scoped_var = Formula::Var(Box::new(elem_sort.clone()), "_x".to_string());
            let set_val = Formula::Pred(
                Box::new(Sort::SetS(Box::new(elem_sort))),
                m_name.clone(),
                vec![Formula::Var(
                    Box::new(to_sort(base_t)),
                    crate::logic::VALUE_VAR_NAME.to_string(),
                )],
            );
            Some(Formula::All(
                Box::new(scoped_var.clone()),
                Box::new(implies(
                    member(scoped_var.clone(), set_val),
                    substitute(
                        &Substitution::from([(
                            crate::logic::VALUE_VAR_NAME.to_string(),
                            scoped_var,
                        )]),
                        fml.clone(),
                    ),
                )),
            ))
        }
        _ => None,
    }
}

/// Apply a type substitution to all symbols of the environment.
#[must_use]
pub fn type_substitute_env(tass: &BTreeMap<Id, RType>, env: &Environment) -> Environment {
    let mut env = env.clone();
    for inner in env.symbols.values_mut() {
        for sch in inner.values_mut() {
            *sch = schema_substitute(tass, sch);
        }
    }
    env
}

/// Insert weakest refinement.
#[must_use]
pub fn refine_top(env: &Environment, t: &SType) -> RType {
    match t {
        TypeSkeleton::ScalarT(base_t, ()) => {
            match base_t {
                BaseType::DatatypeT(name, t_args, p_args) => {
                    let variances = env.datatypes[name].pred_variances.clone();
                    TypeSkeleton::ScalarT(
                        BaseType::DatatypeT(
                            name.clone(),
                            t_args.iter().map(|a| refine_top(env, a)).collect(),
                            p_args
                                .iter()
                                .zip(variances.iter())
                                .map(|((), v)| Formula::BoolLit(!v))
                                .collect(),
                        ),
                        ftrue(),
                    )
                }
                BaseType::IntT => TypeSkeleton::ScalarT(BaseType::IntT, ftrue()),
                BaseType::BoolT => TypeSkeleton::ScalarT(BaseType::BoolT, ftrue()),
                BaseType::TypeVarT(vs, a) => {
                    TypeSkeleton::ScalarT(BaseType::TypeVarT(vs.clone(), a.clone()), ftrue())
                }
            }
        }
        TypeSkeleton::FunctionT(x, t_arg, t_res) => {
            TypeSkeleton::FunctionT(
                x.clone(),
                Box::new(refine_bot(env, t_arg)),
                Box::new(refine_top(env, t_res)),
            )
        }
        other => panic!("refineTop: unexpected skeleton {other:?}"),
    }
}

/// Insert strongest refinement.
#[must_use]
pub fn refine_bot(env: &Environment, t: &SType) -> RType {
    match t {
        TypeSkeleton::ScalarT(base_t, ()) => {
            match base_t {
                BaseType::DatatypeT(name, t_args, p_args) => {
                    let variances = env.datatypes[name].pred_variances.clone();
                    TypeSkeleton::ScalarT(
                        BaseType::DatatypeT(
                            name.clone(),
                            t_args.iter().map(|a| refine_bot(env, a)).collect(),
                            p_args
                                .iter()
                                .zip(variances.iter())
                                .map(|((), v)| Formula::BoolLit(*v))
                                .collect(),
                        ),
                        ffalse(),
                    )
                }
                BaseType::IntT => TypeSkeleton::ScalarT(BaseType::IntT, ffalse()),
                BaseType::BoolT => TypeSkeleton::ScalarT(BaseType::BoolT, ffalse()),
                BaseType::TypeVarT(vs, a) => {
                    TypeSkeleton::ScalarT(BaseType::TypeVarT(vs.clone(), a.clone()), ffalse())
                }
            }
        }
        TypeSkeleton::FunctionT(x, t_arg, t_res) => {
            TypeSkeleton::FunctionT(
                x.clone(),
                Box::new(refine_top(env, t_arg)),
                Box::new(refine_bot(env, t_res)),
            )
        }
        other => panic!("refineBot: unexpected skeleton {other:?}"),
    }
}

// Input language declarations

/// Constructor signature: name and type.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ConstructorSig {
    pub name: Id,
    pub rtype: RType,
}

#[must_use]
pub fn constructor_name(sig: &ConstructorSig) -> Id {
    sig.name.clone()
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum BareDeclaration {
    /// Type name, variables, and definition.
    TypeDecl(Id, Vec<Id>, RType),
    /// Function name and signature.
    FuncDecl(Id, RSchema),
    /// Datatype name, type parameters, predicate parameters, and constructors.
    DataDecl(Id, Vec<Id>, Vec<(PredSig, bool)>, Vec<ConstructorSig>),
    /// Measure name, input sort, output sort, postcondition, definition cases,
    /// constant args, and whether this is a termination metric.
    MeasureDecl(
        Id,
        Sort,
        Sort,
        Formula,
        Vec<MeasureCase>,
        MeasureDefaults,
        bool,
    ),
    /// Module-level predicate.
    PredDecl(PredSig),
    /// Qualifiers.
    QualifierDecl(Vec<Formula>),
    /// Mutual recursion group.
    MutualDecl(Vec<Id>),
    /// Inline predicate.
    InlineDecl(Id, Vec<Id>, Formula),
    /// Name and template for the function to reconstruct.
    SynthesisGoal(Id, UProgram),
}

pub type Declaration = Pos<BareDeclaration>;

#[must_use]
pub const fn is_synthesis_goal(decl: &Declaration) -> bool {
    matches!(&decl.node, BareDeclaration::SynthesisGoal(_, _))
}

// Misc

/// Typing constraints.
///
/// The environment is shared (`Rc`), so copying a constraint or the whole
/// pending list does not deep-clone the environment, which holds the refined
/// types of every bound symbol.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Constraint {
    Subtype(Rc<Environment>, RType, RType, bool, Id),
    WellFormed(Rc<Environment>, RType),
    WellFormedCond(Rc<Environment>, Formula),
    WellFormedMatchCond(Rc<Environment>, Formula),
    WellFormedPredicate(Rc<Environment>, Vec<Sort>, Id),
}

/// Synthesis goal.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Goal {
    /// Function name.
    pub g_name: Id,
    /// Enclosing environment (shared: immutable after resolution).
    pub g_environment: Rc<Environment>,
    /// Specification.
    pub g_spec: RSchema,
    /// Implementation template.
    pub g_impl: UProgram,
    /// Maximum level of auxiliary goal nesting allowed inside this goal.
    pub g_depth: usize,
    /// Source position.
    pub g_source_pos: SourcePos,
    /// Synthesis flag (false implies typechecking only).
    pub g_synthesize: bool,
}

#[must_use]
pub fn unresolved_type(env: &Environment, ident: &Id) -> RSchema {
    env.unresolved_constants[ident].clone()
}

#[must_use]
pub fn unresolved_spec(goal: &Goal) -> RSchema {
    unresolved_type(&goal.g_environment, &goal.g_name)
}

/// Remove measure being typechecked from environment.
#[must_use]
pub fn filter_env(env: &Environment, m: &Id) -> Environment {
    let mut env = env.clone();
    env.measures.retain(|k, _| k == m);
    env
}

/// Transform a resolved measure into a program.
pub fn measure_prog(_name: &Id, m: &MeasureDef) -> UProgram {
    if m.constant_args.is_empty() {
        let t = TypeSkeleton::AnyT;
        Program {
            type_of: t.clone(),
            content: BareProgram::PFun(
                "arg0".to_string(),
                Box::new(Program {
                    type_of: t.clone(),
                    content: BareProgram::PMatch(
                        Box::new(Program {
                            type_of: t,
                            content: BareProgram::PSymbol("arg0".to_string()),
                        }),
                        m.definitions.iter().map(m_case).collect(),
                    ),
                }),
            ),
        }
    } else {
        let (x, _) = &m.constant_args[0];
        let rest = MeasureDef {
            in_sort: m.in_sort.clone(),
            out_sort: m.out_sort.clone(),
            definitions: m.definitions.clone(),
            constant_args: m.constant_args[1..].to_vec(),
            postcondition: m.postcondition.clone(),
        };
        Program {
            type_of: TypeSkeleton::AnyT,
            content: BareProgram::PFun(x.clone(), Box::new(measure_prog(_name, &rest))),
        }
    }
}

/// Transform between case types.
#[must_use]
pub fn m_case(case: &MeasureCase) -> Case<RType> {
    Case {
        constructor: case.constructor.clone(),
        arg_names: case.arg_names.clone(),
        expr: fml_to_u_program(&case.body),
    }
}

/// Transform measure or predicate's sort signature into a
/// synthesis/typechecking schema. Predicate-polymorphic only.
#[must_use]
pub fn generate_schema(
    env: &Environment,
    name: &Id,
    in_sorts: &[(Option<Id>, Sort)],
    out_sort: &Sort,
    post: &Formula,
) -> RSchema {
    let all_pred_params: Vec<PredSig> = in_sorts
        .iter()
        .flat_map(|(_, s)| get_pred_params(env, s))
        .collect();
    pred_polymorphic(&all_pred_params, &[], name, in_sorts, out_sort, post)
}

fn get_pred_params(env: &Environment, s: &Sort) -> Vec<PredSig> {
    match s {
        Sort::DataS(name, _) => {
            env.datatypes
                .get(name)
                .map(|d| d.pred_params.clone())
                .unwrap_or_default()
        }
        _ => vec![],
    }
}

/// Wrap function in appropriate predicate-polymorphic schema skeleton.
fn pred_polymorphic(
    preds: &[PredSig],
    ps: &[Id],
    name: &Id,
    in_sorts: &[(Option<Id>, Sort)],
    out_sort: &Sort,
    post: &Formula,
) -> RSchema {
    match preds {
        [] => gen_skeleton(name, ps, in_sorts, out_sort, post),
        [x, rest @ ..] => {
            let mut ps2 = vec![x.pred_sig_name.clone()];
            ps2.extend(ps.iter().cloned());
            SchemaSkeleton::ForallP(
                x.clone(),
                Box::new(pred_polymorphic(rest, &ps2, name, in_sorts, out_sort, post)),
            )
        }
    }
}

/// Generate non-polymorphic core of schema.
fn gen_skeleton(
    _name: &Id,
    preds: &[Id],
    in_sorts: &[(Option<Id>, Sort)],
    out_sort: &Sort,
    post: &Formula,
) -> RSchema {
    SchemaSkeleton::Monotype(uncurry(preds, 0, in_sorts, out_sort, post))
}

fn uncurry(
    preds: &[Id],
    n: usize,
    in_sorts: &[(Option<Id>, Sort)],
    out_sort: &Sort,
    post: &Formula,
) -> RType {
    match in_sorts {
        [] => TypeSkeleton::ScalarT(base_type_of(&from_sort(out_sort)), post.clone()),
        [(x, s), rest @ ..] => {
            TypeSkeleton::FunctionT(
                x.clone().unwrap_or_else(|| format!("arg{n}")),
                Box::new(TypeSkeleton::ScalarT(to_type(s, preds), ftrue())),
                Box::new(uncurry(preds, n + 1, rest, out_sort, post)),
            )
        }
    }
}

fn to_type(s: &Sort, preds: &[Id]) -> BaseType<Formula> {
    match s {
        Sort::DataS(name, args) => {
            BaseType::DatatypeT(
                name.clone(),
                args.iter().map(from_sort).collect(),
                preds
                    .iter()
                    .map(|p| Formula::Pred(Box::new(Sort::AnyS), p.clone(), vec![]))
                    .collect(),
            )
        }
        _ => base_type_of(&from_sort(s)),
    }
}

/// Default set implementation, needed to typecheck measures involving sets.
#[must_use]
pub fn default_set_type() -> BareDeclaration {
    let tv = || {
        TypeSkeleton::ScalarT(
            BaseType::TypeVarT(Substitution::new(), "a".to_string()),
            Formula::BoolLit(true),
        )
    };
    let set_t = || {
        TypeSkeleton::ScalarT(
            BaseType::DatatypeT(SET_TYPE_NAME.to_string(), vec![tv()], vec![]),
            Formula::BoolLit(true),
        )
    };
    BareDeclaration::DataDecl(
        SET_TYPE_NAME.to_string(),
        vec!["a".to_string()],
        vec![],
        vec![
            ConstructorSig {
                name: crate::types::EMPTY_SET_CTOR.to_string(),
                rtype: set_t(),
            },
            ConstructorSig {
                name: crate::types::SINGLETON_CTOR.to_string(),
                rtype: TypeSkeleton::FunctionT("x".to_string(), Box::new(tv()), Box::new(set_t())),
            },
            ConstructorSig {
                name: crate::types::INSERT_SET_CTOR.to_string(),
                rtype: TypeSkeleton::FunctionT(
                    "x".to_string(),
                    Box::new(tv()),
                    Box::new(TypeSkeleton::FunctionT(
                        "xs".to_string(),
                        Box::new(set_t()),
                        Box::new(set_t()),
                    )),
                ),
            },
        ],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        logic::vars_of,
        types::{int_, is_var_refinement},
    };

    fn any() -> RType {
        TypeSkeleton::AnyT
    }

    fn suntyped(content: BareProgram<RType>) -> RProgram {
        Program {
            content,
            type_of: any(),
        }
    }

    #[test]
    fn lookup_symbol_builtins() {
        let env = empty_env();
        let sch = lookup_symbol(&"True".to_string(), 0, false, &env).unwrap();
        assert!(matches!(
            to_monotype(&sch),
            TypeSkeleton::ScalarT(BaseType::BoolT, _)
        ));
        let sch = lookup_symbol(&"False".to_string(), 0, false, &env).unwrap();
        assert!(matches!(
            to_monotype(&sch),
            TypeSkeleton::ScalarT(BaseType::BoolT, _)
        ));
        let sch = lookup_symbol(&"42".to_string(), 0, false, &env).unwrap();
        assert!(matches!(
            to_monotype(&sch),
            TypeSkeleton::ScalarT(BaseType::IntT, _)
        ));
        let sch = lookup_symbol(&"!".to_string(), 1, false, &env).unwrap();
        assert!(matches!(
            to_monotype(&sch),
            TypeSkeleton::FunctionT(x, _, _) if x == "x"
        ));
        assert!(lookup_symbol(&"nope".to_string(), 0, false, &env).is_none());
    }

    #[test]
    fn lookup_symbol_set_overloading() {
        let env = empty_env();
        // "+" with sets resolves to Union (the second matching operator)
        let sch = lookup_symbol(&"+".to_string(), 2, true, &env).unwrap();
        assert!(matches!(sch, SchemaSkeleton::ForallT(ref a, _) if a == "a"));
        let t = to_monotype(&sch);
        match t {
            TypeSkeleton::FunctionT(_, _, res) => {
                match &*res {
                    TypeSkeleton::FunctionT(_, _, res) => {
                        match &**res {
                            TypeSkeleton::ScalarT(BaseType::DatatypeT(name, ..), _) => {
                                assert_eq!(name, SET_TYPE_NAME);
                            }
                            _ => panic!("union: expected set result type"),
                        }
                    }
                    _ => panic!("union: expected curried function type"),
                }
            }
            _ => panic!("union: expected function type"),
        }
        // without sets, "+" is Plus
        let sch = lookup_symbol(&"+".to_string(), 2, false, &env).unwrap();
        let t = to_monotype(&sch);
        if let TypeSkeleton::FunctionT(_, _, res) = t {
            if let TypeSkeleton::FunctionT(_, _, res) = &*res {
                assert!(matches!(&**res, TypeSkeleton::ScalarT(BaseType::IntT, _)));
            } else {
                panic!("plus: expected curried function type");
            }
        } else {
            panic!("plus: expected function type");
        }
    }

    #[test]
    fn add_and_remove_variables() {
        let env = empty_env();
        let env = add_variable(&"x".to_string(), &int_all(), &env);
        let sch = lookup_symbol(&"x".to_string(), 0, false, &env).unwrap();
        assert!(matches!(
            to_monotype(&sch),
            TypeSkeleton::ScalarT(BaseType::IntT, _)
        ));
        let env = remove_variable(&"x".to_string(), &env);
        assert!(lookup_symbol(&"x".to_string(), 0, false, &env).is_none());
    }

    #[test]
    fn add_variables_are_grouped_by_arity() {
        let env = empty_env();
        let env = add_variable(&"x".to_string(), &int_all(), &env);
        let f_type =
            TypeSkeleton::FunctionT("x".to_string(), Box::new(int_all()), Box::new(int_all()));
        let env = add_variable(&"f".to_string(), &f_type, &env);
        assert_eq!(symbols_of_arity(0, &env).len(), 1);
        assert_eq!(symbols_of_arity(1, &env).len(), 1);
        assert_eq!(all_symbols(&env).len(), 2);
    }

    #[test]
    fn environment_equality_by_logic() {
        let env1 = empty_env();
        let mut env2 = empty_env();
        env2.used_scrutinees.push(u_hole());
        assert_eq!(env1, env2);
        let env3 = add_assumption(ftrue(), &empty_env());
        assert_ne!(env1, env3);
    }

    #[test]
    fn symbols_of_collects_names() {
        let p = suntyped(BareProgram::PApp(
            Box::new(suntyped(BareProgram::PSymbol("f".to_string()))),
            Box::new(suntyped(BareProgram::PSymbol("x".to_string()))),
        ));
        let s = symbols_of(&p);
        assert_eq!(s.len(), 2);
        assert!(s.contains(&"f".to_string()));
        assert!(s.contains(&"x".to_string()));
    }

    #[test]
    fn fml_to_u_program_equality_formula() {
        let fml = eq(int_var("x"), int_lit(1));
        let p = fml_to_u_program(&fml);
        assert_eq!(symbol_list(&p), vec!["==", "x", "1"]);
        assert!(is_hole(&u_hole()));
    }

    #[test]
    fn fml_to_u_program_set_literals() {
        let set = Formula::SetLit(Box::new(Sort::IntS), vec![int_lit(1), int_lit(2)]);
        let p = fml_to_u_program(&set);
        let names = symbol_list(&p);
        assert_eq!(names[0], crate::types::INSERT_SET_CTOR);
        assert!(names.iter().any(|n| n == crate::types::EMPTY_SET_CTOR));
        let single = Formula::SetLit(Box::new(Sort::IntS), vec![int_lit(3)]);
        let p = fml_to_u_program(&single);
        assert_eq!(symbol_list(&p)[0], crate::types::SINGLETON_CTOR);
    }

    #[test]
    fn fml_to_program_variable() {
        let fml = Formula::Var(Box::new(Sort::IntS), "x".to_string());
        let p = fml_to_program(&fml);
        assert_eq!(symbol_name(&p), "x");
        match &p.type_of {
            TypeSkeleton::ScalarT(BaseType::IntT, fml) => {
                assert!(is_var_refinement(fml));
            }
            _ => panic!("fmlToProgram: expected scalar int type"),
        }
    }

    #[test]
    fn rename_as_impl_renames_arguments() {
        let p = suntyped(BareProgram::PFun("y".to_string(), Box::new(u_hole())));
        // The result refinement mentions the outer binder "x"; renaming
        // "x" into "y" must apply to the continuation.
        let t = TypeSkeleton::FunctionT(
            "x".to_string(),
            Box::new(int_all()),
            Box::new(bool_type(eq(bool_var("bx"), eq(int_var("x"), int_lit(0))))),
        );
        let is_bound = |_: &Id| false;
        let t2 = rename_as_impl(&is_bound, &p, &t);
        match &t2 {
            TypeSkeleton::FunctionT(y, _, t_res) => {
                assert_eq!(y, "y");
                match &**t_res {
                    TypeSkeleton::ScalarT(BaseType::BoolT, fml) => {
                        let vars = vars_of(fml);
                        assert!(vars.contains(&int_var("y")));
                        assert!(!vars.contains(&int_var("x")));
                    }
                    _ => panic!("renameAsImpl: expected scalar bool result"),
                }
            }
            _ => panic!("renameAsImpl: expected function type"),
        }
    }

    #[test]
    fn refine_top_and_bot() {
        let env = empty_env();
        let top = refine_top(&env, &int_());
        assert_eq!(top, int_type(ftrue()));
        let bot = refine_bot(&env, &int_());
        assert_eq!(bot, int_type(ffalse()));
    }

    #[test]
    fn measures_are_filtered_by_datatype() {
        let env = empty_env();
        let m = MeasureDef {
            in_sort: Sort::DataS("List".to_string(), vec![Sort::IntS]),
            out_sort: Sort::IntS,
            definitions: vec![],
            constant_args: vec![],
            postcondition: ftrue(),
        };
        let env = add_measure(&"len".to_string(), m, &env);
        assert_eq!(all_measures_of(&"List".to_string(), &env).len(), 1);
        assert!(all_measures_of(&"Nat".to_string(), &env).is_empty());
    }

    #[test]
    fn measure_prog_wraps_constant_args() {
        let m = MeasureDef {
            in_sort: Sort::DataS("List".to_string(), vec![Sort::IntS]),
            out_sort: Sort::IntS,
            definitions: vec![],
            constant_args: vec![("k".to_string(), Sort::IntS)],
            postcondition: ftrue(),
        };
        let p = measure_prog(&"len".to_string(), &m);
        match p.content {
            BareProgram::PFun(x, body) => {
                assert_eq!(x, "k");
                match body.content {
                    BareProgram::PFun(y, inner) => {
                        assert_eq!(y, "arg0");
                        assert!(matches!(inner.content, BareProgram::PMatch(..)));
                    }
                    _ => panic!("expected lambda for body"),
                }
            }
            _ => panic!("expected lambda for constant arg"),
        }
    }

    #[test]
    fn default_set_type_declaration() {
        match default_set_type() {
            BareDeclaration::DataDecl(name, tvs, preds, cons) => {
                assert_eq!(name, SET_TYPE_NAME);
                assert_eq!(tvs, vec!["a".to_string()]);
                assert!(preds.is_empty());
                assert_eq!(cons.len(), 3);
            }
            _ => panic!("defaultSetType: expected data declaration"),
        }
    }

    #[test]
    fn generate_schema_function() {
        let env = empty_env();
        let sch = generate_schema(
            &env,
            &"f".to_string(),
            &[(Some("x".to_string()), Sort::IntS)],
            &Sort::IntS,
            &ftrue(),
        );
        match &sch {
            SchemaSkeleton::Monotype(t) => {
                match t {
                    TypeSkeleton::FunctionT(x, t_arg, t_res) => {
                        assert_eq!(x, "x");
                        assert!(matches!(
                            (**t_arg).clone(),
                            TypeSkeleton::ScalarT(BaseType::IntT, _)
                        ));
                        assert!(matches!(
                            (**t_res).clone(),
                            TypeSkeleton::ScalarT(BaseType::IntT, _)
                        ));
                    }
                    _ => panic!("generateSchema: expected function type"),
                }
            }
            _ => panic!("generateSchema: expected monotype"),
        }
    }

    #[test]
    fn program_equality_ignores_annotations() {
        let p1 = suntyped(BareProgram::PSymbol("x".to_string()));
        let p2 = Program {
            content: BareProgram::PSymbol("x".to_string()),
            type_of: int_all(),
        };
        assert_eq!(p1, p2);
        let p3 = suntyped(BareProgram::PSymbol("y".to_string()));
        assert_ne!(p1, p3);
    }

    #[test]
    fn program_substitute_symbol_test() {
        let p = suntyped(BareProgram::PApp(
            Box::new(suntyped(BareProgram::PSymbol("f".to_string()))),
            Box::new(suntyped(BareProgram::PSymbol("x".to_string()))),
        ));
        let sub = suntyped(BareProgram::PSymbol("z".to_string()));
        let p2 = program_substitute_symbol(&"x".to_string(), &sub, &p);
        assert_eq!(symbol_list(&p2), vec!["f", "z"]);
    }
}

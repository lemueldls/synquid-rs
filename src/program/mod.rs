mod env;

use core::fmt;
use std::collections::BTreeSet;

pub use env::*;
use hashbrown::{HashMap, HashSet};
use itertools::Itertools;
use owo_colors::OwoColorize;

use crate::{
    error::{Pos, SourcePos},
    logic::{
        Formula, PredSig, Sort, Substitution, UnOp, DONT_CARE, EMPTY_SET_CTOR, INSERT_SET_CTOR,
        SET_CONSTRUCTORS, SET_TYPE_NAME, SET_TYPE_VAR, SINGLETON_CTOR,
    },
    r#type::{BaseType, RSchema, RType, SchemaSkeleton, TypeSkeleton},
    tokens::{BIN_OP_TOKENS, UN_OP_TOKENS},
    util::Id,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Case<T: fmt::Display> {
    pub constructor: Id,
    pub arg_names: Vec<Id>,
    pub expr: Program<T>,
}

impl<T: fmt::Display> fmt::Display for Case<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            hang(
                '\t',
                format!(
                    "{constructor} {arg_names} -> {expr}",
                    constructor = self.constructor,
                    arg_names = self.arg_names.iter().format(" "),
                    expr = self.expr
                )
            )
        )
    }
}

#[derive(derive_more::IsVariant, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum BareProgram<T: fmt::Display> {
    Symbol(Id),
    App(Program<T>, Program<T>),
    Fun(Id, Program<T>),
    If(Program<T>, Program<T>, Program<T>),
    Match(Program<T>, Vec<Case<T>>),
    Fix(Vec<Id>, Program<T>),
    Let(Id, Program<T>, Program<T>),
    // Bind(Id, Program<T>, Program<T>),
    // Pure(Id, Program<T>, Program<T>),
    Hole,
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Program<T: fmt::Display> {
    pub content: Box<BareProgram<T>>,
    pub type_of: T,
}

/// Untyped programs
#[repr(transparent)]
#[derive(
    derive_more::AsRef,
    derive_more::Into,
    derive_more::Constructor,
    Debug,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
)]
pub struct UProgram(Program<RType>);

impl fmt::Display for UProgram {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Refinement-typed programs
#[repr(transparent)]
#[derive(
    derive_more::AsRef,
    derive_more::Into,
    derive_more::Constructor,
    Debug,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
)]
pub struct RProgram(Program<RType>);

impl fmt::Display for RProgram {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<T: fmt::Display> Program<T> {
    // pub fn untyped(c: BareProgram<T>) -> Self {
    //     Self {
    //         content: Box::new(c),
    //         type_of: TypeSkeleton::Any,
    //     }
    // }

    // pub fn u_hole() -> Self {
    //     Self::untyped(BareProgram::Hole)
    // }

    // pub fn erase_types()

    pub fn symbol_name(&self) -> &Id {
        match &*self.content {
            BareProgram::Symbol(name) => name,
            _ => todo!(),
        }
    }

    pub fn symbol_list(&self) -> Vec<&Id> {
        match &*self.content {
            BareProgram::Symbol(name) => vec![name],
            BareProgram::App(fun, arg) => {
                let mut vec = fun.symbol_list();
                vec.extend(arg.symbol_list());

                vec
            }
            _ => todo!(),
        }
    }

    pub fn symbols(&self) -> HashSet<&Id> {
        match &*self.content {
            BareProgram::Symbol(name) => {
                let mut set = HashSet::new();
                set.insert(name);

                set
            }
            BareProgram::App(fun, arg) => {
                let mut set = fun.symbols();
                set.extend(arg.symbols());

                set
            }
            BareProgram::Fun(_, body) => body.symbols(),
            BareProgram::If(cond, then, els) => {
                let mut set = cond.symbols();
                set.extend(then.symbols());
                set.extend(els.symbols());

                set
            }
            BareProgram::Match(scr, cases) => {
                let mut set = scr.symbols();

                for case in cases {
                    set.extend(case.expr.symbols());
                }

                set
            }
            BareProgram::Fix(_, body) => body.symbols(),
            BareProgram::Let(_, def, body) => {
                let mut set = def.symbols();
                set.extend(body.symbols());

                set
            }
            _ => HashSet::new(),
        }
    }

    pub fn error(&self) -> TypeSkeleton<Formula> {
        match &*self.content {
            BareProgram::Error => TypeSkeleton::vart(DONT_CARE),
            _ => todo!(),
        }
    }
}

impl<T: fmt::Display> fmt::Display for Program<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // REVIEW implementation of `</>`
        match &*self.content {
            BareProgram::Symbol(s) => write!(f, "{s}"),
            BareProgram::App(fa, x) => {
                let opt_params = |p: &Program<_>| match &*p.content {
                    BareProgram::Symbol(_) => p.to_string(),
                    BareProgram::Hole => p.to_string(),
                    _ => format!("({p})"),
                };

                let prefix = hang('\t', format!("{fa} {x}", x = opt_params(x)));

                let s = match &*fa.content {
                    BareProgram::Symbol(name) => {
                        if UN_OP_TOKENS.contains_right(&name) {
                            hang('\t', format!("{name} {x}", x = opt_params(x)))
                        } else {
                            prefix
                        }
                    }
                    BareProgram::App(g, y) => match &*g.content {
                        BareProgram::Symbol(name) => {
                            if BIN_OP_TOKENS.contains_right(&name) {
                                hang(
                                    '\t',
                                    format!("{y} {name} {x}", y = opt_params(y), x = opt_params(x)),
                                )
                            } else {
                                prefix
                            }
                        }
                        _ => prefix,
                    },
                    _ => prefix,
                };

                write!(f, "{s}")
            }
            BareProgram::Fun(x, e) => write!(f, "{}", nest(2, format!("\\{x} . {e}"))),
            BareProgram::If(c, t, e) => write!(
                f,
                "\n{}",
                hang(
                    '\t',
                    format!(
                        "if {c}\n{}\n{}",
                        hang('\t', format!("then {t}")),
                        hang('\t', format!("else {e}"))
                    ),
                )
            ),
            BareProgram::Match(l, cases) => write!(
                f,
                "\n{}",
                hang(
                    '\t',
                    format!("match {l} with\n{}", cases.iter().format("\n"))
                )
            ),
            BareProgram::Fix(_fs, e) => write!(f, "{e}"),
            BareProgram::Let(x, d, b) => {
                write!(
                    f,
                    "\n{}",
                    hang('\t', format!("let {x} {} = {d} in {b}", d.type_of))
                )
            }
            BareProgram::Hole => {
                if Id::Local(format!("{}", self.type_of).into_boxed_str()) == DONT_CARE {
                    write!(f, "??")
                } else {
                    write!(f, "(?? ::) {}", self.type_of)
                }
            }
            BareProgram::Error => write!(f, "error"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct DatatypeDef {
    /// Type parameters
    pub type_params: Vec<Id>,
    /// Signatures of predicate parameters
    pub pred_params: Vec<PredSig>,
    /// For each predicate parameter, whether it is contravariant
    pub pred_variances: Vec<bool>,
    /// Constructor names
    pub constructors: Vec<Id>,
    /// Name of the measure that serves as well founded termination metric
    pub wf_metric: Option<Id>,
}

/// One case in a measure definition: constructor name, arguments, and body
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct MeasureCase(pub Id, pub Vec<Id>, pub Formula);

impl fmt::Display for MeasureCase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let MeasureCase(con, args, body) = self;

        write!(f, "{con} {args} = {body}", args = args.iter().format(" "))
    }
}

pub type MeasureDefaults = Vec<(Id, Sort)>;

/// User-defined measure function representation
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct MeasureDef {
    pub in_sort: Sort,
    pub out_sort: Sort,
    pub definitions: Vec<MeasureCase>,
    pub constant_args: MeasureDefaults,
    pub postcondition: Formula,
}

// makeLenses ''MeasureDef

/// All possible constant arguments of measures with multiple arguments
pub type ArgMap = HashMap<Id, Vec<HashSet<Formula>>>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructorSig(Id, pub RType);

impl ConstructorSig {
    pub fn name(&self) -> &Id {
        &self.0
    }
}

impl fmt::Display for ConstructorSig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ConstructorSig(name, t) = self;

        write!(f, "{name} :: {t}")
    }
}

#[derive(derive_more::IsVariant, Debug, Clone, PartialEq, Eq)]
pub enum BareDeclaration {
    /// Type name, variables, and definition
    TypeDecl(Id, BTreeSet<Id>, RType),
    /// Function name and signature
    FuncDecl(Id, RSchema),
    /// Datatype name, type parameters, predicate parameters, and constructor definitions
    DataDecl(Id, Vec<Id>, Vec<(PredSig, bool)>, Vec<ConstructorSig>),
    /// Measure name, input sort, output sort, postcondition, definition cases, and whether this is a termination metric
    MeasureDecl(
        Id,
        Sort,
        Sort,
        Formula,
        Vec<MeasureCase>,
        MeasureDefaults,
        bool,
    ),
    /// Module-level predicate
    PredDecl(PredSig),
    /// Qualifiers
    QualifierDecl(Vec<Formula>),
    /// Mutual recursion group
    MutualDecl(Vec<Id>),
    /// Inline predicate
    InlineDecl(Id, HashSet<Id>, Formula),
    /// Name and template for the function to reconstruct
    SynthesisGoal(Id, UProgram),
}

impl BareDeclaration {
    // -- Default set implementation -- Needed to typecheck measures involving sets
    // defaultSetType :: BareDeclaration
    // defaultSetType = DataDecl name typeVars preds cons
    //   where
    //     name = setTypeName
    //     typeVars = ["a"]
    //     preds = []
    //     cons = [empty,single,insert]
    //     empty = ConstructorSig emptySetCtor (ScalarT (DatatypeT setTypeName [ScalarT (TypeVarT Map.empty "a") (BoolLit True)] []) (BoolLit True))
    //     single = ConstructorSig singletonCtor (FunctionT "x" (ScalarT (TypeVarT Map.empty "a") (BoolLit True)) (ScalarT (DatatypeT setTypeName [ScalarT (TypeVarT Map.empty "a") (BoolLit True)] []) (BoolLit True)))
    //     insert = ConstructorSig insertSetCtor (FunctionT "x" (ScalarT (TypeVarT Map.empty "a") (BoolLit True)) (FunctionT "xs" (ScalarT (DatatypeT setTypeName [ScalarT (TypeVarT Map.empty "a") (BoolLit True)] []) (BoolLit True)) (ScalarT (DatatypeT setTypeName [ScalarT (TypeVarT Map.empty "a") (BoolLit True)] []) (BoolLit True))))

    /// Default set implementation -- Needed to typecheck measures involving sets
    pub fn default_set_type() -> BareDeclaration {
        let name = Id::Builtin("Set");
        let type_vars = vec![Id::Builtin("a")];
        let preds = Vec::new();

        let empty = ConstructorSig(
            EMPTY_SET_CTOR,
            RType::Scalar(
                BaseType::Datatype(
                    SET_TYPE_NAME,
                    vec![TypeSkeleton::Scalar(
                        BaseType::TypeVar(Substitution::default(), Id::Builtin("a")),
                        Formula::TRUE,
                    )],
                    Vec::new(),
                ),
                Formula::TRUE,
            ),
        );
        let single = ConstructorSig(
            SINGLETON_CTOR,
            RType::Function {
                x: Id::Builtin("x"),
                t_arg: Box::new(TypeSkeleton::Scalar(
                    BaseType::TypeVar(Substitution::default(), Id::Builtin("a")),
                    Formula::TRUE,
                )),
                t_res: Box::new(TypeSkeleton::Scalar(
                    BaseType::Datatype(
                        SET_TYPE_NAME,
                        vec![TypeSkeleton::Scalar(
                            BaseType::TypeVar(Substitution::default(), Id::Builtin("a")),
                            Formula::TRUE,
                        )],
                        Vec::new(),
                    ),
                    Formula::TRUE,
                )),
            },
        );
        let insert = ConstructorSig(
            INSERT_SET_CTOR,
            RType::Function {
                x: Id::Builtin("x"),
                t_arg: Box::new(TypeSkeleton::Scalar(
                    BaseType::TypeVar(Substitution::default(), Id::Builtin("a")),
                    Formula::TRUE,
                )),
                t_res: Box::new(TypeSkeleton::Function {
                    x: Id::Builtin("xs"),
                    t_arg: Box::new(TypeSkeleton::Scalar(
                        BaseType::Datatype(
                            SET_TYPE_NAME,
                            vec![TypeSkeleton::Scalar(
                                BaseType::TypeVar(Substitution::default(), Id::Builtin("a")),
                                Formula::TRUE,
                            )],
                            Vec::new(),
                        ),
                        Formula::TRUE,
                    )),
                    t_res: Box::new(TypeSkeleton::Scalar(
                        BaseType::Datatype(
                            SET_TYPE_NAME,
                            vec![TypeSkeleton::Scalar(
                                BaseType::TypeVar(Substitution::default(), Id::Builtin("a")),
                                Formula::TRUE,
                            )],
                            Vec::new(),
                        ),
                        Formula::TRUE,
                    )),
                }),
            },
        );

        let cons = vec![empty, single, insert];

        BareDeclaration::DataDecl(name, type_vars, preds, cons)
    }
}

pub fn pretty_variance_param(param: &(PredSig, bool)) -> String {
    let (pred, contra) = param;

    let mut s = pred.to_string();

    if *contra {
        s.push('-');
    }

    s
}

// REVIEW - Verify implementation
pub fn pretty_measure_defaults(args: &Vec<(Id, Sort)>) -> String {
    args.iter().map(|(v, s)| format!("{v} : {s}")).join(" -> ")
}

impl fmt::Display for BareDeclaration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO - syntax highlighting?
        match self {
            BareDeclaration::TypeDecl(name, tvs, t) => {
                write!(f, "type {name} {} = {t}", tvs.iter().format(" "))
            }
            BareDeclaration::FuncDecl(name, t) => write!(f, "{name} :: {t}"),
            BareDeclaration::DataDecl(name, t_params, p_params, ctors) => {
                write!(
                    f,
                    "{}",
                    hang(
                        '\t',
                        format!(
                            "data {name} {t_params} {p_params} where\n{ctors}",
                            t_params = t_params.iter().format(" "),
                            p_params = p_params.iter().format_with(" ", |param, f| f(
                                &format_args!("{}", pretty_variance_param(param))
                            )),
                            ctors = ctors.iter().format("\n"),
                        )
                    )
                )
            }
            BareDeclaration::MeasureDecl(
                name,
                in_sort,
                out_sort,
                post,
                cases,
                args,
                is_termination,
            ) => {
                write!(
                    f,
                    "{}",
                    hang(
                        '\t',
                        format!(
                            "{termination} measure {name} :: {args} {in_sort} -> {out_sort}",
                            termination = if *is_termination { "termination" } else { "" },
                            args = pretty_measure_defaults(args),
                            in_sort = in_sort,
                            out_sort = if *post == Formula::TRUE {
                                format!("{out_sort}")
                            } else {
                                format!(
                                    "{{{out_sort} | {post}}} where\n{cases}",
                                    cases = cases.iter().format("\n")
                                )
                            }
                        )
                    )
                )
            }
            BareDeclaration::QualifierDecl(fmls) => {
                write!(f, "qualifier {{{fmls}}}", fmls = fmls.iter().format(", "))
            }
            BareDeclaration::MutualDecl(names) => {
                write!(f, "mutual {names}", names = names.iter().format(", "))
            }
            BareDeclaration::InlineDecl(name, args, body) => {
                write!(
                    f,
                    "inline {name} {args} = {body}",
                    args = args.iter().format(" ")
                )
            }
            BareDeclaration::SynthesisGoal(name, impl_) => write!(f, "{name} = {impl_}"),
            _ => todo!(),
        }
    }
}

pub fn hang(p: char, s: String) -> String {
    s.replace('\n', &format!("\n{p}"))
}

pub fn nest(n: usize, s: String) -> String {
    s.lines()
        .map(|line| format!("{:n$}", line, n = n))
        .join("\n")
}

pub fn align(s: String) -> String {
    s.lines()
        .map(|line| line.trim())
        .collect::<Vec<&str>>()
        .join("\n")
}

#[derive(
    derive_more::AsRef, derive_more::Into, derive_more::Constructor, Debug, Clone, PartialEq, Eq,
)]
pub struct Declaration(Pos<BareDeclaration>);

impl Declaration {
    pub fn is_synthesis_goal(&self) -> bool {
        match self.as_ref().node {
            BareDeclaration::SynthesisGoal(_, _) => true,
            _ => false,
        }
    }
}

/// Typing constraints
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Constraint {
    Subtype(Environment, RType, RType, bool, Id),
    WellFormed(Environment, RType),
    WellFormedCond(Environment, Formula),
    WellFormedMatchCond(Environment, Formula),
    WellFormedPredicate(Environment, Vec<Sort>, Id),
}

impl fmt::Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constraint::Subtype(env, t1, t2, false, label) => {
                write!(
                    f,
                    "{env} {} {t1} {} {t2} ({label})",
                    "|-".white().dimmed(),
                    "<:".white().dimmed()
                )
            }
            Constraint::Subtype(env, t1, t2, true, label) => write!(
                f,
                "{env} {} {t1} {} {t2} ({label})",
                "|-".white().dimmed(),
                "/\\".white().dimmed()
            ),
            Constraint::WellFormed(env, t) => write!(f, "{env} {} {t}", "|-".white().dimmed()),
            Constraint::WellFormedCond(env, c) => write!(f, "{env} {} {c}", "|-".white().dimmed()),
            Constraint::WellFormedMatchCond(env, c) => {
                write!(f, "{env} {} {c}", "|- (match)".white().dimmed())
            }
            Constraint::WellFormedPredicate(_, sorts, p) => write!(
                f,
                "{} {p} {} {} {}",
                "|-".white().dimmed(),
                "::".white().dimmed(),
                sorts
                    .iter()
                    .format_with(" ", |s, f| f(&format_args!("{s} ->"))),
                Sort::Bool
            ),
        }
    }
}

/// Synthesis goal
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Goal {
    /// Function name
    pub name: Id,
    /// Enclosing environment
    pub environment: Environment,
    /// Specification
    pub spec: RSchema,
    /// Implementation template
    pub impl_: UProgram,
    /// Maximum level of auxiliary goal nesting allowed inside this goal
    pub depth: usize,
    /// Source Position
    pub source_pos: SourcePos,
    /// Synthesis flag (false implies typechecking only)
    pub synthesize: bool,
}

pub fn unresolved_type<'a>(env: &'a Environment, ident: &Id) -> &'a RSchema {
    &env.unresolved_constants[ident]
}

pub fn unresolved_spec<'a>(goal: &'a Goal) -> &'a RSchema {
    unresolved_type(&goal.environment, &goal.name)
}

/// Remove measure being type-checked from environment
pub fn filter_env<'a>(e: &'a mut Environment, m: &Id) -> &'a mut Environment {
    e.measures.retain(|k, _| k == m);

    e
}

/// Transform a resolved measure into a program
pub fn measure_prog(name: &Id, def: MeasureDef) -> UProgram {
    if def.constant_args.is_empty() {
        let id = Id::Builtin("arg0");
        let t = TypeSkeleton::Any;

        UProgram::new(Program {
            content: Box::new(BareProgram::Fun(
                id.clone(),
                Program {
                    content: Box::new(BareProgram::Match(
                        Program {
                            content: Box::new(BareProgram::Symbol(id.clone())),
                            type_of: t.clone(),
                        },
                        def.definitions
                            .into_iter()
                            .map(|mcase| Case {
                                constructor: mcase.0,
                                arg_names: mcase.1,
                                expr: Program {
                                    content: Box::new(BareProgram::Symbol(id.clone())),
                                    type_of: t.clone(),
                                },
                            })
                            .collect(),
                    )),
                    type_of: t.clone(),
                },
            )),
            type_of: t,
        })
    } else {
        let id = def.constant_args[0].0.clone();
        let t = TypeSkeleton::Any;

        UProgram::new(Program {
            content: Box::new(BareProgram::Fun(
                id.clone(),
                measure_prog(
                    name,
                    MeasureDef {
                        in_sort: def.in_sort,
                        out_sort: def.out_sort,
                        definitions: def.definitions,
                        constant_args: def.constant_args[1..].to_vec(),
                        postcondition: def.postcondition,
                    },
                )
                .into(),
            )),
            type_of: t,
        })
    }
}

// -- Transform between case types
// mCase :: MeasureCase -> Case RType
// mCase (MeasureCase con args body) = Case{constructor = con, argNames = args, expr = fmlToUProgram body}

pub fn m_case(measure_case: MeasureCase) -> Case<RType> {
    let MeasureCase(con, args, body) = measure_case;

    Case {
        constructor: con,
        arg_names: args,
        expr: body.to_u_program().into(),
    }
}

// -- Transform measure or predicate's sort signature into a synthesis/typechecking schema
// generateSchema :: Environment -> Id -> [(Maybe Id, Sort)] -> Sort -> Formula -> RSchema
// -- generateSchema e name inSorts outSort post = typePolymorphic allTypeParams allPredParams name inSorts outSort post
// -- predicate polymorphic only:
// generateSchema e name inSorts outSort post = predPolymorphic allPredParams [] name inSorts outSort post
//   where
//     allPredParams = concat $ fmap ((getPredParams e) . snd) inSorts
//     allTypeParams = concat $ fmap ((getTypeParams e) . snd) inSorts

/// Transform measure or predicate's sort signature into a synthesis/typechecking schema
pub fn generate_schema(
    e: &Environment,
    name: &Id,
    in_sorts: &[(Option<Id>, Sort)],
    out_sort: &Sort,
    post: Formula,
) -> RSchema {
    let all_pred_params = in_sorts
        .iter()
        .map(|(_, s)| get_pred_params(e, s))
        .flatten()
        .collect();
    // let all_type_params = in_sorts
    //     .iter()
    //     .map(|(_, s)| get_type_params(e, s))
    //     .flatten()
    //     .collect();

    pred_polymorphic(all_pred_params, Vec::new(), name, in_sorts, out_sort, post)
}

// getTypeParams :: Environment -> Sort -> [Id]
// getTypeParams e (DataS name _) = case Map.lookup name (e ^. datatypes) of
//   Just d -> d ^. typeParams
//   Nothing -> []
// getTypeParams e _              = []

pub fn get_type_params(e: &Environment, sort: &Sort) -> Vec<Id> {
    match sort {
        Sort::Data(name, _) => e
            .datatypes
            .get(name)
            .map_or_else(Vec::new, |d| d.type_params.clone()),
        _ => Vec::new(),
    }
}

// getPredParams :: Environment -> Sort -> [PredSig]
// getPredParams e (DataS name _) = case Map.lookup name (e ^. datatypes) of
//   Just d -> d ^. predParams
//   Nothing -> []
// getPredParams e _              = []

pub fn get_pred_params(e: &Environment, sort: &Sort) -> Vec<PredSig> {
    match sort {
        Sort::Data(name, _) => e
            .datatypes
            .get(name)
            .map_or_else(Vec::new, |d| d.pred_params.clone()),
        _ => Vec::new(),
    }
}

// -- Wrap function in appropriate type-polymorphic Schema skeleton
// typePolymorphic :: [Id] -> [PredSig] -> Id -> [(Maybe Id, Sort)] -> Sort -> Formula -> SchemaSkeleton Formula
// typePolymorphic [] ps name inSorts outSort f = predPolymorphic ps [] name inSorts outSort f
// typePolymorphic (x:xs) ps name inSorts outSort f = ForallT x (typePolymorphic xs ps name inSorts outSort f)

/// Wrap function in appropriate type-polymorphic Schema skeleton
pub fn type_polymorphic(
    xs: Vec<Id>,
    ps: Vec<PredSig>,
    name: &Id,
    in_sorts: &[(Option<Id>, Sort)],
    out_sort: &Sort,
    post: Formula,
) -> SchemaSkeleton<Formula> {
    if xs.is_empty() {
        pred_polymorphic(ps, Vec::new(), name, in_sorts, out_sort, post)
    } else {
        SchemaSkeleton::ForAllType(
            xs[0].clone(),
            Box::new(type_polymorphic(
                xs[1..].to_vec(),
                ps.clone(),
                name,
                in_sorts,
                out_sort,
                post,
            )),
        )
    }
}

// -- Wrap function in appropriate predicate-polymorphic SchemaSkeleton
// predPolymorphic :: [PredSig] -> [Id] -> Id -> [(Maybe Id, Sort)] -> Sort -> Formula -> SchemaSkeleton Formula
// predPolymorphic [] ps name inSorts outSort f = genSkeleton name ps inSorts outSort f
// predPolymorphic (x:xs) ps name inSorts outSort f = ForallP x (predPolymorphic xs  ((predSigName x) : ps) name inSorts outSort f)

/// Wrap function in appropriate predicate-polymorphic SchemaSkeleton
pub fn pred_polymorphic(
    xs: Vec<PredSig>,
    ps: Vec<Id>,
    name: &Id,
    in_sorts: &[(Option<Id>, Sort)],
    out_sort: &Sort,
    post: Formula,
) -> SchemaSkeleton<Formula> {
    if xs.is_empty() {
        gen_skeleton(name, ps, in_sorts, out_sort, post)
    } else {
        SchemaSkeleton::ForAllPredicate(
            xs[0].clone(),
            Box::new(pred_polymorphic(
                xs[1..].to_vec(),
                vec![xs[0].name.clone()],
                name,
                in_sorts,
                out_sort,
                post,
            )),
        )
    }
}

// -- Generate non-polymorphic core of schema
// genSkeleton :: Id -> [Id] -> [(Maybe Id, Sort)] -> Sort -> Formula -> SchemaSkeleton Formula
// genSkeleton name preds inSorts outSort post = Monotype $ uncurry 0 inSorts
//   where
//     uncurry n (x:xs) = FunctionT (fromMaybe ("arg" ++ show n) (fst x)) (ScalarT (toType (snd x)) ftrue) (uncurry (n + 1) xs)
//     uncurry _ [] = ScalarT outType post
//     toType s = case s of
//       (DataS name args) -> DatatypeT name (map fromSort args) pforms
//       _ -> (baseTypeOf . fromSort) s
//     outType = (baseTypeOf . fromSort) outSort
//     pforms = fmap predform preds
//     predform x = Pred AnyS x []

/// Generate non-polymorphic core of schema
pub fn gen_skeleton(
    name: &Id,
    preds: Vec<Id>,
    in_sorts: &[(Option<Id>, Sort)],
    out_sort: &Sort,
    post: Formula,
) -> SchemaSkeleton<Formula> {
    let out_type = TypeSkeleton::from_sort(out_sort).base_type().clone();
    let p_forms = preds
        .into_iter()
        .map(|p| Formula::Pred(Sort::Any, p, Vec::new()))
        .collect();

    SchemaSkeleton::Monotype(uncurry(0, in_sorts, out_type, post, p_forms))
}

fn uncurry(
    n: usize,
    xs: &[(Option<Id>, Sort)],
    out_type: BaseType<Formula>,
    post: Formula,
    p_forms: Vec<Formula>,
) -> TypeSkeleton<Formula> {
    if let Some((x, s)) = xs.first() {
        let x = x
            .clone()
            .unwrap_or_else(|| Id::Local(format!("arg{n}").into_boxed_str()));

        TypeSkeleton::Function {
            x,
            t_arg: Box::new(TypeSkeleton::Scalar(
                to_type(s, p_forms.clone()),
                Formula::TRUE,
            )),
            t_res: Box::new(uncurry(n + 1, &xs[1..], out_type, post, p_forms)),
        }
    } else {
        TypeSkeleton::Scalar(out_type, post)
    }
}

fn to_type(s: &Sort, p_forms: Vec<Formula>) -> BaseType<Formula> {
    match s {
        Sort::Data(name, args) => {
            let args = args.iter().map(TypeSkeleton::from_sort).collect();

            BaseType::Datatype(name.clone(), args, p_forms)
        }
        _ => TypeSkeleton::from_sort(s).base_type().clone(),
    }
}

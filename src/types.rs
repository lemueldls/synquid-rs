//! Refinement types (mirror of `Synquid.Type`).

use std::collections::BTreeMap;

use crate::{
    logic::{
        DONT_CARE, Formula, PredSig, Sort, Substitution, VALUE_VAR_NAME, and_clean, ftrue,
        sort_substitute_fml, substitute, substitute_predicate, val_int, vars_of,
    },
    util::Id,
};

/// Type skeletons (parametrized by refinements).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BaseType<R> {
    BoolT,
    IntT,
    DatatypeT(Id, Vec<TypeSkeleton<R>>, Vec<R>),
    /// A type variable with a pending (formula) substitution.
    TypeVarT(Substitution, Id),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeSkeleton<R> {
    ScalarT(BaseType<R>, R),
    FunctionT(Id, Box<TypeSkeleton<R>>, Box<TypeSkeleton<R>>),
    LetT(Id, Box<TypeSkeleton<R>>, Box<TypeSkeleton<R>>),
    AnyT,
}

pub fn contextual<R: Clone>(x: Id, t_def: TypeSkeleton<R>, t: &TypeSkeleton<R>) -> TypeSkeleton<R> {
    match t {
        TypeSkeleton::FunctionT(y, t_arg, t_res) => {
            TypeSkeleton::FunctionT(
                y.clone(),
                Box::new(contextual(x.clone(), t_def.clone(), t_arg)),
                Box::new(contextual(x, t_def, t_res)),
            )
        }
        TypeSkeleton::AnyT => TypeSkeleton::AnyT,
        _ => TypeSkeleton::LetT(x, Box::new(t_def), Box::new(t.clone())),
    }
}

pub const fn is_scalar_type<R>(t: &TypeSkeleton<R>) -> bool {
    matches!(t, TypeSkeleton::ScalarT(_, _) | TypeSkeleton::LetT(_, _, _))
}

pub fn base_type_of<R: Clone>(t: &TypeSkeleton<R>) -> BaseType<R> {
    match t {
        TypeSkeleton::ScalarT(base_t, _) => (*base_t).clone(),
        TypeSkeleton::LetT(_, _, t) => base_type_of(t),
        _ => panic!("baseTypeOf: applied to a function type"),
    }
}

pub const fn is_function_type<R>(t: &TypeSkeleton<R>) -> bool {
    matches!(t, TypeSkeleton::FunctionT(_, _, _))
}

pub fn arg_type<R: Clone>(t: &TypeSkeleton<R>) -> TypeSkeleton<R> {
    match t {
        TypeSkeleton::FunctionT(_, t, _) => (**t).clone(),
        _ => panic!("argType: not a function type"),
    }
}

pub fn res_type<R: Clone>(t: &TypeSkeleton<R>) -> TypeSkeleton<R> {
    match t {
        TypeSkeleton::FunctionT(_, _, t) => (**t).clone(),
        _ => panic!("resType: not a function type"),
    }
}

pub fn has_any<R>(t: &TypeSkeleton<R>) -> bool {
    match t {
        TypeSkeleton::AnyT => true,
        TypeSkeleton::ScalarT(base_t, _) => {
            match base_t {
                BaseType::DatatypeT(_, t_args, _) => t_args.iter().any(has_any),
                _ => false,
            }
        }
        TypeSkeleton::FunctionT(_, t_arg, t_res) => has_any(t_arg) || has_any(t_res),
        TypeSkeleton::LetT(_, t_def, t_body) => has_any(t_def) || has_any(t_body),
    }
}

/// Convention to indicate "any datatype" (for synthesizing match scrutinees).
#[must_use]
pub fn any_datatype() -> TypeSkeleton<Formula> {
    TypeSkeleton::ScalarT(
        BaseType::DatatypeT(DONT_CARE.to_string(), vec![], vec![]),
        ftrue(),
    )
}

#[must_use]
pub fn to_sort<R: Clone>(base_t: &BaseType<R>) -> Sort {
    match base_t {
        BaseType::BoolT => Sort::BoolS,
        BaseType::IntT => Sort::IntS,
        BaseType::DatatypeT(name, t_args, _) => {
            Sort::DataS(
                name.clone(),
                t_args.iter().map(|a| to_sort(&base_type_of(a))).collect(),
            )
        }
        BaseType::TypeVarT(_, name) => Sort::VarS(name.clone()),
    }
}

#[must_use]
pub fn from_sort(s: &Sort) -> TypeSkeleton<Formula> {
    refine_sort(s, ftrue())
}

pub fn refine_sort(s: &Sort, f: Formula) -> TypeSkeleton<Formula> {
    match s {
        Sort::BoolS => TypeSkeleton::ScalarT(BaseType::BoolT, f),
        Sort::IntS => TypeSkeleton::ScalarT(BaseType::IntT, f),
        Sort::VarS(name) => {
            TypeSkeleton::ScalarT(BaseType::TypeVarT(Substitution::new(), name.clone()), f)
        }
        Sort::DataS(name, s_args) => {
            TypeSkeleton::ScalarT(
                BaseType::DatatypeT(name.clone(), s_args.iter().map(from_sort).collect(), vec![]),
                f,
            )
        }
        Sort::SetS(s) => {
            TypeSkeleton::ScalarT(
                BaseType::DatatypeT(SET_TYPE_NAME.to_string(), vec![from_sort(s)], vec![]),
                f,
            )
        }
        Sort::AnyS => TypeSkeleton::AnyT,
    }
}

pub const fn type_is_data<R>(t: &TypeSkeleton<R>) -> bool {
    matches!(t, TypeSkeleton::ScalarT(BaseType::DatatypeT(_, _, _), _))
}

pub fn arity<R>(t: &TypeSkeleton<R>) -> usize {
    match t {
        TypeSkeleton::FunctionT(_, _, t) => 1 + arity(t),
        TypeSkeleton::LetT(_, _, t) => arity(t),
        _ => 0,
    }
}

pub fn has_set<R>(t: &TypeSkeleton<R>) -> bool {
    match t {
        TypeSkeleton::ScalarT(BaseType::DatatypeT(name, ..), _) => name == SET_TYPE_NAME,
        TypeSkeleton::FunctionT(_, t1, t2) => has_set(t1) || has_set(t2),
        TypeSkeleton::LetT(_, t1, t2) => has_set(t1) || has_set(t2),
        _ => false,
    }
}

pub fn last_type<R: Clone>(t: &TypeSkeleton<R>) -> TypeSkeleton<R> {
    match t {
        TypeSkeleton::FunctionT(_, _, t_res) => last_type(t_res),
        TypeSkeleton::LetT(_, _, t) => last_type(t),
        t => t.clone(),
    }
}

pub fn all_arg_types<R: Clone>(t: &TypeSkeleton<R>) -> Vec<TypeSkeleton<R>> {
    match t {
        TypeSkeleton::FunctionT(_, t_arg, t_res) => {
            let mut res = vec![(**t_arg).clone()];
            res.extend(all_arg_types(t_res));
            res
        }
        TypeSkeleton::LetT(_, _, t) => all_arg_types(t),
        _ => vec![],
    }
}

pub fn all_args<R: Clone>(t: &TypeSkeleton<R>) -> Vec<Formula> {
    match t {
        TypeSkeleton::ScalarT(..) => vec![],
        TypeSkeleton::FunctionT(x, t_arg, t_res) => {
            if let TypeSkeleton::ScalarT(base_t, _) = &**t_arg {
                let mut res = vec![Formula::Var(Box::new(to_sort(base_t)), x.clone())];
                res.extend(all_args(t_res));
                res
            } else {
                all_args(t_res)
            }
        }
        TypeSkeleton::LetT(_, _, t) => all_args(t),
        TypeSkeleton::AnyT => panic!("all_args: any type"),
    }
}

/// Free input variables of a refined type.
#[must_use]
pub fn vars_of_type(t: &TypeSkeleton<Formula>) -> std::collections::BTreeSet<Id> {
    match t {
        TypeSkeleton::ScalarT(base_t, fml) => {
            let mut acc = vars_of_base(base_t);
            acc.extend(
                vars_of(fml)
                    .iter()
                    .map(|v| crate::logic::var_name(v).clone()),
            );
            acc
        }
        TypeSkeleton::FunctionT(x, t_arg, t_res) => {
            let mut acc = vars_of_type(t_arg);
            let mut res_vars = vars_of_type(t_res);
            res_vars.remove(x);
            acc.extend(res_vars);
            acc
        }
        TypeSkeleton::LetT(x, t_def, t_body) => {
            let mut acc = vars_of_type(t_def);
            let mut body_vars = vars_of_type(t_body);
            body_vars.remove(x);
            acc.extend(body_vars);
            acc
        }
        TypeSkeleton::AnyT => std::collections::BTreeSet::new(),
    }
}

fn vars_of_base(base_t: &BaseType<Formula>) -> std::collections::BTreeSet<Id> {
    match base_t {
        BaseType::DatatypeT(_, t_args, p_args) => {
            let mut acc: std::collections::BTreeSet<Id> =
                t_args.iter().flat_map(vars_of_type).collect();
            for p in p_args {
                acc.extend(vars_of(p).iter().map(|v| crate::logic::var_name(v).clone()));
            }
            acc
        }
        _ => std::collections::BTreeSet::new(),
    }
}

/// Free predicate identifiers of a refined type.
#[must_use]
pub fn preds_of_type(t: &TypeSkeleton<Formula>) -> std::collections::BTreeSet<Id> {
    match t {
        TypeSkeleton::ScalarT(base_t, fml) => {
            let mut acc = preds_of_base(base_t);
            acc.extend(crate::logic::preds_of(fml));
            acc
        }
        TypeSkeleton::FunctionT(_, t_arg, t_res) => {
            let mut acc = preds_of_type(t_arg);
            acc.extend(preds_of_type(t_res));
            acc
        }
        TypeSkeleton::LetT(_, t_def, t_body) => {
            let mut acc = preds_of_type(t_def);
            acc.extend(preds_of_type(t_body));
            acc
        }
        TypeSkeleton::AnyT => std::collections::BTreeSet::new(),
    }
}

fn preds_of_base(base_t: &BaseType<Formula>) -> std::collections::BTreeSet<Id> {
    match base_t {
        BaseType::DatatypeT(_, t_args, p_args) => {
            let mut acc: std::collections::BTreeSet<Id> =
                t_args.iter().flat_map(preds_of_type).collect();
            for p in p_args {
                acc.extend(crate::logic::preds_of(p));
            }
            acc
        }
        _ => std::collections::BTreeSet::new(),
    }
}

#[must_use]
pub fn var_refinement(x: &str, s: &Sort) -> Formula {
    eq_var(
        Formula::Var(Box::new(s.clone()), VALUE_VAR_NAME.to_string()),
        Formula::Var(Box::new(s.clone()), x.to_string()),
    )
}

fn eq_var(l: Formula, r: Formula) -> Formula {
    crate::logic::eq(l, r)
}

#[must_use]
pub fn is_var_refinement(fml: &Formula) -> bool {
    matches!(fml, Formula::Binary(crate::logic::BinOp::Eq, l, _)
        if matches!(&**l, Formula::Var(_, v) if v == VALUE_VAR_NAME))
}

/// Polymorphic type skeletons (parametrized by refinements).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SchemaSkeleton<R> {
    Monotype(TypeSkeleton<R>),
    /// Type-polymorphic.
    ForallT(Id, Box<SchemaSkeleton<R>>),
    /// Predicate-polymorphic.
    ForallP(PredSig, Box<SchemaSkeleton<R>>),
}

pub fn to_monotype<R: Clone>(sch: &SchemaSkeleton<R>) -> TypeSkeleton<R> {
    match sch {
        SchemaSkeleton::Monotype(t) => t.clone(),
        SchemaSkeleton::ForallT(_, t) => to_monotype(t),
        SchemaSkeleton::ForallP(_, t) => to_monotype(t),
    }
}

pub fn bound_vars_of<R>(sch: &SchemaSkeleton<R>) -> Vec<Id> {
    match sch {
        SchemaSkeleton::ForallT(a, sch) => {
            let mut res = vec![a.clone()];
            res.extend(bound_vars_of(sch));
            res
        }
        _ => vec![],
    }
}

/// Building types.
pub const fn bool<R>(f: R) -> TypeSkeleton<R> {
    TypeSkeleton::ScalarT(BaseType::BoolT, f)
}
#[must_use]
pub const fn bool_() -> TypeSkeleton<()> {
    bool(())
}
#[must_use]
pub const fn bool_all() -> TypeSkeleton<Formula> {
    bool(ftrue())
}

pub const fn int<R>(f: R) -> TypeSkeleton<R> {
    TypeSkeleton::ScalarT(BaseType::IntT, f)
}
#[must_use]
pub const fn int_() -> TypeSkeleton<()> {
    int(())
}
#[must_use]
pub const fn int_all() -> TypeSkeleton<Formula> {
    int(ftrue())
}

#[must_use]
pub fn nat() -> TypeSkeleton<Formula> {
    int(crate::logic::ge(val_int(), crate::logic::int_lit(0)))
}
#[must_use]
pub fn pos() -> TypeSkeleton<Formula> {
    int(crate::logic::gt(val_int(), crate::logic::int_lit(0)))
}

#[must_use]
pub fn vart_(n: &str) -> TypeSkeleton<()> {
    TypeSkeleton::ScalarT(BaseType::TypeVarT(Substitution::new(), n.to_string()), ())
}
#[must_use]
pub fn vart_all(n: &str) -> TypeSkeleton<Formula> {
    TypeSkeleton::ScalarT(
        BaseType::TypeVarT(Substitution::new(), n.to_string()),
        ftrue(),
    )
}

#[must_use]
pub fn set_(n: &str) -> TypeSkeleton<()> {
    TypeSkeleton::ScalarT(
        BaseType::DatatypeT(SET_TYPE_NAME.to_string(), vec![vart_(n)], vec![]),
        (),
    )
}
#[must_use]
pub fn set_all(n: &str) -> TypeSkeleton<Formula> {
    TypeSkeleton::ScalarT(
        BaseType::DatatypeT(SET_TYPE_NAME.to_string(), vec![vart_all(n)], vec![]),
        ftrue(),
    )
}

/// Mapping from type variables to types.
pub type TypeSubstitution = BTreeMap<Id, TypeSkeleton<Formula>>;

#[must_use]
pub fn as_sort_subst(subst: &TypeSubstitution) -> crate::logic::SortSubstitution {
    subst
        .iter()
        .map(|(k, v)| (k.clone(), to_sort(&base_type_of(v))))
        .collect()
}

/// Substitute all free type variables in `t`.
#[must_use]
pub fn type_substitute(
    subst: &TypeSubstitution,
    t: &TypeSkeleton<Formula>,
) -> TypeSkeleton<Formula> {
    match t {
        TypeSkeleton::ScalarT(base_t, r) => {
            let substitute_base = match base_t {
                BaseType::TypeVarT(var_subst, a) => {
                    match subst.get(a) {
                        Some(t) => {
                            let is_bound = |_: &Id| false;
                            substitute_in_type(&is_bound, var_subst, &type_substitute(subst, t))
                        }
                        None => {
                            TypeSkeleton::ScalarT(
                                BaseType::TypeVarT(var_subst.clone(), a.clone()),
                                ftrue(),
                            )
                        }
                    }
                }
                BaseType::DatatypeT(name, t_args, p_args) => {
                    TypeSkeleton::ScalarT(
                        BaseType::DatatypeT(
                            name.clone(),
                            t_args.iter().map(|a| type_substitute(subst, a)).collect(),
                            p_args
                                .iter()
                                .map(|p| sort_substitute_fml(&as_sort_subst(subst), p))
                                .collect(),
                        ),
                        ftrue(),
                    )
                }
                _ => TypeSkeleton::ScalarT(base_t.clone(), ftrue()),
            };
            add_refinement(
                substitute_base,
                &sort_substitute_fml(&as_sort_subst(subst), r),
            )
        }
        TypeSkeleton::FunctionT(x, t_arg, t_res) => {
            TypeSkeleton::FunctionT(
                x.clone(),
                Box::new(type_substitute(subst, t_arg)),
                Box::new(type_substitute(subst, t_res)),
            )
        }
        TypeSkeleton::LetT(x, t_def, t_body) => {
            TypeSkeleton::LetT(
                x.clone(),
                Box::new(type_substitute(subst, t_def)),
                Box::new(type_substitute(subst, t_body)),
            )
        }
        TypeSkeleton::AnyT => TypeSkeleton::AnyT,
    }
}

#[must_use]
pub fn noncapture_type_subst(
    t_vars: &[Id],
    t_args: &[TypeSkeleton<Formula>],
    t: &TypeSkeleton<Formula>,
) -> TypeSkeleton<Formula> {
    let distinct = crate::logic::distinct_type_vars(t_vars.len());
    let subst1: TypeSubstitution = t_vars
        .iter()
        .zip(distinct.iter())
        .map(|(v, d)| (v.clone(), vart_all(d)))
        .collect();
    let t_fresh = type_substitute(&subst1, t);
    let subst2: TypeSubstitution = distinct
        .iter()
        .zip(t_args.iter())
        .map(|(d, a)| (d.clone(), a.clone()))
        .collect();
    type_substitute(&subst2, &t_fresh)
}

#[must_use]
pub fn schema_substitute(
    tass: &TypeSubstitution,
    sch: &SchemaSkeleton<Formula>,
) -> SchemaSkeleton<Formula> {
    match sch {
        SchemaSkeleton::Monotype(t) => SchemaSkeleton::Monotype(type_substitute(tass, t)),
        SchemaSkeleton::ForallT(a, sch) => {
            let mut tass2 = tass.clone();
            tass2.remove(a);
            SchemaSkeleton::ForallT(a.clone(), Box::new(schema_substitute(&tass2, sch)))
        }
        SchemaSkeleton::ForallP(sig, sch) => {
            SchemaSkeleton::ForallP(sig.clone(), Box::new(schema_substitute(tass, sch)))
        }
    }
}

#[must_use]
pub fn type_substitute_pred(
    p_subst: &Substitution,
    t: &TypeSkeleton<Formula>,
) -> TypeSkeleton<Formula> {
    match t {
        TypeSkeleton::ScalarT(BaseType::DatatypeT(name, t_args, p_args), fml) => {
            TypeSkeleton::ScalarT(
                BaseType::DatatypeT(
                    name.clone(),
                    t_args
                        .iter()
                        .map(|a| type_substitute_pred(p_subst, a))
                        .collect(),
                    p_args
                        .iter()
                        .map(|p| substitute_predicate(p_subst, p))
                        .collect(),
                ),
                substitute_predicate(p_subst, fml),
            )
        }
        TypeSkeleton::ScalarT(base_t, fml) => {
            TypeSkeleton::ScalarT(base_t.clone(), substitute_predicate(p_subst, fml))
        }
        TypeSkeleton::FunctionT(x, t_arg, t_res) => {
            TypeSkeleton::FunctionT(
                x.clone(),
                Box::new(type_substitute_pred(p_subst, t_arg)),
                Box::new(type_substitute_pred(p_subst, t_res)),
            )
        }
        TypeSkeleton::LetT(x, t_def, t_body) => {
            TypeSkeleton::FunctionT(
                x.clone(),
                Box::new(type_substitute_pred(p_subst, t_def)),
                Box::new(type_substitute_pred(p_subst, t_body)),
            )
        }
        TypeSkeleton::AnyT => TypeSkeleton::AnyT,
    }
}

/// All type variables in a type skeleton.
pub fn type_vars_of<R>(t: &TypeSkeleton<R>) -> std::collections::BTreeSet<Id> {
    match t {
        TypeSkeleton::ScalarT(base_t, _) => {
            match base_t {
                BaseType::TypeVarT(_, name) => std::collections::BTreeSet::from([name.clone()]),
                BaseType::DatatypeT(_, t_args, _) => {
                    let mut acc = std::collections::BTreeSet::new();
                    for a in t_args {
                        acc.extend(type_vars_of(a));
                    }
                    acc
                }
                _ => std::collections::BTreeSet::new(),
            }
        }
        TypeSkeleton::FunctionT(_, t_arg, t_res) => {
            let mut acc = type_vars_of(t_arg);
            acc.extend(type_vars_of(t_res));
            acc
        }
        TypeSkeleton::LetT(_, t_def, t_body) => {
            let mut acc = type_vars_of(t_def);
            acc.extend(type_vars_of(t_body));
            acc
        }
        TypeSkeleton::AnyT => std::collections::BTreeSet::new(),
    }
}

/// Unrefined types.
pub type SType = TypeSkeleton<()>;
/// Refined types.
pub type RType = TypeSkeleton<Formula>;
/// Unrefined schemas.
pub type SSchema = SchemaSkeleton<()>;
/// Refined schemas.
pub type RSchema = SchemaSkeleton<Formula>;

/// Forget refinements of a type.
pub fn shape(t: &RType) -> SType {
    match t {
        TypeSkeleton::ScalarT(BaseType::DatatypeT(name, t_args, p_args), _) => {
            TypeSkeleton::ScalarT(
                BaseType::DatatypeT(name.clone(), t_args.iter().map(shape).collect(), vec![
                    ();
                    p_args
                        .len(
                        )
                ]),
                (),
            )
        }
        TypeSkeleton::ScalarT(BaseType::IntT, _) => TypeSkeleton::ScalarT(BaseType::IntT, ()),
        TypeSkeleton::ScalarT(BaseType::BoolT, _) => TypeSkeleton::ScalarT(BaseType::BoolT, ()),
        TypeSkeleton::ScalarT(BaseType::TypeVarT(_, a), _) => {
            TypeSkeleton::ScalarT(BaseType::TypeVarT(Substitution::new(), a.clone()), ())
        }
        TypeSkeleton::FunctionT(x, t_arg, t_fun) => {
            TypeSkeleton::FunctionT(x.clone(), Box::new(shape(t_arg)), Box::new(shape(t_fun)))
        }
        TypeSkeleton::LetT(_, _, t) => shape(t),
        TypeSkeleton::AnyT => TypeSkeleton::AnyT,
    }
}

/// Conjoin a refinement to a type.
#[must_use]
pub fn add_refinement(t: TypeSkeleton<Formula>, fml: &Formula) -> TypeSkeleton<Formula> {
    match t {
        TypeSkeleton::ScalarT(base, fml_old) => {
            if is_var_refinement(fml) {
                TypeSkeleton::ScalarT(base, fml.clone())
            } else {
                TypeSkeleton::ScalarT(base, and_clean(fml_old, fml.clone()))
            }
        }
        TypeSkeleton::LetT(x, t_def, t_body) => {
            TypeSkeleton::LetT(x, t_def, Box::new(add_refinement(*t_body, fml)))
        }
        TypeSkeleton::AnyT => TypeSkeleton::AnyT,
        t => {
            if *fml == crate::logic::ftrue() {
                t
            } else {
                panic!("addRefinement: applied to function type")
            }
        }
    }
}

/// Conjoin a refinement to the return type.
#[must_use]
pub fn add_refinement_to_last(t: TypeSkeleton<Formula>, fml: Formula) -> TypeSkeleton<Formula> {
    match t {
        t @ TypeSkeleton::ScalarT(..) => add_refinement(t, &fml),
        TypeSkeleton::FunctionT(x, t_arg, t_res) => {
            TypeSkeleton::FunctionT(x, t_arg, Box::new(add_refinement_to_last(*t_res, fml)))
        }
        TypeSkeleton::LetT(x, t_def, t_body) => {
            TypeSkeleton::LetT(x, t_def, Box::new(add_refinement_to_last(*t_body, fml)))
        }
        TypeSkeleton::AnyT => panic!("add_refinement_to_last: any type"),
    }
}

/// Conjoin a refinement to the return type inside a schema.
#[must_use]
pub fn add_refinement_to_last_sch(
    sch: &SchemaSkeleton<Formula>,
    fml: Formula,
) -> SchemaSkeleton<Formula> {
    match sch {
        SchemaSkeleton::Monotype(t) => {
            SchemaSkeleton::Monotype(add_refinement_to_last(t.clone(), fml))
        }
        SchemaSkeleton::ForallT(a, sch) => {
            SchemaSkeleton::ForallT(a.clone(), Box::new(add_refinement_to_last_sch(sch, fml)))
        }
        SchemaSkeleton::ForallP(sig, sch) => {
            SchemaSkeleton::ForallP(sig.clone(), Box::new(add_refinement_to_last_sch(sch, fml)))
        }
    }
}

/// Apply a variable substitution in all formulas inside a type.
pub fn substitute_in_type(
    _is_bound: &impl Fn(&Id) -> bool,
    subst: &Substitution,
    t: &TypeSkeleton<Formula>,
) -> TypeSkeleton<Formula> {
    match t {
        TypeSkeleton::ScalarT(base_t, fml) => {
            let substitute_base = match base_t {
                BaseType::TypeVarT(old_subst, a) => {
                    BaseType::TypeVarT(old_subst.clone(), a.clone())
                }
                BaseType::DatatypeT(name, t_args, p_args) => {
                    BaseType::DatatypeT(
                        name.clone(),
                        t_args
                            .iter()
                            .map(|a| substitute_in_type(_is_bound, subst, a))
                            .collect(),
                        p_args
                            .iter()
                            .map(|p| substitute(subst, p.clone()))
                            .collect(),
                    )
                }
                base_t => base_t.clone(),
            };
            TypeSkeleton::ScalarT(substitute_base, substitute(subst, fml.clone()))
        }
        TypeSkeleton::FunctionT(x, t_arg, t_res) => {
            assert!(
                !subst.contains_key(x),
                "Attempt to substitute variable {x} bound in a function type"
            );
            TypeSkeleton::FunctionT(
                x.clone(),
                Box::new(substitute_in_type(_is_bound, subst, t_arg)),
                Box::new(substitute_in_type(_is_bound, subst, t_res)),
            )
        }
        TypeSkeleton::LetT(x, t_def, t_body) => {
            assert!(
                !subst.contains_key(x),
                "Attempt to substitute variable {x} bound in a contextual type"
            );
            TypeSkeleton::LetT(
                x.clone(),
                Box::new(substitute_in_type(_is_bound, subst, t_def)),
                Box::new(substitute_in_type(_is_bound, subst, t_body)),
            )
        }
        TypeSkeleton::AnyT => TypeSkeleton::AnyT,
    }
}

/// Rename all occurrences of `old` into `new` (of type `t`) in `typ`.
pub fn rename_var(
    is_bound: &impl Fn(&Id) -> bool,
    old: &Id,
    new: &Id,
    source: &TypeSkeleton<Formula>,
    t: &TypeSkeleton<Formula>,
) -> TypeSkeleton<Formula> {
    match source {
        TypeSkeleton::ScalarT(b, _) => {
            let mut subst = Substitution::new();
            subst.insert(old.clone(), Formula::Var(Box::new(to_sort(b)), new.clone()));
            substitute_in_type(is_bound, &subst, t)
        }
        TypeSkeleton::LetT(_, _, t_body) => rename_var(is_bound, old, new, t_body, t),
        _ => t.clone(),
    }
}

/// Intersection of two types (assuming the types were already checked for
/// consistency).
pub fn intersection(
    is_bound: &impl Fn(&Id) -> bool,
    t: &TypeSkeleton<Formula>,
    t2: &TypeSkeleton<Formula>,
) -> TypeSkeleton<Formula> {
    match t2 {
        TypeSkeleton::AnyT => t.clone(),
        _ => {
            match t {
                TypeSkeleton::AnyT => t2.clone(),
                TypeSkeleton::ScalarT(base_t, fml) => {
                    match t2 {
                        TypeSkeleton::ScalarT(base_t2, fml2) => {
                            match base_t {
                                BaseType::DatatypeT(name, t_args, p_args) => {
                                    let BaseType::DatatypeT(_, t_args2, p_args2) = base_t2 else {
                                        panic!("intersection: inconsistent datatype bases");
                                    };
                                    TypeSkeleton::ScalarT(
                                        BaseType::DatatypeT(
                                            name.clone(),
                                            t_args
                                                .iter()
                                                .zip(t_args2)
                                                .map(|(a, b)| intersection(is_bound, a, b))
                                                .collect(),
                                            p_args
                                                .iter()
                                                .zip(p_args2)
                                                .map(|(a, b)| and_clean(a.clone(), b.clone()))
                                                .collect(),
                                        ),
                                        and_clean(fml.clone(), fml2.clone()),
                                    )
                                }
                                _ => {
                                    TypeSkeleton::ScalarT(
                                        base_t.clone(),
                                        and_clean(fml.clone(), fml2.clone()),
                                    )
                                }
                            }
                        }
                        _ => panic!("intersection: inconsistent type skeletons"),
                    }
                }
                TypeSkeleton::FunctionT(x, t_arg, t_res) => {
                    match t2 {
                        TypeSkeleton::FunctionT(y, t_arg2, t_res2) => {
                            TypeSkeleton::FunctionT(
                                x.clone(),
                                t_arg.clone(),
                                Box::new(intersection(
                                    is_bound,
                                    t_res,
                                    &rename_var(is_bound, y, x, t_arg2, t_res2),
                                )),
                            )
                        }
                        _ => panic!("intersection: inconsistent type skeletons"),
                    }
                }
                TypeSkeleton::LetT(..) => panic!("intersection: contextual type"),
            }
        }
    }
}

/// Instantiate unknowns in a type.
#[must_use]
pub fn type_apply_solution(
    sol: &crate::logic::Solution,
    t: &TypeSkeleton<Formula>,
) -> TypeSkeleton<Formula> {
    match t {
        TypeSkeleton::ScalarT(BaseType::DatatypeT(name, t_args, p_args), fml) => {
            TypeSkeleton::ScalarT(
                BaseType::DatatypeT(
                    name.clone(),
                    t_args.iter().map(|a| type_apply_solution(sol, a)).collect(),
                    p_args
                        .iter()
                        .map(|p| crate::logic::apply_solution(sol, p))
                        .collect(),
                ),
                crate::logic::apply_solution(sol, fml),
            )
        }
        TypeSkeleton::ScalarT(base, fml) => {
            TypeSkeleton::ScalarT(base.clone(), crate::logic::apply_solution(sol, fml))
        }
        TypeSkeleton::FunctionT(x, t_arg, t_res) => {
            TypeSkeleton::FunctionT(
                x.clone(),
                Box::new(type_apply_solution(sol, t_arg)),
                Box::new(type_apply_solution(sol, t_res)),
            )
        }
        TypeSkeleton::LetT(x, t_def, t_body) => {
            TypeSkeleton::LetT(
                x.clone(),
                Box::new(type_apply_solution(sol, t_def)),
                Box::new(type_apply_solution(sol, t_body)),
            )
        }
        TypeSkeleton::AnyT => TypeSkeleton::AnyT,
    }
}

#[must_use]
pub fn type_from_schema(sch: &SchemaSkeleton<Formula>) -> TypeSkeleton<Formula> {
    match sch {
        SchemaSkeleton::Monotype(t) => t.clone(),
        SchemaSkeleton::ForallT(_, t) => type_from_schema(t),
        SchemaSkeleton::ForallP(_, t) => type_from_schema(t),
    }
}

#[must_use]
pub fn all_refinements_of(sch: &SchemaSkeleton<Formula>) -> Vec<Formula> {
    all_refinements_of_inner(&type_from_schema(sch))
}

fn all_refinements_of_inner(t: &TypeSkeleton<Formula>) -> Vec<Formula> {
    match t {
        TypeSkeleton::ScalarT(_, refn) => vec![refn.clone()],
        TypeSkeleton::FunctionT(_, arg_t, res_t) => {
            let mut acc = all_refinements_of_inner(arg_t);
            acc.extend(all_refinements_of_inner(res_t));
            acc
        }
        _ => panic!("allRefinementsOf called on contextual or any type"),
    }
}

/// Set strings: used for the "fake" set type for typechecking measures.
pub const EMPTY_SET_CTOR: &str = "Emptyset";
pub const SINGLETON_CTOR: &str = "Singleton";
pub const INSERT_SET_CTOR: &str = "Insert";
pub const SET_TYPE_NAME: &str = "DSet";
pub const SET_TYPE_VAR: &str = "setTypeVar";
pub const SET_CONSTRUCTORS: [&str; 3] = [EMPTY_SET_CTOR, SINGLETON_CTOR, INSERT_SET_CTOR];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::logic::val_bool;

    #[test]
    fn test_arity() {
        let t = TypeSkeleton::FunctionT("x".to_string(), Box::new(int_all()), Box::new(int_all()));
        assert_eq!(arity(&t), 1);
        let t2 = TypeSkeleton::FunctionT(
            "x".to_string(),
            Box::new(int_all()),
            Box::new(TypeSkeleton::FunctionT(
                "y".to_string(),
                Box::new(int_all()),
                Box::new(int_all()),
            )),
        );
        assert_eq!(arity(&t2), 2);
        assert_eq!(arity(&int_all()), 0);
    }

    #[test]
    fn test_add_refinement() {
        let t = int_all();
        let r = add_refinement(t, &crate::logic::ftrue());
        assert_eq!(r, int_all());
    }

    #[test]
    fn test_shape() {
        let t = TypeSkeleton::FunctionT(
            "x".to_string(),
            Box::new(int_all()),
            Box::new(TypeSkeleton::ScalarT(BaseType::BoolT, val_bool())),
        );
        let s = shape(&t);
        assert_eq!(
            s,
            TypeSkeleton::FunctionT("x".to_string(), Box::new(int_()), Box::new(bool_()))
        );
    }

    #[test]
    fn test_type_vars_of() {
        let t = vart_all("a");
        let tv = type_vars_of(&t);
        assert_eq!(tv.len(), 1);
        assert!(tv.contains("a"));
    }

    #[test]
    fn test_intersection() {
        let is_bound = |_: &Id| false;
        let val = crate::logic::val_int();
        let t1 = TypeSkeleton::ScalarT(
            BaseType::DatatypeT("List".to_string(), vec![], vec![]),
            crate::logic::eq(val.clone(), crate::logic::int_lit(0)),
        );
        let t2 = TypeSkeleton::ScalarT(
            BaseType::DatatypeT("List".to_string(), vec![], vec![]),
            crate::logic::le(val, crate::logic::int_lit(1)),
        );
        let r = intersection(&is_bound, &t1, &t2);
        assert!(matches!(r, TypeSkeleton::ScalarT(BaseType::DatatypeT(n, _, _), _) if n == "List"));
    }
}

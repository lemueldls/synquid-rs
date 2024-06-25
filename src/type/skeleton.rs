use core::fmt;
use std::{
    collections::{BTreeMap, BTreeSet},
    hash::{self, Hash},
};

use hashbrown::HashSet;
use num_bigint::BigInt;
use owo_colors::OwoColorize;

use super::{base, BaseType, Nothing, RSchema};
use crate::{
    logic::{
        compose_substitutions, BinOp, Formula, Solution, Sort, Substitution, DONT_CARE,
        SET_TYPE_NAME, VALUE_VAR_NAME,
    },
    program::{BareProgram, Program, UProgram},
    util::Id,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum TypeSkeleton<R: fmt::Display + Clone + Eq + Hash> {
    Scalar(BaseType<R>, R),
    Function {
        x: Id,
        t_arg: Box<TypeSkeleton<R>>,
        t_res: Box<TypeSkeleton<R>>,
    },
    // Gen
    Let(Id, Box<TypeSkeleton<R>>, Box<TypeSkeleton<R>>),
    Any,
}

impl<R: fmt::Display + Clone + Eq + Hash> TypeSkeleton<R> {
    pub const fn bool(x: R) -> Self {
        Self::Scalar(BaseType::Bool, x)
    }

    pub const fn int(x: R) -> Self {
        Self::Scalar(BaseType::Int, x)
    }

    pub fn contextual(self, x: Id, to_def: TypeSkeleton<R>) -> Self {
        match self {
            Self::Function { x: y, t_arg, t_res } => {
                Self::Function {
                    x: y,
                    // REVIEW: Test if [`TypeSkeleton<R>`] and [`BaseType<R>`] are safe to clone
                    t_arg: Box::new(t_arg.contextual(x.clone(), to_def.clone())),
                    t_res: Box::new(t_res.contextual(x, to_def)),
                }
            }
            Self::Any => Self::Any,
            t => Self::Let(x, Box::new(to_def), Box::new(t)),
        }
    }

    pub fn is_scalar_type(&self) -> bool {
        matches!(self, Self::Scalar(_, _) | Self::Let(_, _, _))
    }

    #[doc(alias = "base_type_of")]
    pub fn base_type(&self) -> &BaseType<R> {
        match self {
            Self::Scalar(base_t, _) => base_t,
            Self::Let(_, _, t) => t.base_type(),
            _ => todo!("applied to a function type"),
        }
    }

    pub fn is_function_type(&self) -> bool {
        matches!(self, Self::Function { .. })
    }

    pub fn has_any(&self) -> bool {
        match self {
            Self::Any => true,
            Self::Scalar(base_t, _) => base_t.has_any(),
            Self::Function { x: _, t_arg, t_res } => t_arg.has_any() || t_res.has_any(),
            Self::Let(_, t_def, t_body) => t_def.has_any() || t_body.has_any(),
            _ => todo!(),
        }
    }

    pub fn is_data(&self) -> bool {
        matches!(self, TypeSkeleton::Scalar(BaseType::Datatype(_, _, _), _))
    }

    pub fn arity(&self) -> usize {
        match self {
            TypeSkeleton::Function {
                x: _,
                t_arg: _,
                t_res,
            } => 1 + t_res.arity(),
            TypeSkeleton::Let(_, _, t) => t.arity(),
            _ => 0,
        }
    }

    pub fn has_set(&self) -> bool {
        match self {
            TypeSkeleton::Scalar(BaseType::Datatype(name, ..), _) => *name == SET_TYPE_NAME,
            TypeSkeleton::Function { x: y, t_arg, t_res } => t_arg.has_set() || t_res.has_set(),
            TypeSkeleton::Let(_, t1, t2) => t1.has_set() || t2.has_set(),
            // TODO: make sure the [`Any`] case is OK
            TypeSkeleton::Any => todo!(),
            _ => false,
        }
    }

    pub fn last_type(&self) -> &Self {
        match self {
            TypeSkeleton::Function {
                x: _,
                t_arg: _,
                t_res,
            } => t_res.last_type(),
            TypeSkeleton::Let(_, _, t) => t.last_type(),
            t => t,
        }
    }

    pub fn all_arg_types(&self) -> Vec<&Self> {
        match self {
            TypeSkeleton::Function { x: _, t_arg, t_res } => {
                let mut vec = t_res.all_arg_types();
                vec.push(&**t_arg);

                vec
            }
            TypeSkeleton::Let(..) => todo!(),
            _ => Vec::new(),
        }
    }

    pub fn all_args(self) -> Vec<Formula> {
        match self {
            TypeSkeleton::Scalar(..) => Vec::new(),
            TypeSkeleton::Function { x, t_arg, t_res } => match *t_arg {
                TypeSkeleton::Scalar(base_t, _) => {
                    let mut vec = t_res.all_args();
                    vec.push(Formula::Var(base_t.to_sort(), x.clone()));

                    vec
                }
                _ => t_res.all_args(),
            },
            TypeSkeleton::Let(..) => todo!(),
            TypeSkeleton::Any => todo!(),
        }
    }

    // allRefinementsOf' (ScalarT _ ref) = [ref]
    // allRefinementsOf' (FunctionT _ argT resT) = allRefinementsOf' argT ++ allRefinementsOf' resT
    // allRefinementsOf' _ = error "allRefinementsOf called on contextual or any type"

    #[doc(alias = "all_refinements_of")]
    pub fn all_refinements(&self) -> HashSet<R> {
        match self {
            Self::Scalar(_, ref r) => std::iter::once(r.clone()).collect(),
            Self::Function { x: _, t_arg, t_res } => t_arg
                .all_refinements()
                .union(&t_res.all_refinements())
                .cloned()
                .collect(),
            _ => todo!("all_refinements_of called on contextual or any type"),
        }
    }

    // -- | 'typeVarsOf' @t@ : all type variables in @t@
    // typeVarsOf :: TypeSkeleton r -> Set Id
    // typeVarsOf t@(ScalarT baseT r) = case baseT of
    //   TypeVarT _ name -> Set.singleton name
    //   DatatypeT _ tArgs _ -> Set.unions (map typeVarsOf tArgs)
    //   _ -> Set.empty
    // typeVarsOf (FunctionT _ tArg tRes) = typeVarsOf tArg `Set.union` typeVarsOf tRes
    // typeVarsOf (LetT _ tDef tBody) = typeVarsOf tDef `Set.union` typeVarsOf tBody
    // typeVarsOf _ = Set.empty

    #[doc(alias = "type_vars_of")]
    pub fn type_vars(&self) -> BTreeSet<Id> {
        match self {
            TypeSkeleton::Scalar(base_t, _) => match base_t {
                BaseType::TypeVar(_, name) => [name.clone()].iter().cloned().collect(),
                BaseType::Datatype(_, t_args, _) => t_args
                    .iter()
                    .map(|t| t.type_vars())
                    .fold(BTreeSet::new(), |acc, x| acc.union(&x).cloned().collect()),
                _ => BTreeSet::new(),
            },
            TypeSkeleton::Function { t_arg, t_res, .. } => t_arg
                .type_vars()
                .union(&t_res.type_vars())
                .cloned()
                .collect(),
            TypeSkeleton::Let(_, t_def, t_body) => t_def
                .type_vars()
                .union(&t_body.type_vars())
                .cloned()
                .collect(),
            _ => BTreeSet::new(),
        }
    }
}

impl TypeSkeleton<Nothing> {
    pub const BOOL_: Self = Self::bool(Nothing);

    pub const INT_: Self = Self::bool(Nothing);
}

impl fmt::Display for TypeSkeleton<Nothing> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeSkeleton::Scalar(base, _) => write!(f, "{base}"),
            TypeSkeleton::Function { x: _, t_arg, t_res } => {
                write!(f, "({t_arg} {} {t_res})", "->".white().dimmed(),)
            }

            TypeSkeleton::Any => write!(f, "_"),
            TypeSkeleton::Let(_, _, _) => panic!("untyped let"),
        }
    }
}

impl TypeSkeleton<Formula> {
    pub const BOOL_ALL: Self = Self::bool(Formula::TRUE);

    pub const INT_ALL: Self = Self::int(Formula::TRUE);

    pub fn nat() -> Self {
        Self::int(Formula::VAL_INT.ge(Formula::IntLit(BigInt::ZERO)))
    }
    pub fn pos() -> Self {
        Self::int(Formula::VAL_INT.gt(Formula::IntLit(BigInt::ZERO)))
    }

    // vart n = ScalarT (TypeVarT Map.empty n)
    // vart_ n = vart n ()
    // vartAll n = vart n ftrue

    pub fn vart(n: Id) -> Self {
        TypeSkeleton::Scalar(BaseType::TypeVar(Substitution::default(), n), Formula::TRUE)
    }

    pub fn vart_all(n: Id) -> Self {
        TypeSkeleton::Scalar(BaseType::TypeVar(Substitution::default(), n), Formula::TRUE)
    }

    pub fn set(n: Id, x: Formula) -> Self {
        let tvar: TypeSkeleton<Formula> = TypeSkeleton::Scalar(
            BaseType::TypeVar(Substitution::default(), n.clone()),
            Formula::TRUE,
        );
        TypeSkeleton::Scalar(BaseType::Datatype(SET_TYPE_NAME, vec![tvar], Vec::new()), x)
    }

    pub fn set_all(n: Id) -> Self {
        Self::set(n, Formula::TRUE)
    }

    pub fn any_datatype() -> Self {
        Self::Scalar(
            BaseType::Datatype(DONT_CARE, Vec::new(), Vec::new()),
            Formula::TRUE,
        )
    }

    pub fn from_sort(sort: &Sort) -> Self {
        sort.clone().refine(Formula::TRUE)
    }

    // -- | Forget refinements of a type
    // shape :: RType -> SType
    // shape (ScalarT (DatatypeT name tArgs pArgs) _) = ScalarT (DatatypeT name (map shape tArgs) (replicate (length pArgs) ())) ()
    // shape (ScalarT IntT _) = ScalarT IntT ()
    // shape (ScalarT BoolT _) = ScalarT BoolT ()
    // shape (ScalarT (TypeVarT _ a) _) = ScalarT (TypeVarT Map.empty a) ()
    // shape (FunctionT x tArg tFun) = FunctionT x (shape tArg) (shape tFun)
    // shape (LetT _ _ t) = shape t
    // shape AnyT = AnyT

    /// Forget refinements of a type
    pub fn shape(&self) -> TypeSkeleton<Nothing> {
        match self {
            TypeSkeleton::Scalar(BaseType::Datatype(name, t_args, _), _) => TypeSkeleton::Scalar(
                BaseType::Datatype(
                    name.clone(),
                    t_args.iter().map(|t| t.shape()).collect(),
                    Vec::new(),
                ),
                Nothing,
            ),
            TypeSkeleton::Scalar(BaseType::Int, _) => TypeSkeleton::INT_,
            TypeSkeleton::Scalar(BaseType::Bool, _) => TypeSkeleton::BOOL_,
            TypeSkeleton::Scalar(BaseType::TypeVar(_, a), _) => TypeSkeleton::Scalar(
                BaseType::TypeVar(Substitution::default(), a.clone()),
                Nothing,
            ),
            TypeSkeleton::Function { x, t_arg, t_res } => TypeSkeleton::Function {
                x: x.clone(),
                t_arg: Box::new(t_arg.shape()),
                t_res: Box::new(t_res.shape()),
            },
            TypeSkeleton::Let(_, _, t) => t.shape(),
            TypeSkeleton::Any => TypeSkeleton::Any,
        }
    }

    // -- | Conjoin refinement to a type
    // addRefinement :: TypeSkeleton Formula -> Formula -> TypeSkeleton Formula
    // addRefinement (ScalarT base fml) fml' = if isVarRefinemnt fml'
    //   then ScalarT base fml' -- the type of a polymorphic variable does not require any other refinements
    //   else ScalarT base (fml `andClean` fml')
    // addRefinement (LetT x tDef tBody) fml = LetT x tDef (addRefinement tBody fml)
    // addRefinement t (BoolLit True) = t
    // addRefinement AnyT _ = AnyT
    // addRefinement t _ = error $ "addRefinement: applied to function type"

    /// Conjoin refinement to a type
    pub fn add_refinement(self, formula: Formula) -> Self {
        match self {
            TypeSkeleton::Scalar(base, scalar_fml) => {
                if is_var_refinement(&scalar_fml) {
                    TypeSkeleton::Scalar(base, scalar_fml)
                } else {
                    TypeSkeleton::Scalar(base, Formula::and_clean(formula, scalar_fml))
                }
            }
            TypeSkeleton::Let(x, t_def, t_body) => {
                TypeSkeleton::Let(x, t_def, Box::new(t_body.add_refinement(formula)))
            }
            TypeSkeleton::Any => TypeSkeleton::Any,
            t => match formula {
                Formula::BoolLit(true) => t,
                _ => panic!("applied to function type"),
            },
        }
    }

    // -- | Conjoin refinement to the return type
    // addRefinementToLast t@(ScalarT _ _) fml = addRefinement t fml
    // addRefinementToLast (FunctionT x tArg tRes) fml = FunctionT x tArg (addRefinementToLast tRes fml)
    // addRefinementToLast (LetT x tDef tBody) fml = LetT x tDef (addRefinementToLast tBody fml)

    /// Conjoin refinement to the return type
    pub fn add_refinement_to_last(self, formula: Formula) -> Self {
        match self {
            TypeSkeleton::Scalar(_, _) => self.add_refinement(formula),
            TypeSkeleton::Function { x, t_arg, t_res } => TypeSkeleton::Function {
                x,
                t_arg,
                t_res: Box::new(t_res.add_refinement_to_last(formula)),
            },
            TypeSkeleton::Let(x, t_def, t_body) => {
                TypeSkeleton::Let(x, t_def, Box::new(t_body.add_refinement_to_last(formula)))
            }
            _ => panic!("applied to function type"),
        }
    }

    // -- | Apply variable substitution in all formulas inside a type
    // substituteInType :: (Id -> Bool) -> Substitution -> RType -> RType
    // substituteInType isBound subst (ScalarT baseT fml) = ScalarT (substituteBase baseT) (substitute subst fml)
    //   where
    //     substituteBase (TypeVarT oldSubst a) = TypeVarT oldSubst a
    //       -- Looks like pending substitutions on types are not actually needed, since renamed variables are always out of scope
    //        -- if isBound a
    //           -- then TypeVarT oldSubst a
    //           -- else TypeVarT (oldSubst `composeSubstitutions` subst) a
    //     substituteBase (DatatypeT name tArgs pArgs) = DatatypeT name (map (substituteInType isBound subst) tArgs) (map (substitute subst) pArgs)
    //     substituteBase baseT = baseT
    // substituteInType isBound subst (FunctionT x tArg tRes) =
    //   if Map.member x subst
    //     then error $ unwords ["Attempt to substitute variable", x, "bound in a function type"]
    //     else FunctionT x (substituteInType isBound subst tArg) (substituteInType isBound subst tRes)
    // substituteInType isBound subst (LetT x tDef tBody) =
    //   if Map.member x subst
    //     then error $ unwords ["Attempt to substitute variable", x, "bound in a contextual type"]
    //     else LetT x (substituteInType isBound subst tDef) (substituteInType isBound subst tBody)
    // substituteInType isBound subst AnyT = AnyT

    /// Apply variable substitution in all formulas inside a type
    pub fn substitute_in_type(
        &self,
        is_bound: &impl Fn(&Id) -> bool,
        subst: &Substitution,
    ) -> Self {
        match self {
            TypeSkeleton::Scalar(base_t, fml) => {
                let base_t = self.substitute_base(base_t.clone(), fml.clone(), is_bound, subst);
                let fml = fml.clone().substitute(subst);
                TypeSkeleton::Scalar(base_t, fml)
            }
            TypeSkeleton::Function { x, t_arg, t_res } => {
                if subst.as_ref().contains_key(x) {
                    panic!(
                        "Attempt to substitute variable {} bound in a function type",
                        x
                    )
                }
                TypeSkeleton::Function {
                    x: x.clone(),
                    t_arg: Box::new(t_arg.substitute_in_type(is_bound, subst)),
                    t_res: Box::new(t_res.substitute_in_type(is_bound, subst)),
                }
            }
            TypeSkeleton::Let(x, t_def, t_body) => {
                if subst.as_ref().contains_key(x) {
                    panic!(
                        "Attempt to substitute variable {} bound in a contextual type",
                        x
                    )
                }
                TypeSkeleton::Let(
                    x.clone(),
                    Box::new(t_def.substitute_in_type(is_bound, subst)),
                    Box::new(t_body.substitute_in_type(is_bound, subst)),
                )
            }
            TypeSkeleton::Any => TypeSkeleton::Any,
        }
    }

    pub fn substitute_base(
        &self,
        base_t: BaseType<Formula>,
        r: Formula,
        is_bound: &impl Fn(&Id) -> bool,
        subst: &Substitution,
    ) -> BaseType<Formula> {
        match base_t {
            BaseType::TypeVar(old_subst, a) => {
                if is_bound(&a) {
                    BaseType::TypeVar(old_subst, a)
                } else {
                    BaseType::TypeVar(compose_substitutions(old_subst, subst), a)
                }
            }
            BaseType::Datatype(name, t_args, p_args) => BaseType::Datatype(
                name.clone(),
                t_args
                    .iter()
                    .map(|t| t.substitute_in_type(is_bound, subst))
                    .collect(),
                p_args.iter().map(|p| p.clone().substitute(subst)).collect(),
            ),
            _ => base_t,
        }
    }

    // -- | 'renameVar' @old new t typ@: rename all occurrences of @old@ in @typ@ into @new@ of type @t@
    // renameVar :: (Id -> Bool) -> Id -> Id -> RType -> RType -> RType
    // renameVar isBound old new (ScalarT b _)     t = substituteInType isBound (Map.singleton old (Var (toSort b) new)) t
    // renameVar isBound old new (LetT _ _ tBody)  t = renameVar isBound old new tBody t
    // renameVar _ _ _ _                           t = t -- function arguments cannot occur in types (and AnyT is assumed to be function)

    /// Rename all occurrences of `old` in `typ` into `new` of type `t`
    pub fn rename_var(
        &self,
        t: &Self,
        old: &Id,
        new: &Id,
        is_bound: &impl Fn(&Id) -> bool,
    ) -> Self {
        match self {
            TypeSkeleton::Scalar(base_t, _) => {
                let subst = Substitution::new(BTreeMap::from_iter([(
                    old.clone(),
                    Formula::Var(base_t.to_sort(), new.clone()),
                )]));
                t.substitute_in_type(is_bound, &subst)
            }
            TypeSkeleton::Let(_, _, t_body) => t_body.rename_var(t, old, new, is_bound),
            _ => t.clone(),
        }
    }

    // -- | Intersection of two types (assuming the types were already checked for consistency)
    // intersection _ t AnyT = t
    // intersection _ AnyT t = t
    // intersection isBound (ScalarT baseT fml) (ScalarT baseT' fml') = case baseT of
    //   DatatypeT name tArgs pArgs -> let DatatypeT _ tArgs' pArgs' = baseT' in
    //                                   ScalarT (DatatypeT name (zipWith (intersection isBound) tArgs tArgs') (zipWith andClean pArgs pArgs')) (fml `andClean` fml')
    //   _ -> ScalarT baseT (fml `andClean` fml')
    // intersection isBound (FunctionT x tArg tRes) (FunctionT y tArg' tRes') = FunctionT x tArg (intersection isBound tRes (renameVar isBound y x tArg tRes'))

    /// Intersection of two types (assuming the types were already checked for consistency)
    pub fn intersection(&self, other: &Self, is_bound: &impl Fn(&Id) -> bool) -> Self {
        match (self, other) {
            (_, TypeSkeleton::Any) => self.clone(),
            (TypeSkeleton::Any, _) => other.clone(),
            (TypeSkeleton::Scalar(base_t, fml), TypeSkeleton::Scalar(base_t_, fml_)) => {
                match base_t {
                    BaseType::Datatype(name, t_args, p_args) => {
                        let BaseType::Datatype(_, t_args_, p_args_) = base_t_.clone() else {
                            unreachable!("intersection: applied to incompatible types")
                        };

                        TypeSkeleton::Scalar(
                            BaseType::Datatype(
                                name.clone(),
                                t_args
                                    .iter()
                                    .zip(t_args_)
                                    .map(|(t, t_)| t.intersection(&t_, is_bound))
                                    .collect(),
                                p_args
                                    .iter()
                                    .zip(p_args_)
                                    .map(|(p, p_)| Formula::and_clean(p.clone(), p_.clone()))
                                    .collect(),
                            ),
                            Formula::and_clean(fml.clone(), fml_.clone()),
                        )
                    }
                    _ => TypeSkeleton::Scalar(
                        base_t.clone(),
                        Formula::and_clean(fml.clone(), fml_.clone()),
                    ),
                }
            }
            (
                TypeSkeleton::Function { x, t_arg, t_res },
                TypeSkeleton::Function {
                    x: y,
                    t_arg: t_arg_,
                    t_res: t_res_,
                },
            ) => TypeSkeleton::Function {
                x: x.clone(),
                t_arg: t_arg.clone(),
                t_res: Box::new(
                    t_res.intersection(&t_arg.rename_var(t_res_, y, x, is_bound), is_bound),
                ),
            },
            _ => panic!("intersection: applied to function type"),
        }
    }

    // -- | Instantiate unknowns in a type
    // typeApplySolution :: Solution -> RType -> RType
    // typeApplySolution sol (ScalarT (DatatypeT name tArgs pArgs) fml) = ScalarT (DatatypeT name (map (typeApplySolution sol) tArgs) (map (applySolution sol) pArgs)) (applySolution sol fml)
    // typeApplySolution sol (ScalarT base fml) = ScalarT base (applySolution sol fml)
    // typeApplySolution sol (FunctionT x tArg tRes) = FunctionT x (typeApplySolution sol tArg) (typeApplySolution sol tRes)
    // typeApplySolution sol (LetT x tDef tBody) = LetT x (typeApplySolution sol tDef) (typeApplySolution sol tBody)
    // typeApplySolution _ AnyT = AnyT

    /// Instantiate unknowns in a type
    pub fn apply_solution(&self, sol: &Solution) -> Self {
        match self {
            TypeSkeleton::Scalar(BaseType::Datatype(name, t_args, p_args), fml) => {
                TypeSkeleton::Scalar(
                    BaseType::Datatype(
                        name.clone(),
                        t_args.iter().map(|t| t.apply_solution(sol)).collect(),
                        p_args
                            .iter()
                            .map(|p| p.clone().apply_solution(sol))
                            .collect(),
                    ),
                    fml.clone().apply_solution(sol),
                )
            }
            TypeSkeleton::Scalar(base, fml) => {
                TypeSkeleton::Scalar(base.clone(), fml.clone().apply_solution(sol))
            }
            TypeSkeleton::Function { x, t_arg, t_res } => TypeSkeleton::Function {
                x: x.clone(),
                t_arg: Box::new(t_arg.apply_solution(sol)),
                t_res: Box::new(t_res.apply_solution(sol)),
            },
            TypeSkeleton::Let(x, t_def, t_body) => TypeSkeleton::Let(
                x.clone(),
                Box::new(t_def.apply_solution(sol)),
                Box::new(t_body.apply_solution(sol)),
            ),
            TypeSkeleton::Any => TypeSkeleton::Any,
        }
    }

    // typeFromSchema :: RSchema -> RType
    // typeFromSchema (Monotype t) = t
    // typeFromSchema (ForallT _ t) = typeFromSchema t
    // typeFromSchema (ForallP _ t) = typeFromSchema t

    pub fn from_schema(schema: RSchema) -> Self {
        match schema {
            RSchema::Monotype(t) => t,
            RSchema::ForAllType(_, t) => Self::from_schema(*t),
            RSchema::ForAllPredicate(_, t) => Self::from_schema(*t),
        }
    }

    // pub fn vars(&self) -> HashSet<Id> {
    //     match self {
    //         TypeSkeleton::Scalar(base_t, fml) =>  {
    //             let mut set = fml.vars().into_iter().map(|v| v.var_name())
    //         },
    //         TypeSkeleton::Function { x, t_arg, t_res } => todo!(),
    //         TypeSkeleton::Let(_, _, _) => todo!(),
    //         TypeSkeleton::Any => todo!(),
    //     }
    // }

    pub fn format_at(&self, n: usize) -> String {
        match self {
            TypeSkeleton::Scalar(base, Formula::BoolLit(true)) => format!("{base}"),
            TypeSkeleton::Scalar(base, fml) => format!("{{{base}|{fml}}}"),
            TypeSkeleton::Function { x, t_arg, t_res } => format!(
                "{x}{}{} {} {}",
                ':'.white().dimmed(),
                t_arg.format_at(n),
                "->".white().dimmed(),
                t_res.format_at(0)
            ),
            TypeSkeleton::Let(x, t1, t2) => format!(
                "LET {x}{}{} IN {}",
                ':'.white().dimmed(),
                t1.format_at(n),
                t2.format_at(0)
            ),
            TypeSkeleton::Any => format!("_"),
        }
    }

    pub fn type_power(&self) -> usize {
        match self {
            TypeSkeleton::Scalar(BaseType::Datatype(_, t_args, t_res), r)
            // REVIEW implementation
                if *r == Formula::TRUE =>
            {
                2
            }
            TypeSkeleton::Function { .. } => 1,
            _ => 3,
        }
    }

    // -- | 'renameAsImpl' @p t@: change argument names in function type @t@ to be the same as in the abstraction @p@
    // renameAsImpl :: (Id -> Bool) -> UProgram -> RType -> RType
    // renameAsImpl isBound = renameAsImpl' Map.empty
    //   where
    //     renameAsImpl' subst (Program (PFun y pRes) _) (FunctionT x tArg tRes) = case tArg of
    //       ScalarT baseT fml -> FunctionT y (substituteInType isBound subst tArg) (renameAsImpl' (Map.insert x (Var (toSort baseT) y) subst) pRes tRes)
    //       _ -> FunctionT y (substituteInType isBound subst tArg) (renameAsImpl' subst pRes tRes)
    //     renameAsImpl' subst  _ t = substituteInType isBound subst t

    /// Change argument names in function type `t` to be the same as in the abstraction `p`
    pub fn rename_as_impl(&self, p: UProgram, is_bound: &impl Fn(&Id) -> bool) -> Self {
        self.rename_as_impl_(p, Substitution::default(), is_bound)
    }

    fn rename_as_impl_(
        &self,
        p: UProgram,
        subst: Substitution,
        is_bound: &impl Fn(&Id) -> bool,
    ) -> Self {
        let program: Program<Self> = p.into();

        match (*program.content, self) {
            (BareProgram::Fun(y, p_res), TypeSkeleton::Function { x, t_arg, t_res }) => {
                let p_res = UProgram::new(p_res);

                match &**t_arg {
                    TypeSkeleton::Scalar(base_t, _fml) => {
                        let t_arg = Box::new(t_arg.substitute_in_type(is_bound, &subst));

                        let mut subst = subst.as_ref().clone();
                        subst.insert(x.clone(), Formula::Var(base_t.to_sort(), y.clone()));

                        let t_res = Box::new(t_res.rename_as_impl_(
                            p_res,
                            Substitution::new(subst),
                            is_bound,
                        ));

                        TypeSkeleton::Function {
                            x: y.clone(),
                            t_arg,
                            t_res,
                        }
                    }
                    _ => TypeSkeleton::Function {
                        x: y.clone(),
                        t_arg: Box::new(t_arg.substitute_in_type(is_bound, &subst)),
                        t_res: Box::new(t_res.rename_as_impl_(p_res, subst.clone(), is_bound)),
                    },
                }
            }
            _ => self.substitute_in_type(is_bound, &subst),
        }
    }
}

impl fmt::Display for TypeSkeleton<Formula> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.format_at(0))
    }
}

pub fn var_refinement(x: Id, s: Sort) -> Formula {
    Formula::Var(s.clone(), VALUE_VAR_NAME).eq(Formula::Var(s, x))
}

pub fn is_var_refinement(x: &Formula) -> bool {
    match x {
        Formula::Binary(BinOp::Eq, l, r) => match (&**l, &**r) {
            (Formula::Var(_, v), Formula::Var(_, _)) => *v == VALUE_VAR_NAME,
            _ => false,
        },
        _ => false,
    }
}

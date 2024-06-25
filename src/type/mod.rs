mod base;
mod schema;
mod skeleton;

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    hash::Hash,
};

pub use base::*;
pub use schema::SchemaSkeleton;
// pub use skeleton::*;
use hashbrown::{HashMap, HashSet};
use num_bigint::BigInt;
pub use skeleton::*;

use crate::{
    logic::{distinct_type_vars, Formula, Sort, SortSubstitution, Substitution, DONT_CARE},
    util::Id,
};

#[doc(alias = "()")]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Nothing;

impl fmt::Display for Nothing {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "()")
    }
}

pub type SType = TypeSkeleton<Nothing>;
pub type RType = TypeSkeleton<Formula>;

pub type SSchema = SchemaSkeleton<Nothing>;
pub type RSchema = SchemaSkeleton<Formula>;

/// Mapping from type variables to types
#[repr(transparent)]
#[derive(derive_more::AsRef, derive_more::Constructor, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeSubstitution(BTreeMap<Id, RType>);

impl TypeSubstitution {
    // asSortSubst :: TypeSubstitution -> SortSubstitution
    // asSortSubst = Map.map (toSort . baseTypeOf)

    pub fn as_sort_subst(&self) -> SortSubstitution {
        SortSubstitution::new(
            self.0
                .iter()
                .map(|(k, v)| (k.clone(), v.base_type().to_sort()))
                .collect(),
        )
    }

    // -- | 'typeSubstitute' @t@ : substitute all free type variables in @t@
    // typeSubstitute :: TypeSubstitution -> RType -> RType
    // typeSubstitute subst (ScalarT baseT r) = addRefinement substituteBase (sortSubstituteFml (asSortSubst subst) r)
    //   where
    //     substituteBase = case baseT of
    //       TypeVarT varSubst a -> case Map.lookup a subst of
    //         Just t -> substituteInType (not . (`Map.member` subst)) varSubst $ typeSubstitute subst t
    //         Nothing -> ScalarT (TypeVarT varSubst a) ftrue
    //       DatatypeT name tArgs pArgs ->
    //         let
    //           tArgs' = map (typeSubstitute subst) tArgs
    //           pArgs' = map (sortSubstituteFml (asSortSubst subst)) pArgs
    //         in ScalarT (DatatypeT name tArgs' pArgs') ftrue
    //       _ -> ScalarT baseT ftrue
    // typeSubstitute subst (FunctionT x tArg tRes) = FunctionT x (typeSubstitute subst tArg) (typeSubstitute subst tRes)
    // typeSubstitute subst (LetT x tDef tBody) = LetT x (typeSubstitute subst tDef) (typeSubstitute subst tBody)
    // typeSubstitute _ AnyT = AnyT

    /// Substitute all free type variables in `t`
    pub fn type_substitute(&self, t: RType) -> RType {
        match t {
            TypeSkeleton::Scalar(base_t, r) => {
                let substitute_base = match base_t {
                    BaseType::TypeVar(var_subst, a) => match self.as_ref().get(&a) {
                        Some(t) => {
                            let t = self.type_substitute(t.clone());
                            t.substitute_in_type(&|x| !self.as_ref().contains_key(x), &var_subst)
                        }
                        None => RType::Scalar(BaseType::TypeVar(var_subst, a), Formula::TRUE),
                    },
                    BaseType::Datatype(name, t_args, p_args) => {
                        let t_args = t_args
                            .into_iter()
                            .map(|t| self.type_substitute(t))
                            .collect();
                        let p_args = p_args
                            .into_iter()
                            .map(|p| self.as_sort_subst().sort_substitute_fml(p))
                            .collect();

                        RType::Scalar(BaseType::Datatype(name, t_args, p_args), Formula::TRUE)
                    }
                    _ => RType::Scalar(base_t, Formula::TRUE),
                };

                substitute_base.add_refinement(r)
            }
            TypeSkeleton::Function { x, t_arg, t_res } => TypeSkeleton::Function {
                x,
                t_arg: Box::new(self.type_substitute(*t_arg)),
                t_res: Box::new(self.type_substitute(*t_res)),
            },
            TypeSkeleton::Let(x, t_def, t_body) => TypeSkeleton::Let(
                x,
                Box::new(self.type_substitute(*t_def)),
                Box::new(self.type_substitute(*t_body)),
            ),
            TypeSkeleton::Any => TypeSkeleton::Any,
        }
    }

    // noncaptureTypeSubst :: [Id] -> [RType] -> RType -> RType
    // noncaptureTypeSubst tVars tArgs t =
    //   let tFresh = typeSubstitute (Map.fromList $ zip tVars (map vartAll distinctTypeVars)) t
    //   in typeSubstitute (Map.fromList $ zip distinctTypeVars tArgs) tFresh

    pub fn non_capture_type_subst(&self, t_vars: Vec<Id>, t_args: Vec<RType>, t: RType) -> RType {
        let t_fresh = TypeSubstitution::new(
            t_vars
                .into_iter()
                .zip(t_args.iter().map(|t| t.clone()))
                .collect(),
        )
        .type_substitute(t);

        TypeSubstitution::new(
            distinct_type_vars(&t_args)
                .into_iter()
                .zip(t_args.into_iter())
                .collect(),
        )
        .type_substitute(t_fresh)
    }

    // schemaSubstitute :: TypeSubstitution -> RSchema -> RSchema
    // schemaSubstitute tass (Monotype t) = Monotype $ typeSubstitute tass t
    // schemaSubstitute tass (ForallT a sch) = ForallT a $ schemaSubstitute (Map.delete a tass) sch
    // schemaSubstitute tass (ForallP sig sch) = ForallP sig $ schemaSubstitute tass sch

    pub fn schema_substitute(&self, schema: RSchema) -> RSchema {
        match schema {
            SchemaSkeleton::Monotype(t) => SchemaSkeleton::Monotype(self.type_substitute(t)),
            SchemaSkeleton::ForAllType(a, sch) => {
                let x = TypeSubstitution::new(
                    self.0
                        .iter()
                        .filter(|(k, _)| **k != a)
                        .map(|(k, v)| (k.clone(), v.clone()))
                        .collect(),
                )
                .schema_substitute(*sch);

                SchemaSkeleton::ForAllType(a, Box::new(x))
            }
            SchemaSkeleton::ForAllPredicate(sig, sch) => {
                SchemaSkeleton::ForAllPredicate(sig, Box::new(self.schema_substitute(*sch)))
            }
        }
    }

    // typeSubstitutePred :: Substitution -> RType -> RType
    // typeSubstitutePred pSubst t = let tsp = typeSubstitutePred pSubst
    //   in case t of
    //     ScalarT (DatatypeT name tArgs pArgs) fml -> ScalarT (DatatypeT name (map tsp tArgs) (map (substitutePredicate pSubst) pArgs)) (substitutePredicate pSubst fml)
    //     ScalarT baseT fml -> ScalarT baseT (substitutePredicate pSubst fml)
    //     FunctionT x tArg tRes -> FunctionT x (tsp tArg) (tsp tRes)
    //     LetT x tDef tBody -> FunctionT x (tsp tDef) (tsp tBody)
    //     AnyT -> AnyT

    pub fn type_substitute_pred(&self, p_subst: &Substitution, t: RType) -> RType {
        let tsp = |t: RType| self.type_substitute_pred(p_subst, t);

        match t {
            TypeSkeleton::Scalar(BaseType::Datatype(name, t_args, p_args), fml) => {
                let t_args = t_args.into_iter().map(|t| tsp(t)).collect();
                let p_args = p_args
                    .into_iter()
                    .map(|p| p.substitute_predicate(&p_subst))
                    .collect();

                RType::Scalar(
                    BaseType::Datatype(name, t_args, p_args),
                    fml.substitute_predicate(&p_subst),
                )
            }
            TypeSkeleton::Scalar(base_t, fml) => {
                RType::Scalar(base_t, fml.substitute_predicate(&p_subst))
            }
            TypeSkeleton::Function { x, t_arg, t_res } => TypeSkeleton::Function {
                x,
                t_arg: Box::new(tsp(*t_arg)),
                t_res: Box::new(tsp(*t_res)),
            },
            TypeSkeleton::Let(x, t_def, t_body) => {
                TypeSkeleton::Let(x, Box::new(tsp(*t_def)), Box::new(tsp(*t_body)))
            }
            TypeSkeleton::Any => TypeSkeleton::Any,
        }
    }
}

pub fn non_capture_type_subst(t_vars: BTreeSet<Id>, t_args: Vec<RType>, t: RType) -> RType {
    let t_fresh = TypeSubstitution::new(
        t_vars
            .into_iter()
            .zip(t_args.iter().map(|t| t.clone()))
            .collect(),
    )
    .type_substitute(t);

    TypeSubstitution::new(
        distinct_type_vars(&t_args)
            .into_iter()
            .zip(t_args.into_iter())
            .collect(),
    )
    .type_substitute(t_fresh)
}

use core::fmt;
use std::hash::Hash;

use hashbrown::HashSet;

use super::{Nothing, TypeSkeleton};
use crate::{
    logic::{BinOp, Formula, PredSig, UnOp},
    util::Id,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum SchemaSkeleton<R: fmt::Display + Clone + Eq + Hash> {
    Monotype(TypeSkeleton<R>),
    /// Type-polymorphic
    ForAllType(Id, Box<SchemaSkeleton<R>>),
    /// Predicate-polymorphic
    ForAllPredicate(PredSig, Box<SchemaSkeleton<R>>),
}

impl<R: fmt::Display + Clone + Eq + Hash> SchemaSkeleton<R> {
    pub fn to_monotype(&self) -> &TypeSkeleton<R> {
        match self {
            SchemaSkeleton::Monotype(t) => t,
            SchemaSkeleton::ForAllType(_, t) => t.to_monotype(),
            SchemaSkeleton::ForAllPredicate(_, t) => t.to_monotype(),
        }
    }

    pub fn bound_vars(&self) -> HashSet<&Id> {
        match self {
            SchemaSkeleton::ForAllType(a, sch) => {
                let mut set = sch.bound_vars();
                set.insert(a);

                set
            }
            _ => HashSet::new(),
        }
    }

    // allRefinementsOf :: RSchema -> [Formula]
    // allRefinementsOf sch = allRefinementsOf' $ typeFromSchema sch

    #[doc(alias = "all_refinements_of")]
    pub fn all_refinements(&self) -> HashSet<R> {
        self.to_monotype().all_refinements()
    }
}

impl fmt::Display for SchemaSkeleton<Nothing> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SchemaSkeleton::Monotype(t) => write!(f, "{t}"),
            SchemaSkeleton::ForAllType(a, sch) => write!(f, "<{a}> . {sch}"),
            SchemaSkeleton::ForAllPredicate(sig, sch) => write!(f, "{sig} . {sch}"),
        }
    }
}

impl fmt::Display for SchemaSkeleton<Formula> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SchemaSkeleton::Monotype(t) => write!(f, "{t}"),
            SchemaSkeleton::ForAllType(a, sch) => write!(f, "<{a}> . {sch}"),
            SchemaSkeleton::ForAllPredicate(sig, sch) => write!(f, "{sig} . {sch}"),
        }
    }
}

impl SchemaSkeleton<Formula> {
    pub fn un_op_type(un_op: &UnOp) -> Self {
        match un_op {
            UnOp::Neg => SchemaSkeleton::Monotype(TypeSkeleton::Function {
                x: Id::Builtin("x"),
                t_arg: Box::new(TypeSkeleton::INT_ALL),
                t_res: Box::new(TypeSkeleton::int(
                    Formula::VAL_INT.eq(-Formula::int_var(Id::Builtin("x"))),
                )),
            }),
            UnOp::Not => SchemaSkeleton::Monotype(TypeSkeleton::Function {
                x: Id::Builtin("x"),
                t_arg: Box::new(TypeSkeleton::BOOL_ALL),
                t_res: Box::new(TypeSkeleton::bool(
                    Formula::VAL_BOOL.eq(!Formula::bool_var(Id::Builtin("x"))),
                )),
            }),
        }
    }

    pub fn bin_op_type(bin_op: &BinOp) -> Self {
        match bin_op {
            BinOp::Times => SchemaSkeleton::Monotype(TypeSkeleton::Function {
                x: Id::Builtin("x"),
                t_arg: Box::new(TypeSkeleton::INT_ALL),
                t_res: Box::new(TypeSkeleton::Function {
                    x: Id::Builtin("y"),
                    t_arg: Box::new(TypeSkeleton::INT_ALL),
                    t_res: Box::new(TypeSkeleton::int(
                        Formula::VAL_INT.eq(Formula::int_var(Id::Builtin("x"))
                            .times(Formula::int_var(Id::Builtin("y")))),
                    )),
                }),
            }),
            BinOp::Plus => SchemaSkeleton::Monotype(TypeSkeleton::Function {
                x: Id::Builtin("x"),
                t_arg: Box::new(TypeSkeleton::INT_ALL),
                t_res: Box::new(TypeSkeleton::Function {
                    x: Id::Builtin("y"),
                    t_arg: Box::new(TypeSkeleton::INT_ALL),
                    t_res: Box::new(TypeSkeleton::int(Formula::VAL_INT.eq(
                        Formula::int_var(Id::Builtin("x")).plus(Formula::int_var(Id::Builtin("y"))),
                    ))),
                }),
            }),
            BinOp::Minus => SchemaSkeleton::Monotype(TypeSkeleton::Function {
                x: Id::Builtin("x"),
                t_arg: Box::new(TypeSkeleton::INT_ALL),
                t_res: Box::new(TypeSkeleton::Function {
                    x: Id::Builtin("y"),
                    t_arg: Box::new(TypeSkeleton::INT_ALL),
                    t_res: Box::new(TypeSkeleton::int(
                        Formula::VAL_INT.eq(Formula::int_var(Id::Builtin("x"))
                            .minus(Formula::int_var(Id::Builtin("y")))),
                    )),
                }),
            }),
            BinOp::Eq => SchemaSkeleton::ForAllType(
                Id::Builtin("a"),
                Box::new(SchemaSkeleton::Monotype(TypeSkeleton::Function {
                    x: Id::Builtin("x"),
                    t_arg: Box::new(TypeSkeleton::vart_all(Id::Builtin("a"))),
                    t_res: Box::new(TypeSkeleton::Function {
                        x: Id::Builtin("y"),
                        t_arg: Box::new(TypeSkeleton::vart_all(Id::Builtin("a"))),
                        t_res: Box::new(TypeSkeleton::bool(
                            Formula::VAL_BOOL.eq(Formula::vart_var(
                                Id::Builtin("a"),
                                Id::Builtin("x"),
                            )
                            .eq(Formula::vart_var(Id::Builtin("a"), Id::Builtin("y")))),
                        )),
                    }),
                })),
            ),
            BinOp::Neq => SchemaSkeleton::ForAllType(
                Id::Builtin("a"),
                Box::new(SchemaSkeleton::Monotype(TypeSkeleton::Function {
                    x: Id::Builtin("x"),
                    t_arg: Box::new(TypeSkeleton::vart_all(Id::Builtin("a"))),
                    t_res: Box::new(TypeSkeleton::Function {
                        x: Id::Builtin("y"),
                        t_arg: Box::new(TypeSkeleton::vart_all(Id::Builtin("a"))),
                        t_res: Box::new(TypeSkeleton::bool(
                            Formula::VAL_BOOL.eq(Formula::vart_var(
                                Id::Builtin("a"),
                                Id::Builtin("x"),
                            )
                            .neq(Formula::vart_var(Id::Builtin("a"), Id::Builtin("y")))),
                        )),
                    }),
                })),
            ),
            BinOp::Lt => SchemaSkeleton::ForAllType(
                Id::Builtin("a"),
                Box::new(SchemaSkeleton::Monotype(TypeSkeleton::Function {
                    x: Id::Builtin("x"),
                    t_arg: Box::new(TypeSkeleton::vart_all(Id::Builtin("a"))),
                    t_res: Box::new(TypeSkeleton::Function {
                        x: Id::Builtin("y"),
                        t_arg: Box::new(TypeSkeleton::vart_all(Id::Builtin("a"))),
                        t_res: Box::new(TypeSkeleton::bool(
                            Formula::VAL_BOOL.eq(Formula::vart_var(
                                Id::Builtin("a"),
                                Id::Builtin("x"),
                            )
                            .lt(Formula::vart_var(Id::Builtin("a"), Id::Builtin("y")))),
                        )),
                    }),
                })),
            ),
            BinOp::Le => SchemaSkeleton::ForAllType(
                Id::Builtin("a"),
                Box::new(SchemaSkeleton::Monotype(TypeSkeleton::Function {
                    x: Id::Builtin("x"),
                    t_arg: Box::new(TypeSkeleton::vart_all(Id::Builtin("a"))),
                    t_res: Box::new(TypeSkeleton::Function {
                        x: Id::Builtin("y"),
                        t_arg: Box::new(TypeSkeleton::vart_all(Id::Builtin("a"))),
                        t_res: Box::new(TypeSkeleton::bool(
                            Formula::VAL_BOOL.eq(Formula::vart_var(
                                Id::Builtin("a"),
                                Id::Builtin("x"),
                            )
                            .le(Formula::vart_var(Id::Builtin("a"), Id::Builtin("y")))),
                        )),
                    }),
                })),
            ),
            BinOp::Gt => SchemaSkeleton::ForAllType(
                Id::Builtin("a"),
                Box::new(SchemaSkeleton::Monotype(TypeSkeleton::Function {
                    x: Id::Builtin("x"),
                    t_arg: Box::new(TypeSkeleton::vart_all(Id::Builtin("a"))),
                    t_res: Box::new(TypeSkeleton::Function {
                        x: Id::Builtin("y"),
                        t_arg: Box::new(TypeSkeleton::vart_all(Id::Builtin("a"))),
                        t_res: Box::new(TypeSkeleton::bool(
                            Formula::VAL_BOOL.eq(Formula::vart_var(
                                Id::Builtin("a"),
                                Id::Builtin("x"),
                            )
                            .gt(Formula::vart_var(Id::Builtin("a"), Id::Builtin("y")))),
                        )),
                    }),
                })),
            ),
            BinOp::Ge => SchemaSkeleton::ForAllType(
                Id::Builtin("a"),
                Box::new(SchemaSkeleton::Monotype(TypeSkeleton::Function {
                    x: Id::Builtin("x"),
                    t_arg: Box::new(TypeSkeleton::vart_all(Id::Builtin("a"))),
                    t_res: Box::new(TypeSkeleton::Function {
                        x: Id::Builtin("y"),
                        t_arg: Box::new(TypeSkeleton::vart_all(Id::Builtin("a"))),
                        t_res: Box::new(TypeSkeleton::bool(
                            Formula::VAL_BOOL.eq(Formula::vart_var(
                                Id::Builtin("a"),
                                Id::Builtin("x"),
                            )
                            .ge(Formula::vart_var(Id::Builtin("a"), Id::Builtin("y")))),
                        )),
                    }),
                })),
            ),
            BinOp::And => SchemaSkeleton::Monotype(TypeSkeleton::Function {
                x: Id::Builtin("x"),
                t_arg: Box::new(TypeSkeleton::BOOL_ALL),
                t_res: Box::new(TypeSkeleton::Function {
                    x: Id::Builtin("y"),
                    t_arg: Box::new(TypeSkeleton::BOOL_ALL),
                    t_res: Box::new(TypeSkeleton::bool(
                        Formula::VAL_BOOL.eq(Formula::bool_var(Id::Builtin("x"))
                            .and(Formula::bool_var(Id::Builtin("y")))),
                    )),
                }),
            }),
            BinOp::Or => SchemaSkeleton::Monotype(TypeSkeleton::Function {
                x: Id::Builtin("x"),
                t_arg: Box::new(TypeSkeleton::BOOL_ALL),
                t_res: Box::new(TypeSkeleton::Function {
                    x: Id::Builtin("y"),
                    t_arg: Box::new(TypeSkeleton::BOOL_ALL),
                    t_res: Box::new(TypeSkeleton::bool(Formula::VAL_BOOL.eq(
                        Formula::bool_var(Id::Builtin("x")).or(Formula::bool_var(Id::Builtin("y"))),
                    ))),
                }),
            }),
            BinOp::Implies => SchemaSkeleton::Monotype(TypeSkeleton::Function {
                x: Id::Builtin("x"),
                t_arg: Box::new(TypeSkeleton::BOOL_ALL),
                t_res: Box::new(TypeSkeleton::Function {
                    x: Id::Builtin("y"),
                    t_arg: Box::new(TypeSkeleton::BOOL_ALL),
                    t_res: Box::new(TypeSkeleton::bool(
                        Formula::VAL_BOOL.eq(Formula::bool_var(Id::Builtin("x"))
                            .implies(Formula::bool_var(Id::Builtin("y")))),
                    )),
                }),
            }),
            BinOp::Iff => SchemaSkeleton::Monotype(TypeSkeleton::Function {
                x: Id::Builtin("x"),
                t_arg: Box::new(TypeSkeleton::BOOL_ALL),
                t_res: Box::new(TypeSkeleton::Function {
                    x: Id::Builtin("y"),
                    t_arg: Box::new(TypeSkeleton::BOOL_ALL),
                    t_res: Box::new(TypeSkeleton::bool(
                        Formula::VAL_BOOL.eq(Formula::bool_var(Id::Builtin("x"))
                            .iff(Formula::bool_var(Id::Builtin("y")))),
                    )),
                }),
            }),
            BinOp::Union => SchemaSkeleton::ForAllType(
                Id::Builtin("a"),
                Box::new(SchemaSkeleton::Monotype(TypeSkeleton::Function {
                    x: Id::Builtin("x"),
                    t_arg: Box::new(TypeSkeleton::set_all(Id::Builtin("a"))),
                    t_res: Box::new(TypeSkeleton::Function {
                        x: Id::Builtin("y"),
                        t_arg: Box::new(TypeSkeleton::set_all(Id::Builtin("a"))),
                        t_res: Box::new(TypeSkeleton::set(
                            Id::Builtin("a"),
                            Formula::val_set(Id::Builtin("a")).eq(Formula::set_var(
                                Id::Builtin("a"),
                                Id::Builtin("x"),
                            )
                            .union(Formula::set_var(Id::Builtin("a"), Id::Builtin("y")))),
                        )),
                    }),
                })),
            ),
            BinOp::Intersect => SchemaSkeleton::ForAllType(
                Id::Builtin("a"),
                Box::new(SchemaSkeleton::Monotype(TypeSkeleton::Function {
                    x: Id::Builtin("x"),
                    t_arg: Box::new(TypeSkeleton::set_all(Id::Builtin("a"))),
                    t_res: Box::new(TypeSkeleton::Function {
                        x: Id::Builtin("y"),
                        t_arg: Box::new(TypeSkeleton::set_all(Id::Builtin("a"))),
                        t_res: Box::new(TypeSkeleton::set(
                            Id::Builtin("a"),
                            Formula::val_set(Id::Builtin("a")).eq(Formula::set_var(
                                Id::Builtin("a"),
                                Id::Builtin("x"),
                            )
                            .intersect(Formula::set_var(Id::Builtin("a"), Id::Builtin("y")))),
                        )),
                    }),
                })),
            ),
            BinOp::Diff => SchemaSkeleton::ForAllType(
                Id::Builtin("a"),
                Box::new(SchemaSkeleton::Monotype(TypeSkeleton::Function {
                    x: Id::Builtin("x"),
                    t_arg: Box::new(TypeSkeleton::set_all(Id::Builtin("a"))),
                    t_res: Box::new(TypeSkeleton::Function {
                        x: Id::Builtin("y"),
                        t_arg: Box::new(TypeSkeleton::set_all(Id::Builtin("a"))),
                        t_res: Box::new(TypeSkeleton::set(
                            Id::Builtin("a"),
                            Formula::val_set(Id::Builtin("a")).eq(Formula::set_var(
                                Id::Builtin("a"),
                                Id::Builtin("x"),
                            )
                            .diff(Formula::set_var(Id::Builtin("a"), Id::Builtin("y")))),
                        )),
                    }),
                })),
            ),
            BinOp::Member => SchemaSkeleton::ForAllType(
                Id::Builtin("a"),
                Box::new(SchemaSkeleton::Monotype(TypeSkeleton::Function {
                    x: Id::Builtin("x"),
                    t_arg: Box::new(TypeSkeleton::vart_all(Id::Builtin("a"))),
                    t_res: Box::new(TypeSkeleton::Function {
                        x: Id::Builtin("y"),
                        t_arg: Box::new(TypeSkeleton::set_all(Id::Builtin("a"))),
                        t_res: Box::new(TypeSkeleton::bool(
                            Formula::VAL_BOOL.eq(Formula::vart_var(
                                Id::Builtin("a"),
                                Id::Builtin("x"),
                            )
                            .member(Formula::set_var(Id::Builtin("a"), Id::Builtin("y")))),
                        )),
                    }),
                })),
            ),
            BinOp::Subset => SchemaSkeleton::ForAllType(
                Id::Builtin("a"),
                Box::new(SchemaSkeleton::Monotype(TypeSkeleton::Function {
                    x: Id::Builtin("x"),
                    t_arg: Box::new(TypeSkeleton::set_all(Id::Builtin("a"))),
                    t_res: Box::new(TypeSkeleton::Function {
                        x: Id::Builtin("y"),
                        t_arg: Box::new(TypeSkeleton::set_all(Id::Builtin("a"))),
                        t_res: Box::new(TypeSkeleton::bool(
                            Formula::VAL_BOOL.eq(Formula::set_var(
                                Id::Builtin("a"),
                                Id::Builtin("x"),
                            )
                            .subset(Formula::set_var(Id::Builtin("a"), Id::Builtin("y")))),
                        )),
                    }),
                })),
            ),
        }
    }

    // -- | Conjoin refinement to the return type inside a schema
    // addRefinementToLastSch (Monotype t) fml = Monotype $ addRefinementToLast t fml
    // addRefinementToLastSch (ForallT a sch) fml = ForallT a $ addRefinementToLastSch sch fml
    // addRefinementToLastSch (ForallP sig sch) fml = ForallP sig $ addRefinementToLastSch sch fml

    /// Conjoin refinement to the return type inside a schema
    pub fn add_refinement_to_last_sch(self, fml: Formula) -> Self {
        match self {
            SchemaSkeleton::Monotype(t) => SchemaSkeleton::Monotype(t.add_refinement(fml)),
            SchemaSkeleton::ForAllType(a, sch) => {
                SchemaSkeleton::ForAllType(a, Box::new(sch.add_refinement_to_last_sch(fml)))
            }
            SchemaSkeleton::ForAllPredicate(sig, sch) => {
                SchemaSkeleton::ForAllPredicate(sig, Box::new(sch.add_refinement_to_last_sch(fml)))
            }
        }
    }
}

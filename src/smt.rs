use std::{cell::RefCell, collections::BTreeMap, rc::Rc};

use crate::{
    logic::{self, Formula},
    util,
};
use bimap::BiHashMap;
use hashbrown::{HashMap, HashSet};
// use parking_lot::RwLock;
use slotmap::{new_key_type, SlotMap};
use z3::{ast, AstKind, Config, Context, Solver, Sort};

new_key_type! {
    pub struct FormulaId;
    pub struct Z3AstId;
    // pub struct Z3SortId;
}

#[derive(Debug)]
pub struct Z3State<'ctx> {
    /// Z3 environment for the main solver
    pub env: &'ctx Z3Env<'ctx>,
    /// Mapping from Synquid sorts to Z3 sorts
    pub sorts: HashMap<logic::Sort, z3::Sort<'ctx>>,
    /// AST nodes for scalar variables
    pub vars: HashMap<util::Id, ast::Dynamic<'ctx>>,
    /// Function declarations for measures, predicates, and constructors
    pub functions: HashMap<util::Id, Rc<z3::FuncDecl<'ctx>>>,
    /// Datatypes mapped directly to Z3 datatypes (monomorphic only)
    pub stored_datatypes: HashSet<util::Id>,
    /// Control literals for computing UNSAT cores
    pub control_literals: BiHashMap<Formula, ast::Dynamic<'ctx>>,
    /// Z3 environment for the auxiliary solver
    pub aux_env: &'ctx Z3Env<'ctx>,
    /// Boolean sort in the auxiliary solver
    pub bool_sort_aux: Option<z3::Sort<'ctx>>,
    /// Control literals for computing UNSAT cores in the auxiliary solver
    pub control_literals_aux: BiHashMap<Formula, ast::Dynamic<'ctx>>,
}

impl<'ctx> Z3State<'ctx> {
    pub fn new(env: &'ctx Z3Env) -> Self {
        Self {
            env,
            sorts: HashMap::new(),
            vars: HashMap::new(),
            functions: HashMap::new(),
            stored_datatypes: HashSet::new(),
            control_literals: BiHashMap::new(),
            aux_env: env,
            bool_sort_aux: None,
            control_literals_aux: BiHashMap::new(),
            // formula_map: SlotMap::with_key(),
            // z3_ast_map: SlotMap::with_key(),
            // z3_sort_map: SlotMap::with_key(),
        }
    }

    pub fn ctx(&self) -> &'ctx z3::Context {
        &self.env.context
    }

    pub fn register_z3_ast(&mut self, z3_ast: &dyn ast::Ast<'ctx>) -> ast::Dynamic<'ctx> {
        ast::Dynamic::from_ast(z3_ast)
    }

    // pub fn register_z3_ast(&mut self, z3_ast: &dyn ast::Ast<'ctx>) -> Z3AstId {
    //     self.z3_ast_map.insert(ast::Dynamic::from_ast(z3_ast))
    // }

    // pub fn get_z3_ast(&self, id: Z3AstId) -> &ast::Dynamic<'ctx> {
    //     self.z3_ast_map.get(id).unwrap()
    // }

    // pub fn register_z3_sort(&mut self, z3_sort: z3::Sort<'ctx>) -> Z3SortId {
    //     self.z3_sort_map.insert(z3_sort)
    // }

    // pub fn get_z3_sort(&self, id: Z3SortId) -> &z3::Sort<'ctx> {
    //     self.z3_sort_map.get(id).unwrap()
    // }
}

#[derive(Debug)]
pub struct Z3Env<'ctx> {
    pub solver: z3::Solver<'ctx>,
    pub context: z3::Context,
}

//   isSat fml = do
//       res <- local $ (fmlToAST >=> assert) fml >> check

//       case res of
//         Unsat -> debug 2 (text "SMT CHECK" <+> pretty fml <+> text "UNSAT") $ return False
//         Sat -> debug 2 (text "SMT CHECK" <+> pretty fml <+> text "SAT") $ return True
//         -- _ -> error $ unwords ["isValid: Z3 returned Unknown for", show fml]
//         _ -> debug 2 (text "SMT CHECK" <+> pretty fml <+> text "UNKNOWN treating as SAT") $ return True

pub fn is_sat<'ctx>(fml: &Formula, state: &mut Z3State<'ctx>) -> bool {
    fml.clone().to_ast(state);
    let res = state.env.solver.check();

    match res {
        z3::SatResult::Unsat => {
            log::debug!("SMT CHECK {fml} UNSAT");

            false
        }
        z3::SatResult::Sat => {
            log::debug!("SMT CHECK {fml} SAT");

            true
        }
        _ => {
            log::debug!("SMT CHECK {fml} UNKNOWN treating as SAT");

            true
        }
    }
}

#[derive(Debug)]
pub struct SmtWrapper<'ctx> {
    pub state: &'ctx mut Z3State<'ctx>,
    pub context: &'ctx z3::Context,
}

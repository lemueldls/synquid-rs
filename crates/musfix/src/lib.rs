//! `MARCO` ("`MUSfix`") solver: enumerate all minimal unsatisfiable subsets.
//!
//! Mirrors the `getAllMUSs` algorithm from `Synquid.Z3` (the "Marco
//! algorithm by Mark H. Liffiton et al."), backed by the `MonadSMT`
//! `allUnsatCores` operation of `Synquid.SolverMonad`. The extraction is
//! engine-agnostic: the MARCO control flow lives here while the concrete SMT
//! services (formula→Z3 translation, control-literal cache, solver
//! plumbing) are supplied by the caller through the [`SmtEngine`] trait.
//!
//! Semantics preserved from the reference:
//! - returned cores are in discovery order and contain the *formulas* of `fmls`
//!   (excluding `must_have`, which every returned core nonetheless contains).
//! - the whole loop runs inside one `push`/`pop` per solver;
//!   `minimize`/`maximize` each run inside their own `local`.
//! - `Unknown` from the auxiliary solver is a panic; from the main solver
//!   `minimize`/`maximize` treat it as satisfiable (all idempotent).
//! - the engine-owned control-literal cache persists across calls.

mod marco;

pub use marco::{CheckResult, SmtEngine, get_all_mus};

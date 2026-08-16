//! Command-line interface and synthesis parameters.

use std::str::FromStr;

use crate::error::no_pos;

/// Output format for messages.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum OutputFormat {
    #[default]
    Plain,
    Ansi,
    Html,
}

impl FromStr for OutputFormat {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "plain" => Ok(OutputFormat::Plain),
            "ansi" => Ok(OutputFormat::Ansi),
            "html" => Ok(OutputFormat::Html),
            _ => Err(format!("unknown output format: {s}")),
        }
    }
}

/// What should the termination metric for fixpoints be derived from?
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum FixpointStrategy {
    DisableFixpoint,
    #[default]
    FirstArgument,
    AllArguments,
    Nonterminating,
}

impl FromStr for FixpointStrategy {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "DisableFixpoint" => Ok(FixpointStrategy::DisableFixpoint),
            "FirstArgument" => Ok(FixpointStrategy::FirstArgument),
            "AllArguments" => Ok(FixpointStrategy::AllArguments),
            "Nonterminating" => Ok(FixpointStrategy::Nonterminating),
            _ => Err(format!("unknown fixpoint strategy: {s}")),
        }
    }
}

impl std::fmt::Display for FixpointStrategy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            FixpointStrategy::DisableFixpoint => "DisableFixpoint",
            FixpointStrategy::FirstArgument => "FirstArgument",
            FixpointStrategy::AllArguments => "AllArguments",
            FixpointStrategy::Nonterminating => "Nonterminating",
        };
        f.write_str(s)
    }
}

/// Parameters for template exploration (mirror of `ExplorerParams`).
#[derive(Clone, Debug)]
pub struct ExplorerParams {
    pub e_guess_depth: usize,
    pub scrutinee_depth: usize,
    pub match_depth: usize,
    pub aux_depth: usize,
    pub fix_strategy: FixpointStrategy,
    pub poly_recursion: bool,
    pub pred_poly_recursion: bool,
    pub abduce_scrutinees: bool,
    pub unfold_locals: bool,
    pub partial_solution: bool,
    pub incremental_checking: bool,
    pub consistency_checking: bool,
    pub split_measures: bool,
    pub use_memoization: bool,
    pub symmetry_reduction: bool,
    pub source_pos: crate::error::SourcePos,
    pub explorer_log_level: usize,
}

#[must_use]
pub fn default_explorer_params() -> ExplorerParams {
    ExplorerParams {
        e_guess_depth: 3,
        scrutinee_depth: 1,
        match_depth: 2,
        aux_depth: 1,
        fix_strategy: FixpointStrategy::AllArguments,
        poly_recursion: true,
        pred_poly_recursion: false,
        abduce_scrutinees: true,
        unfold_locals: false,
        partial_solution: false,
        incremental_checking: true,
        consistency_checking: false,
        split_measures: true,
        use_memoization: false,
        symmetry_reduction: false,
        source_pos: no_pos(),
        explorer_log_level: 0,
    }
}

/// How to choose optimal valuations when solving second-order constraints.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OptimalValuationsStrategy {
    BfsValuations,
    MarcoValuations,
}

/// How to pick a candidate in the constraint loop.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CandidatePickStrategy {
    FirstCandidate,
    ValidWeakCandidate,
    InitializedWeakCandidate,
}

/// How to pick the next constraint to solve.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConstraintPickStrategy {
    FirstConstraint,
    SmallSpaceConstraint,
}

/// Parameters for constraint solving (mirror of `HornSolverParams`).
#[derive(Clone, Debug)]
pub struct HornSolverParams {
    pub prune_quals: bool,
    pub is_least_fixpoint: bool,
    pub optimal_valuations_strategy: OptimalValuationsStrategy,
    pub semantic_prune: bool,
    pub aggressive_prune: bool,
    pub candidate_pick_strategy: CandidatePickStrategy,
    pub constraint_pick_strategy: ConstraintPickStrategy,
    pub solver_log_level: usize,
}

#[must_use]
pub const fn default_horn_solver_params() -> HornSolverParams {
    HornSolverParams {
        prune_quals: true,
        is_least_fixpoint: false,
        optimal_valuations_strategy: OptimalValuationsStrategy::MarcoValuations,
        semantic_prune: true,
        aggressive_prune: true,
        candidate_pick_strategy: CandidatePickStrategy::InitializedWeakCandidate,
        constraint_pick_strategy: ConstraintPickStrategy::SmallSpaceConstraint,
        solver_log_level: 0,
    }
}

/// Parameters of the synthesis run (mirror of `SynquidParams`).
#[derive(Clone, Debug)]
pub struct SynquidParams {
    pub goal_filter: Option<Vec<String>>,
    pub output_format: OutputFormat,
    pub resolve_only: bool,
    pub show_spec: bool,
    pub show_stats: bool,
}

#[must_use]
pub const fn default_synquid_params() -> SynquidParams {
    SynquidParams {
        goal_filter: None,
        output_format: OutputFormat::Plain,
        resolve_only: false,
        show_spec: true,
        show_stats: false,
    }
}

/// Flags accepted on the command line.
#[derive(clap::Parser, Debug)]
#[command(
    name = "synquid",
    version = "0.4",
    about = "Synquid program synthesizer",
    long_about = None
)]
pub struct Cli {
    /// Input file
    #[arg(value_name = "FILE")]
    pub file: String,

    /// Additional library files
    #[arg(value_name = "FILES")]
    pub libs: Vec<String>,

    /// Only synthesize the specified functions
    #[arg(long, value_name = "GOAL,...")]
    pub only: Option<String>,

    /// Maximum depth of an application term (default: 3)
    #[arg(short = 'a', long = "app-max", default_value_t = 3, value_name = "INT")]
    pub app_max: u32,

    /// Maximum depth of a match scrutinee (default: 1)
    #[arg(long, default_value_t = 1, value_name = "INT")]
    pub scrutinee_max: u32,

    /// Maximum depth of matches (default: 2)
    #[arg(short = 'm', long, default_value_t = 2, value_name = "INT")]
    pub match_max: u32,

    /// Maximum depth of auxiliary functions (default: 1)
    #[arg(short = 'x', long, default_value_t = 1, value_name = "INT")]
    pub aux_max: u32,

    /// What should the termination metric for fixpoints be derived from?
    #[arg(
        short = 'f',
        long,
        default_value = "FirstArgument",
        value_parser = <FixpointStrategy as FromStr>::from_str
    )]
    pub fix: FixpointStrategy,

    /// Make recursion polymorphic in abstract refinements (default: True in
    /// the Haskell reference despite its help text)
    #[arg(short = 'g', long = "generalize-preds", num_args = 0..=1, default_missing_value = "true", require_equals = true, default_value_t = true, value_parser = parse_bool_flag, action = clap::ArgAction::Set)]
    pub generalize_preds: bool,

    /// Do not abduce match scrutinees (default: False)
    #[arg(short = 'e', long = "explicit-match", num_args = 0..=1, default_missing_value = "true", require_equals = true, default_value_t = false, value_parser = parse_bool_flag, action = clap::ArgAction::Set)]
    pub explicit_match: bool,

    /// Use all variables in match scrutinee abduction (default: False)
    #[arg(short = 'u', long = "unfold-locals", num_args = 0..=1, default_missing_value = "true", require_equals = true, default_value_t = false, value_parser = parse_bool_flag, action = clap::ArgAction::Set)]
    pub unfold_locals: bool,

    /// Generate best-effort partial solutions (default: False)
    #[arg(short = 'p', long, num_args = 0..=1, default_missing_value = "true", require_equals = true, default_value_t = false, value_parser = parse_bool_flag, action = clap::ArgAction::Set)]
    pub partial: bool,

    /// Subtyping checks during bottom-up phase (default: True)
    #[arg(long, num_args = 0..=1, default_missing_value = "true", require_equals = true, default_value_t = true, value_parser = parse_bool_flag, action = clap::ArgAction::Set)]
    pub incremental: bool,

    /// Check incomplete application types for consistency (default: True)
    #[arg(long, num_args = 0..=1, default_missing_value = "true", require_equals = true, default_value_t = true, value_parser = parse_bool_flag, action = clap::ArgAction::Set)]
    pub consistency: bool,

    /// Use memoization (default: False)
    #[arg(short = 'z', long, num_args = 0..=1, default_missing_value = "true", require_equals = true, default_value_t = false, value_parser = parse_bool_flag, action = clap::ArgAction::Set)]
    pub memoize: bool,

    /// Use symmetry reductions (default: False)
    #[arg(short = 's', long, num_args = 0..=1, default_missing_value = "true", require_equals = true, default_value_t = false, value_parser = parse_bool_flag, action = clap::ArgAction::Set)]
    pub symmetry: bool,

    /// Use least fixpoint solver (only works for type checking, default: False)
    #[arg(long, num_args = 0..=1, default_missing_value = "true", require_equals = true, default_value_t = false, value_parser = parse_bool_flag, action = clap::ArgAction::Set)]
    pub lfp: bool,

    /// Use BFS instead of MARCO to solve second-order constraints (default:
    /// False)
    #[arg(long = "bfs-solver", num_args = 0..=1, default_missing_value = "true", require_equals = true, default_value_t = false, value_parser = parse_bool_flag, action = clap::ArgAction::Set)]
    pub bfs_solver: bool,

    /// Resolve only; no type checking or synthesis (default: False)
    #[arg(long, num_args = 0..=1, default_missing_value = "true", require_equals = true, default_value_t = false, value_parser = parse_bool_flag, action = clap::ArgAction::Set)]
    pub resolve: bool,

    /// Generate Haskell output file (default: none)
    #[arg(short = 'o', long = "out-file", value_name = "FILE")]
    pub out_file: Option<String>,

    /// Name of Haskell module to generate (default: from file name)
    #[arg(long = "out-module", value_name = "Name")]
    pub out_module: Option<String>,

    /// Output format: Plain, Ansi or Html (default: Plain)
    #[arg(
        long,
        default_value = "Plain",
        value_parser = <OutputFormat as FromStr>::from_str
    )]
    pub output: OutputFormat,

    /// Show specification of each synthesis goal (default: True)
    #[arg(long = "print-spec", num_args = 0..=1, default_missing_value = "true", require_equals = true, default_value_t = true, value_parser = parse_bool_flag, action = clap::ArgAction::Set)]
    pub print_spec: bool,

    /// Show specification and solution size (default: False)
    #[arg(long = "print-stats", num_args = 0..=1, default_missing_value = "true", require_equals = true, default_value_t = false, value_parser = parse_bool_flag, action = clap::ArgAction::Set)]
    pub print_stats: bool,

    /// Logger verboseness level (default: 0)
    #[arg(short = 'l', long, default_value_t = 0, value_name = "INT")]
    pub log: u8,
}

/// Parse a boolean flag value (`--flag`, `--flag=0`, `--flag=False`, ...).
///
/// Accepts the cmdargs spellings (`0`/`1` and the Haskell `Read` instances
/// `True`/`False`), plus lowercase `true`/`false` as an extension.
fn parse_bool_flag(s: &str) -> Result<bool, String> {
    match s {
        "true" | "True" | "1" => Ok(true),
        "false" | "False" | "0" => Ok(false),
        _ => Err(format!("expected 0/1 or true/false, got {s}")),
    }
}

/// Turn parsed command-line flags into the parameter records used by the
/// pipeline.
///
/// Mirrors the `cmdArgsRun` → `runOnFile` wiring in `Synquid.hs`.
#[must_use]
pub fn cli_to_params(cli: &Cli) -> (SynquidParams, ExplorerParams, HornSolverParams) {
    let explorer_params = ExplorerParams {
        e_guess_depth: cli.app_max as usize,
        scrutinee_depth: cli.scrutinee_max as usize,
        match_depth: cli.match_max as usize,
        aux_depth: cli.aux_max as usize,
        fix_strategy: cli.fix,
        pred_poly_recursion: cli.generalize_preds,
        abduce_scrutinees: !cli.explicit_match,
        unfold_locals: cli.unfold_locals,
        partial_solution: cli.partial,
        incremental_checking: cli.incremental,
        consistency_checking: cli.consistency,
        use_memoization: cli.memoize,
        symmetry_reduction: cli.symmetry,
        explorer_log_level: cli.log as usize,
        ..default_explorer_params()
    };
    let solver_params = HornSolverParams {
        is_least_fixpoint: cli.lfp,
        optimal_valuations_strategy: if cli.bfs_solver {
            OptimalValuationsStrategy::BfsValuations
        } else {
            OptimalValuationsStrategy::MarcoValuations
        },
        solver_log_level: cli.log as usize,
        ..default_horn_solver_params()
    };
    let synquid_params = SynquidParams {
        goal_filter: cli
            .only
            .as_ref()
            .map(|o| o.split(',').map(|s| s.to_string()).collect()),
        output_format: cli.output,
        resolve_only: cli.resolve,
        show_spec: cli.print_spec,
        show_stats: cli.print_stats,
    };
    (synquid_params, explorer_params, solver_params)
}

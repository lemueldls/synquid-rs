//! Entry point for the `synquid` binary.

use std::{fs, process::ExitCode};

use clap::Parser;
use synquid::{
    cli::{Cli, ExplorerParams, HornSolverParams, OutputFormat, SynquidParams, cli_to_params},
    horn_solver::FixPointSolver,
    html,
    parser::parse_program,
    pretty::{
        Doc, Pretty, empty, hsp, parens, plain, pretty_error_msg, pretty_solution, pretty_spec,
        program_node_count, render_pretty, show_doc, text, type_node_count, vsep,
    },
    program::{BareDeclaration, Declaration, Goal, RProgram, unresolved_spec},
    resolver::resolve_decls,
    synthesizer::synthesize,
    types::to_monotype,
};

fn main() -> ExitCode {
    let cli = Cli::parse();
    let (synquid_params, explorer_params, solver_params) = cli_to_params(&cli);
    run_on_file(
        &synquid_params,
        &explorer_params,
        &solver_params,
        &cli.file,
        &cli.libs,
    )
}

/// `printDoc`: render and print a document per the output
/// format.
fn print_doc(format: OutputFormat, d: &Doc) {
    match format {
        OutputFormat::Plain => println!("{}", show_doc(&plain(d))),
        OutputFormat::Ansi => println!("{}", show_doc(d)),
        OutputFormat::Html => print!("{}", html::show_doc_html(&render_pretty(0.4, 100, d))),
    }
}

/// `runOnFile`: parse and resolve file, then synthesize the
/// specified goals.
fn run_on_file(
    synquid_params: &SynquidParams,
    explorer_params: &ExplorerParams,
    solver_params: &HornSolverParams,
    file: &str,
    libs: &[String],
) -> ExitCode {
    let mut inputs = libs.to_vec();
    inputs.push(file.to_string());
    let mut decls: Vec<Declaration> = Vec::new();
    let mut sources = inputs.iter();
    while let Some(src) = sources.next() {
        let is_lib = sources.clone().next().is_some();
        let input = match fs::read_to_string(src) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("synquid-rs: cannot read {src}: {e}");
                return ExitCode::from(1);
            }
        };
        match parse_program(&input, src) {
            Err(parse_err) => {
                print_doc(synquid_params.output_format, &pretty_error_msg(&parse_err));
                print_doc(synquid_params.output_format, &empty());
                return ExitCode::from(1);
            }
            Ok(parsed) => {
                let mut parsed = parsed;
                if is_lib {
                    parsed.retain(|d| !is_synthesis_goal(&d.node));
                }
                decls.extend(parsed);
            }
        }
    }
    match resolve_decls(&decls) {
        Err(resolution_error) => {
            print_doc(
                synquid_params.output_format,
                &pretty_error_msg(&resolution_error),
            );
            print_doc(synquid_params.output_format, &empty());
            ExitCode::from(1)
        }
        Ok((goals, cquals, tquals)) => {
            if synquid_params.resolve_only {
                return ExitCode::SUCCESS;
            }
            let requested: Vec<&Goal> = match &synquid_params.goal_filter {
                Some(filt) => goals.iter().filter(|g| filt.contains(&g.g_name)).collect(),
                None => goals.iter().collect(),
            };
            let mut results: Vec<(Goal, RProgram)> = Vec::new();
            for goal in &requested {
                match synthesize_goal(
                    synquid_params,
                    explorer_params,
                    solver_params,
                    goal,
                    &cquals,
                    &tquals,
                ) {
                    Err(e) => {
                        print_doc(synquid_params.output_format, &pretty_error_msg(&e));
                        print_doc(synquid_params.output_format, &empty());
                        return ExitCode::from(1);
                    }
                    Ok(prog) => {
                        if goal.g_synthesize {
                            // `pdoc (prettySolution goal prog) >> pdoc empty`
                            //: solution followed by a blank
                            // line.
                            print_doc(synquid_params.output_format, &pretty_solution(goal, &prog));
                            print_doc(synquid_params.output_format, &empty());
                        }
                        results.push(((*goal).clone(), prog));
                    }
                }
            }
            if synquid_params.show_stats && !results.is_empty() {
                print_stats(synquid_params.output_format, &results);
            }
            ExitCode::SUCCESS
        }
    }
}

/// `synthesizeGoal`.
fn synthesize_goal(
    synquid_params: &SynquidParams,
    explorer_params: &ExplorerParams,
    solver_params: &HornSolverParams,
    goal: &Goal,
    cquals: &[synquid::logic::Formula],
    tquals: &[synquid::logic::Formula],
) -> Result<RProgram, synquid::error::ErrorMessage> {
    if goal.g_synthesize && synquid_params.show_spec {
        print_doc(synquid_params.output_format, &pretty_spec(goal));
    }
    let mut horn = FixPointSolver::init_horn_solver(&goal.g_environment, solver_params);
    synthesize(
        explorer_params,
        solver_params,
        goal,
        cquals,
        tquals,
        &mut horn,
    )
}

/// `printStats`.
fn print_stats(format: OutputFormat, results: &[(Goal, RProgram)]) {
    let env = &results[0].0.g_environment;
    let measure_count = env.measures.len();
    let spec_size: usize = results
        .iter()
        .map(|(g, _)| type_node_count(&to_monotype(&unresolved_spec(g))))
        .sum();
    let solution_size: usize = results.iter().map(|(_, p)| program_node_count(p)).sum();
    let stats = vsep(vec![
        parens(hsp(text("Goals:"), results.len().pretty())),
        parens(hsp(text("Measures:"), measure_count.pretty())),
        parens(hsp(text("Spec size:"), spec_size.pretty())),
        parens(hsp(text("Solution size:"), solution_size.pretty())),
    ]);
    print_doc(format, &stats);
}

const fn is_synthesis_goal(d: &BareDeclaration) -> bool {
    matches!(d, BareDeclaration::SynthesisGoal(..))
}

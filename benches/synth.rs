//! Benchmark the end-to-end `synthesize` hot path on representative pldi16
//! benchmarks (mirrors `cargo run --release -- specs/test/pldi16/<N>.sq`).
//!
//! Run with: `cargo bench --bench synth -- --nocapture`

use std::fs;

use criterion::{Criterion, criterion_group, criterion_main};
use synquid::{
    cli::{default_explorer_params, default_horn_solver_params},
    horn_solver::FixPointSolver,
    parser::parse_program,
    resolver::resolve_decls,
    synthesizer::synthesize,
};

fn synth_file(name: &str) {
    let src = fs::read_to_string(format!("specs/test/pldi16/{name}.sq")).unwrap();
    let decls = parse_program(&src, name).unwrap();
    let (goals, cquals, tquals) = resolve_decls(&decls).unwrap();
    let goal = &goals[0];
    let explorer_params = default_explorer_params();
    let solver_params = default_horn_solver_params();
    let mut horn = FixPointSolver::init_horn_solver(&goal.g_environment, &solver_params);
    let _ = synthesize(
        &explorer_params,
        &solver_params,
        goal,
        &cquals,
        &tquals,
        &mut horn,
    )
    .unwrap();
}

fn bench_synth(c: &mut Criterion) {
    let mut group = c.benchmark_group("synth");
    group.sample_size(10);
    for name in ["List-Null", "List-Replicate", "BST-Member"] {
        group.bench_function(name, |b| b.iter(|| synth_file(name)));
    }
    group.finish();
}

criterion_group!(benches, bench_synth);
criterion_main!(benches);

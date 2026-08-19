use std::fs;

use synquid::{pretty::show_doc, resolver::resolve_decls};

/// Path of a fixture under the workspace root (this crate's tests run with
/// the package manifest dir as CWD).
fn repo_root() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

#[test]
fn resolves_all_pldi16_benchmarks() {
    let dir = fs::read_dir(repo_root().join("specs/test/pldi16"))
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().map_or(false, |x| x == "sq"))
        .collect::<Vec<_>>();
    assert_eq!(dir.len(), 64, "expected 64 pldi16 benchmark files");
    for path in dir {
        let file = path.file_name().unwrap().to_string_lossy().into_owned();
        let src = fs::read_to_string(&path).unwrap_or_else(|e| panic!("{file}: read: {e}"));
        let decls = synquid::parser::parse_program(&src, &file).unwrap_or_else(|e| {
            panic!(
                "{file}: parse: {} at {}:{}",
                show_doc(&e.description),
                e.position.line,
                e.position.column
            )
        });
        let (goals, ..) = resolve_decls(&decls).unwrap_or_else(|e| {
            panic!(
                "{file}: resolve: {} at {}:{}",
                show_doc(&e.description),
                e.position.line,
                e.position.column
            )
        });
        assert!(!goals.is_empty(), "{file}: no goals");
        assert!(
            goals.iter().any(|g| g.g_synthesize),
            "{file}: no synthesis goal"
        );
    }
}

#[test]
fn resolves_list_append_to_expected_goals() {
    let src = fs::read_to_string(repo_root().join("specs/test/pldi16/List-Append.sq")).unwrap();
    let decls = synquid::parser::parse_program(&src, "List-Append.sq").unwrap();
    let (goals, ..) = resolve_decls(&decls).unwrap();
    let synth = goals.iter().filter(|g| g.g_synthesize).collect::<Vec<_>>();
    assert_eq!(synth.len(), 1, "expected exactly one synthesis goal");
    assert_eq!(synth[0].g_name, "append");
    let checked = goals.iter().filter(|g| !g.g_synthesize).collect::<Vec<_>>();
    assert_eq!(checked.len(), 1, "expected one measure checking goal");
    assert_eq!(checked[0].g_name, "len");
}

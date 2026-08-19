use std::fs;

use synquid::pretty::show_doc;

/// Path of a fixture under the workspace root (this crate's tests run with
/// the package manifest dir as CWD).
fn repo_root() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

#[test]
fn parses_all_pldi16_benchmarks() {
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
                "{file}: {} at {}:{}",
                show_doc(&e.description),
                e.position.line,
                e.position.column
            )
        });
        assert!(!decls.is_empty(), "{file}: no declarations");
    }
}

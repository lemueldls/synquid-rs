use std::io::Cursor;

use tree_sitter::{Node, Parser, TreeCursor};

use crate::{
    error::Pos,
    program::{BareDeclaration, Declaration},
};

#[test]
fn parse() {
    let code = std::fs::read_to_string("test.sq").unwrap();

    let mut parser = Parser::new();
    parser
        .set_language(&tree_sitter_synquid::language())
        .expect("Error loading Synquid grammar");

    let tree = parser.parse(&code, None).unwrap();
    // assert!(!tree.root_node().has_error());

    let root = tree.root_node();
    let mut cursor = root.walk();

    dbg!(to_ast(&code, root, &mut cursor));
}

// pub fn to_ast(code: &str, tree: tree_sitter::Tree) -> Vec<Declaration> {
pub fn to_ast<'tree>(
    code: &str,
    node: Node<'tree>,
    cursor: &mut TreeCursor<'tree>,
) -> Vec<Declaration> {
    let mut defs = Vec::new();

    // let decl = Pos {
    //     position: todo!(),
    //     node: bare_decl,
    // }

    for child in node.children(cursor) {
        let def = match child.kind() {
            "comment" => continue,
            "declarations" => {
                let mut cursor = child.walk();
                let children = child.children(&mut cursor);

                for child in children {
                    match child.kind() {
                        "type_synomym" => {
                            dbg!(child.to_sexp());
                        }
                        kind => todo!("{kind}"),
                    }
                }
            }
            _ => unreachable!(),
        };

        // defs.push(def);
    }

    defs
}

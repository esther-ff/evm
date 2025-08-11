pub mod def;
pub mod lowering_ast;
pub mod name_resolution;
pub mod node;
pub mod visitor;

pub use name_resolution::{LateResolver, ThingDefResolver};

use crate::ast::Visitor;
use crate::session::Session;

pub fn lower_universe<'hir>(sess: &'hir Session<'hir>, ast: &crate::ast::Universe) {
    let mut first_pass = ThingDefResolver::new();
    for decl in &ast.thingies {
        first_pass.visit_thing(decl);
    }

    let mut inner = LateResolver::new(first_pass, ast);
    for decl in &ast.thingies {
        inner.visit_thing(decl);
    }

    // dbg!(ast);

    let mappings = inner.into_mappings();

    for (id, res) in mappings.debug_resolutions() {
        println!("{id:?} resolves to: {res:?}");
    }

    let mut ast_lowerer = lowering_ast::AstLowerer::new(mappings, sess);

    let hir = ast_lowerer.lower_universe(ast);
    println!("hir: \n{hir:#?}");
    println!("hir bodies:\n");
    sess.hir(|map| {
        dbg!(map.bodies());
        for (ix, body) in map.bodies().iter().enumerate() {
            println!("body({ix}): {body:#?}");
        }
    });
}

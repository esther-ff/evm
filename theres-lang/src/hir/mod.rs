pub mod def;
pub mod lowering_ast;
pub mod map_builder;
pub mod name_resolution;
pub mod node;
pub mod visitor;
pub use name_resolution::{LateResolver, ThingDefResolver};

use crate::ast::Visitor;
use crate::hir::node::Universe;
use crate::hir::visitor::HirVisitor;
use crate::session::Session;

pub fn lower_universe<'hir>(
    sess: &'hir Session<'hir>,
    ast: &crate::ast::Universe,
) -> &'hir Universe<'hir> {
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

    let hir_universe = ast_lowerer.lower_universe(ast);
    sess.hir(|hir| map_builder::MapBuilder::new(hir).visit_universe(hir_universe));
    println!("hir: \n{hir_universe:#?}");
    println!("hir bodies:\n");
    sess.hir(|map| {
        for (ix, body) in map.bodies().iter().enumerate() {
            println!("body({ix}): {body:#?}");
        }

        for (ix, node) in map.nodes().into_iter().enumerate() {
            println!("node({ix}): \n{node:#?}")
        }
    });

    hir_universe
}

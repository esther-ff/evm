pub mod check;
pub mod def;
pub mod lowering_ast;
pub mod map_builder;
pub mod name_resolution;
pub mod node;
pub mod visitor;
pub use name_resolution::{LateResolver, ThingDefResolver};

use crate::ast::Visitor;
use crate::driver::HirDump;
use crate::hir::def::DefId;
use crate::hir::node::Universe;
use crate::hir::visitor::HirVisitor;
use crate::session::Session;

pub fn lower_universe<'hir>(
    sess: &'hir Session<'hir>,
    ast: &crate::ast::Universe,
) -> (&'hir Universe<'hir>, Option<DefId>) {
    let mut first_pass = ThingDefResolver::new();
    for decl in &ast.thingies {
        first_pass.visit_thing(decl);
    }

    let mut inner = LateResolver::new(first_pass, ast);
    for decl in &ast.thingies {
        inner.visit_thing(decl);
    }

    let mappings = inner.into_mappings();
    let entry = mappings.entry_point();

    let mut ast_lowerer = lowering_ast::AstLowerer::new(mappings, sess);

    let hir_universe = ast_lowerer.lower_universe(ast);
    sess.hir_mut(|hir| map_builder::MapBuilder::new(hir).visit_universe(hir_universe));

    match sess.dump_hir_mode() {
        HirDump::All => {
            println!("--- HIR tree dump --- \n{hir_universe:#?}\n --- HIR tree dump ---\n",);
            println!("--- HIR body dump ---");

            sess.hir(|map| {
                for (ix, body) in map.bodies().iter().enumerate() {
                    println!("body({ix}): \n{body:#?}");
                }
            });

            println!("--- HIR body dump ---\n");
        }

        HirDump::OnlyItems => {
            println!("--- HIR tree dump --- \n{hir_universe:#?}\n --- HIR tree dump ---\n",);
        }

        HirDump::None => {}
    }

    (hir_universe, entry)
}

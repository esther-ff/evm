pub mod check;
pub mod def;
pub mod node;
pub mod visitor;

mod lowering_ast;
mod map_builder;
mod name_res;
mod passes;

use crate::ast::Universe;
use crate::driver::HirDump;
use crate::hir::node::Universe as HirUniverse;
use crate::hir::visitor::HirVisitor;
use crate::session::Session;
pub use lowering_ast::{HirId, HirIdMap, HirMap, Mappings};

pub fn lower_universe<'hir>(sess: &'hir Session<'hir>, ast: &Universe) -> &'hir HirUniverse<'hir> {
    let mappings = name_res::resolve(sess, ast);
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

    hir_universe
}

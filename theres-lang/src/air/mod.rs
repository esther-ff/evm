pub mod check;
pub mod def;
pub mod node;
pub mod visitor;

mod lowering_ast;
mod map_builder;
mod name_res;
mod passes;

use crate::air::node::Universe as AirUniverse;
use crate::air::visitor::AirVisitor;
use crate::ast::Universe;
use crate::driver::HirDump;
use crate::session::Session;
pub use lowering_ast::{AirId, AirIdMap, AirMap, Mappings};

pub fn lower_universe<'air>(sess: &'air Session<'air>, ast: &Universe) -> &'air AirUniverse<'air> {
    let mappings = name_res::resolve(sess, ast);
    let mut ast_lowerer = lowering_ast::AstLowerer::new(mappings, sess);

    let air_universe = ast_lowerer.lower_universe(ast);
    sess.air_mut(|air| map_builder::MapBuilder::new(air).visit_universe(air_universe));

    match sess.dump_air_mode() {
        HirDump::All => {
            println!("--- air tree dump --- \n{air_universe:#?}\n --- air tree dump ---\n",);
            println!("--- air body dump ---");

            sess.air(|map| {
                for (ix, body) in map.bodies().iter().enumerate() {
                    println!("body({ix}): \n{body:#?}");
                }
            });

            println!("--- air body dump ---\n");
        }

        HirDump::OnlyItems => {
            println!("--- air tree dump --- \n{air_universe:#?}\n --- air tree dump ---\n",);
        }

        HirDump::None => {}
    }

    air_universe
}

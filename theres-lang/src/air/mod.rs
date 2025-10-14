pub mod check;
pub mod def;
pub mod node;
pub mod passes;
pub mod visitor;

mod lowering_ast;
mod map_builder;
mod name_res;

pub use lowering_ast::{AirId, AirIdMap, AirMap, Mappings};

use crate::air::node::Universe as AirUniverse;
use crate::air::visitor::AirVisitor;
use crate::ast::Universe;
use crate::driver::HirDump;
use crate::session::Session;
use std::mem;

pub fn lower_universe<'air>(sess: &'air Session<'air>, ast: &Universe) -> &'air AirUniverse<'air> {
    let mut mappings = name_res::resolve(sess, ast);
    let deftypes = mem::take(&mut mappings.def_types);
    let mut air_builder = lowering_ast::AirBuilder::new(mappings, sess);

    let air_universe = air_builder.lower_universe(ast);
    sess.air_mut(|air| {
        map_builder::MapBuilder::new(air).visit_universe(air_universe);
        air.def_types = deftypes;
    });

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

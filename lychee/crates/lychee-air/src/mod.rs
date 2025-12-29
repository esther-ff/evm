pub mod check;
pub mod def;
pub mod node;
pub mod passes;
pub mod visitor;

mod lowering_ast;
mod map_builder;
mod name_res;

pub use lowering_ast::{AirId, AirMap, Mappings};

use crate::air::node::Universe as AirUniverse;
use crate::air::visitor::AirVisitor;
use crate::arena::Arena;
use crate::ast::Universe;
use crate::driver::HirDump;
use crate::errors::DiagEmitter;
use std::mem;

pub fn lower_universe<'air>(
    arena: &'air Arena,
    diag: &'air DiagEmitter<'air>,
    ast: &Universe,
) -> (&'air AirUniverse<'air>, AirMap<'air>) {
    let mut mappings = name_res::resolve(diag, ast);
    let deftypes = mem::take(&mut mappings.def_types);
    let air_builder = lowering_ast::AirBuilder::new(mappings, arena);

    let (air_universe, mut air_map) = air_builder.lower_universe(ast);
    map_builder::MapBuilder::new(&mut air_map).visit_universe(air_universe);
    air_map.def_types = deftypes;

    (air_universe, air_map)
}

pub fn dump_air(
    w: &mut dyn std::io::Write,
    mode: HirDump,
    air_universe: &AirUniverse<'_>,
    map: &AirMap<'_>,
) -> std::io::Result<()> {
    match mode {
        HirDump::All => {
            writeln!(
                w,
                "--- air tree dump --- \n{air_universe:#?}\n --- air tree dump ---\n",
            )?;
            writeln!(w, "--- air body dump ---")?;

            for (ix, body) in map.bodies().iter().enumerate() {
                writeln!(w, "body({ix}): \n{body:#?}")?;
            }

            writeln!(w, "--- air body dump ---\n")
        }

        HirDump::OnlyItems => {
            writeln!(
                w,
                "--- air tree dump --- \n{air_universe:#?}\n --- air tree dump ---\n",
            )
        }

        HirDump::None => Ok(()),
    }
}

pub mod lowering_ast;
pub mod name_res;
pub mod node;
pub mod visitor;

mod map_builder;
use crate::lowering_ast::AirMap;
use crate::node::Universe as AirUniverse;
use crate::visitor::AirVisitor;
use lychee_ast::Universe;
use lychee_util::arena::Arena;
use lychee_util::errors::DiagEmitter;
use lychee_util::flags::HirDump;
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
        HirDump::WithBodies => {
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

        HirDump::Simple => {
            writeln!(
                w,
                "--- air tree dump --- \n{air_universe:#?}\n --- air tree dump ---\n",
            )
        }

        HirDump::None => Ok(()),
    }
}

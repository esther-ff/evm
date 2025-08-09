pub mod def;
pub mod expr;
pub mod lowering_ast;
pub mod name_resolution;
pub mod node;

pub use name_resolution::{LateResolver, ThingDefResolver};

use crate::ast::Visitor;
use crate::session::Session;

pub fn lower_universe<'hir>(sess: &'hir Session<'hir>, ast: &crate::ast::Universe) {
    let mut first_pass = ThingDefResolver::new(ast);
    for decl in &ast.thingies {
        first_pass.visit_thing(decl);
    }

    let mut inner = LateResolver::new(first_pass);
    for decl in &ast.thingies {
        inner.visit_thing(decl);
    }

    for (id, res) in inner.res_map() {
        println!("ast id of res: {id:?} -> resolved as: {res:?}",);
    }

    let _ast_lowerer = lowering_ast::AstLowerer::new(inner.into_mappings(), sess);
}

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
use crate::ty::TyKind;

pub struct TyTest<'a> {
    s: &'a Session<'a>,
}

impl visitor::HirVisitor<'_> for TyTest<'_> {
    type Result = ();

    fn visit_ty(&mut self, ty: &node::Ty<'_>) {
        let ty = self.s.lower_ty(ty);
        println!("ty: {}", self.s.stringify_ty(ty));

        if let TyKind::Instance(def) = *ty {
            for field in def.fields {
                let ty = self.s.def_type_of(field.def_id);
                println!("   field ty: {}", self.s.stringify_ty(ty));
            }
        }
    }

    fn visit_local(&mut self, local: &node::Local<'_>) -> Self::Result {
        let node::Local {
            mutability: _,
            name: _,
            init,
            ty,
            hir_id: _,
        } = local;

        let _ = init.map(|expr| self.visit_expr(expr));
        self.visit_ty(ty);
    }

    fn visit_fn_sig(&mut self, fn_sig: &node::FnSig<'_>) -> Self::Result {
        let node::FnSig {
            span: _,
            return_type,
            arguments,
            body,
        } = fn_sig;

        self.visit_ty(return_type);

        for param in *arguments {
            self.visit_param(param);
        }

        self.visit_expr(self.s.hir(|x| x.get_body(*body)));
    }
}

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
    sess.hir_mut(|hir| map_builder::MapBuilder::new(hir).visit_universe(hir_universe));
    // println!("hir: \n{hir_universe:#?}");

    // println!("hir bodies:\n");
    // sess.hir(|map| {
    //     for (ix, body) in map.bodies().iter().enumerate() {
    //         println!("body({ix}): {body:#?}");
    //     }
    // });

    let mut test = TyTest { s: sess };

    test.visit_universe(hir_universe);

    hir_universe
}

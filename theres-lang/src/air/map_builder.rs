use crate::air::lowering_ast::AirMap;
use crate::air::node::{self, Expr, Field, Node, Param, Path, Stmt, StmtKind, Thing, Ty};
use crate::air::visitor::{AirVisitor, walk_expr, walk_thing, walk_ty};

pub struct MapBuilder<'map, 'air>
where
    'air: 'map,
{
    m: &'map mut AirMap<'air>,
}

impl<'air, 'map> MapBuilder<'map, 'air>
where
    'air: 'map,
{
    pub fn new(m: &'map mut AirMap<'air>) -> Self {
        Self { m }
    }
}

impl<'air> AirVisitor<'air> for MapBuilder<'_, 'air> {
    type Result = ();

    // fn visit_universe(&mut self, universe: &'air Universe<'air>) -> Self::Result {
    //     let Universe {
    //         air_id: _,
    //         things,
    //         span: _,
    //     } = universe;

    //     visit_iter!(v: self, m: visit_thing, *things);
    // }

    fn visit_thing(&mut self, thing: &'air Thing<'air>) -> Self::Result {
        self.m.insert_node(Node::Thing(thing), thing.air_id);
        walk_thing(self, thing)
    }

    fn visit_bind_item(&mut self, bind_item: &'air node::BindItem<'air>) -> Self::Result {
        self.m
            .insert_node(Node::BindItem(bind_item), bind_item.air_id);

        match bind_item.kind {
            node::BindItemKind::Fun { sig, name: _ } => self.visit_fn_sig(sig),
            node::BindItemKind::Const { ty, expr, sym: _ } => {
                self.visit_ty(ty);
                self.visit_expr(expr);
            }
        }
    }

    // fn visit_fn_sig(&mut self, fn_sig: &'air FnSig<'air>) -> Self::Result {
    //     self.visit_ty(fn_sig.return_type);
    //     visit_iter!(v: self, m: visit_param, fn_sig.arguments);
    //     self.visit_expr(self.m.get_body(fn_sig.body));
    // }

    fn visit_param(&mut self, param: &'air Param<'air>) -> Self::Result {
        self.visit_ty(param.ty);
        self.m.insert_node(Node::FnParam(param), param.air_id);
    }

    fn visit_field(&mut self, field: &'air Field<'air>) -> Self::Result {
        self.visit_ty(field.ty);

        self.m.insert_node(Node::Field(field), field.air_id);
    }

    fn visit_ty(&mut self, ty: &'air Ty<'air>) -> Self::Result {
        self.m.insert_node(Node::Ty(ty), ty.air_id);

        walk_ty(self, ty)
    }

    fn visit_path(&mut self, path: &'air Path<'air>) -> Self::Result {
        self.m.insert_node(Node::Path(path), path.air_id);
    }

    fn visit_expr(&mut self, expr: &'air Expr<'air>) -> Self::Result {
        self.m.insert_node(Node::Expr(expr), expr.air_id);

        walk_expr(self, expr)
    }

    fn visit_stmt(&mut self, stmt: &'air Stmt<'air>) -> Self::Result {
        self.m.insert_node(Node::Stmt(stmt), stmt.air_id);

        match stmt.kind {
            StmtKind::Local(local) => self.visit_local(local),
            StmtKind::Expr(expr) => self.visit_expr(expr),
            StmtKind::Thing(thing) => self.visit_thing(thing),
        }
    }

    fn visit_local(&mut self, local: &'air node::Local<'air>) -> Self::Result {
        self.m.insert_node(Node::Local(local), local.air_id);

        self.visit_ty(local.ty);
        if let Some(expr) = local.init {
            self.visit_expr(expr);
        }
    }
}

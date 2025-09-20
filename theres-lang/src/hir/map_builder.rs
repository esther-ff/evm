use crate::hir::lowering_ast::HirMap;
use crate::hir::node::{
    self, Expr, ExprKind, Field, FnSig, Node, Param, Path, Stmt, StmtKind, Thing, ThingKind, Ty,
    TyKind, Universe,
};
use crate::hir::visitor::HirVisitor;
use crate::visitor_common::VisitorResult;
use crate::{maybe_visit, try_visit, visit_iter};

pub struct MapBuilder<'map, 'hir>
where
    'hir: 'map,
{
    m: &'map mut HirMap<'hir>,
}

impl<'hir, 'map> MapBuilder<'map, 'hir>
where
    'hir: 'map,
{
    pub fn new(m: &'map mut HirMap<'hir>) -> Self {
        Self { m }
    }
}

impl<'hir> HirVisitor<'hir> for MapBuilder<'_, 'hir> {
    type Result = ();

    fn visit_universe(&mut self, universe: &'hir Universe<'hir>) -> Self::Result {
        let Universe {
            hir_id: _,
            things,
            span: _,
        } = universe;

        visit_iter!(v: self, m: visit_thing, *things);
    }

    fn visit_thing(&mut self, thing: &'hir Thing<'hir>) -> Self::Result {
        let Thing {
            kind,
            span: _,
            hir_id,
            def_id: _,
        } = thing;

        self.m.insert_node(Node::Thing(thing), *hir_id);

        match kind {
            ThingKind::Fn { name: _, sig } => self.visit_fn_sig(sig),
            ThingKind::Instance {
                fields,
                name: _,
                ctor_id: _,
            } => {
                visit_iter!(v: self, m: visit_field, *fields);
            }
            ThingKind::Realm { name: _, things } => visit_iter!(v: self, m: visit_thing, *things),
            ThingKind::Global {
                mutability: _,
                name: _,
                init,
                ty,
            } => try_visit!(self.visit_ty(ty), self.visit_expr(init)),
            ThingKind::Bind(node::Bind {
                with,
                items,
                mask: _,
            }) => try_visit!(
                self.visit_ty(with),
                visit_iter!(v: self, m: visit_bind_item, *items)
            ),
        }
    }

    fn visit_bind_item(&mut self, bind_item: &'hir node::BindItem<'hir>) -> Self::Result {
        self.m
            .insert_node(Node::BindItem(bind_item), bind_item.hir_id);

        match bind_item.kind {
            node::BindItemKind::Fun { sig, name: _ } => self.visit_fn_sig(sig),
            node::BindItemKind::Const { ty, expr, sym: _ } => {
                self.visit_ty(ty);
                self.visit_expr(expr);
            }
        }
    }

    fn visit_fn_sig(&mut self, fn_sig: &'hir FnSig<'hir>) -> Self::Result {
        self.visit_ty(fn_sig.return_type);
        visit_iter!(v: self, m: visit_param, fn_sig.arguments);
        self.visit_expr(self.m.get_body(fn_sig.body));
    }

    fn visit_param(&mut self, param: &'hir Param<'hir>) -> Self::Result {
        self.visit_ty(param.ty);
        self.m.insert_node(Node::FnParam(param), param.hir_id);
    }

    fn visit_field(&mut self, field: &'hir Field<'hir>) -> Self::Result {
        self.visit_ty(field.ty);

        self.m.insert_node(Node::Field(field), field.hir_id);
    }

    fn visit_ty(&mut self, ty: &'hir Ty<'hir>) -> Self::Result {
        self.m.insert_node(Node::Ty(ty), ty.hir_id);

        match ty.kind {
            TyKind::MethodSelf | TyKind::Err => (),
            TyKind::Array(ty) => self.visit_ty(ty),
            TyKind::Path(path) => self.visit_path(path),
        }
    }

    fn visit_path(&mut self, path: &'hir Path<'hir>) -> Self::Result {
        self.m.insert_node(Node::Path(path), path.hir_id);
    }

    fn visit_expr(&mut self, expr: &'hir Expr<'hir>) -> Self::Result {
        self.m.insert_node(Node::Expr(expr), expr.hir_id);

        let Expr {
            kind,
            span: _,
            hir_id: _,
        } = expr;

        match kind {
            ExprKind::Binary { lhs, rhs, op: _ } => {
                try_visit!(self.visit_expr(lhs), self.visit_expr(rhs));
            }

            ExprKind::Unary { target, op: _ } => self.visit_expr(target),

            ExprKind::Assign { variable, value }
            | ExprKind::AssignWithOp {
                variable,
                value,
                op: _,
            } => {
                try_visit!(self.visit_expr(variable), self.visit_expr(value));
            }

            ExprKind::Call { function, args } => {
                try_visit!(
                    self.visit_expr(function),
                    visit_iter!(v: self, m: visit_expr, *args)
                );
            }

            ExprKind::MethodCall {
                receiver,
                method: _,
                args,
            } => try_visit!(
                self.visit_expr(receiver),
                visit_iter!(v: self, m: visit_expr, *args)
            ),

            ExprKind::Block(block) => self.visit_block(block),

            ExprKind::If {
                condition,
                block,
                else_,
            } => {
                try_visit!(self.visit_expr(condition), self.visit_block(block));
                maybe_visit!(v: self, m: visit_expr, else_);
            }

            ExprKind::Return { expr } => maybe_visit!(v: self, m: visit_expr, expr),

            ExprKind::Field { src, field: _ } => self.visit_expr(src),

            ExprKind::Loop { body, reason: _ } => self.visit_block(body),

            ExprKind::Index {
                index,
                indexed_thing,
            } => try_visit!(self.visit_expr(index), self.visit_expr(indexed_thing)),

            ExprKind::CommaSep(exprs) | ExprKind::List(exprs) => {
                visit_iter!(v: self, m: visit_expr, *exprs);
            }

            ExprKind::Path(path) => self.visit_path(path),

            ExprKind::Literal(..) | ExprKind::Break => Self::Result::normal(),
        }
    }

    fn visit_stmt(&mut self, stmt: &'hir Stmt<'hir>) -> Self::Result {
        self.m.insert_node(Node::Stmt(stmt), stmt.hir_id);

        match stmt.kind {
            StmtKind::Local(local) => self.visit_local(local),
            StmtKind::Expr(expr) => self.visit_expr(expr),
            StmtKind::Thing(thing) => self.visit_thing(thing),
        }
    }

    fn visit_local(&mut self, local: &'hir node::Local<'hir>) -> Self::Result {
        self.m.insert_node(Node::Local(local), local.hir_id);

        self.visit_ty(local.ty);
        if let Some(expr) = local.init {
            self.visit_expr(expr);
        }
    }
}

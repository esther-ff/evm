use crate::{
    hir::{
        def::Resolved,
        lowering_ast::HirId,
        node::{
            self, BindItem, BindItemKind, Block, Expr, ExprKind, Field, FnSig, Local, Param, Path,
            Stmt, StmtKind, Thing, ThingKind, Ty, TyKind, Universe,
        },
    },
    maybe_visit, try_visit, visit_iter,
};

use crate::visitor_common::VisitorResult;

pub trait HirVisitor<'hir> {
    type Result: VisitorResult;

    fn visit_universe(&mut self, universe: &'hir Universe<'hir>) -> Self::Result {
        let Universe {
            hir_id: _,
            things,
            span: _,
        } = universe;

        for thing in *things {
            self.visit_thing(thing);
        }

        Self::Result::normal()
    }

    fn visit_thing(&mut self, thing: &'hir Thing<'hir>) -> Self::Result {
        let Thing {
            kind,
            span: _,
            hir_id: _,
            def_id: _,
        } = thing;
        match kind {
            ThingKind::Fn { name: _, sig } => self.visit_fn_sig(sig),
            ThingKind::Instance {
                fields,
                name: _,
                ctor_id: _,
            } => {
                visit_iter!(v: self, m: visit_field, *fields)
            }
            ThingKind::Realm { name: _, things } => visit_iter!(v: self, m: visit_thing, *things),
            ThingKind::Global {
                mutability: _,
                name: _,
                init,
                ty,
            } => {
                try_visit!(self.visit_ty(ty));
                self.visit_expr(init)
            }
            ThingKind::Bind(node::Bind {
                with,
                mask: _,
                items,
            }) => {
                try_visit!(self.visit_ty(with));
                visit_iter!(v: self, m: visit_bind_item, *items)
            }
        };

        Self::Result::normal()
    }

    fn visit_bind_item(&mut self, bind_item: &'hir BindItem<'hir>) -> Self::Result {
        let BindItem {
            hir_id: _,
            span: _,
            kind,
            def_id: _,
        } = bind_item;

        match kind {
            BindItemKind::Fun { sig, name: _ } => self.visit_fn_sig(sig),
            BindItemKind::Const { ty, expr, sym: _ } => {
                try_visit!(self.visit_ty(ty));
                self.visit_expr(expr)
            }
        }
    }

    fn visit_fn_sig(&mut self, fn_sig: &'hir FnSig<'hir>) -> Self::Result {
        let FnSig {
            span: _,
            return_type,
            arguments,
            body: _,
        } = fn_sig;

        try_visit!(self.visit_ty(return_type));

        visit_iter!(v: self, m: visit_param, *arguments)
    }

    fn visit_param(&mut self, param: &'hir Param<'hir>) -> Self::Result {
        let Param {
            name: _,
            ty,
            hir_id: _,
        } = param;
        self.visit_ty(ty)
    }

    fn visit_field(&mut self, field: &'hir Field<'hir>) -> Self::Result {
        let Field {
            mutability: _,
            name: _,
            span: _,
            hir_id: _,
            def_id: _,
            ty,
        } = field;

        self.visit_ty(ty)
    }

    fn visit_ty(&mut self, ty: &'hir Ty<'hir>) -> Self::Result {
        let Ty {
            span: _,
            hir_id: _,
            kind,
        } = ty;

        match kind {
            TyKind::MethodSelf | TyKind::Err => Self::Result::normal(),
            TyKind::Array(ty) => self.visit_ty(ty),
            TyKind::Path(path) => self.visit_path(path),
        }
    }

    fn visit_path(&mut self, path: &'hir Path<'hir>) -> Self::Result {
        let Path {
            res,
            segments: _,
            span: _,
            hir_id: _,
        } = path;

        self.visit_resolved(res)
    }

    fn visit_resolved(&mut self, _res: &'hir Resolved<HirId>) -> Self::Result {
        Self::Result::normal()
    }

    fn visit_block(&mut self, block: &'hir Block<'hir>) -> Self::Result {
        let Block {
            stmts,
            expr,
            span: _,
            hir_id: _,
        } = block;

        visit_iter!(v: self, m: visit_stmt, *stmts);
        maybe_visit!(v: self, m: visit_expr, expr)
    }

    fn visit_stmt(&mut self, stmt: &'hir Stmt<'hir>) -> Self::Result {
        let Stmt {
            span: _,
            kind,
            hir_id: _,
        } = stmt;

        match kind {
            StmtKind::Local(local) => self.visit_local(local),
            StmtKind::Expr(expr) => self.visit_expr(expr),
            StmtKind::Thing(t) => self.visit_thing(t),
        }
    }

    fn visit_local(&mut self, local: &'hir Local<'hir>) -> Self::Result {
        let Local {
            mutability: _,
            name: _,
            init,
            ty,
            hir_id: _,
        } = local;

        try_visit!(
            maybe_visit!(v: self, m: visit_expr, init),
            self.visit_ty(ty)
        )
    }

    fn visit_expr(&mut self, expr: &'hir Expr<'hir>) -> Self::Result {
        let Expr {
            kind,
            span: _,
            hir_id: _,
        } = expr;

        match kind {
            ExprKind::Binary { lhs, rhs, op: _ } => {
                try_visit!(self.visit_expr(lhs), self.visit_expr(rhs))
            }

            ExprKind::Unary { target, op: _ } => self.visit_expr(target),

            ExprKind::Assign { variable, value }
            | ExprKind::AssignWithOp {
                variable,
                value,
                op: _,
            } => {
                try_visit!(self.visit_expr(variable), self.visit_expr(value))
            }

            ExprKind::Call { function, args } => {
                try_visit!(
                    self.visit_expr(function),
                    visit_iter!(v: self, m: visit_expr, *args)
                )
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

                maybe_visit!(v: self, m: visit_expr, else_)
            }

            ExprKind::Return { expr } => maybe_visit!(v: self, m: visit_expr, expr),

            ExprKind::Field { src, field: _ } => self.visit_expr(src),

            ExprKind::Loop { body, reason: _ } => self.visit_block(body),

            ExprKind::Index {
                index,
                indexed_thing,
            } => try_visit!(self.visit_expr(index), self.visit_expr(indexed_thing)),

            ExprKind::CommaSep(exprs) | ExprKind::List(exprs) => {
                visit_iter!(v: self, m: visit_expr, *exprs)
            }

            ExprKind::Path(path) => self.visit_path(path),

            ExprKind::Literal(..) | ExprKind::Break => Self::Result::normal(),
        }
    }
}

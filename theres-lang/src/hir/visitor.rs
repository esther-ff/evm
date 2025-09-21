use crate::hir::HirId;
use crate::hir::def::Resolved;
use crate::hir::node::{
    self, BindItem, BindItemKind, Block, Expr, ExprKind, Field, FnSig, Local, Param, Path, Stmt,
    StmtKind, Thing, ThingKind, Ty, TyKind, Universe,
};
use crate::visitor_common::VisitorResult;
use crate::{maybe_visit, try_visit, visit_iter};

pub trait HirVisitor<'hir>: Sized {
    type Result: VisitorResult;

    fn visit_universe(&mut self, universe: &'hir Universe<'hir>) -> Self::Result {
        walk_universe(self, universe)
    }

    fn visit_thing(&mut self, thing: &'hir Thing<'hir>) -> Self::Result {
        walk_thing(self, thing)
    }

    fn visit_bind_item(&mut self, bind_item: &'hir BindItem<'hir>) -> Self::Result {
        walk_bind_item(self, bind_item)
    }

    fn visit_fn_sig(&mut self, fn_sig: &'hir FnSig<'hir>) -> Self::Result {
        walk_fn_sig(self, fn_sig)
    }

    fn visit_param(&mut self, param: &'hir Param<'hir>) -> Self::Result {
        walk_param(self, param)
    }

    fn visit_field(&mut self, field: &'hir Field<'hir>) -> Self::Result {
        walk_field(self, field)
    }

    fn visit_ty(&mut self, ty: &'hir Ty<'hir>) -> Self::Result {
        walk_ty(self, ty)
    }

    fn visit_path(&mut self, path: &'hir Path<'hir>) -> Self::Result {
        walk_path(self, path)
    }

    fn visit_resolved(&mut self, _: &'hir Resolved<HirId>) -> Self::Result {
        Self::Result::normal()
    }

    fn visit_block(&mut self, block: &'hir Block<'hir>) -> Self::Result {
        walk_block(self, block)
    }

    fn visit_stmt(&mut self, stmt: &'hir Stmt<'hir>) -> Self::Result {
        walk_stmt(self, stmt)
    }

    fn visit_local(&mut self, local: &'hir Local<'hir>) -> Self::Result {
        walk_local(self, local)
    }

    fn visit_expr(&mut self, expr: &'hir Expr<'hir>) -> Self::Result {
        walk_expr(self, expr)
    }
}

pub fn walk_param<'vis, V: HirVisitor<'vis>>(v: &mut V, param: &'vis Param<'vis>) -> V::Result {
    let Param {
        name: _,
        ty,
        hir_id: _,
    } = param;
    v.visit_ty(ty)
}

pub fn walk_field<'vis, V: HirVisitor<'vis>>(v: &mut V, field: &'vis Field<'vis>) -> V::Result {
    let Field {
        mutability: _,
        name: _,
        span: _,
        hir_id: _,
        def_id: _,
        ty,
    } = field;

    v.visit_ty(ty)
}
pub fn walk_ty<'vis, V: HirVisitor<'vis>>(v: &mut V, ty: &'vis Ty<'vis>) -> V::Result {
    let Ty {
        span: _,
        hir_id: _,
        kind,
    } = ty;

    match kind {
        TyKind::MethodSelf | TyKind::Err => V::Result::normal(),
        TyKind::Array(ty) => v.visit_ty(ty),
        TyKind::Path(path) => v.visit_path(path),
    }
}

pub fn walk_fn_sig<'vis, V: HirVisitor<'vis>>(v: &mut V, fn_sig: &'vis FnSig<'vis>) -> V::Result {
    let FnSig {
        span: _,
        return_type,
        arguments,
        body: _,
    } = fn_sig;

    try_visit!(v.visit_ty(return_type));

    visit_iter!(v: v, m: visit_param, *arguments);
    V::Result::normal()
}

pub fn walk_universe<'vis, V: HirVisitor<'vis>>(
    v: &mut V,
    universe: &'vis Universe<'vis>,
) -> V::Result {
    let Universe {
        hir_id: _,
        things,
        span: _,
    } = universe;

    for thing in *things {
        v.visit_thing(thing);
    }

    V::Result::normal()
}

pub fn walk_path<'vis, V: HirVisitor<'vis>>(v: &mut V, path: &'vis Path<'vis>) -> V::Result {
    let Path {
        res,
        segments: _,
        span: _,
        hir_id: _,
    } = path;

    v.visit_resolved(res)
}

pub fn walk_bind_item<'vis, V: HirVisitor<'vis>>(
    v: &mut V,
    bind_item: &'vis BindItem<'vis>,
) -> V::Result {
    let BindItem {
        hir_id: _,
        span: _,
        kind,
        def_id: _,
    } = bind_item;

    match kind {
        BindItemKind::Fun { sig, name: _ } => v.visit_fn_sig(sig),
        BindItemKind::Const { ty, expr, sym: _ } => {
            try_visit!(v.visit_ty(ty));
            v.visit_expr(expr)
        }
    }
}

pub fn walk_thing<'vis, V: HirVisitor<'vis>>(v: &mut V, thing: &'vis Thing<'vis>) -> V::Result {
    let Thing {
        kind,
        span: _,
        hir_id: _,
        def_id: _,
    } = thing;
    match kind {
        ThingKind::Fn { name: _, sig } => {
            v.visit_fn_sig(sig);
        }
        ThingKind::Instance {
            fields,
            name: _,
            ctor_id: _,
        } => {
            visit_iter!(v: v, m: visit_field, *fields)
        }
        ThingKind::Realm { name: _, things } => visit_iter!(v: v, m: visit_thing, *things),
        ThingKind::Global {
            mutability: _,
            name: _,
            init,
            ty,
        } => {
            try_visit!(v.visit_ty(ty));
            return v.visit_expr(init);
        }
        ThingKind::Bind(node::Bind {
            with,
            mask: _,
            items,
        }) => {
            try_visit!(v.visit_ty(with));
            visit_iter!(v: v, m: visit_bind_item, *items)
        }
    };

    V::Result::normal()
}

pub fn walk_stmt<'vis, V: HirVisitor<'vis>>(v: &mut V, stmt: &'vis Stmt<'vis>) -> V::Result {
    let Stmt {
        span: _,
        kind,
        hir_id: _,
    } = stmt;

    match kind {
        StmtKind::Local(local) => v.visit_local(local),
        StmtKind::Expr(expr) => v.visit_expr(expr),
        StmtKind::Thing(t) => v.visit_thing(t),
    }
}

pub fn walk_block<'vis, V: HirVisitor<'vis>>(v: &mut V, block: &'vis Block<'vis>) -> V::Result {
    let Block {
        stmts,
        expr,
        span: _,
        hir_id: _,
    } = block;

    visit_iter!(v: v, m: visit_stmt, *stmts);
    maybe_visit!(v: v, m: visit_expr, expr);

    V::Result::normal()
}

pub fn walk_local<'vis, V: HirVisitor<'vis>>(v: &mut V, local: &'vis Local<'vis>) -> V::Result {
    let Local {
        mutability: _,
        name: _,
        init,
        ty,
        hir_id: _,
    } = local;

    maybe_visit!(v: v, m: visit_expr, init);
    v.visit_ty(ty)
}

pub fn walk_expr<'vis, V: HirVisitor<'vis>>(v: &mut V, expr: &'vis Expr<'vis>) -> V::Result {
    let Expr {
        kind,
        span: _,
        hir_id: _,
    } = expr;

    match kind {
        ExprKind::Binary { lhs, rhs, op: _ } => {
            try_visit!(v.visit_expr(lhs), v.visit_expr(rhs));
        }

        ExprKind::Unary { target, op: _ } => return v.visit_expr(target),

        ExprKind::Assign { variable, value }
        | ExprKind::AssignWithOp {
            variable,
            value,
            op: _,
        } => {
            try_visit!(v.visit_expr(variable), v.visit_expr(value));
        }

        ExprKind::Call { function, args } => {
            try_visit!(v.visit_expr(function));
            visit_iter!(v: v, m: visit_expr, *args)
        }

        ExprKind::MethodCall {
            receiver,
            method: _,
            args,
        } => {
            try_visit!(v.visit_expr(receiver));
            visit_iter!(v: v, m: visit_expr, *args)
        }

        ExprKind::Block(block) => return v.visit_block(block),

        ExprKind::If {
            condition,
            block,
            else_,
        } => {
            try_visit!(v.visit_expr(condition), v.visit_block(block));

            maybe_visit!(v: v, m: visit_expr, else_)
        }

        ExprKind::Return { expr } => maybe_visit!(v: v, m: visit_expr, expr),

        ExprKind::Field { src, field: _ } => return v.visit_expr(src),

        ExprKind::Loop { body, reason: _ } => return v.visit_block(body),

        ExprKind::Index {
            index,
            indexed_thing,
        } => try_visit!(v.visit_expr(index), v.visit_expr(indexed_thing)),

        ExprKind::CommaSep(exprs) | ExprKind::List(exprs) => {
            visit_iter!(v: v, m: visit_expr, *exprs)
        }

        ExprKind::Path(path) => return v.visit_path(path),

        ExprKind::Literal(..) | ExprKind::Break => (),
    };

    V::Result::normal()
}

mod private {
    crate::newtyped_index!(LocalId, LocalMap, LocalVec, LocalSlice);
    crate::newtyped_index!(ParamId, ParamMap, ParamVec, ParamSlice);

    pub type Locals<'ir> = LocalVec<super::LocalData<'ir>>;
    pub type Params<'ir> = LocalVec<super::ParamData<'ir>>;
}

use crate::air::node::{self, ExprKind as AirKind};

use crate::ast;
use crate::{
    air::{
        node::{AirLiteral, Constant, Expr as AirExpr, Local},
        visitor::AirVisitor,
    },
    arena::Arena,
    session::Session,
    span::Span,
    types::{
        fun_cx::TypeTable,
        ty::{FnSig, LambdaEnv, Ty},
    },
};
use private::{LocalId, Locals, Params};

pub struct LocalData<'ir> {
    ty: Ty<'ir>,
    mutbl: Constant,
}

pub struct ParamData<'ir> {
    ty: Ty<'ir>,
}

pub struct Expr<'ir> {
    kind: ExprKind<'ir>,
    ty: Ty<'ir>,
    span: Span,
}

pub enum LogicalOp {
    And,
    Or,
}

pub enum BinOp {
    Shl,
    Shr,
    Add,
    Sub,
    Mul,
    Div,
    Xor,
    Or,
    And,
    Mod,
    Eq,
    Neq,
    Gte,
    Gr,
    Lt,
    Le,
}

pub enum UnaryOp {
    Not,
    Neg,
}

pub enum ExprKind<'ir> {
    Call {
        callee: &'ir Expr<'ir>,
        args: &'ir [Expr<'ir>],
    },

    Logical {
        lhs: &'ir Expr<'ir>,
        rhs: &'ir Expr<'ir>,
        op: LogicalOp,
    },

    Binary {
        lhs: &'ir Expr<'ir>,
        rhs: &'ir Expr<'ir>,
        op: BinOp,
    },

    Assign {
        lvalue: &'ir Expr<'ir>,
        rvalue: &'ir Expr<'ir>,
        from_lowering: bool,
    },

    Lambda {
        env: &'ir LambdaEnv<'ir>,
    },

    Unary {
        operand: &'ir Expr<'ir>,
        op: UnaryOp,
    },

    Block(Block<'ir>),

    If {
        cond: &'ir Expr<'ir>,
        true_: &'ir Expr<'ir>,
        false_: &'ir Expr<'ir>,
    },

    Return(Option<&'ir Expr<'ir>>),

    Loop(Block<'ir>),

    Lit(AirLiteral),

    Index {
        base: &'ir Expr<'ir>,
        idx: &'ir Expr<'ir>,
    },

    Local {
        local: LocalId,
    },

    Upvar {
        upvar: LocalId,
    },
}

pub struct Block<'ir> {
    exprs: Vec<Expr<'ir>, &'ir Arena>,
}

pub struct Eair<'ir> {
    locals: Locals<'ir>,
    params: Params<'ir>,
    entry: &'ir Expr<'ir>,
    span: Span,
    kind: BodyKind,
}

enum BodyKind {
    Lambda,
    Function,
}

pub struct EairBuilder<'ir> {
    eair: Eair<'ir>,
    types: TypeTable<'ir>,
    cx: &'ir Session<'ir>,
    current_block: Vec<Expr<'ir>, &'ir Arena>,
}

impl<'ir> EairBuilder<'ir> {
    fn lower_body(&mut self, _typed_sig: FnSig<'ir>, _body: &'ir AirExpr<'ir>, _kind: BodyKind) {
        todo!()
    }

    fn lower_local(&mut self, local: &Local<'_>) -> LocalId {
        let ty = self.types.node_ty(local.air_id);
        let id = self.eair.locals.push(LocalData {
            ty,
            mutbl: local.mutability,
        });

        if let Some(expr) = local.init {
            let init = self.lower_expr(expr);
            let local_ref = self.cx.arena().alloc(Expr {
                span: Span::DUMMY,
                ty,
                kind: ExprKind::Local { local: id },
            });

            let actual_init = Expr {
                kind: ExprKind::Assign {
                    lvalue: local_ref,
                    rvalue: self.cx.arena().alloc(init),
                    from_lowering: true,
                },
                span: expr.span,
                ty: self.cx.nil(),
            };

            self.current_block.push(actual_init);
        };

        id
    }

    fn lower_expr_alloc(&mut self, expr: &AirExpr<'_>) -> &'ir Expr<'ir> {
        self.cx.arena().alloc(self.lower_expr(expr))
    }

    fn lower_expr(&mut self, expr: &AirExpr<'_>) -> Expr<'ir> {
        use crate::air::node::ExprKind::*;

        match expr.kind {
            Binary { lhs, rhs, op } => match bin_op_to_eair(op) {
                Ops::Regular(op) => {
                    /* later check for overloads */
                    let lhs = self.lower_expr_alloc(lhs);
                    let rhs = self.lower_expr_alloc(rhs);
                    Expr {
                        kind: ExprKind::Binary { lhs, rhs, op },
                        span: expr.span,
                        ty: self.types.type_of(expr),
                    }
                }
                Ops::Logic(op) => Expr {
                    kind: ExprKind::Logical {
                        lhs: self.lower_expr_alloc(lhs),
                        rhs: self.lower_expr_alloc(rhs),
                        op,
                    },
                    ty: self.types.type_of(expr),
                    span: expr.span,
                },
            },

            _ => todo!(),
        }
    }
}

enum Ops {
    Regular(BinOp),
    Logic(LogicalOp),
}

fn bin_op_to_eair(binop: ast::BinOp) -> Ops {
    use ast::BinOp::*;

    let reg = match binop {
        Add => BinOp::Add,
        Sub => BinOp::Sub,
        Div => BinOp::Div,
        Mul => BinOp::Mul,
        Shl => BinOp::Shl,
        Shr => BinOp::Shr,

        Mod => BinOp::Mod,
        BitOr => BinOp::Or,
        BitAnd => BinOp::And,
        BitXor => BinOp::Xor,
        Equality => BinOp::Eq,
        NotEquality => BinOp::Neq,
        Greater => BinOp::Gr,
        GreaterOrEq => BinOp::Gte,
        Lesser => BinOp::Lt,
        LesserOrEq => BinOp::Le,

        LogicalAnd => return Ops::Logic(LogicalOp::And),
        LogicalOr => return Ops::Logic(LogicalOp::Or),
    };

    Ops::Regular(reg)
}

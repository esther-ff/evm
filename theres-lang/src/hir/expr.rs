use crate::{
    ast::{AssignMode, BinOp, Name, UnaryOp},
    hir::def::{DefId, Ty},
    lexer::Span,
};

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum DesugaredLoop {
    Loop,
    While,
    For,
    Until,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct Stmt {
    span: Span,
    kind: StmtKind,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum BindingMode {
    Const,
    Let,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct BindingStmt {
    mode: BindingMode,
    name: Name,
    init: Option<Expr>,
    ty: Ty,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum StmtKind {
    Expr(Expr),
    Var(BindingStmt),
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct Block {
    span: Span,
    stmts: Vec<Stmt>,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum ExprKind {
    Loop {
        body: Block,
        desugared: DesugaredLoop,
    },

    Call {
        callee: Box<Expr>,
        args: Vec<Expr>,
    },

    Method {
        receiver: Box<Expr>,
        method: Name,
        args: Vec<Expr>,
    },

    FieldAccess {
        origin: Box<Expr>,
        accessed: Name,
    },

    Variable(DefId),

    Binary {
        kind: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },

    Assign {
        kind: AssignMode,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },

    Unary {
        kind: UnaryOp,
        victim: Box<Expr>,
    },

    Array {
        init: Vec<Expr>,
        size: Box<Expr>,
        ty: Ty,
    },

    Make {
        new_instance: DefId,
        ctor_args: Vec<Expr>,
    },

    Ret(Option<Box<Expr>>),
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

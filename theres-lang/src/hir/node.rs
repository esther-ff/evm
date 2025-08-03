use crate::{
    ast::{BinOp, Name, UnaryOp},
    hir::{
        def::{BodyId, DefId, Resolved},
        lowering_ast::HirId,
    },
    lexer::Span,
    session::SymbolId,
};

pub enum Node<'h> {
    Thing(&'h Thing<'h>),
    Expr(&'h Expr<'h>),
    Block(&'h Block<'h>),
    Stmt(&'h Stmt<'h>),
    Ty(&'h Ty<'h>),
    VariableStmt(&'h Local<'h>),
    Field(&'h Field<'h>),
}

pub struct Expr<'h> {
    kind: ExprKind<'h>,
    span: Span,
    hir_id: HirId,
}

pub enum AssignOp {
    Add,
    Sub,
    Mul,
    Div,
    ShiftLeft,
    ShiftRight,
}

pub enum LoopDesugarKind {
    For,
    While,
    Until,

    None,
}

pub enum ExprKind<'h> {
    Binary {
        lhs: &'h Expr<'h>,
        rhs: &'h Expr<'h>,
        op: BinOp,
    },

    Unary {
        target: &'h Expr<'h>,
        op: UnaryOp,
    },

    Paren {
        inner: &'h Expr<'h>,
    },

    Assign {
        variable: &'h Expr<'h>,
        value: &'h Expr<'h>,
    },

    AssignWithOp {
        variable: &'h Expr<'h>,
        value: &'h Expr<'h>,
        op: AssignOp,
    },

    Call {
        function: &'h Expr<'h>,
        args: &'h [Expr<'h>],
    },

    MethodCall {
        receiver: &'h Expr<'h>,
        method: SymbolId,
        args: &'h [Expr<'h>],
    },

    Block(&'h Block<'h>),

    If {
        condition: &'h Expr<'h>,
        block: &'h Block<'h>,
        else_ifs: &'h [(Block<'h>, Expr<'h>)],
        otherwise: Option<&'h Expr<'h>>,
    },

    Return {
        expr: Option<&'h Expr<'h>>,
    },

    Field {
        src: &'h Expr<'h>,
        field: SymbolId,
    },

    Loop {
        body: &'h Block<'h>,
        reason: LoopDesugarKind,
    },
}

pub struct Block<'h> {
    stmts: &'h [Stmt<'h>],
    expr: Option<&'h Expr<'h>>,
    span: Span,
}

pub struct Stmt<'h> {
    span: Span,
    kind: StmtKind<'h>,
}

pub enum StmtKind<'h> {
    Local(&'h Local<'h>),
    Expr(&'h Expr<'h>),
    Thing(&'h Thing<'h>),
}

pub enum Constant {
    Yes,
    No,
}

pub struct Local<'h> {
    mutability: Constant,
    name: Name,
    init: Option<&'h Expr<'h>>,
    ty: &'h Ty<'h>,
    hir_id: HirId,
}

pub struct Thing<'h> {
    hir_id: HirId,
    def_id: DefId,
    kind: ThingKind<'h>,
    span: Span,
}

pub enum ThingKind<'h> {
    Fn {
        name: Name,
        sig: FnSig<'h>,
    },

    Instance {
        fields: &'h [HirId],
        constants: &'h [DefId],
        methods: &'h [DefId],
        name: Name,
    },

    Realm {
        name: Name,
        things: &'h [Thing<'h>],
    },

    Global {
        mutability: Constant,
        name: Name,
        init: &'h Expr<'h>,
        ty: &'h Ty<'h>,
    },
}

pub struct FnSig<'h> {
    span: Span,
    return_type: &'h Ty<'h>,
    arguments: &'h [Param<'h>],
    body: BodyId,
}

pub struct Param<'h> {
    name: Name,
    ty: &'h Ty<'h>,
}

pub struct Ty<'h> {
    span: Span,
    hir_id: HirId,
    kind: TyKind<'h>,
}

impl<'a> Ty<'a> {
    pub fn new(span: Span, hir_id: HirId, kind: TyKind<'a>) -> Self {
        Self { span, hir_id, kind }
    }
}

pub enum TyKind<'h> {
    MethodSelf,
    Array(&'h Ty<'h>),
    Normal(Resolved<HirId>),
}

pub struct Field<'h> {
    mutability: Constant,
    span: Span,
    hir_id: HirId,
    name: Name,
    ty: &'h Ty<'h>,
}

use crate::{
    ast::{AssignMode, BinOp, Name, UnaryOp},
    hir::{
        def::{BodyId, DefId, Resolved},
        lowering_ast::HirId,
    },
    lexer::Span,
    session::SymbolId,
};

#[derive(Debug, Clone, Copy)]
pub enum Node<'h> {
    Local(&'h Local<'h>),

    BindItem(&'h BindItem<'h>),
    Thing(&'h Thing<'h>),
    Expr(&'h Expr<'h>),
    Block(&'h Block<'h>),
    Stmt(&'h Stmt<'h>),
    Ty(&'h Ty<'h>),
    VariableStmt(&'h Local<'h>),
    Field(&'h Field<'h>),
    Path(&'h Path<'h>),
    FnParam(&'h Param<'h>),
}

impl<'h> Node<'h> {
    pub fn is_thing(&self) -> bool {
        matches!(self, Self::Thing(..))
    }

    pub fn get_thing(&'h self) -> Option<&'h Thing<'h>> {
        if let Node::Thing(t) = self {
            return Some(t);
        }

        None
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Universe<'h> {
    pub hir_id: HirId,
    pub things: &'h [Thing<'h>],
    pub span: Span,
}

impl<'h> Universe<'h> {
    pub fn new(hir_id: HirId, things: &'h [Thing<'h>], span: Span) -> Self {
        Self {
            hir_id,
            things,
            span,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Expr<'h> {
    pub kind: ExprKind<'h>,
    pub span: Span,
    pub hir_id: HirId,
}

impl<'h> Expr<'h> {
    pub fn new(kind: ExprKind<'h>, span: Span, hir_id: HirId) -> Self {
        Self { kind, span, hir_id }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum AssignOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    ShiftLeft,
    ShiftRight,
    Xor,
    Or,
    And,
}

impl AssignOp {
    pub fn lower_assign_mode(mode: AssignMode) -> Self {
        match mode {
            AssignMode::Add => Self::Add,
            AssignMode::Sub => Self::Sub,
            AssignMode::Mul => Self::Mul,
            AssignMode::Div => Self::Div,
            AssignMode::Mod => Self::Mod,
            AssignMode::Shl => Self::ShiftLeft,
            AssignMode::Shr => Self::ShiftRight,
            AssignMode::Xor => Self::Xor,
            AssignMode::Or => Self::Or,
            AssignMode::And => Self::And,
            AssignMode::Regular => unreachable!(),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum LoopDesugarKind {
    For,
    While,
    Until,

    None,
}

#[derive(Debug, Clone, Copy)]
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
        otherwise: Option<&'h Block<'h>>,
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

    Literal(HirLiteral),

    List(&'h [Expr<'h>]),

    Index {
        index: &'h Expr<'h>,
        indexed_thing: &'h Expr<'h>,
    },

    Path(&'h Path<'h>),

    CommaSep(&'h [Expr<'h>]),

    Break,
}

#[derive(Debug, Clone, Copy)]
pub enum HirLiteral {
    Bool(bool),
    Float(f64),
    Uint(u64),
    Int(i64),
    Str(SymbolId),
}

#[derive(Debug, Clone, Copy)]
pub struct Block<'h> {
    pub stmts: &'h [Stmt<'h>],
    pub expr: Option<&'h Expr<'h>>,
    pub span: Span,
    pub hir_id: HirId,
}

impl<'h> Block<'h> {
    pub fn new(
        span: Span,
        stmts: &'h [Stmt<'h>],
        hir_id: HirId,
        expr: Option<&'h Expr<'h>>,
    ) -> Self {
        Self {
            stmts,

            expr,
            span,

            hir_id,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Stmt<'h> {
    pub span: Span,
    pub kind: StmtKind<'h>,
    pub hir_id: HirId,
}

impl<'h> Stmt<'h> {
    pub fn new(span: Span, kind: StmtKind<'h>, hir_id: HirId) -> Self {
        Self { span, kind, hir_id }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum StmtKind<'h> {
    Local(&'h Local<'h>),
    Expr(&'h Expr<'h>),
    Thing(&'h Thing<'h>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Constant {
    Yes,
    No,
}

#[derive(Debug, Clone, Copy)]
pub struct Local<'h> {
    pub mutability: Constant,
    pub name: Name,
    pub init: Option<&'h Expr<'h>>,
    pub ty: &'h Ty<'h>,
    pub hir_id: HirId,
}

impl<'h> Local<'h> {
    pub fn new(
        mutability: Constant,
        name: Name,
        hir_id: HirId,
        ty: &'h Ty<'h>,
        init: Option<&'h Expr<'h>>,
    ) -> Self {
        Self {
            mutability,
            name,

            init,
            ty,

            hir_id,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Thing<'h> {
    pub kind: ThingKind<'h>,
    pub span: Span,
    pub hir_id: HirId,
    pub def_id: DefId,
}

impl<'h> Thing<'h> {
    pub fn new(kind: ThingKind<'h>, span: Span, id: HirId, def_id: DefId) -> Self {
        Self {
            span,
            kind,

            hir_id: id,
            def_id,
        }
    }

    pub fn get_bind(&self) -> Option<Bind<'h>> {
        if let ThingKind::Bind(b) = self.kind {
            return Some(b);
        }

        None
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ThingKind<'h> {
    Fn {
        name: Name,
        sig: &'h FnSig<'h>,
    },

    Instance {
        fields: &'h [Field<'h>],
        name: Name,
        ctor_id: (HirId, DefId),
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

    Bind(Bind<'h>),
}

#[derive(Debug, Clone, Copy)]
pub struct Bind<'h> {
    pub with: &'h Ty<'h>,
    pub items: &'h [BindItem<'h>],
    pub mask: Option<&'h Path<'h>>,
}

#[derive(Debug, Clone, Copy)]
pub struct BindItem<'h> {
    pub hir_id: HirId,
    pub def_id: DefId,
    pub span: Span,
    pub kind: BindItemKind<'h>,
}

impl<'h> BindItem<'h> {
    pub fn new(hir_id: HirId, def_id: DefId, span: Span, kind: BindItemKind<'h>) -> Self {
        Self {
            hir_id,
            def_id,
            span,
            kind,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum BindItemKind<'h> {
    Fun {
        sig: &'h FnSig<'h>,
        name: SymbolId,
    },

    Const {
        ty: &'h Ty<'h>,
        expr: &'h Expr<'h>,
        sym: SymbolId,
    },
}

#[derive(Debug, Clone, Copy)]
pub struct FnSig<'h> {
    pub span: Span,
    pub return_type: &'h Ty<'h>,
    pub arguments: &'h [Param<'h>],
    pub body: BodyId,
}

impl<'h> FnSig<'h> {
    pub fn new(
        span: Span,
        return_type: &'h Ty<'h>,
        arguments: &'h [Param<'h>],
        body: BodyId,
    ) -> Self {
        Self {
            span,
            return_type,
            arguments,
            body,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Param<'h> {
    pub name: Name,
    pub ty: &'h Ty<'h>,
    pub hir_id: HirId,
}

impl<'h> Param<'h> {
    pub fn new(name: Name, ty: &'h Ty<'h>, hir_id: HirId) -> Self {
        Self { name, ty, hir_id }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Ty<'h> {
    pub span: Span,
    pub hir_id: HirId,
    pub kind: TyKind<'h>,
}

impl<'a> Ty<'a> {
    pub fn new(span: Span, hir_id: HirId, kind: TyKind<'a>) -> Self {
        Self { span, hir_id, kind }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum TyKind<'h> {
    MethodSelf,
    Array(&'h Ty<'h>),
    Path(&'h Path<'h>),

    Err,
}

#[derive(Debug, Clone, Copy)]
pub struct Path<'h> {
    pub res: Resolved<HirId>,
    pub segments: &'h [SymbolId],
    pub span: Span,
    pub hir_id: HirId,
}

impl<'h> Path<'h> {
    pub fn new(res: Resolved<HirId>, segments: &'h [SymbolId], span: Span, hir_id: HirId) -> Self {
        Self {
            res,
            segments,
            span,
            hir_id,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Field<'h> {
    pub mutability: Constant,
    pub name: Name,
    pub span: Span,
    pub hir_id: HirId,
    pub def_id: DefId,
    pub ty: &'h Ty<'h>,
}

impl<'h> Field<'h> {
    pub fn new(
        mutability: Constant,
        span: Span,
        hir_id: HirId,
        name: Name,
        def_id: DefId,
        ty: &'h Ty<'h>,
    ) -> Self {
        Self {
            mutability,

            name,

            span,
            hir_id,
            def_id,

            ty,
        }
    }
}

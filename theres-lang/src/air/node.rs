use crate::air::AirId;
use crate::air::def::{BodyId, DefId, Resolved};
use crate::ast::{AssignMode, BinOp, Name, UnaryOp};
use crate::span::Span;
use crate::symbols::SymbolId;

#[derive(Debug, Clone, Copy)]
#[allow(dead_code)] // for later
pub enum Node<'h> {
    Local(&'h Local<'h>),
    BindItem(&'h BindItem<'h>),
    Thing(&'h Thing<'h>),
    Expr(&'h Expr<'h>),
    Block(&'h Block<'h>),
    Stmt(&'h Stmt<'h>),
    Ty(&'h Ty<'h>),
    Field(&'h Field<'h>),
    Path(&'h Path<'h>),
    FnParam(&'h Param<'h>),
    Lambda(&'h Lambda<'h>),
    NativeItem(&'h NativeItem<'h>),
}

impl<'h> Node<'h> {
    pub fn get_thing(&'h self) -> Option<&'h Thing<'h>> {
        if let Node::Thing(t) = self {
            return Some(t);
        }

        None
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Universe<'h> {
    pub things: &'h [Thing<'h>],
}

impl<'h> Universe<'h> {
    pub fn new(things: &'h [Thing<'h>]) -> Self {
        Self { things }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Expr<'h> {
    pub kind: ExprKind<'h>,
    pub span: Span,
    pub air_id: AirId,
}

impl<'h> Expr<'h> {
    pub fn new(kind: ExprKind<'h>, span: Span, air_id: AirId) -> Self {
        Self { kind, span, air_id }
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

impl From<AssignOp> for BinOp {
    fn from(value: AssignOp) -> Self {
        match value {
            AssignOp::Add => BinOp::Add,
            AssignOp::Sub => BinOp::Sub,
            AssignOp::Div => BinOp::Div,
            AssignOp::Mul => BinOp::Mul,
            AssignOp::Mod => BinOp::Mod,
            AssignOp::ShiftLeft => BinOp::Shl,
            AssignOp::ShiftRight => BinOp::Shr,

            AssignOp::Xor => BinOp::BitXor,
            AssignOp::And => BinOp::BitAnd,
            AssignOp::Or => BinOp::BitOr,
        }
    }
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
pub struct Lambda<'h> {
    pub did: DefId,
    pub inputs: &'h [Param<'h>],

    // if `None` - infer return
    // if `Some` typeck against the type
    pub output: Option<Ty<'h>>,
    pub body: BodyId,
    pub span: Span,
    pub expr_air_id: AirId,
}

#[derive(Debug, Clone, Copy)]
pub enum ExprKind<'h> {
    Binary {
        lhs: &'h Expr<'h>,
        rhs: &'h Expr<'h>,
        op: BinOp,
    },

    Lambda(&'h Lambda<'h>),

    Unary {
        target: &'h Expr<'h>,
        op: UnaryOp,
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
        else_: Option<&'h Expr<'h>>,
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
    },

    Literal(AirLiteral),

    List(&'h [Expr<'h>]),

    Index {
        index: &'h Expr<'h>,
        indexed_thing: &'h Expr<'h>,
    },

    Path(&'h Path<'h>),

    Break,
}

#[derive(Debug, Clone, Copy)]
pub enum AirLiteral {
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
    pub air_id: AirId,
}

impl<'h> Block<'h> {
    pub fn new(
        span: Span,
        stmts: &'h [Stmt<'h>],
        air_id: AirId,
        expr: Option<&'h Expr<'h>>,
    ) -> Self {
        Self {
            stmts,

            expr,
            span,

            air_id,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct NativeItem<'h> {
    pub name: Name,
    pub span: Span,
    pub kind: NativeItemKind<'h>,
    pub air_id: AirId,
}

#[derive(Debug, Clone, Copy)]
pub enum NativeItemKind<'h> {
    Fun {
        args: &'h [Param<'h>],
        ret: &'h Ty<'h>,
    },
}

#[derive(Debug, Clone, Copy)]
pub struct Stmt<'h> {
    pub span: Span,
    pub kind: StmtKind<'h>,
    pub air_id: AirId,
}

impl<'h> Stmt<'h> {
    pub fn new(span: Span, kind: StmtKind<'h>, air_id: AirId) -> Self {
        Self { span, kind, air_id }
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
    pub ty: Option<&'h Ty<'h>>,
    pub air_id: AirId,
}

impl<'h> Local<'h> {
    pub fn new(
        mutability: Constant,
        name: Name,
        air_id: AirId,
        ty: Option<&'h Ty<'h>>,
        init: Option<&'h Expr<'h>>,
    ) -> Self {
        Self {
            mutability,
            name,

            init,
            ty,

            air_id,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Thing<'h> {
    pub kind: ThingKind<'h>,
    pub span: Span,
    pub air_id: AirId,
    pub def_id: DefId,
}

impl<'h> Thing<'h> {
    pub fn new(kind: ThingKind<'h>, span: Span, id: AirId, def_id: DefId) -> Self {
        Self {
            span,
            kind,

            air_id: id,
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
        ctor_id: (AirId, DefId),
    },

    Realm {
        name: Name,
        things: &'h [Thing<'h>],
    },

    Native {
        items: &'h [NativeItem<'h>],
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
    pub air_id: AirId,
    pub def_id: DefId,
    pub span: Span,
    pub kind: BindItemKind<'h>,
}

impl<'h> BindItem<'h> {
    pub fn new(air_id: AirId, def_id: DefId, span: Span, kind: BindItemKind<'h>) -> Self {
        Self {
            air_id,
            def_id,
            span,
            kind,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum BindItemKind<'h> {
    Fun { sig: &'h FnSig<'h>, name: SymbolId },
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
    pub air_id: AirId,
}

impl<'h> Param<'h> {
    pub fn new(name: Name, ty: &'h Ty<'h>, air_id: AirId) -> Self {
        Self { name, ty, air_id }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Ty<'h> {
    pub span: Span,
    pub air_id: AirId,
    pub kind: TyKind<'h>,
}

impl<'a> Ty<'a> {
    pub fn new(span: Span, air_id: AirId, kind: TyKind<'a>) -> Self {
        Self { span, air_id, kind }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum TyKind<'h> {
    Array(&'h Ty<'h>),
    Path(&'h Path<'h>),
    Fun {
        inputs: &'h [Ty<'h>],
        output: Option<&'h Ty<'h>>,
    },

    Infer,

    Err,
}

#[derive(Debug, Clone, Copy)]
pub struct Path<'h> {
    pub res: Resolved<AirId>,
    pub segments: &'h [SymbolId],
    pub span: Span,
    pub air_id: AirId,
}

impl<'h> Path<'h> {
    pub fn new(res: Resolved<AirId>, segments: &'h [SymbolId], span: Span, air_id: AirId) -> Self {
        Self {
            res,
            segments,
            span,
            air_id,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Field<'h> {
    pub mutability: Constant,
    pub name: Name,
    pub span: Span,
    pub air_id: AirId,
    pub def_id: DefId,
    pub ty: &'h Ty<'h>,
}

impl<'h> Field<'h> {
    pub fn new(
        mutability: Constant,
        span: Span,
        air_id: AirId,
        name: Name,
        def_id: DefId,
        ty: &'h Ty<'h>,
    ) -> Self {
        Self {
            mutability,

            name,

            span,
            air_id,
            def_id,

            ty,
        }
    }
}

#![allow(dead_code)]

use crate::arena::Id;
use crate::lexer::Span;
use crate::session::SymbolId;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Shl,
    Shr,
    Mod,
    BitOr,
    BitXor,
    BitAnd,

    LogicalOr,
    LogicalAnd,

    Equality,
    NotEquality,

    GreaterOrEq,
    LesserOrEq,
    Lesser,
    Greater,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum UnaryOp {
    Negation,
    Not,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum ConstantExpr {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(SymbolId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum AssignMode {
    Regular,
    Add,
    Sub,
    Mul,
    Mod,
    Div,
    Shl,
    Shr,
    And,
    Xor,
    Or,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct Expr {
    pub ty: ExprType,
    pub span: Span,
}

impl Expr {
    pub fn new(ty: ExprType, span: Span) -> Self {
        Self { ty, span }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct ElseIf {
    cond: Expr,
    body: Block,
}

impl ElseIf {
    pub fn new(cond: Expr, body: Block) -> Self {
        Self { cond, body }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct Pat {
    span: Span,
    ty: PatType,
}

impl Pat {
    pub fn new(ty: PatType, span: Span) -> Self {
        Self { span, ty }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum PatType {
    Ident { name: Name },
    Tuple { pats: Vec<Pat> },
    Wild,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum ExprType {
    BinaryExpr {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        op: BinOp,
    },

    UnaryExpr {
        op: UnaryOp,
        target: Box<Expr>,
    },

    Constant(ConstantExpr),

    Group(Box<Expr>),

    CommaGroup(Vec<Expr>),

    Assign {
        lvalue: Box<Expr>,
        rvalue: Box<Expr>,
        mode: AssignMode,
    },

    FunCall {
        callee: Box<Expr>,
        args: Vec<Expr>,
    },

    Variable {
        name: Name,
    },

    For {
        iterable: Box<Expr>,
        pat: Pat, // todo
        body: Block,
    },

    While {
        cond: Box<Expr>,
        body: Block,
    },

    Until {
        cond: Box<Expr>,
        body: Block,
    },

    Loop {
        body: Block,
    },

    If {
        cond: Box<Expr>,
        if_block: Block,
        else_ifs: Vec<ElseIf>, // can just be empty
        otherwise: Option<Block>,
    },

    FieldAccess {
        source: Box<Expr>,
        field: Name,
    },

    ArrayDecl {
        ty: Ty,
        size: Box<Expr>,
        initialize: Vec<Expr>,
    },

    Lambda {
        args: Vec<Pat>,
        body: LambdaBody,
    },
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum LambdaBody {
    Block(Block),
    Expr(Box<Expr>),
}

impl LambdaBody {
    pub fn span(&self) -> Span {
        match self {
            Self::Block(block) => block.span,
            Self::Expr(expr) => expr.span,
        }
    }
}

pub struct Constraint {
    // todo
}

pub struct GenericTyParam {
    ident: Name,
    constraint: Constraint,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum TyKind {
    /// Function/lambda type
    /// like `fun(...) -> ...`
    Fn { args: Vec<Ty>, ret: Option<Box<Ty>> },

    /// Array
    /// like [u64]
    Array(Box<Ty>),

    /// Regular type like `u32`
    Regular(SymbolId),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Ty {
    pub kind: TyKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub span: Span,
}

impl Block {
    pub fn new(stmts: Vec<Stmt>, span: Span) -> Self {
        Self { stmts, span }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct FnDecl {
    name: Name,
    args: FnArgs,
    ret_type: Ty,
    block: Block,
    span: Span,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct FnArgs {
    pub has_self: bool,
    pub args: Vec<Arg>,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct Arg {
    ident: Name,
    ty: Ty,
}

impl Arg {
    pub fn new(ident: Name, ty: Ty) -> Self {
        Self { ident, ty }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum VarMode {
    Let,
    Const,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct VariableStmt {
    mode: VarMode,
    name: Name,
    initializer: Option<Expr>,
    ty: Ty,
}

impl VariableStmt {
    pub fn new(mode: VarMode, name: Name, initializer: Option<Expr>, ty: Ty) -> Self {
        Self {
            mode,
            name,
            initializer,
            ty,
        }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct GlobalDecl {
    name: Name,
    initializer: Option<Expr>,
    ty: Ty,
    constant: bool,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum Stmt {
    Block(Block),
    Expr(Expr),
    LocalVar(VariableStmt),
    Definition(AstDef),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct AstId {
    chunk: usize,
    vec: usize,
}

impl Id for AstId {
    fn new(chunk: usize, vec: usize) -> Self {
        Self { chunk, vec }
    }

    fn get_inside_chunk_index(&self) -> usize {
        self.vec
    }

    fn get_arena_chunk_index(&self) -> usize {
        self.chunk
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum DefKind {
    Function(FnDecl),
    Global(GlobalDecl), // todo
                        // Expr(Expr),
}

impl DefKind {
    pub fn function(name: Name, args: FnArgs, block: Block, ret_type: Ty, span: Span) -> Self {
        Self::Function(FnDecl {
            span,
            name,
            args,
            block,
            ret_type,
        })
    }

    pub fn global(name: Name, initializer: Option<Expr>, ty: Ty, constant: bool) -> Self {
        Self::Global(GlobalDecl {
            name,
            initializer,
            ty,
            constant,
        })
    }

    // pub fn expr(expr: Expr) -> Self {
    //     Self::Expr(expr)
    // }
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct AstDef {
    kind: DefKind,
}

impl AstDef {
    pub fn new(kind: DefKind) -> Self {
        Self { kind }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Name {
    pub interned: SymbolId,
    pub span: Span,
}

impl Name {
    pub fn new(interned: SymbolId, span: Span) -> Self {
        Self { span, interned }
    }
}

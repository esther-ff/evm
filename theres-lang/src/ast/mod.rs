mod pretty;
pub use pretty::PrettyPrinter;

use crate::lexer::Span;
use crate::symbols::SymbolId;

pub use crate::parser::AstId;
use crate::visitor_common::VisitorResult;
use crate::{maybe_visit, try_visit, visit_iter};

use core::fmt::{Display, Formatter, Result};

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

impl Display for BinOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let write = match self {
            Self::Add => "add",
            Self::Sub => "sub",
            Self::Mul => "mul",
            Self::Div => "div",
            Self::Shl => "shl",
            Self::Shr => "shr",
            Self::Mod => "mod",
            Self::BitOr => "bitor",
            Self::BitXor => "bitxor",
            Self::BitAnd => "bitand",
            Self::LogicalOr => "or",
            Self::LogicalAnd => "and",
            Self::Equality => "eq",
            Self::NotEquality => "ne",
            Self::GreaterOrEq => "gteq",
            Self::LesserOrEq => "lteq",
            Self::Lesser => "lt",
            Self::Greater => "gt",
        };

        write!(f, "{write}")
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum UnaryOp {
    Negation,
    Not,
}

impl Display for UnaryOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let write = match self {
            UnaryOp::Negation => "neg",
            UnaryOp::Not => "not",
        };

        write!(f, "{write}")
    }
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
    pub id: AstId,
}

impl Expr {
    pub fn new(ty: ExprType, span: Span, id: AstId) -> Self {
        Self { ty, span, id }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct ElseIf {
    pub cond: Expr,
    pub body: Block,
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

    Assign {
        lvalue: Box<Expr>,
        rvalue: Box<Expr>,
        mode: AssignMode,
    },

    FunCall {
        callee: Box<Expr>,
        args: Vec<Expr>,
    },

    MethodCall {
        receiver: Box<Expr>,
        args: Vec<Expr>,
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

    List(Vec<Expr>),

    Lambda {
        args: Vec<Arg>,
        body: LambdaBody,
    },

    Return {
        ret: Option<Box<Expr>>,
    },

    Index {
        indexed: Box<Expr>,
        index: Box<Expr>,
    },

    Path(Path),

    Block(Block),

    Break,
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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Path {
    #[allow(clippy::struct_field_names)]
    pub path: Vec<PathSeg>,
    pub span: Span,
    pub id: AstId,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct PathSeg {
    pub name: Name,
    pub span: Span,
    pub id: AstId,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum TyKind {
    /// Function/lambda type
    /// like `fun(...) -> ...`
    Fn { args: Vec<Ty>, ret: Option<Box<Ty>> },

    /// Array
    /// like [u64]
    Array(Box<Ty>),

    /// Some path to a type
    Path(Path),

    /// `self` argument
    /// in methods
    MethodSelf,

    /// Inference!
    Infer,

    /// failed parsing
    Err,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Ty {
    pub kind: TyKind,
    pub span: Span,
    pub id: AstId,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub expr: Option<Box<Expr>>,
    pub span: Span,
    pub id: AstId,
}

impl Block {
    pub fn new(stmts: Vec<Stmt>, span: Span, id: AstId, expr: Option<Expr>) -> Self {
        Self {
            stmts,
            span,
            id,
            expr: expr.map(Box::new),
        }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct FnSig {
    pub name: Name,
    pub args: Vec<Arg>,
    pub ret_type: Ty,
    pub span: Span,
    pub id: AstId,
}

impl FnSig {
    pub fn new(name: Name, span: Span, ret_type: Ty, args: Vec<Arg>, id: AstId) -> Self {
        FnSig {
            name,

            args,
            ret_type,
            span,
            id,
        }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct FnDecl {
    pub sig: FnSig,
    pub block: Block,
    pub span: Span,
    pub id: AstId,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct Arg {
    pub ident: Name,
    pub ty: Ty,

    pub id: AstId,
}

impl Arg {
    pub fn new(ident: Name, ty: Ty, id: AstId) -> Self {
        Self { ident, ty, id }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum VarMode {
    Let,
    Const,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct VariableStmt {
    pub mode: VarMode,
    pub name: Name,
    pub init: Option<Expr>,
    pub ty: Option<Ty>,
    pub id: AstId,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum StmtKind {
    Expr(Expr),
    LocalVar(VariableStmt),
    Thing(Thing),
}

impl StmtKind {
    pub fn span(&self) -> Span {
        match self {
            Self::Expr(x) => x.span,
            Self::LocalVar(l) => l.name.span,
            Self::Thing(t) => t.kind.span(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
    pub id: AstId,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Field {
    pub constant: bool,
    pub name: Name,
    pub ty: Ty,
    pub span: Span,
    pub id: AstId,
}

impl Field {
    pub fn new(constant: bool, name: Name, ty: Ty, span: Span, id: AstId) -> Self {
        Self {
            constant,
            name,

            ty,
            span,

            id,
        }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct Instance {
    pub name: Name,
    pub span: Span,
    pub fields: Vec<Field>,
    pub id: AstId,

    /// id of it's constructor
    pub ctor_id: AstId,
}

impl Instance {
    pub fn new(name: Name, span: Span, fields: Vec<Field>, id: AstId, ctor_id: AstId) -> Self {
        Self {
            name,

            span,
            fields,

            id,
            ctor_id,
        }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct Thing {
    pub id: AstId,
    pub kind: ThingKind,
}

impl Thing {
    pub fn new(kind: ThingKind, id: AstId) -> Self {
        Self { id, kind }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum ThingKind {
    Function(FnDecl),
    Instance(Instance),
    Realm(Realm),
    Bind(Bind),
}

impl ThingKind {
    pub fn function(block: Block, span: Span, sig: FnSig, id: AstId) -> Self {
        Self::Function(FnDecl {
            sig,

            block,
            span,
            id,
        })
    }

    pub fn instance(name: Name, span: Span, fields: Vec<Field>, id: AstId, ctor_id: AstId) -> Self {
        Self::Instance(Instance::new(name, span, fields, id, ctor_id))
    }

    pub fn span(&self) -> Span {
        match self {
            Self::Function(f) => f.span,
            Self::Instance(i) => i.span,
            Self::Bind(a) => a.span,
            Self::Realm(r) => r.span,
        }
    }
}

#[derive(Debug, PartialEq, PartialOrd, Clone)]
pub struct Bind {
    pub victim: Ty,
    pub items: Vec<BindItem>,
    pub span: Span,
    pub id: AstId,
}

#[derive(Debug, PartialEq, PartialOrd, Clone)]
pub struct BindItem {
    pub kind: BindItemKind,
    pub id: AstId,
}

#[derive(Debug, PartialEq, PartialOrd, Clone)]
pub enum BindItemKind {
    // Const(VariableStmt),
    Fun(FnDecl),
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct Realm {
    pub items: Vec<Thing>,
    pub span: Span,
    pub name: Name,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct Universe {
    pub id: AstId,
    pub thingies: Vec<Thing>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Name {
    pub interned: SymbolId,
    pub span: Span,
}

impl Name {
    pub const DUMMY: Self = Self {
        interned: SymbolId::DUMMY,
        span: Span::DUMMY,
    };

    pub fn new(interned: SymbolId, span: Span) -> Self {
        Self { interned, span }
    }
}

pub trait Visitor<'a>: Sized {
    type Result: VisitorResult;

    fn visit_realm(&mut self, val: &'a Realm) -> Self::Result {
        let Realm {
            items,
            span: _,
            name,
        } = val;

        visit_iter!(v: self, m: visit_thing, items);
        self.visit_name(name)
    }

    fn visit_thing(&mut self, val: &'a Thing) -> Self::Result {
        let Thing { kind, id: _ } = val;

        self.visit_def(kind)
    }

    fn visit_def(&mut self, val: &'a ThingKind) -> Self::Result {
        match val {
            ThingKind::Function(f) => self.visit_fn_decl(f),
            ThingKind::Realm(r) => self.visit_realm(r),
            ThingKind::Instance(i) => self.visit_instance(i),
            ThingKind::Bind(a) => self.visit_bind(a),
        }
    }

    fn visit_instance(&mut self, val: &'a Instance) -> Self::Result {
        let Instance {
            name: _,
            id: _,
            span: _,
            fields,
            ctor_id: _,
        } = val;

        for field in fields {
            try_visit!(self.visit_field(field));
        }

        Self::Result::normal()
    }

    fn visit_field(&mut self, val: &'a Field) -> Self::Result {
        let Field {
            constant: _,
            name,
            ty,
            span: _,
            id: _,
        } = val;

        try_visit!(self.visit_ty(ty));

        self.visit_name(name)
    }

    fn visit_var_stmt(&mut self, val: &'a VariableStmt) -> Self::Result {
        let VariableStmt {
            mode: _,
            name: _,
            init,
            ty,
            id: _,
        } = val;

        maybe_visit!(v: self, m: visit_ty, ty);
        maybe_visit!(v: self, m: visit_expr, init);

        Self::Result::normal()
    }

    fn visit_ty(&mut self, val: &'a Ty) -> Self::Result {
        let Ty {
            kind,
            span: _,
            id: _,
        } = val;

        match kind {
            TyKind::Fn { args, ret } => {
                visit_iter!(v: self, m: visit_ty, args);

                maybe_visit!(v: self, m: visit_ty, ret);

                Self::Result::normal()
            }

            TyKind::Array(ty) => self.visit_ty(ty),

            TyKind::Path(p) => self.visit_path(p),

            TyKind::MethodSelf | TyKind::Infer | TyKind::Err => Self::Result::normal(),
        }
    }

    fn visit_bind(&mut self, val: &'a Bind) -> Self::Result {
        let Bind {
            victim,
            span: _,
            items,
            id: _,
        } = val;

        try_visit!(self.visit_ty(victim));
        visit_iter!(v: self, m: visit_bind_item, items);
        Self::Result::normal()
    }

    fn visit_bind_item(&mut self, val: &'a BindItem) -> Self::Result {
        let BindItem { kind, id: _ } = val;

        match kind {
            // BindItemKind::Const(var) => self.visit_var_stmt(var),
            BindItemKind::Fun(f) => self.visit_fn_decl(f),
        }
    }

    fn visit_pat(&mut self, val: &'a Pat) -> Self::Result {
        let Pat { span: _, ty } = val;

        match ty {
            PatType::Ident { name } => self.visit_name(name),
            PatType::Tuple { pats } => {
                visit_iter!(v: self, m: visit_pat, pats);
                Self::Result::normal()
            }

            PatType::Wild => Self::Result::normal(),
        }
    }

    fn visit_expr(&mut self, val: &'a Expr) -> Self::Result {
        walk_expr(self, val)
    }

    fn visit_path(&mut self, val: &'a Path) -> Self::Result {
        let Path {
            path,
            span: _,
            id: _,
        } = val;

        visit_iter!(v: self, m: visit_path_seg, path);

        Self::Result::normal()
    }

    fn visit_path_seg(&mut self, val: &'a PathSeg) -> Self::Result {
        let PathSeg {
            name,
            span: _,
            id: _,
        } = val;

        self.visit_name(name)
    }

    fn visit_fn_decl(&mut self, val: &'a FnDecl) -> Self::Result {
        let FnDecl {
            sig,
            block,
            span: _,
            id: _,
        } = val;

        try_visit!(self.visit_fn_sig(sig));
        self.visit_block(block)
    }

    fn visit_fn_sig(&mut self, val: &'a FnSig) -> Self::Result {
        let FnSig {
            name,
            args,
            ret_type,
            span: _,
            id: _,
        } = val;

        try_visit!(self.visit_name(name));

        visit_iter!(v: self, m: visit_arg, args);

        self.visit_ty(ret_type)
    }

    fn visit_arg(&mut self, val: &'a Arg) -> Self::Result {
        let Arg { ident, ty, id: _ } = val;

        try_visit!(self.visit_name(ident));
        self.visit_ty(ty)
    }

    fn visit_block(&mut self, val: &'a Block) -> Self::Result {
        let Block {
            stmts,
            span: _,
            id: _,
            expr,
        } = val;

        visit_iter!(v: self, m: visit_stmt, stmts);
        maybe_visit!(v: self, m: visit_expr, expr);

        Self::Result::normal()
    }

    fn visit_stmt(&mut self, val: &'a Stmt) -> Self::Result {
        let Stmt {
            kind,
            span: _,
            id: _,
        } = val;
        match kind {
            StmtKind::Expr(e) => self.visit_expr(e),
            StmtKind::LocalVar(v) => self.visit_var_stmt(v),
            StmtKind::Thing(d) => self.visit_thing(d),
        }
    }

    fn visit_name(&mut self, _: &'a Name) -> Self::Result {
        Self::Result::normal()
    }
}

pub fn walk_expr<'vis, V: Visitor<'vis>>(v: &mut V, expr: &'vis Expr) -> V::Result {
    let Expr { ty, span: _, id: _ } = expr;

    match ty {
        ExprType::Index { indexed, index } => {
            try_visit!(v.visit_expr(indexed), v.visit_expr(index));
            V::Result::normal()
        }
        ExprType::Break | ExprType::Constant(..) => V::Result::normal(),

        ExprType::BinaryExpr { lhs, rhs, op: _ } => {
            try_visit!(v.visit_expr(lhs), v.visit_expr(rhs));

            V::Result::normal()
        }

        ExprType::UnaryExpr { op: _, target } => v.visit_expr(target),

        ExprType::Group(e) => v.visit_expr(e),

        ExprType::List(exprs) => {
            visit_iter!(v: v, m: visit_expr, exprs);
            V::Result::normal()
        }

        ExprType::Assign {
            lvalue,
            rvalue,
            mode: _,
        } => {
            try_visit!(v.visit_expr(lvalue));
            v.visit_expr(rvalue)
        }

        ExprType::FunCall { callee, args } => {
            try_visit!(v.visit_expr(callee));
            visit_iter!(v: v, m: visit_expr, args);
            V::Result::normal()
        }

        ExprType::MethodCall {
            receiver,
            args,
            name,
        } => {
            try_visit!(v.visit_expr(receiver));
            visit_iter!(v: v, m: visit_expr, args);
            v.visit_name(name)
        }

        ExprType::Path(p) => v.visit_path(p),

        ExprType::While { cond, body } | ExprType::Until { cond, body } => {
            try_visit!(v.visit_expr(cond));
            v.visit_block(body)
        }

        ExprType::For {
            iterable,
            pat,
            body,
        } => {
            try_visit!(v.visit_expr(iterable), v.visit_pat(pat));
            v.visit_block(body)
        }

        ExprType::Loop { body } => v.visit_block(body),

        ExprType::If {
            cond,
            if_block,
            else_ifs,
            otherwise,
        } => {
            try_visit!(v.visit_expr(cond), v.visit_block(if_block));

            for ElseIf { cond, body } in else_ifs {
                v.visit_expr(cond);
                v.visit_block(body);
            }

            maybe_visit!(v: v, m: visit_block, otherwise);

            V::Result::normal()
        }

        ExprType::FieldAccess { source, field } => {
            try_visit!(v.visit_expr(source));
            v.visit_name(field)
        }

        ExprType::Lambda { args, body } => {
            for args in args {
                v.visit_arg(args);
            }

            match body {
                LambdaBody::Block(b) => v.visit_block(b),
                LambdaBody::Expr(e) => v.visit_expr(e),
            }
        }

        ExprType::Return { ret } => {
            maybe_visit!(v: v, m: visit_expr, ret);
            V::Result::normal()
        }

        ExprType::Block(b) => v.visit_block(b),
    }
}

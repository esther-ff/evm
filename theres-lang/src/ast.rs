use crate::lexer::Span;
use crate::session::SymbolId;
use core::ops::ControlFlow;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AstId {
    private: u32,
}

impl AstId {
    pub fn new(n: u32) -> Self {
        Self { private: n }
    }
}

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
    pub id: AstId,
}

impl Expr {
    pub fn new(ty: ExprType, span: Span, id: AstId) -> Self {
        Self { ty, span, id }
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

    MethodCall {
        receiver: Box<Expr>,
        args: Vec<Expr>,
        name: Name,
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

    Return {
        ret: Option<Box<Expr>>,
    },

    Make {
        created: Ty,
        ctor_args: Vec<Expr>,
    },

    Path(Path),
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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Bound {
    pub span: Span,
    pub interface: Path,
    pub id: AstId,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct GenericParam {
    pub ident: Name,
    pub bounds: Vec<Bound>,
    pub id: AstId,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Generics {
    pub params: Vec<GenericParam>,
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

    /// Regular type like `u32`
    Regular(Name),

    /// With generics
    Params { base: Name, generics: Vec<Ty> },

    /// `self` argument
    /// in methods
    MethodSelf,
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
            ret_type,
            args,
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
pub struct FnArgs {
    pub args: Vec<Arg>,
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
    pub initializer: Option<Expr>,
    pub ty: Ty,
    pub id: AstId,
}

impl VariableStmt {
    pub fn new(mode: VarMode, name: Name, initializer: Option<Expr>, ty: Ty, id: AstId) -> Self {
        Self {
            mode,
            name,
            initializer,
            ty,
            id,
        }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct GlobalDecl {
    name: Name,
    initializer: Expr,
    ty: Ty,
    constant: bool,

    pub id: AstId,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum StmtKind {
    Block(Block),
    Expr(Expr),
    LocalVar(VariableStmt),
    Thing(Thing),
}

impl StmtKind {
    pub fn span(&self) -> Span {
        match self {
            Self::Block(b) => b.span,
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
            id,
            ty,
            span,
        }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct Instance {
    pub name: Name,
    pub span: Span,
    pub fields: Vec<Field>,
    pub assoc: Option<Block>,
    pub generics: Generics,
    pub id: AstId,
}

impl Instance {
    pub fn new(
        name: Name,
        span: Span,
        fields: Vec<Field>,
        assoc: Option<Block>,
        generics: Generics,
        id: AstId,
    ) -> Self {
        Self {
            name,
            id,
            span,
            fields,
            assoc,
            generics,
        }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct AnonConst {
    expr: Expr,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct AssocConst {
    value: AnonConst,
    span: Span,
    ty: Ty,
    name: Name,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct Interface {
    span: Span,
    name: Name,
    entries: Vec<InterfaceEntry>,
}

#[derive(Debug, PartialEq, PartialOrd, Clone)]
pub enum InterfaceEntry {
    ProvidedFn(FnDecl),
    TemplateFn(FnSig),
    Const(VariableStmt),
}

impl Interface {
    pub fn new(span: Span, name: Name, entries: Vec<InterfaceEntry>) -> Self {
        Self {
            span,
            name,
            entries,
        }
    }
}

#[derive(Debug, PartialEq, PartialOrd, Clone)]
pub struct Apply {
    interface: Name,
    receiver: Ty,
    span: Span,
    items: Vec<InterfaceEntry>,
}

impl Apply {
    pub fn new(interface: Name, receiver: Ty, span: Span, items: Vec<InterfaceEntry>) -> Self {
        Self {
            interface,
            receiver,
            span,
            items,
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
        Self { kind, id }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum ThingKind {
    Function(FnDecl),
    Global(GlobalDecl),
    Instance(Instance),
    Realm(Realm),
    Interface(Interface),
    Apply(Apply),
}

impl ThingKind {
    pub fn function(block: Block, span: Span, sig: FnSig, id: AstId) -> Self {
        Self::Function(FnDecl {
            span,
            block,
            sig,
            id,
        })
    }

    pub fn global(name: Name, initializer: Expr, ty: Ty, constant: bool, id: AstId) -> Self {
        Self::Global(GlobalDecl {
            name,
            initializer,
            ty,
            constant,
            id,
        })
    }

    pub fn instance(
        name: Name,
        span: Span,
        fields: Vec<Field>,
        methods: Option<Block>,
        gens: Generics,
        id: AstId,
    ) -> Self {
        Self::Instance(Instance::new(name, span, fields, methods, gens, id))
    }

    pub fn interface(name: Name, span: Span, entries: Vec<InterfaceEntry>) -> Self {
        Self::Interface(Interface::new(span, name, entries))
    }

    pub fn span(&self) -> Span {
        match self {
            Self::Function(f) => f.span,
            Self::Global(g) => g.name.span,
            Self::Instance(i) => i.span,
            Self::Interface(it) => it.span,
            Self::Apply(a) => a.span,
            Self::Realm(r) => r.span,
        }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct Realm {
    pub items: Vec<Thing>,
    pub id: AstId,
    pub span: Span,
    pub name: Name,
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
        Self { span, interned }
    }
}

pub trait VisitorResult {
    type Return;

    fn normal() -> Self;

    fn into_flow(self) -> ControlFlow<Self::Return>;

    fn into_branch(p: Self::Return) -> Self;
}

impl VisitorResult for () {
    type Return = ();

    fn into_flow(self) -> ControlFlow<Self::Return> {
        ControlFlow::Continue(())
    }

    fn normal() -> Self {}

    fn into_branch(_: Self::Return) -> Self {}
}

impl<T> VisitorResult for std::ops::ControlFlow<T> {
    type Return = T;

    fn into_flow(self) -> ControlFlow<Self::Return> {
        self
    }

    fn into_branch(p: Self::Return) -> Self {
        Self::Break(p)
    }

    fn normal() -> Self {
        ControlFlow::Continue(())
    }
}

macro_rules! try_visit {
    ($($e:expr),*) => {
        $(
            match $e.into_flow() {
                ::core::ops::ControlFlow::Continue(()) => (),

                ::core::ops::ControlFlow::Break(p) => return $crate::ast::VisitorResult::into_branch(p)

            }

       )*
    };
}

macro_rules! maybe_visit {
    (v: $v:expr, m: $m: ident, $($e:expr),*) => {$(
       {
        if let Some(thing) = $e {
            try_visit!($v.$m(thing));

            Self::Result::normal()
        } else {
            Self::Result::normal()
        }
    }
    )*};
}

macro_rules! visit_iter {
    (v: $v:expr, m: $m:ident, $($i:expr),*) => {
        $(
            {
                for entry in $i {
                    try_visit!($v.$m(entry))
                }

                Self::Result::normal()
            }
        )*
    };
}

pub trait Visitor<'a> {
    type Result: VisitorResult;

    fn visit_realm(&mut self, val: &'a Realm) -> Self::Result {
        let Realm {
            items,
            id: _,
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
            ThingKind::Global(g) => self.visit_global(g),
            ThingKind::Instance(i) => self.visit_instance(i),
            ThingKind::Apply(a) => self.visit_apply_decl(a),
            ThingKind::Interface(ia) => self.visit_interface(ia),
        }
    }

    fn visit_instance(&mut self, val: &'a Instance) -> Self::Result {
        let Instance {
            name,
            id: _,
            span: _,
            fields,
            assoc,
            generics,
        } = val;

        try_visit!(self.visit_name(name), self.visit_generics(generics));

        for field in fields {
            try_visit!(self.visit_field(field))
        }

        assoc
            .as_ref()
            .map(|x| self.visit_block(x))
            .unwrap_or_else(Self::Result::normal)
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

    fn visit_interface(&mut self, val: &'a Interface) -> Self::Result {
        let Interface {
            span: _,
            name,
            entries,
        } = val;

        visit_iter!(v: self, m: visit_interface_entry, entries);
        self.visit_name(name)
    }

    fn visit_interface_entry(&mut self, val: &'a InterfaceEntry) -> Self::Result {
        match val {
            InterfaceEntry::ProvidedFn(f) => self.visit_fn_decl(f),
            InterfaceEntry::TemplateFn(s) => self.visit_fn_sig(s),
            InterfaceEntry::Const(c) => self.visit_var_stmt(c),
        }
    }

    fn visit_var_stmt(&mut self, val: &'a VariableStmt) -> Self::Result {
        let VariableStmt {
            mode: _,
            name,
            initializer,
            ty,
            id: _,
        } = val;

        try_visit!(self.visit_name(name), self.visit_ty(ty));

        maybe_visit!(v: self, m: visit_expr, initializer)
    }

    fn visit_ty(&mut self, val: &'a Ty) -> Self::Result {
        let Ty {
            kind,
            span: _,
            id: _,
        } = val;

        match kind {
            TyKind::Fn { args, ret } => {
                try_visit!(visit_iter!(v: self, m: visit_ty, args));

                maybe_visit!(v: self, m: visit_ty, ret)
            }

            TyKind::Array(ty) => self.visit_ty(ty),

            TyKind::Params { base, generics } => {
                try_visit!(self.visit_name(base));

                visit_iter!(v: self, m: visit_ty, generics)
            }

            TyKind::MethodSelf | TyKind::Regular(..) => Self::Result::normal(),
        }
    }

    fn visit_assoc_const(&mut self, val: &'a AssocConst) -> Self::Result {
        let AssocConst {
            value,
            span: _,
            ty,
            name,
        } = val;

        try_visit!(
            self.visit_anon_const(value),
            self.visit_ty(ty),
            self.visit_name(name)
        );

        Self::Result::normal()
    }

    fn visit_anon_const(&mut self, val: &'a AnonConst) -> Self::Result {
        let AnonConst { expr } = val;
        self.visit_expr(expr)
    }

    fn visit_apply_decl(&mut self, val: &'a Apply) -> Self::Result {
        let Apply {
            interface,
            receiver,
            span: _,
            items,
        } = val;

        try_visit!(self.visit_name(interface), self.visit_ty(receiver));

        visit_iter!(v: self, m: visit_interface_entry, items)
    }

    fn visit_pat(&mut self, val: &'a Pat) -> Self::Result {
        let Pat { span: _, ty } = val;

        match ty {
            PatType::Ident { name } => self.visit_name(name),
            PatType::Tuple { pats } => visit_iter!(v: self, m: visit_pat, pats),

            PatType::Wild => Self::Result::normal(),
        }
    }

    fn visit_expr(&mut self, val: &'a Expr) -> Self::Result {
        let Expr { ty, span: _, id: _ } = val;

        match ty {
            ExprType::BinaryExpr { lhs, rhs, op: _ } => {
                try_visit!(self.visit_expr(lhs), self.visit_expr(rhs));

                Self::Result::normal()
            }

            ExprType::UnaryExpr { op: _, target } => self.visit_expr(target),

            ExprType::Constant(..) => Self::Result::normal(),

            ExprType::Group(e) => self.visit_expr(e),

            ExprType::CommaGroup(exprs) => visit_iter!(v: self, m: visit_expr, exprs),

            ExprType::Assign {
                lvalue,
                rvalue,
                mode: _,
            } => {
                try_visit!(self.visit_expr(lvalue));
                self.visit_expr(rvalue)
            }

            ExprType::FunCall { callee, args } => {
                try_visit!(self.visit_expr(callee));
                visit_iter!(v: self, m: visit_expr, args)
            }

            ExprType::MethodCall {
                receiver,
                args,
                name,
            } => {
                try_visit!(self.visit_expr(receiver));
                visit_iter!(v: self, m: visit_expr, args);
                self.visit_name(name)
            }

            ExprType::Variable { name } => self.visit_name(name),

            ExprType::While { cond, body } => {
                try_visit!(self.visit_expr(cond));
                self.visit_block(body)
            }

            ExprType::Until { cond, body } => {
                try_visit!(self.visit_expr(cond));
                self.visit_block(body)
            }

            ExprType::For {
                iterable,
                pat,
                body,
            } => {
                try_visit!(self.visit_expr(iterable), self.visit_pat(pat));
                self.visit_block(body)
            }

            ExprType::Loop { body } => self.visit_block(body),

            ExprType::If {
                cond,
                if_block,
                else_ifs,
                otherwise,
            } => {
                try_visit!(self.visit_expr(cond), self.visit_block(if_block));

                for ElseIf { cond, body } in else_ifs {
                    self.visit_expr(cond);
                    self.visit_block(body);
                }

                maybe_visit!(v: self, m: visit_block, otherwise)
            }

            ExprType::ArrayDecl {
                ty,
                size,
                initialize,
            } => {
                try_visit!(self.visit_ty(ty), self.visit_expr(size));
                visit_iter!(v: self, m: visit_expr, initialize)
            }

            ExprType::FieldAccess { source, field } => {
                try_visit!(self.visit_expr(source));
                self.visit_name(field)
            }

            ExprType::Path(path) => self.visit_path(path),

            ExprType::Lambda { args, body } => {
                visit_iter!(v: self, m: visit_pat, args);

                match body {
                    LambdaBody::Block(b) => self.visit_block(b),
                    LambdaBody::Expr(e) => self.visit_expr(e),
                }
            }

            ExprType::Return { ret } => maybe_visit!(v: self, m: visit_expr, ret),

            ExprType::Make { created, ctor_args } => {
                try_visit!(self.visit_ty(created));
                visit_iter!(v: self, m: visit_expr, ctor_args)
            }
        }
    }

    fn visit_generics(&mut self, val: &'a Generics) -> Self::Result {
        let Generics {
            params,
            span: _,
            id: _,
        } = val;
        visit_iter!(v: self, m: visit_generic_param, params)
    }

    fn visit_generic_param(&mut self, val: &'a GenericParam) -> Self::Result {
        let GenericParam {
            ident,
            bounds,
            id: _,
        } = val;

        try_visit!(self.visit_name(ident));

        visit_iter!(v: self, m: visit_bound, bounds)
    }

    fn visit_bound(&mut self, val: &'a Bound) -> Self::Result {
        let Bound {
            span: _,
            interface,
            id: _,
        } = val;

        self.visit_path(interface)
    }

    fn visit_path(&mut self, val: &'a Path) -> Self::Result {
        let Path {
            path,
            span: _,
            id: _,
        } = val;

        visit_iter!(v: self, m: visit_path_seg, path)
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
        maybe_visit!(v: self, m: visit_expr, expr)
    }

    fn visit_stmt(&mut self, val: &'a Stmt) -> Self::Result {
        let Stmt {
            kind,
            span: _,
            id: _,
        } = val;
        match kind {
            StmtKind::Block(b) => self.visit_block(b),
            StmtKind::Expr(e) => self.visit_expr(e),
            StmtKind::LocalVar(v) => self.visit_var_stmt(v),
            StmtKind::Thing(d) => self.visit_thing(d),
        }
    }

    fn visit_global(&mut self, val: &'a GlobalDecl) -> Self::Result {
        let GlobalDecl {
            name,
            initializer,
            ty,
            constant: _,
            id: _,
        } = val;

        try_visit!(
            self.visit_name(name),
            self.visit_expr(initializer),
            self.visit_ty(ty)
        );

        Self::Result::normal()
    }

    fn visit_name(&mut self, _: &'a Name) -> Self::Result {
        Self::Result::normal()
    }
}

mod private {
    crate::newtyped_index!(LocalId, LocalMap, LocalVec, LocalSlice);
    crate::newtyped_index!(ParamId, ParamMap, ParamVec, ParamSlice);

    pub type Locals<'ir> = LocalVec<super::LocalData<'ir>>;
    pub type Params<'ir> = ParamVec<super::ParamData<'ir>>;
}

use std::collections::{HashMap, HashSet};
use std::iter::once;
use std::mem;

use crate::air::def::{DefId, DefType, Resolved};
use crate::air::node::{self, StmtKind};

use crate::air::AirId;
use crate::air::node::{AirLiteral, Constant, Expr as AirExpr, Local};
use crate::arena::Arena;
use crate::ast::{self, UnaryOp};
use crate::id::IdxVec;
use crate::pill;
use crate::symbols::SymbolId;
use crate::types::fun_cx::FieldId;
use crate::types::ty::{Instance, TyKind};

use crate::session::Session;
use crate::span::Span;
use crate::types::{fun_cx::TypeTable, ty::Ty};

pub use private::{LocalId, Locals, ParamId, Params};

#[derive(Debug, Clone, Copy)]
pub struct LocalData<'ir> {
    ty: Ty<'ir>,
    mutbl: Constant,
    name: Option<SymbolId>,
}

impl<'ir> LocalData<'ir> {
    pub fn ty(&self) -> Ty<'ir> {
        self.ty
    }
}

impl<'ir> From<LocalData<'ir>> for crate::pill::body::LocalData<'ir> {
    fn from(value: LocalData<'ir>) -> Self {
        match value.name {
            None => crate::pill::body::LocalData::new(value.mutbl, value.ty),

            Some(v) => crate::pill::body::LocalData::new_user(value.mutbl, value.ty, v),
        }
    }
}

#[derive(Debug)]
pub struct ParamData<'ir> {
    ty: Ty<'ir>,
    name: Option<SymbolId>,
}

impl<'ir> ParamData<'ir> {
    pub fn ty(&self) -> Ty<'ir> {
        self.ty
    }

    pub fn name(&self) -> Option<SymbolId> {
        self.name
    }
}

#[derive(Debug)]
pub struct Expr<'ir> {
    pub kind: ExprKind<'ir>,
    pub ty: Ty<'ir>,
    pub span: Span,
}

impl Expr<'_> {
    pub(crate) fn is_assignable_to(&self) -> bool {
        matches!(
            self.kind,
            ExprKind::Deref(..)
                | ExprKind::Field { .. }
                | ExprKind::Local(..)
                | ExprKind::Upvar { .. }
                | ExprKind::Index { .. }
                | ExprKind::Param(..)
        )
    }
}

#[derive(Debug, Copy, Clone)]
pub enum LogicalOp {
    And,
    Or,
}

#[derive(Debug, Copy, Clone)]
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

impl From<BinOp> for pill::op::BinOp {
    fn from(value: BinOp) -> Self {
        #[allow(clippy::enum_glob_use)]
        use pill::op::BinOp::*;

        match value {
            BinOp::Add => Add,
            BinOp::Sub => Sub,
            BinOp::Div => Div,
            BinOp::Mul => Mul,
            BinOp::Shl => Shl,
            BinOp::Shr => Shr,
            BinOp::Mod => Mod,
            BinOp::Or => BitOr,
            BinOp::And => BitAnd,
            BinOp::Xor => BitXor,
            BinOp::Eq => Eq,
            BinOp::Neq => Ne,
            BinOp::Gr => Gr,
            BinOp::Gte => Ge,
            BinOp::Lt => Lt,
            BinOp::Le => Le,
        }
    }
}

impl From<LogicalOp> for pill::op::BinOp {
    fn from(value: LogicalOp) -> Self {
        match value {
            LogicalOp::And => pill::op::BinOp::BitAnd,
            LogicalOp::Or => pill::op::BinOp::BitOr,
        }
    }
}

#[derive(Debug)]
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

    Lambda,

    Unary {
        operand: &'ir Expr<'ir>,
        op: UnaryOp,
    },

    Block(Block<'ir>),

    If {
        cond: &'ir Expr<'ir>,
        true_: &'ir Expr<'ir>,
        false_: Option<&'ir Expr<'ir>>,
    },

    Return(Option<&'ir Expr<'ir>>),

    Loop(Block<'ir>),

    Lit(AirLiteral),

    Index {
        base: &'ir Expr<'ir>,
        idx: &'ir Expr<'ir>,
    },

    AddrOf(&'ir Expr<'ir>),

    Deref(&'ir Expr<'ir>),

    Local(LocalId),

    Param(ParamId),

    List(&'ir [Expr<'ir>]),

    Upvar {
        upvar: AirId,
    },

    Field {
        base: &'ir Expr<'ir>,
        field_idx: FieldId,
    },

    Adt {
        def: Instance<'ir>,
        fields: &'ir [Expr<'ir>],
    },

    Semi(&'ir Expr<'ir>),

    Break,

    /// Represents the literal for some zero-sized type
    /// like a function type
    Empty,
}

#[derive(Debug)]
pub struct Block<'ir> {
    exprs: Vec<Expr<'ir>, &'ir Arena>,
}

impl<'ir> Block<'ir> {
    pub fn exprs(&self) -> &[Expr<'ir>] {
        &self.exprs
    }
}

#[derive(Debug)]
pub struct Eair<'ir> {
    pub locals: Locals<'ir>,
    pub params: Params<'ir>,
    pub entry: Option<Expr<'ir>>,
    pub kind: BodyKind,
    pub air_id_map: HashMap<AirId, LocalId>,
}

#[derive(Debug)]
pub enum BodyKind {
    Lambda,
    Function,
}

pub struct EairBuilder<'ir> {
    eair: Eair<'ir>,
    types: &'ir TypeTable<'ir>,
    cx: &'ir Session<'ir>,
    current_block: Vec<Expr<'ir>, &'ir Arena>,
    upvars: &'ir HashSet<AirId>,
    lowered_locals: HashMap<AirId, LocalId>,
    lowered_params: HashMap<AirId, ParamId>,
}

impl<'ir> EairBuilder<'ir> {
    fn lower_local(&mut self, local: &Local<'_>) -> LocalId {
        let ty = self.types.node_ty(local.air_id);
        let id = self.eair.locals.push(LocalData {
            ty,
            mutbl: local.mutability,
            name: local.name.interned.into(),
        });

        if let Some(expr) = local.init {
            let init = self.lower_expr(expr);
            let local_ref = self.cx.arena().alloc(Expr {
                span: Span::DUMMY,
                ty,
                kind: ExprKind::Local(id),
            });

            let actual_init = Expr {
                kind: ExprKind::Assign {
                    lvalue: local_ref,
                    rvalue: self.cx.arena().alloc(init),
                    from_lowering: true,
                },
                span: expr.span,
                ty: self.cx.types.nil,
            };

            self.current_block.push(actual_init);
        }

        id
    }

    fn lower_block(&mut self, block: &node::Block<'_>) -> Block<'ir> {
        let old = mem::replace(&mut self.current_block, Vec::new_in(self.cx.arena()));

        for stmt in block.stmts {
            match stmt.kind {
                StmtKind::Local(local) => {
                    let id = self.lower_local(local);
                    assert!(self.lowered_locals.insert(local.air_id, id).is_none());
                }

                StmtKind::Expr(expr) => {
                    let expr = self.lower_expr(expr);

                    let actual = Expr {
                        ty: self.cx.types.nil,
                        span: expr.span,
                        kind: ExprKind::Semi(self.cx.arena().alloc(expr)),
                    };

                    self.current_block.push(actual);
                }

                StmtKind::Thing(..) => (),
            }
        }

        if let Some(ret) = block.expr {
            let expr = self.lower_expr(ret);
            self.current_block.push(expr);
        }

        let new = mem::replace(&mut self.current_block, old);
        Block { exprs: new }
    }

    fn lower_expr_alloc(&mut self, expr: &AirExpr<'_>) -> &'ir Expr<'ir> {
        self.cx.arena().alloc(self.lower_expr(expr))
    }

    #[allow(clippy::too_many_lines)]
    fn lower_expr(&mut self, expr: &AirExpr<'_>) -> Expr<'ir> {
        #[allow(clippy::enum_glob_use)]
        use crate::air::node::ExprKind::*;

        let ty = self.types.type_of(expr);
        assert!(
            ty.maybe_infer().is_none(),
            "type variables in expr! {expr:#?}"
        );
        let span = expr.span;

        match expr.kind {
            Binary { lhs, rhs, op } => {
                let lhs = self.lower_expr_alloc(lhs);
                let rhs = self.lower_expr_alloc(rhs);

                match bin_op_to_eair(op) {
                    Ops::Regular(op) => {
                        /* later check for overloads */
                        Expr {
                            kind: ExprKind::Binary { lhs, rhs, op },
                            span,
                            ty,
                        }
                    }
                    Ops::Logic(op) => Expr {
                        kind: ExprKind::Logical { lhs, rhs, op },
                        ty,
                        span: expr.span,
                    },
                }
            }

            Unary { target, op } => match op {
                UnaryOp::Negation | UnaryOp::Not => Expr {
                    kind: ExprKind::Unary {
                        operand: self.lower_expr_alloc(target),
                        op,
                    },
                    ty,
                    span,
                },

                UnaryOp::Deref => Expr {
                    ty,
                    span,
                    kind: ExprKind::Deref(self.lower_expr_alloc(target)),
                },

                UnaryOp::AddrOf => Expr {
                    ty,
                    span,
                    kind: ExprKind::AddrOf(self.lower_expr_alloc(target)),
                },
            },

            Assign { variable, value } => Expr {
                kind: ExprKind::Assign {
                    lvalue: self.lower_expr_alloc(variable),
                    rvalue: self.lower_expr_alloc(value),
                    from_lowering: false,
                },
                ty,
                span,
            },

            AssignWithOp {
                variable,
                value,
                op,
            } => {
                let Ops::Regular(op) = bin_op_to_eair(op.into()) else {
                    unreachable!()
                };

                let lvalue = self.lower_expr_alloc(variable);
                let part = self.lower_expr_alloc(value);
                let rhs = Expr {
                    kind: ExprKind::Binary {
                        lhs: lvalue,
                        rhs: part,
                        op,
                    },
                    span,
                    ty,
                };

                Expr {
                    kind: ExprKind::Assign {
                        lvalue,
                        rvalue: self.cx.arena().alloc(rhs),
                        from_lowering: false,
                    },
                    ty,
                    span,
                }
            }

            List(exprs) => Expr {
                kind: ExprKind::List(
                    self.cx
                        .arena()
                        .alloc_from_iter(exprs.iter().map(|expr| self.lower_expr(expr))),
                ),
                ty,
                span,
            },

            Return { expr } => Expr {
                kind: ExprKind::Return(expr.map(|expr| self.lower_expr_alloc(expr))),
                ty,
                span,
            },

            Loop { body } => Expr {
                kind: ExprKind::Loop(self.lower_block(body)),
                ty,
                span,
            },

            Block(block) => Expr {
                kind: ExprKind::Block(self.lower_block(block)),
                ty,
                span,
            },

            Call { function, args } => {
                if let Path(path) = function.kind
                    && let Resolved::Def(did, DefType::AdtCtor) = path.res
                {
                    let instance_did = self.cx.air_get_instance_of_ctor(did);
                    let def = self.cx.instance_def(instance_did);
                    let fields = self
                        .cx
                        .arena()
                        .alloc_from_iter(args.iter().map(|arg| self.lower_expr(arg)));

                    return Expr {
                        kind: ExprKind::Adt { def, fields },
                        span,
                        ty,
                    };
                }

                let args = self
                    .cx
                    .arena()
                    .alloc_from_iter(args.iter().map(|arg| self.lower_expr(arg)));

                Expr {
                    kind: ExprKind::Call {
                        callee: self.lower_expr_alloc(function),
                        args,
                    },
                    ty,
                    span,
                }
            }

            MethodCall {
                receiver,
                method: _,
                args,
            } => {
                let did = self.types.resolve_method(expr.air_id);

                let callee = self.cx.arena().alloc(Expr {
                    kind: ExprKind::Empty,
                    span: receiver.span,
                    ty: self.cx.intern_ty(TyKind::FnDef(did)),
                });

                let args = self
                    .cx
                    .arena()
                    .alloc_from_iter(once(receiver).chain(args).map(|expr| self.lower_expr(expr)));

                Expr {
                    kind: ExprKind::Call { callee, args },
                    ty,
                    span,
                }
            }

            Field { src, field } => {
                let base = self.lower_expr_alloc(src);
                let instance = base.ty.expect_instance();
                let (field_idx, _) = instance
                    .fields
                    .iter()
                    .find(|(_, f)| f.name == field)
                    .expect("typeck should have caught this!");

                Expr {
                    kind: ExprKind::Field { base, field_idx },
                    span,
                    ty,
                }
            }

            Lambda(..) => Expr {
                kind: ExprKind::Lambda,
                ty,
                span,
            },

            If {
                condition,
                block,
                else_,
            } => {
                let cond = self.lower_expr_alloc(condition);
                let block_span = block.span;
                let block = self.lower_block(block);
                let false_ = else_.map(|expr| self.lower_expr_alloc(expr));

                let true_ = self.cx.arena().alloc(Expr {
                    ty: block.exprs.last().map_or(self.cx.types.nil, |expr| expr.ty),
                    kind: ExprKind::Block(block),
                    span: block_span,
                });

                Expr {
                    kind: ExprKind::If {
                        cond,
                        true_,
                        false_,
                    },
                    ty,
                    span,
                }
            }

            Literal(lit) => Expr {
                kind: ExprKind::Lit(lit),
                ty,
                span,
            },

            Index {
                index,
                indexed_thing,
            } => Expr {
                kind: ExprKind::Index {
                    base: self.lower_expr_alloc(indexed_thing),
                    idx: self.lower_expr_alloc(index),
                },
                ty,
                span,
            },

            Break => Expr {
                kind: ExprKind::Break,
                ty,
                span,
            },

            Path(path) => match self.types.resolve_path(path) {
                Resolved::Err => unreachable!("shouldn't put `Resolved::Err`s in EAIR"),

                Resolved::Local(ref local_id) => {
                    let kind = if self.upvars.contains(local_id) {
                        ExprKind::Upvar { upvar: *local_id }
                    } else {
                        match self.lowered_params.get(local_id) {
                            None => {
                                let lowered_id = *self.lowered_locals.get(local_id).unwrap();
                                ExprKind::Local(lowered_id)
                            }

                            Some(p) => ExprKind::Param(*p),
                        }
                    };

                    Expr { kind, ty, span }
                }

                Resolved::Def(did, def_ty) => match def_ty {
                    DefType::Fun | DefType::NativeFn => Expr {
                        kind: ExprKind::Empty,
                        ty: self.cx.intern_ty(TyKind::FnDef(did)),
                        span,
                    },

                    DefType::Instance
                    | DefType::AdtCtor
                    | DefType::Field
                    | DefType::Bind
                    | DefType::Lambda
                    | DefType::Realm => unreachable!("non-sense"),
                },

                Resolved::Prim(..) => unreachable!("`Resolved::Prim` in path expr?"),
            },
        }
    }
}

enum Ops {
    Regular(BinOp),
    Logic(LogicalOp),
}

fn bin_op_to_eair(binop: ast::BinOp) -> Ops {
    #[allow(clippy::enum_glob_use)]
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

pub fn build_eair<'cx>(cx: &'cx Session<'cx>, did: DefId) -> &'cx Eair<'cx> {
    let dummy = cx.arena().alloc(HashSet::new());

    let types;
    let inputs;

    let mut params: Params<'cx> = IdxVec::new();
    let locals: Locals<'cx> = IdxVec::new();

    let kind = match cx.def_type(did) {
        DefType::Lambda => BodyKind::Lambda,
        DefType::Fun => BodyKind::Function,

        wrong => unreachable!("`build_eair`: trying to lower a {wrong:#?}"),
    };

    let upvars = if let DefType::Lambda = cx.def_type(did) {
        let parent = cx.air_get_parent(did);
        let upvars = cx.upvars_of(did);
        types = cx.typeck(parent);
        let def = cx.air_get_lambda(did);
        inputs = def.inputs;
        upvars
    } else {
        types = cx.typeck(did);
        let air_sig = cx.air_get_fn(did).0;

        inputs = air_sig.arguments;

        dummy
    };

    let lowered_params: HashMap<_, _> = inputs
        .iter()
        .map(|param| {
            let ty = types.node_ty(param.air_id);
            let id = params.push(ParamData {
                ty,
                name: param.name.interned.into(),
            });
            (param.air_id, id)
        })
        .collect();

    let body = cx.air_body(did);

    let eair = Eair {
        locals,
        params,
        entry: None,
        kind,
        air_id_map: HashMap::new(),
    };

    let mut builder = EairBuilder {
        eair,
        cx,
        types,
        current_block: Vec::new_in(cx.arena()),
        upvars,
        lowered_locals: HashMap::new(),
        lowered_params,
    };

    let entry = builder.lower_expr(body);
    builder.eair.entry.replace(entry);
    assert!(builder.eair.entry.is_some());

    if cx.flags().dump_eair {
        use std::io::Write as _;

        let w = std::io::stdout();
        let mut lock = w.lock();
        writeln!(&mut lock, "{:#?}", &builder.eair).expect("writing to stdout failed!");
    }

    let map = mem::take(&mut builder.lowered_locals);
    builder.eair.air_id_map = map;
    cx.arena().alloc(builder.eair)
}

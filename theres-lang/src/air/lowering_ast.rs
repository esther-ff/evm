use core::panic;
use std::collections::HashMap;
use std::panic::Location;

#[allow(clippy::wildcard_imports)]
use crate::ast::*;

use crate::air;
use crate::air::def::{BodyId, BodyVec, DefId, DefMap, DefType, DefVec, Resolved};
use crate::air::node::{self, Constant, ExprKind, Lambda, Node, Param};
use crate::errors::{Phase, TheresError};
use crate::id::IdxVec;
use crate::lexer::Span;
use crate::parser::{AstId, AstIdMap};
use crate::session::{Session, SymbolId};

crate::newtyped_index!(AirId, AirIdMap, AirVec);
crate::newtyped_index!(LocalId, LocalMap, LocalVec);

pub enum AstLowerError {
    WrongAssign,
}

impl TheresError for AstLowerError {
    fn phase() -> Phase {
        Phase::LoweringAst
    }

    fn message(&self) -> std::borrow::Cow<'static, str> {
        "cannot assign into this expression".into()
    }
}

pub struct Mappings {
    instance_to_field_list: AstIdMap<Vec<DefId>>,
    field_id_to_instance: AstIdMap<DefId>,
    resolution_map: AstIdMap<Resolved<AstId>>,
    ast_id_to_def_id: AstIdMap<DefId>,
    def_id_to_ast_id: DefMap<AstId>,
    instance_to_bind: DefMap<Vec<AstId>>,
    binds_to_resolved_ty_id: AstIdMap<AstId>,
    binds_to_items: AstIdMap<Vec<AstId>>,

    self_ty_ast_id_to_ty: AstIdMap<Ty>,
    pub(super) def_types: DefVec<DefType>,
}

impl Mappings {
    pub fn new(
        ast_id_to_def_id: AstIdMap<DefId>,
        def_id_to_ast_id: DefMap<AstId>,
        def_types: DefVec<DefType>,
    ) -> Self {
        Self {
            instance_to_field_list: HashMap::new(),
            field_id_to_instance: HashMap::new(),
            resolution_map: HashMap::new(),
            ast_id_to_def_id,
            def_id_to_ast_id,
            instance_to_bind: HashMap::new(),
            binds_to_resolved_ty_id: HashMap::new(),
            binds_to_items: HashMap::new(),
            self_ty_ast_id_to_ty: HashMap::new(),
            def_types,
        }
    }

    pub fn debug_resolutions(&self) -> impl IntoIterator<Item = (&AstId, &Resolved<AstId>)> {
        &self.resolution_map
    }

    pub fn instance_to_bind(&self, id: DefId) -> Option<&Vec<AstId>> {
        self.instance_to_bind.get(&id)
    }

    pub fn insert_instance_to_bind(&mut self, id: DefId, bind: AstId) {
        match self.instance_to_bind.get_mut(&id) {
            Some(storage) => storage.push(bind),

            None => {
                self.instance_to_bind.insert(id, vec![bind]);
            }
        }
    }

    pub fn insert_instance_field(&mut self, instance_id: AstId, field_id: DefId) {
        match self.instance_to_field_list.get_mut(&instance_id) {
            Some(storage) => storage.push(field_id),

            None => {
                self.instance_to_field_list
                    .insert(instance_id, vec![field_id]);
            }
        }
    }

    pub fn def_id_of(&self, id: AstId) -> DefId {
        match self.ast_id_to_def_id.get(&id) {
            Some(id) => *id,
            None => panic!("Provided `AstId` ({id:?}) is not mapped to any DefId!"),
        }
    }

    pub fn ast_id_of(&self, id: DefId) -> AstId {
        match self.def_id_to_ast_id.get(&id) {
            Some(id) => *id,
            None => panic!("Provided `DefId` ({id:?}) is not mapped to any AstId!"),
        }
    }

    pub fn map_to_resolved(&mut self, id: AstId, res: Resolved<AstId>) {
        log::trace!("{id} resolves to {res:?}, loc: {}", Location::caller());
        self.resolution_map.insert(id, res);
    }

    #[track_caller]
    pub fn resolve(&mut self, id: AstId) -> Resolved<AstId> {
        log::trace!("`resolve` id={id}");
        let ret = self
            .resolution_map
            .get(&id)
            .copied()
            .expect("Given AstId is not mapped to any resolution!");
        log::trace!("`resolved` resolved to {ret:?}");
        ret
    }
}

pub struct AirMap<'air> {
    nodes: AirIdMap<Node<'air>>,
    def_id_to_air_id: DefMap<AirId>,
    bodies: BodyVec<&'air node::Expr<'air>>,
    node_to_body: DefMap<BodyId>,

    pub(super) child_to_parent: HashMap<DefId, DefId>,
    field_to_instance: HashMap<DefId, DefId>,
    ctor_to_instance: HashMap<DefId, DefId>,

    pub(super) def_types: DefVec<DefType>,
}

impl<'air> AirMap<'air> {
    pub fn new() -> Self {
        Self {
            nodes: HashMap::new(),

            def_id_to_air_id: HashMap::new(),
            bodies: IdxVec::new(),

            child_to_parent: HashMap::new(),
            node_to_body: HashMap::new(),
            field_to_instance: HashMap::new(),
            ctor_to_instance: HashMap::new(),
            def_types: IdxVec::new(),
        }
    }

    #[track_caller]
    pub fn map_def_id_to_air(&mut self, def_id: DefId, air_id: AirId) {
        let dbg = self.def_id_to_air_id.insert(def_id, air_id);
        assert!(
            dbg.is_none(),
            "{def_id:?} already mapped to a AirId!, loc: {}",
            Location::caller()
        );
    }

    pub fn map_field_to_instance(&mut self, instance: DefId, field: DefId) {
        self.field_to_instance.insert(field, instance);
    }

    pub fn get_instance_of_field(&self, field: DefId) -> DefId {
        self.field_to_instance
            .get(&field)
            .copied()
            .expect("Field's DefId wasn't mapped to any instance")
    }

    pub fn get_def(&'air self, def_id: DefId) -> &'air Node<'air> {
        self.get_node(
            self.def_id_to_air_id
                .get(&def_id)
                .copied()
                .expect("DefId wasn't mapped to any AirId"),
        )
    }

    pub fn get_thing(&'air self, def_id: DefId) -> &'air node::Thing<'air> {
        let Node::Thing(thing) = self.get_node(
            self.def_id_to_air_id
                .get(&def_id)
                .copied()
                .expect("DefId wasn't mapped to any AirId"),
        ) else {
            dbg!(
                self.get_node(
                    self.def_id_to_air_id
                        .get(&def_id)
                        .copied()
                        .expect("DefId wasn't mapped to any AirId"),
                )
            );
            panic!("`DefId` pointed to not a definition")
        };

        thing
    }

    pub fn get_local(&'air self, air_id: AirId) -> &'air node::Local<'air> {
        let node::Node::Local(local) = self.get_node(air_id) else {
            panic!("air id doesn't point to a stmt",)
        };

        local
    }

    pub fn insert_node(&mut self, node: node::Node<'air>, air_id: AirId) {
        self.nodes.insert(air_id, node);
    }

    pub fn nodes(&self) -> impl IntoIterator<Item = &Node<'air>> {
        self.nodes.values()
    }

    pub fn get_node(&'air self, air_id: AirId) -> &'air Node<'air> {
        log::trace!("get_node air_id={air_id}");
        match self.nodes.get(&air_id) {
            None => panic!(
                "Invalid `AirId` ({air_id:?}) given to `get_node`! loc: {}",
                Location::caller()
            ),
            Some(node) => node,
        }
    }

    pub fn insert_body_of(&mut self, body: &'air node::Expr<'air>, body_owner: DefId) -> BodyId {
        let body_id = self.bodies.push(body);
        self.node_to_body.insert(body_owner, body_id);
        body_id
    }

    pub fn body_of(&self, body: DefId) -> &'air node::Expr<'air> {
        let id = self.node_to_body[&body];
        self.get_body(id)
    }

    pub fn bodies(&self) -> &[&node::Expr<'air>] {
        self.bodies.as_slice()
    }

    pub fn get_body(&self, body: BodyId) -> &'air node::Expr<'air> {
        let Some(expr_body) = self.bodies.get(body).copied() else {
            panic!("Invalid `BodyId` given ({body:#?}), no function body mapped to it!",)
        };

        expr_body
    }

    pub fn expect_fn(&'air self, def_id: DefId) -> (&'air node::FnSig<'air>, SymbolId) {
        match self.get_def(def_id) {
            Node::Thing(thing) => {
                let node::ThingKind::Fn { sig, name } = thing.kind else {
                    panic!(
                        "`DefId` given to `expect_fn` did not point to any function, but: {thing:#?}"
                    )
                };

                (sig, name.interned)
            }

            Node::BindItem(bind_item) => {
                let node::BindItemKind::Fun { sig, name } = bind_item.kind else {
                    panic!(
                        "`DefId` given to `expect_fn` did not point to any function (checked bind item)"
                    )
                };

                (sig, name)
            }

            any => {
                panic!("`DefId` given to `expect_fn` did not point to any function, but: {any:#?}")
            }
        }
    }

    pub fn expect_instance(&'air self, def_id: DefId) -> (&'air [node::Field<'air>], Name) {
        let node::ThingKind::Instance {
            fields,
            name,
            ctor_id: _,
        } = self.get_thing(def_id).kind
        else {
            panic!("`DefId` given to `expect_fn` did not point to a `instance`")
        };

        (fields, name)
    }

    #[inline]
    pub fn is_ctor(&self, id: DefId) -> bool {
        self.ctor_to_instance.contains_key(&id)
    }

    pub fn get_instance_of_ctor(&self, ctor_def_id: DefId) -> DefId {
        self.ctor_to_instance
            .get(&ctor_def_id)
            .copied()
            .expect("this `DefId` of a ctor wasn't mapped to any Instance")
    }

    pub fn def_type(&self, did: DefId) -> DefType {
        self.def_types[did]
    }
}

#[derive(Debug, Clone, Copy)]
enum DesugarLoop {
    While,
    Until,
}

pub struct AstLowerer<'air> {
    session: &'air Session<'air>,

    map: Mappings,

    air_id_counter: u32,

    ast_id_to_air_id: AstIdMap<AirId>,

    current_instance: Option<DefId>,

    current_bind_ty: Option<&'air node::Ty<'air>>,
}

impl<'air> AstLowerer<'air> {
    pub fn new(map: Mappings, session: &'air Session<'air>) -> Self {
        Self {
            map,
            current_instance: None,
            current_bind_ty: None,
            session,

            air_id_counter: 0,
            ast_id_to_air_id: HashMap::new(),
        }
    }

    /// Returns the next id that will be valid
    /// after inserting a node into the air map
    ///
    /// Panics if the same `AstId` is again used for this function
    /// as it maps `AstId`s to `AirId`s for lowering `Resolved`s
    pub fn next_air_id(&mut self, ast_id: AstId) -> AirId {
        log::trace!("next_air_id ast_id={ast_id}");

        let air_id = AirId::new(self.air_id_counter);
        self.air_id_counter += 1;
        let ret = self.ast_id_to_air_id.insert(ast_id, air_id);

        assert!(
            ret.is_none(),
            "duplicate `AstId` given to `next_air_id` ({} -> {})\n",
            ast_id,
            ret.unwrap(),
        );

        if let Some(def_id) = self.map.ast_id_to_def_id.get(&ast_id) {
            self.session
                .air_mut(|map| map.map_def_id_to_air(*def_id, air_id));
        }

        air_id
    }

    /// Generates another `AirId`
    /// with no requirements
    fn new_air_id(&mut self) -> AirId {
        let air_id = AirId::new(self.air_id_counter);
        self.air_id_counter += 1;
        air_id
    }

    #[track_caller]
    fn map_ast_id_to_air_id(&self, ast_id: AstId) -> AirId {
        self.ast_id_to_air_id
            .get(&ast_id)
            .copied()
            .unwrap_or_else(|| panic!("AstId ({ast_id:#?}) isn't mapped to any AirId!"))
    }

    fn lower_args<'a>(&mut self, a: impl Iterator<Item = &'a Expr>) -> &'air [node::Expr<'air>] {
        self.session
            .arena()
            .alloc_from_iter(a.map(|arg| self.lower_expr_noalloc(arg)))
    }

    #[allow(clippy::too_many_lines)]
    #[track_caller]
    fn lower_expr_noalloc(&mut self, expr: &Expr) -> node::Expr<'air> {
        let air_id = self.next_air_id(expr.id);

        let air_expr_kind = match &expr.ty {
            ExprType::Break => node::ExprKind::Break,

            ExprType::Index { indexed, index } => node::ExprKind::Index {
                index: self.lower_expr(index),
                indexed_thing: self.lower_expr(indexed),
            },
            ExprType::BinaryExpr { lhs, rhs, op } => node::ExprKind::Binary {
                lhs: self.lower_expr(lhs),
                rhs: self.lower_expr(rhs),
                op: *op,
            },

            ExprType::UnaryExpr { op, target } => node::ExprKind::Unary {
                target: self.lower_expr(target),
                op: *op,
            },

            ExprType::Assign {
                lvalue,
                rvalue,
                mode,
            } => {
                let variable = self.lower_expr(lvalue);
                if !is_assignable_expr(variable) {
                    self.session
                        .diag()
                        .emit_err(AstLowerError::WrongAssign, lvalue.span);
                }

                match mode {
                    AssignMode::Regular => node::ExprKind::Assign {
                        variable,
                        value: self.lower_expr(rvalue),
                    },

                    any => node::ExprKind::AssignWithOp {
                        variable,
                        value: self.lower_expr(rvalue),
                        op: node::AssignOp::lower_assign_mode(*any),
                    },
                }
            }

            ExprType::FunCall { callee, args } => node::ExprKind::Call {
                function: self.lower_expr(callee),
                args: self.lower_args(args.iter()),
            },

            ExprType::MethodCall {
                receiver,
                args,
                name,
            } => node::ExprKind::MethodCall {
                receiver: self.lower_expr(receiver),
                method: name.interned,
                args: self.lower_args(args.iter()),
            },

            ExprType::Constant(val) => {
                let lit = match val {
                    ConstantExpr::Int(v) => node::AirLiteral::Int(*v),
                    ConstantExpr::Str(v) => node::AirLiteral::Str(*v),
                    ConstantExpr::Float(v) => node::AirLiteral::Float(*v),
                    ConstantExpr::Bool(v) => node::AirLiteral::Bool(*v),
                };

                node::ExprKind::Literal(lit)
            }

            ExprType::For {
                iterable: _,
                pat: _,
                body: _,
            } => {
                todo!("lowering for loop")
            }

            ExprType::While { cond, body } => node::ExprKind::Loop {
                body: self.lower_while_or_until_loop(cond, body, DesugarLoop::While),
                reason: node::LoopDesugarKind::While,
            },

            ExprType::Until { cond, body } => node::ExprKind::Loop {
                body: self.lower_while_or_until_loop(cond, body, DesugarLoop::Until),
                reason: node::LoopDesugarKind::Until,
            },

            ExprType::Loop { body } => node::ExprKind::Loop {
                body: self.lower_block(body),
                reason: node::LoopDesugarKind::None,
            },

            ExprType::Group(expr) => return self.lower_expr_noalloc(expr),

            ExprType::CommaGroup(exprs) => node::ExprKind::CommaSep(
                self.session
                    .arena()
                    .alloc_from_iter(exprs.iter().map(|expr| self.lower_expr_noalloc(expr))),
            ),

            ExprType::List(exprs) => node::ExprKind::List(
                self.session
                    .arena()
                    .alloc_from_iter(exprs.iter().map(|expr| self.lower_expr_noalloc(expr))),
            ),

            ExprType::Return { ret } => node::ExprKind::Return {
                expr: ret.as_ref().map(|expr| self.lower_expr(expr)),
            },

            ExprType::Lambda { args, body } => {
                let did = self.map.def_id_of(expr.id);
                let inputs = self.session.arena().alloc_from_iter(args.iter().map(|arg| {
                    let id = self.next_air_id(arg.id);
                    Param::new(arg.ident, self.lower_ty(&arg.ty), id)
                }));

                let body_block = match body {
                    LambdaBody::Block(block) => {
                        let lowered_block = self.lower_block(block);

                        self.session.arena().alloc(node::Expr::new(
                            node::ExprKind::Block(lowered_block),
                            lowered_block.span,
                            lowered_block.air_id,
                        ))
                    }

                    LambdaBody::Expr(expr) => self.lower_expr(expr),
                };

                let body = self
                    .session
                    .air_mut(|air| air.insert_body_of(body_block, did));

                let lambda_desc = Lambda {
                    did,
                    inputs,
                    body,
                    output: None,
                };

                node::ExprKind::Lambda(self.session.arena().alloc(lambda_desc))
            }

            ExprType::FieldAccess { source, field } => node::ExprKind::Field {
                src: self.lower_expr(source),
                field: field.interned,
            },

            ExprType::Path(path) => node::ExprKind::Path(self.lower_path(path)),

            ExprType::Block(b) => node::ExprKind::Block(self.lower_block(b)),

            ExprType::If {
                cond,
                if_block,
                else_ifs,
                otherwise,
            } => self.lower_expr_if(cond, if_block, else_ifs, otherwise.as_ref()),
        };

        node::Expr::new(air_expr_kind, expr.span, air_id)
    }

    fn lower_while_or_until_loop(
        &mut self,
        cond: &Expr,
        body: &Block,
        desugar: DesugarLoop,
    ) -> &'air node::Block<'air> {
        log::debug!("lower while or until loop");
        let cond_block = node::Block::new(
            Span::DUMMY,
            &[],
            self.new_air_id(),
            Some(self.session.arena().alloc(node::Expr::new(
                node::ExprKind::Break,
                Span::DUMMY,
                self.new_air_id(),
            ))),
        );

        let condition = node::Expr::new(
            node::ExprKind::If {
                condition: match desugar {
                    DesugarLoop::While => self.session.arena().alloc(node::Expr::new(
                        node::ExprKind::Unary {
                            target: self.lower_expr(cond),
                            op: UnaryOp::Not,
                        },
                        cond.span,
                        self.new_air_id(),
                    )),

                    DesugarLoop::Until => self.lower_expr(cond),
                },
                block: self.session.arena().alloc(cond_block),
                else_: None,
            },
            cond.span,
            self.new_air_id(),
        );

        let loop_body = match &body.expr {
            None => node::Block::new(
                body.span,
                self.session
                    .arena()
                    .alloc_from_iter(body.stmts.iter().map(|stmt| self.lower_stmt(stmt))),
                self.next_air_id(body.id),
                Some(self.session.arena().alloc(condition)),
            ),
            Some(expr) => {
                let block_id = self.next_air_id(body.id);
                let lowered = self.lower_expr(expr);

                node::Block::new(
                    body.span,
                    self.session.arena().alloc_from_iter(
                        body.stmts.iter().map(|stmt| self.lower_stmt(stmt)).chain(
                            core::iter::once(node::Stmt::new(
                                expr.span,
                                node::StmtKind::Expr(lowered),
                                lowered.air_id,
                            )),
                        ),
                    ),
                    block_id,
                    Some(self.session.arena().alloc(condition)),
                )
            }
        };

        self.session.arena().alloc(loop_body)
    }

    // might be broken!
    fn lower_expr_if(
        &mut self,
        cond: &Expr,
        if_block: &Block,
        else_ifs: &[ElseIf],
        otherwise: Option<&Block>,
    ) -> air::node::ExprKind<'air> {
        let first = else_ifs.first();
        let rest = else_ifs.get(1..).unwrap_or(&[]);

        node::ExprKind::If {
            condition: self.lower_expr(cond),
            block: self.lower_block(if_block),
            else_: first
                .map(|first| {
                    let expr_kind = self.lower_expr_if(&first.cond, &first.body, rest, otherwise);
                    let expr = node::Expr::new(
                        expr_kind,
                        Span::between(first.cond.span, first.body.span),
                        self.new_air_id(),
                    );

                    self.session.arena().alloc(expr)
                })
                .or_else(|| {
                    if let Some(expr) = otherwise {
                        let new_expr = node::Expr::new(
                            node::ExprKind::Block(self.lower_block(expr)),
                            expr.span,
                            self.new_air_id(),
                        );
                        return Some(self.session.arena().alloc(new_expr));
                    }

                    None
                }),
        }
    }

    #[track_caller]
    fn lower_expr(&mut self, expr: &Expr) -> &'air node::Expr<'air> {
        log::debug!("lower_expr expr.id={} loc={}", expr.id, Location::caller());
        self.session.arena().alloc(self.lower_expr_noalloc(expr))
    }

    fn lower_block_noalloc(&mut self, block: &Block) -> node::Block<'air> {
        let Block {
            stmts,
            expr,
            span,
            id,
        } = block;

        node::Block::new(
            *span,
            self.session
                .arena()
                .alloc_from_iter(stmts.iter().map(|stmt| self.lower_stmt(stmt))),
            self.next_air_id(*id),
            expr.as_ref().map(|expr| self.lower_expr(expr)),
        )
    }

    fn lower_block(&mut self, block: &Block) -> &'air node::Block<'air> {
        self.session.arena().alloc(self.lower_block_noalloc(block))
    }

    fn lower_stmt(&mut self, stmt: &Stmt) -> node::Stmt<'air> {
        let Stmt { kind, span, id } = stmt;

        let air_id = self.next_air_id(*id);

        let new_kind = match kind {
            StmtKind::Expr(expr) => node::StmtKind::Expr(self.lower_expr(expr)),
            StmtKind::LocalVar(local) => node::StmtKind::Local(self.lower_variable_stmt(local)),
            StmtKind::Thing(thing) => {
                node::StmtKind::Thing(self.session.arena().alloc(self.lower_thing(thing)))
            }
        };

        node::Stmt::new(*span, new_kind, air_id)
    }

    fn lower_variable_stmt(&mut self, var: &VariableStmt) -> &'air node::Local<'air> {
        let mutability = match var.mode {
            VarMode::Let => Constant::No,
            VarMode::Const => Constant::Yes,
        };

        let init = var.init.as_ref().map(|expr| self.lower_expr(expr));
        let ty = var.ty.as_ref().map(|ty| self.lower_ty(ty));
        let local = node::Local::new(mutability, var.name, self.next_air_id(var.id), ty, init);

        self.session.arena().alloc(local)
    }

    fn lower_ty(&mut self, ty: &Ty) -> &'air node::Ty<'air> {
        self.session.arena().alloc(self.lower_ty_noalloc(ty))
    }

    fn lower_ty_noalloc(&mut self, ty: &Ty) -> node::Ty<'air> {
        let kind = match &ty.kind {
            TyKind::Fn { args, ret } => node::TyKind::Fun {
                inputs: self
                    .session
                    .arena()
                    .alloc_from_iter(args.iter().map(|this| self.lower_ty_noalloc(this))),
                output: ret.as_ref().map(|this| self.lower_ty(this)),
            },
            TyKind::Array(inner) => node::TyKind::Array(self.lower_ty(inner)),
            TyKind::MethodSelf => {
                if let Some(bind_ty) = self.current_bind_ty {
                    return node::Ty::new(ty.span, self.next_air_id(ty.id), bind_ty.kind);
                }

                log::error!("self ty outside bind");
                node::TyKind::Err
            }
            TyKind::Path(path) => node::TyKind::Path(self.lower_path(path)),
            TyKind::Err => node::TyKind::Err,
            TyKind::Infer => node::TyKind::Infer,
        };

        node::Ty::new(ty.span, self.next_air_id(ty.id), kind)
    }

    fn lower_path(&mut self, path: &Path) -> &'air node::Path<'air> {
        let segments = self
            .session
            .arena()
            .alloc_from_iter(path.path.iter().map(|seg| seg.name.interned));

        let res = self.map.resolve(path.id);

        self.session.arena().alloc(node::Path::new(
            self.lower_resolved(res),
            segments,
            path.span,
            self.next_air_id(path.id),
        ))
    }

    fn lower_thing(&mut self, thing: &Thing) -> node::Thing<'air> {
        let def_id = self.map.def_id_of(thing.id);
        let air_id = self.next_air_id(thing.id);

        self.session
            .air_mut(|x| x.def_id_to_air_id.insert(def_id, air_id));

        let kind = match &thing.kind {
            ThingKind::Function(decl) => self.lower_fn_decl(decl, def_id),
            ThingKind::Instance(inst) => self.lower_instance(inst, def_id),
            ThingKind::Bind(bind) => self.lower_bind(bind),
            ThingKind::Realm(realm) => self.lower_realm(realm),
        };

        node::Thing::new(kind, thing.kind.span(), air_id, def_id)
    }

    fn lower_bind(&mut self, bind: &Bind) -> node::ThingKind<'air> {
        let ty = self.lower_ty(&bind.victim);
        self.current_bind_ty.replace(ty);

        let bind_node = node::ThingKind::Bind(node::Bind {
            with: ty,
            items: self
                .session
                .arena()
                .alloc_from_iter(bind.items.iter().map(|item| self.lower_bind_item(item))),
            mask: None,
        });

        self.current_bind_ty.take();
        bind_node
    }

    fn lower_bind_item(&mut self, kind: &BindItem) -> node::BindItem<'air> {
        let (lowered_kind, _, span) = match &kind.kind {
            BindItemKind::Const(variable) => (
                node::BindItemKind::Const {
                    ty: self.lower_ty(variable.ty.as_ref().expect("consts should have types")),
                    expr: self.lower_expr(
                        variable
                            .init
                            .as_ref()
                            .expect("guarantee broken: all associated consts have an init expr"),
                    ),
                    sym: variable.name.interned,
                },
                variable.id,
                variable.name.span,
            ),

            BindItemKind::Fun(fn_decl) => {
                let sig =
                    self.lower_fn_sig(&fn_decl.sig, self.session.air(|map| map.bodies.future_id()));

                let body = self.session.arena().alloc(node::Expr::new(
                    node::ExprKind::Block(self.lower_block(&fn_decl.block)),
                    fn_decl.span,
                    self.new_air_id(),
                ));

                let def_id = self.map.def_id_of(kind.id);
                self.session.air_mut(|map| map.insert_body_of(body, def_id));

                log::trace!("after fn decl in bind");

                (
                    node::BindItemKind::Fun {
                        sig,
                        name: fn_decl.sig.name.interned,
                    },
                    fn_decl.id,
                    fn_decl.span,
                )
            }
        };

        node::BindItem::new(
            self.next_air_id(kind.id),
            self.map.def_id_of(kind.id),
            span,
            lowered_kind,
        )
    }

    fn lower_fn_decl(&mut self, fn_decl: &FnDecl, def_id: DefId) -> node::ThingKind<'air> {
        let params =
            self.session
                .arena()
                .alloc_from_iter(fn_decl.sig.args.iter().map(|arg| {
                    Param::new(arg.ident, self.lower_ty(&arg.ty), self.next_air_id(arg.id))
                }));

        let body = self.lower_block(&fn_decl.block);
        let body_id = self.session.air_mut(|air| {
            air.insert_body_of(
                self.session.arena().alloc(node::Expr::new(
                    node::ExprKind::Block(body),
                    body.span,
                    body.air_id,
                )),
                def_id,
            )
        });

        node::ThingKind::Fn {
            name: fn_decl.sig.name,
            sig: self.session.arena().alloc(node::FnSig::new(
                fn_decl.sig.span,
                self.lower_ty(&fn_decl.sig.ret_type),
                params,
                body_id,
            )),
        }
    }

    fn lower_fn_sig(&mut self, sig: &FnSig, body_id: BodyId) -> &'air node::FnSig<'air> {
        let air_sig = node::FnSig::new(
            sig.span,
            self.lower_ty(&sig.ret_type),
            self.session
                .arena()
                .alloc_from_iter(sig.args.iter().map(|arg| {
                    Param::new(arg.ident, self.lower_ty(&arg.ty), self.next_air_id(arg.id))
                })),
            body_id,
        );

        self.session.arena().alloc(air_sig)
    }

    fn lower_realm(&mut self, realm: &Realm) -> node::ThingKind<'air> {
        node::ThingKind::Realm {
            name: realm.name,
            things: self
                .session
                .arena()
                .alloc_from_iter(realm.items.iter().map(|thing| self.lower_thing(thing))),
        }
    }

    #[track_caller]
    fn lower_instance(&mut self, inst: &Instance, def_id: DefId) -> node::ThingKind<'air> {
        self.current_instance.replace(def_id);

        let ctor_air_id = self.next_air_id(inst.ctor_id);
        let ctor_def_id = self.map.def_id_of(inst.ctor_id);

        let kind = node::ThingKind::Instance {
            fields: self.session.arena().alloc_from_iter(
                inst.fields
                    .iter()
                    .map(|ast_field| self.lower_field(ast_field, def_id)),
            ),
            name: inst.name,
            ctor_id: (ctor_air_id, ctor_def_id),
        };

        self.session
            .air_mut(|map| map.ctor_to_instance.insert(ctor_def_id, def_id));

        self.current_instance.take();

        kind
    }

    pub fn lower_field(&mut self, field: &Field, current_instance: DefId) -> node::Field<'air> {
        let def_id = self.map.def_id_of(field.id);

        let air_id = self.next_air_id(field.id);

        self.session.air_mut(|x| {
            x.field_to_instance.insert(def_id, current_instance);
        });

        node::Field::new(
            [Constant::No, Constant::Yes][usize::from(field.constant)],
            field.span,
            air_id,
            field.name,
            def_id,
            self.lower_ty(&field.ty),
        )
    }

    #[track_caller]
    pub fn lower_resolved(&mut self, res: Resolved<AstId>) -> Resolved<AirId> {
        match res {
            Resolved::Local(ast_id) => Resolved::Local(self.map_ast_id_to_air_id(ast_id)),
            Resolved::Def(id, deftype) => Resolved::Def(id, deftype),
            Resolved::Prim(ty) => Resolved::Prim(ty),
            Resolved::Err => Resolved::Err,
        }
    }

    pub fn lower_universe(&mut self, universe: &Universe) -> &'air node::Universe<'air> {
        let id = self.next_air_id(universe.id);
        let universe = node::Universe::new(
            id,
            self.session.arena().alloc_from_iter(
                universe
                    .thingies
                    .iter()
                    .map(|thing| self.lower_thing(thing)),
            ),
            universe.span,
        );

        self.session.arena().alloc(universe)
    }
}

fn is_assignable_expr(expr: &node::Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::Index { .. } | ExprKind::Field { .. } => true,
        // `Resolved::Err` case isn't technically valid but we *don't* know
        // what is behind it, so to not report extra errors it's included
        ExprKind::Path(path) => matches!(path.res, Resolved::Local(..) | Resolved::Err),
        _ => false,
    }
}

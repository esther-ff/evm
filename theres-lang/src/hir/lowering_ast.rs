use std::collections::HashMap;
use std::panic::Location;

#[allow(clippy::wildcard_imports)]
use crate::ast::*;

use crate::hir;
use crate::hir::def::{BodyId, BodyVec, DefId, DefMap, Resolved};
use crate::hir::node::{self, Constant, Node, Param};
use crate::id::IdxVec;
use crate::lexer::Span;
use crate::parser::{AstId, AstIdMap};
use crate::session::Session;

crate::newtyped_index!(HirId, HirIdMap, HirVec);
crate::newtyped_index!(LocalId, LocalMap, LocalVec);

pub struct Mappings {
    instance_to_field_list: AstIdMap<Vec<DefId>>,
    field_id_to_instance: AstIdMap<DefId>,
    resolution_map: AstIdMap<Resolved<AstId>>,
    ast_id_to_def_id: AstIdMap<DefId>,
    def_id_to_ast_id: DefMap<AstId>,
    instance_to_bind: DefMap<Vec<AstId>>,
    binds_to_resolved_ty_id: AstIdMap<AstId>,
    binds_to_items: AstIdMap<Vec<AstId>>,
}

impl Mappings {
    pub fn new(ast_id_to_def_id: AstIdMap<DefId>, def_id_to_ast_id: DefMap<AstId>) -> Self {
        Self {
            instance_to_field_list: HashMap::new(),
            field_id_to_instance: HashMap::new(),
            resolution_map: HashMap::new(),
            ast_id_to_def_id,
            def_id_to_ast_id,
            instance_to_bind: HashMap::new(),
            binds_to_resolved_ty_id: HashMap::new(),
            binds_to_items: HashMap::new(),
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

    #[track_caller]
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
        log::trace!("{id} resolves to {res:?}");
        self.resolution_map.insert(id, res);
    }

    pub fn resolve(&mut self, id: AstId) -> Resolved<AstId> {
        self.resolution_map
            .get(&id)
            .copied()
            .expect("Given AstId is not mapped to any resolution!")
    }
}

pub struct HirMap<'hir> {
    nodes: HirIdMap<Node<'hir>>,

    def_id_to_hir_id: DefMap<HirId>,

    bodies: BodyVec<&'hir node::Expr<'hir>>,
    node_to_body: DefMap<BodyId>,

    field_to_instance: HashMap<DefId, DefId>,
}

impl<'hir> HirMap<'hir> {
    pub fn new() -> Self {
        Self {
            nodes: HashMap::new(),

            def_id_to_hir_id: HashMap::new(),
            bodies: IdxVec::new(),
            node_to_body: HashMap::new(),
            field_to_instance: HashMap::new(),
        }
    }

    #[track_caller]
    pub fn map_def_id_to_hir(&mut self, def_id: DefId, hir_id: HirId) {
        let dbg = self.def_id_to_hir_id.insert(def_id, hir_id);
        assert!(
            dbg.is_none(),
            "{def_id:?} already mapped to a HirId!, loc: {}",
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

    pub fn get_def(&'hir self, def_id: DefId) -> &'hir Node<'hir> {
        self.get_node(
            self.def_id_to_hir_id
                .get(&def_id)
                .copied()
                .expect("DefId wasn't mapped to any HirId"),
        )
    }

    pub fn get_thing(&'hir self, def_id: DefId) -> &'hir node::Thing<'hir> {
        let Node::Thing(thing) = self.get_node(
            self.def_id_to_hir_id
                .get(&def_id)
                .copied()
                .expect("DefId wasn't mapped to any HirId"),
        ) else {
            panic!("`DefId` pointed to not a definition ")
        };

        thing
    }

    #[track_caller]
    pub fn get_local(&'hir self, hir_id: HirId) -> &'hir node::Local<'hir> {
        let node::Node::Local(local) = self.get_node(hir_id) else {
            panic!("hir id doesn't point to a stmt",)
        };

        local
    }

    pub fn insert_node(&mut self, node: node::Node<'hir>, hir_id: HirId) {
        self.nodes.insert(hir_id, node);
    }

    pub fn nodes(&self) -> impl IntoIterator<Item = &Node<'hir>> {
        self.nodes.values()
    }

    #[track_caller]
    pub fn get_node(&'hir self, hir_id: HirId) -> &'hir Node<'hir> {
        match self.nodes.get(&hir_id) {
            None => panic!(
                "Invalid `HirId` ({hir_id:?}) given to `get_node`! loc: {}",
                Location::caller()
            ),
            Some(node) => node,
        }
    }

    pub fn insert_body_of(&mut self, body: &'hir node::Expr<'hir>, body_owner: DefId) -> BodyId {
        let body_id = self.bodies.push(body);
        self.node_to_body.insert(body_owner, body_id);
        body_id
    }

    pub fn bodies(&self) -> &[&node::Expr<'hir>] {
        self.bodies.as_slice()
    }

    pub fn get_body(&self, body: BodyId) -> &'hir node::Expr<'hir> {
        let Some(expr_body) = self.bodies.get(body).copied() else {
            panic!("Invalid `BodyId` given ({body:#?}), no function body mapped to it!",)
        };

        expr_body
    }

    pub fn expect_fn(&'hir self, def_id: DefId) -> (&'hir node::FnSig<'hir>, Name) {
        let node::ThingKind::Fn { name, sig } = self.get_thing(def_id).kind else {
            panic!("`DefId` given to `expect_fn` did not point to a `Fn`")
        };

        (sig, name)
    }

    pub fn expect_instance(&'hir self, def_id: DefId) -> (&'hir [node::Field<'hir>], Name) {
        let node::ThingKind::Instance { fields, name } = self.get_thing(def_id).kind else {
            panic!("`DefId` given to `expect_fn` did not point to a `instance`")
        };

        (fields, name)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum DesugarLoop {
    While,
    Until,
}

pub struct AstLowerer<'hir> {
    session: &'hir Session<'hir>,

    map: Mappings,

    hir_id_counter: u32,

    ast_id_to_hir_id: AstIdMap<HirId>,

    current_instance: Option<DefId>,
}

impl<'hir> AstLowerer<'hir> {
    pub fn new(map: Mappings, session: &'hir Session<'hir>) -> Self {
        Self {
            map,
            current_instance: None,
            session,

            hir_id_counter: 0,
            ast_id_to_hir_id: HashMap::new(),
        }
    }

    /// Returns the next id that will be valid
    /// after inserting a node into the HIR map
    ///
    /// Panics if the same `AstId` is again used for this function
    /// as it maps `AstId`s to `HirId`s for lowering `Resolved`s
    #[track_caller]
    pub fn next_hir_id(&mut self, ast_id: AstId) -> HirId {
        let hir_id = HirId::new(self.hir_id_counter);
        self.hir_id_counter += 1;
        let ret = self.ast_id_to_hir_id.insert(ast_id, hir_id);

        assert!(
            ret.is_none(),
            "duplicate `AstId` given to `next_hir_id` ({} -> {})\nat loc: {:?}",
            ast_id,
            ret.unwrap(),
            Location::caller()
        );

        if let Some(def_id) = self.map.ast_id_to_def_id.get(&ast_id) {
            self.session
                .hir_mut(|map| map.map_def_id_to_hir(*def_id, hir_id));
        }

        hir_id
    }

    /// Generates another `HirId`
    /// with no requirements
    fn new_hir_id(&mut self) -> HirId {
        let hir_id = HirId::new(self.hir_id_counter);
        self.hir_id_counter += 1;
        hir_id
    }

    fn map_ast_id_to_hir_id(&self, ast_id: AstId) -> HirId {
        self.ast_id_to_hir_id
            .get(&ast_id)
            .copied()
            .expect("AstId wasn't mapped to any HirId!")
    }

    pub fn lower_args<'a>(
        &mut self,
        a: impl Iterator<Item = &'a Expr>,
    ) -> &'hir [node::Expr<'hir>] {
        self.session
            .arena()
            .alloc_from_iter(a.map(|arg| self.lower_expr_noalloc(arg)))
    }

    #[allow(clippy::too_many_lines)]
    pub fn lower_expr_noalloc(&mut self, expr: &Expr) -> node::Expr<'hir> {
        let hir_id = self.next_hir_id(expr.id);

        let hir_expr_kind = match &expr.ty {
            ExprType::Break => node::ExprKind::Break,
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
            } => match mode {
                AssignMode::Regular => node::ExprKind::Assign {
                    variable: self.lower_expr(lvalue),
                    value: self.lower_expr(rvalue),
                },

                any => node::ExprKind::AssignWithOp {
                    variable: self.lower_expr(lvalue),
                    value: self.lower_expr(rvalue),
                    op: node::AssignOp::lower_assign_mode(*any),
                },
            },

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
                    ConstantExpr::Int(v) => node::HirLiteral::Int(*v),
                    ConstantExpr::Str(v) => node::HirLiteral::Str(*v),
                    ConstantExpr::Float(v) => node::HirLiteral::Float(*v),
                    ConstantExpr::Bool(v) => node::HirLiteral::Bool(*v),
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

            ExprType::ArrayDecl {
                ty,
                size,
                initialize,
            } => node::ExprKind::Array {
                ty_of_array: self.lower_ty(ty),
                init: self
                    .session
                    .arena()
                    .alloc_from_iter(initialize.iter().map(|expr| self.lower_expr_noalloc(expr))),
                size: self.lower_expr(size),
            },

            ExprType::Return { ret } => node::ExprKind::Return {
                expr: ret.as_ref().map(|expr| self.lower_expr(expr)),
            },

            ExprType::Make {
                created: _,
                ctor_args: _,
            } => todo!("Make in HIR!"),

            ExprType::Lambda { args: _, body: _ } => todo!("Lambdas in HIR!"),

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

        node::Expr::new(hir_expr_kind, expr.span, hir_id)
    }

    pub fn lower_while_or_until_loop(
        &mut self,
        cond: &Expr,
        body: &Block,
        desugar: DesugarLoop,
    ) -> &'hir node::Block<'hir> {
        let cond_block = node::Block::new(
            Span::DUMMY,
            &[],
            self.new_hir_id(),
            Some(self.session.arena().alloc(node::Expr::new(
                node::ExprKind::Break,
                Span::DUMMY,
                self.new_hir_id(),
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
                        self.new_hir_id(),
                    )),

                    DesugarLoop::Until => self.lower_expr(cond),
                },
                block: self.session.arena().alloc(cond_block),
                else_ifs: &[],
                otherwise: None,
            },
            cond.span,
            self.new_hir_id(),
        );

        let loop_body = match &body.expr {
            None => node::Block::new(
                body.span,
                self.session
                    .arena()
                    .alloc_from_iter(body.stmts.iter().map(|stmt| self.lower_stmt(stmt))),
                self.next_hir_id(body.id),
                Some(self.session.arena().alloc(condition)),
            ),
            Some(expr) => {
                let id = self.next_hir_id(expr.id);
                let block_id = self.next_hir_id(body.id);
                let lowered = self.lower_expr(expr);

                node::Block::new(
                    body.span,
                    self.session.arena().alloc_from_iter(
                        body.stmts.iter().map(|stmt| self.lower_stmt(stmt)).chain(
                            core::iter::once(node::Stmt::new(
                                expr.span,
                                node::StmtKind::Expr(lowered),
                                id,
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

    pub fn lower_expr_if(
        &mut self,
        cond: &Expr,
        if_block: &Block,
        else_ifs: &[ElseIf],
        otherwise: Option<&Block>,
    ) -> hir::node::ExprKind<'hir> {
        node::ExprKind::If {
            condition: self.lower_expr(cond),
            block: self.lower_block(if_block),
            else_ifs: self
                .session
                .arena()
                .alloc_from_iter(else_ifs.iter().map(|els| {
                    (
                        self.lower_block_noalloc(&els.body),
                        self.lower_expr_noalloc(&els.cond),
                    )
                })),
            otherwise: otherwise.as_ref().map(|target| self.lower_block(target)),
        }
    }

    pub fn lower_expr(&mut self, expr: &Expr) -> &'hir node::Expr<'hir> {
        self.session.arena().alloc(self.lower_expr_noalloc(expr))
    }

    pub fn lower_block_noalloc(&mut self, block: &Block) -> node::Block<'hir> {
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
            self.next_hir_id(*id),
            expr.as_ref().map(|expr| self.lower_expr(expr)),
        )
    }

    pub fn lower_block(&mut self, block: &Block) -> &'hir node::Block<'hir> {
        self.session.arena().alloc(self.lower_block_noalloc(block))
    }

    pub fn lower_stmt(&mut self, stmt: &Stmt) -> node::Stmt<'hir> {
        let Stmt { kind, span, id } = stmt;

        let hir_id = self.next_hir_id(*id);

        let new_kind = match kind {
            StmtKind::Expr(expr) => node::StmtKind::Expr(self.lower_expr(expr)),
            StmtKind::LocalVar(local) => node::StmtKind::Local(self.lower_variable_stmt(local)),
            StmtKind::Thing(thing) => {
                node::StmtKind::Thing(self.session.arena().alloc(self.lower_thing(thing)))
            }
        };

        node::Stmt::new(*span, new_kind, hir_id)
    }

    pub fn lower_variable_stmt(&mut self, var: &VariableStmt) -> &'hir node::Local<'hir> {
        let mutability = match var.mode {
            VarMode::Let => Constant::No,
            VarMode::Const => Constant::Yes,
        };

        let init = var.initializer.as_ref().map(|x| self.lower_expr(x));
        let ty = self.lower_ty(&var.ty);
        let local = node::Local::new(mutability, var.name, self.next_hir_id(var.id), ty, init);

        self.session.arena().alloc(local)
    }

    pub fn lower_ty(&mut self, ty: &Ty) -> &'hir node::Ty<'hir> {
        let kind = match &ty.kind {
            TyKind::Fn { args: _, ret: _ } => todo!(),
            TyKind::Array(inner) => node::TyKind::Array(self.lower_ty(inner)),
            TyKind::MethodSelf => node::TyKind::MethodSelf,
            TyKind::Path(path) => node::TyKind::Path(self.lower_path(path)),
            TyKind::Err => node::TyKind::Err,
        };

        let ty = node::Ty::new(ty.span, self.next_hir_id(ty.id), kind);
        self.session.arena().alloc(ty)
    }

    pub fn lower_path(&mut self, path: &Path) -> &'hir node::Path<'hir> {
        let segments = self
            .session
            .arena()
            .alloc_from_iter(path.path.iter().map(|seg| seg.name.interned));

        let res = self.map.resolve(path.id);

        self.session.arena().alloc(node::Path::new(
            self.lower_resolved(res),
            segments,
            path.span,
            self.next_hir_id(path.id),
        ))
    }

    pub fn lower_thing(&mut self, thing: &Thing) -> node::Thing<'hir> {
        let def_id = self.map.def_id_of(thing.id);
        let hir_id = self.next_hir_id(thing.id);

        self.session
            .hir_mut(|x| x.def_id_to_hir_id.insert(def_id, hir_id));

        let kind = match &thing.kind {
            ThingKind::Function(decl) => self.lower_fn_decl(decl, def_id),
            ThingKind::Instance(inst) => self.lower_instance(inst, def_id),
            ThingKind::Bind(bind) => self.lower_bind(bind),
            ThingKind::Realm(realm) => self.lower_realm(realm),

            _ => todo!("other parts "),
        };

        node::Thing::new(kind, thing.kind.span(), hir_id, def_id)
    }

    pub fn lower_bind(&mut self, bind: &Bind) -> node::ThingKind<'hir> {
        node::ThingKind::Bind(node::Bind {
            with: self.lower_ty(&bind.victim),
            items: self
                .session
                .arena()
                .alloc_from_iter(bind.items.iter().map(|item| self.lower_bind_item(item))),
            mask: None,
        })
    }

    pub fn lower_bind_item(&mut self, kind: &BindItem) -> node::BindItem<'hir> {
        let (lowered_kind, ast_id, span) = match &kind.kind {
            BindItemKind::Const(variable) => (
                node::BindItemKind::Const {
                    ty: self.lower_ty(&variable.ty),
                    expr: self.lower_expr(
                        variable
                            .initializer
                            .as_ref()
                            .expect("guarantee broken: all associated consts have an init expr"),
                    ),
                    sym: variable.name.interned,
                },
                variable.id,
                variable.name.span,
            ),

            BindItemKind::Fun(fn_decl) => {
                let body = self.session.arena().alloc(node::Expr::new(
                    node::ExprKind::Block(self.lower_block(&fn_decl.block)),
                    fn_decl.span,
                    self.new_hir_id(),
                ));
                let def_id = self.map.def_id_of(fn_decl.id);

                let sig = self.lower_fn_sig(
                    &fn_decl.sig,
                    self.session.hir_mut(|map| map.insert_body_of(body, def_id)),
                );

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
            self.next_hir_id(ast_id),
            self.map.def_id_of(ast_id),
            span,
            lowered_kind,
        )
    }

    pub fn lower_fn_decl(&mut self, fn_decl: &FnDecl, def_id: DefId) -> node::ThingKind<'hir> {
        let expr_body = node::Expr::new(
            node::ExprKind::Block(self.lower_block(&fn_decl.block)),
            fn_decl.span,
            self.new_hir_id(),
        );

        let body = self.session.arena().alloc(expr_body);

        node::ThingKind::Fn {
            name: fn_decl.sig.name,
            sig: self.lower_fn_sig(
                &fn_decl.sig,
                self.session.hir_mut(|map| map.insert_body_of(body, def_id)),
            ),
        }
    }

    pub fn lower_fn_sig(&mut self, sig: &FnSig, body_id: BodyId) -> &'hir node::FnSig<'hir> {
        let hir_sig = node::FnSig::new(
            sig.span,
            self.lower_ty(&sig.ret_type),
            self.session.arena().alloc_from_iter(
                sig.args
                    .iter()
                    .map(|arg| Param::new(arg.ident, self.lower_ty(&arg.ty), self.new_hir_id())),
            ),
            body_id,
        );

        self.session.arena().alloc(hir_sig)
    }

    pub fn lower_realm(&mut self, realm: &Realm) -> node::ThingKind<'hir> {
        node::ThingKind::Realm {
            name: realm.name,
            things: self
                .session
                .arena()
                .alloc_from_iter(realm.items.iter().map(|thing| self.lower_thing(thing))),
        }
    }

    #[track_caller]
    pub fn lower_instance(&mut self, inst: &Instance, def_id: DefId) -> node::ThingKind<'hir> {
        self.current_instance.replace(def_id);

        let kind = node::ThingKind::Instance {
            fields: self.session.arena().alloc_from_iter(
                inst.fields
                    .iter()
                    .map(|ast_field| self.lower_field(ast_field, def_id)),
            ),
            name: inst.name,
        };

        self.current_instance.take();

        kind
    }

    pub fn lower_field(&mut self, field: &Field, current_instance: DefId) -> node::Field<'hir> {
        let def_id = self.map.def_id_of(field.id);

        let hir_id = self.next_hir_id(field.id);

        self.session.hir_mut(|x| {
            x.field_to_instance.insert(def_id, current_instance);
        });

        node::Field::new(
            [Constant::No, Constant::Yes][usize::from(field.constant)],
            field.span,
            hir_id,
            field.name,
            def_id,
            self.lower_ty(&field.ty),
        )
    }

    pub fn lower_resolved(&mut self, res: Resolved<AstId>) -> Resolved<HirId> {
        match res {
            Resolved::Local(ast_id) => Resolved::Local(self.map_ast_id_to_hir_id(ast_id)),
            Resolved::Def(id, deftype) => Resolved::Def(id, deftype),
            Resolved::Prim(ty) => Resolved::Prim(ty),
            Resolved::Err => Resolved::Err,
        }
    }

    pub fn lower_universe(&mut self, universe: &Universe) -> &'hir node::Universe<'hir> {
        let id = self.next_hir_id(universe.id);
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

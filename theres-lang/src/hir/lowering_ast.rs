use std::collections::HashMap;

use crate::ast::*;
use crate::hir::def::{BodyId, BodyVec, DefId, DefMap, Resolved};
use crate::hir::node::{self, Constant};
use crate::hir::node::{Node, Param};
use crate::id::IdxVec;
use crate::parser::{AstId, AstIdMap};
use crate::session::Session;

crate::newtyped_index!(HirId, HirIdMap, HirVec);
crate::newtyped_index!(LocalId, LocalMap, LocalVec);

pub struct Mappings {
    instance_to_field_list: AstIdMap<Vec<AstId>>,
    field_id_to_instance: AstIdMap<AstId>,

    resolution_map: AstIdMap<Resolved<AstId>>,
    ast_id_to_def_id: AstIdMap<DefId>,
}

impl Mappings {
    pub fn new(
        instance_to_field_list: AstIdMap<Vec<AstId>>,
        field_id_to_instance: AstIdMap<AstId>,
        resolution_map: AstIdMap<Resolved<AstId>>,
        ast_id_to_def_id: AstIdMap<DefId>,
    ) -> Self {
        Self {
            instance_to_field_list,
            field_id_to_instance,
            resolution_map,
            ast_id_to_def_id,
        }
    }
}

pub struct HirMap<'hir> {
    nodes: HirIdMap<Node<'hir>>,
    child_to_parent: HirIdMap<HirId>,

    def_id_to_hir_id: DefMap<HirId>,
    hir_id_to_def_id: DefMap<HirId>,

    bodies: BodyVec<&'hir node::Expr<'hir>>,
    node_to_body: DefMap<BodyId>,
}

impl<'hir> HirMap<'hir> {
    pub fn new() -> Self {
        Self {
            nodes: HashMap::new(),
            child_to_parent: HashMap::new(),

            def_id_to_hir_id: HashMap::new(),
            hir_id_to_def_id: HashMap::new(),
            bodies: IdxVec::new(),
            node_to_body: HashMap::new(),
        }
    }

    pub fn insert_node(&mut self, node: node::Node<'hir>, hir_id: HirId) {
        self.nodes.insert(hir_id, node);
    }

    pub fn associate_parent(&mut self, parent: HirId, child: HirId) {
        self.child_to_parent.insert(child, parent);
    }

    pub fn get_parent_of(&mut self, child: HirId) {
        self.child_to_parent
            .get(&child)
            .expect("HirId wasn't mapped to any parent");
    }

    pub fn insert_body_of(&mut self, body: &'hir node::Expr<'hir>, body_owner: DefId) -> BodyId {
        let body_id = self.bodies.push(body);
        self.node_to_body.insert(body_owner, body_id);
        body_id
    }
}

pub struct AstLowerer<'hir> {
    session: &'hir Session<'hir>,

    current_parent: HirId,
    map: Mappings,

    hir_id_counter: u32,

    ast_id_to_hir_id: AstIdMap<HirId>,
}

impl<'hir> AstLowerer<'hir> {
    pub fn new(map: Mappings, session: &'hir mut Session<'hir>) -> Self {
        Self {
            map,
            session,
            current_parent: HirId::DUMMY,

            hir_id_counter: 0,
            ast_id_to_hir_id: HashMap::new(),
        }
    }

    fn get_def_id(&self, ast_id: &AstId) -> DefId {
        match self.map.ast_id_to_def_id.get(ast_id).copied() {
            Some(v) => v,
            None => panic!("{ast_id:?} was not mapped to any DefId!"),
        }
    }

    /// Returns the next id that will be valid
    /// after inserting a node into the HIR map
    ///
    /// Panics if the same AstId is again used for this function
    /// as it maps `AstId`s to `HirId`s for lowering `Resolved`s
    pub fn next_hir_id(&mut self, ast_id: AstId) -> HirId {
        let hir_id = HirId::new(self.hir_id_counter);
        self.hir_id_counter += 1;

        let ret = self.ast_id_to_hir_id.insert(ast_id, hir_id);
        assert!(ret.is_none());

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
            .alloc_from_iter(a.map(|arg| self.lower_expr_alone(arg)))
    }

    pub fn lower_expr_alone(&mut self, expr: &Expr) -> node::Expr<'hir> {
        let hir_id = self.next_hir_id(expr.id);

        let hir_expr_kind = match &expr.ty {
            ExprType::BinaryExpr { lhs, rhs, op } => node::ExprKind::Binary {
                lhs: self.lower_expr_arena(&lhs),
                rhs: self.lower_expr_arena(&rhs),
                op: *op,
            },

            ExprType::UnaryExpr { op, target } => node::ExprKind::Unary {
                target: self.lower_expr_arena(&target),
                op: *op,
            },

            ExprType::Assign {
                lvalue,
                rvalue,
                mode,
            } => match mode {
                AssignMode::Regular => node::ExprKind::Assign {
                    variable: self.lower_expr_arena(&lvalue),
                    value: self.lower_expr_arena(&rvalue),
                },

                any => node::ExprKind::AssignWithOp {
                    variable: self.lower_expr_arena(&lvalue),
                    value: self.lower_expr_arena(&rvalue),
                    op: node::AssignOp::lower_assign_mode(*any),
                },
            },

            ExprType::FunCall { callee, args } => node::ExprKind::Call {
                function: self.lower_expr_arena(&callee),
                args: self.lower_args(args.iter()),
            },

            ExprType::MethodCall {
                receiver,
                args,
                name,
            } => node::ExprKind::MethodCall {
                receiver: self.lower_expr_arena(&receiver),
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

            ExprType::While { cond: _, body: _ } => {
                todo!("lowering while loop")
            }

            ExprType::Until { cond: _, body: _ } => {
                todo!("lowering while loop")
            }

            ExprType::If {
                cond,
                if_block,
                else_ifs,
                otherwise,
            } => node::ExprKind::If {
                condition: self.lower_expr_arena(cond),
                block: self.lower_block(if_block),
                else_ifs: self
                    .session
                    .arena()
                    .alloc_from_iter(else_ifs.iter().map(|els| {
                        (
                            self.lower_block_noalloc(&els.body),
                            self.lower_expr_alone(&els.cond),
                        )
                    })),
                otherwise: otherwise.as_ref().map(|target| self.lower_block(&target)),
            },

            _ => todo!(),
        };

        node::Expr::new(hir_expr_kind, expr.span, hir_id)
    }

    pub fn lower_expr_arena(&mut self, expr: &Expr) -> &'hir node::Expr<'hir> {
        self.session.arena().alloc(self.lower_expr_alone(expr))
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
            expr.as_ref().map(|expr| self.lower_expr_arena(expr)),
        )
    }

    pub fn lower_block(&mut self, block: &Block) -> &'hir node::Block<'hir> {
        self.session.arena().alloc(self.lower_block_noalloc(block))
    }

    pub fn lower_block_into_expr(&mut self, block: &Block) -> &'hir node::Expr<'hir> {
        let kind = node::ExprKind::Block(self.lower_block(block));

        let v = node::Expr::new(kind, block.span, self.new_hir_id());

        self.session.arena().alloc(v)
    }

    pub fn lower_stmt(&mut self, stmt: &Stmt) -> node::Stmt<'hir> {
        let Stmt { kind, span, id } = stmt;

        let hir_id = self.next_hir_id(*id);

        let new_kind = match kind {
            StmtKind::Expr(expr) => node::StmtKind::Expr(self.lower_expr_arena(expr)),
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

        let init = var.initializer.as_ref().map(|x| self.lower_expr_arena(x));
        let ty = self.lower_ty(&var.ty);
        let local = node::Local::new(mutability, var.name, self.next_hir_id(var.id), ty, init);

        self.session.arena().alloc(local)
    }

    pub fn lower_ty(&mut self, ty: &Ty) -> &'hir node::Ty<'hir> {
        let kind = match &ty.kind {
            TyKind::Fn { args: _, ret: _ } => todo!(),
            TyKind::Array(inner) => node::TyKind::Array(self.lower_ty(&inner)),
            TyKind::MethodSelf => node::TyKind::MethodSelf,
            TyKind::Path(path) => node::TyKind::Path(self.lower_path(&path)),
        };

        let ty = node::Ty::new(ty.span, self.next_hir_id(ty.id), kind);
        self.session.arena().alloc(ty)
    }

    pub fn lower_path(&mut self, path: &Path) -> &'hir node::Path<'hir> {
        let Path { path, span, id } = path;
        let segments = self
            .session
            .arena()
            .alloc_from_iter(path.iter().map(|seg| seg.name.interned));

        let res = self.map.resolution_map.get(id).expect("no res for this id");

        let path = node::Path::new(self.lower_resolved(*res), segments, *span);

        self.session.arena().alloc(path)
    }

    pub fn lower_thing(&mut self, thing: &Thing) -> node::Thing<'hir> {
        let kind = match &thing.kind {
            ThingKind::Function(decl) => return self.lower_fn_decl(&decl),
            ThingKind::Realm(realm) => self.lower_realm(realm),
            ThingKind::Instance(_inst) => todo!(),

            _ => todo!("other parts "),
        };

        node::Thing::new(kind, thing.kind.span(), self.new_hir_id())
    }

    pub fn lower_fn_decl(&mut self, fndecl: &FnDecl) -> node::Thing<'hir> {
        let FnDecl {
            sig,
            block,
            span,
            id: fn_id,
        } = fndecl;

        let expr_body = node::Expr::new(
            node::ExprKind::Block(self.lower_block(block)),
            *span,
            self.new_hir_id(),
        );

        let body = self.session.arena().alloc(expr_body);
        let def_id = self.get_def_id(fn_id);

        node::Thing::new(
            node::ThingKind::Fn {
                name: sig.name,
                sig: self.lower_fn_sig(
                    sig,
                    self.session.hir(|map| map.insert_body_of(body, def_id)),
                ),
            },
            *span,
            self.next_hir_id(*fn_id),
        )
    }

    pub fn lower_fn_sig(&mut self, sig: &FnSig, body_id: BodyId) -> &'hir node::FnSig<'hir> {
        let hir_sig = node::FnSig::new(
            sig.span,
            self.lower_ty(&sig.ret_type),
            self.session.arena().alloc_from_iter(
                sig.args
                    .iter()
                    .map(|arg| Param::new(arg.ident, self.lower_ty(&arg.ty))),
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
                .alloc_from_iter(realm.items.iter().map(|t| self.lower_thing(t))),
        }
    }

    pub fn lower_instance(&mut self, inst: &Instance) -> node::Thing<'hir> {
        let hir_id = self.next_hir_id(inst.id);

        let Instance {
            name,
            span,
            fields,
            assoc,
            generics: _,
            id: _,
        } = inst;

        todo!();
    }

    pub fn lower_resolved(&mut self, res: Resolved<AstId>) -> Resolved<HirId> {
        match res {
            Resolved::Local(ast_id) => Resolved::Local(self.map_ast_id_to_hir_id(ast_id)),
            Resolved::Def(id, deftype) => Resolved::Def(id, deftype),
            Resolved::Prim(ty) => Resolved::Prim(ty),
            Resolved::Err => Resolved::Err,
        }
    }
}

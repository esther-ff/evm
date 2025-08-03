use std::collections::HashMap;

use crate::ast::*;
use crate::hir::def::{DefId, DefMap, Resolved};
use crate::hir::node::{self, Constant};
use crate::hir::node::{Node, Param};
use crate::id::IdxVec;
use crate::parser::{AstId, AstIdMap};
use crate::session::Session;

crate::newtyped_index!(OwnerId, OwnerMap, OwnerVec);
crate::newtyped_index!(BodyId, BodyMap, BodyVec);
crate::newtyped_index!(LocalId, LocalMap, LocalVec);

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct HirId {
    owner: OwnerId,
    itself: LocalId,
}

impl HirId {
    pub fn new(owner: OwnerId, itself: LocalId) -> Self {
        Self { owner, itself }
    }
}

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
    nodes: LocalVec<Node<'hir>>,
    owner_id_to_local_id: OwnerMap<LocalId>,

    def_id_to_hir_id: DefMap<HirId>,
    hir_id_to_def_id: DefMap<HirId>,
}

impl HirMap<'_> {
    pub fn new() -> Self {
        Self {
            nodes: IdxVec::new(),
            owner_id_to_local_id: HashMap::new(),

            def_id_to_hir_id: HashMap::new(),
            hir_id_to_def_id: HashMap::new(),
        }
    }
}

pub struct AstLowerer<'hir> {
    session: &'hir Session<'hir>,
    current_owner: Option<OwnerId>,
    current_function: Option<DefId>,
    current_instance: Option<DefId>,

    map: Mappings,

    local_id_counter: u32,
    owner_id_counter: u32,

    ast_id_to_hir_id: AstIdMap<HirId>,
}

impl<'hir> AstLowerer<'hir> {
    pub fn new(map: Mappings, session: &'hir mut Session<'hir>) -> Self {
        Self {
            map,
            session,

            current_owner: None,
            current_function: None,
            current_instance: None,

            local_id_counter: 0,
            owner_id_counter: 0,
            ast_id_to_hir_id: HashMap::new(),
        }
    }

    pub fn get_def_id(&self, ast_id: &AstId) -> DefId {
        match self.map.ast_id_to_def_id.get(ast_id).copied() {
            Some(v) => v,
            None => panic!("{ast_id:?} was not mapped to any DefId!"),
        }
    }

    pub fn new_owner(&mut self) {
        let id = OwnerId::new(self.owner_id_counter);
        self.owner_id_counter += 1;
        self.current_owner.replace(id);
    }

    pub fn new_local_id(&mut self) -> LocalId {
        let id = LocalId::new(self.owner_id_counter);
        self.local_id_counter += 1;
        id
    }

    pub fn lower_ast_id(&mut self, id: AstId) -> HirId {
        let owner = self.current_owner.expect("no owner currently");
        let local = self.new_local_id();

        let hir_id = HirId::new(owner, local);

        self.ast_id_to_hir_id.insert(id, hir_id);

        hir_id
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
        let Expr { ty, span, id } = expr;
        let hir_id = self.lower_ast_id(*id);

        let hir_expr_kind = match ty {
            ExprType::BinaryExpr { lhs, rhs, op } => node::ExprKind::Binary {
                lhs: self.lower_expr_arena(lhs),
                rhs: self.lower_expr_arena(rhs),
                op: *op,
            },

            ExprType::UnaryExpr { op, target } => node::ExprKind::Unary {
                target: self.lower_expr_arena(target),
                op: *op,
            },

            ExprType::Assign {
                lvalue,
                rvalue,
                mode,
            } => match mode {
                AssignMode::Regular => node::ExprKind::Assign {
                    variable: self.lower_expr_arena(lvalue),
                    value: self.lower_expr_arena(rvalue),
                },

                any => node::ExprKind::AssignWithOp {
                    variable: self.lower_expr_arena(lvalue),
                    value: self.lower_expr_arena(rvalue),
                    op: node::AssignOp::lower_assign_mode(*any),
                },
            },

            ExprType::FunCall { callee, args } => node::ExprKind::Call {
                function: self.lower_expr_arena(callee),
                args: self.lower_args(args.iter()),
            },

            ExprType::MethodCall {
                receiver,
                args,
                name,
            } => node::ExprKind::MethodCall {
                receiver: self.lower_expr_arena(receiver),
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
                iterable,
                pat,
                body,
            } => {
                todo!("lowering for loop")
            }

            ExprType::While { cond, body } => {
                todo!("lowering while loop")
            }

            ExprType::Until { cond, body } => {
                todo!("lowering while loop")
            }

            ExprType::If {
                cond,
                if_block,
                else_ifs,
                otherwise,
            } => {
                todo!("need block")
            }

            _ => todo!(),
        };

        node::Expr::new(hir_expr_kind, *span, hir_id)
    }

    pub fn lower_expr_arena(&mut self, expr: &Expr) -> &'hir node::Expr<'hir> {
        self.session.arena().alloc(self.lower_expr_alone(expr))
    }

    pub fn lower_block(&mut self, block: &Block) -> &'hir node::Block<'hir> {
        let Block {
            stmts,
            expr,
            span,
            id,
        } = block;

        todo!()
    }

    pub fn lower_stmt(&mut self, stmt: &Stmt) -> &'hir node::Stmt<'hir> {
        let Stmt { kind, span, id } = stmt;

        let hir_id = self.lower_ast_id(*id);

        let new_kind = match kind {
            StmtKind::Expr(expr) => node::StmtKind::Expr(self.lower_expr_arena(expr)),
            StmtKind::LocalVar(local) => node::StmtKind::Local(self.lower_variable_stmt(local)),
            StmtKind::Thing(i) => todo!(),
        };

        let new_stmt = node::Stmt::new(*span, new_kind, hir_id);

        self.session.arena().alloc(new_stmt)
    }

    pub fn lower_variable_stmt(&mut self, var: &VariableStmt) -> &'hir node::Local<'hir> {
        let VariableStmt {
            mode,
            name,
            initializer,
            ty,
            id,
        } = var;

        let mutability = match mode {
            VarMode::Let => Constant::No,
            VarMode::Const => Constant::Yes,
        };

        let init = initializer.as_ref().map(|x| self.lower_expr_arena(x));

        let ty = self.lower_ty(ty);

        let local = node::Local::new(mutability, *name, self.lower_ast_id(*id), ty, init);

        self.session.arena().alloc(local)
    }

    pub fn lower_ty(&mut self, ty: &Ty) -> &'hir node::Ty<'hir> {
        let Ty { kind, span, id } = ty;

        let kind = match kind {
            TyKind::Fn { args: _, ret: _ } => todo!(),
            TyKind::Array(inner) => node::TyKind::Array(self.lower_ty(inner)),
            TyKind::MethodSelf => node::TyKind::MethodSelf,
            TyKind::Path(path) => node::TyKind::Path(self.lower_path(path)),
        };

        let ty = node::Ty::new(*span, self.lower_ast_id(*id), kind);
        self.session.arena().alloc(ty)
    }

    pub fn lower_path(&mut self, path: &Path) -> &'hir node::Path<'hir> {
        let Path { path, span, id } = path;
        let hir_id = self.lower_ast_id(*id);
        let segments = self
            .session
            .arena()
            .alloc_from_iter(path.iter().map(|seg| seg.name.interned));

        let res = self.map.resolution_map.get(id).expect("no res for this id");

        let path = node::Path::new(self.lower_resolved(*res), segments, hir_id, *span);

        self.session.arena().alloc(path)
    }

    pub fn lower_thing(&mut self, thing: &Thing) -> &'hir node::Thing<'hir> {
        let Thing {
            id: ast_id,
            kind: ast_kind,
        } = thing;

        let hir_id = self.lower_ast_id(*ast_id);
        let def_id = self.get_def_id(ast_id);

        self.session.map_def_id(def_id, hir_id);

        let kind = match ast_kind {
            ThingKind::Function(decl) => self.lower_fn_decl(decl),
            ThingKind::Realm(_realm) => todo!(),
            ThingKind::Instance(_inst) => todo!(),

            _ => todo!("other parts "),
        };

        self.session
            .arena()
            .alloc(node::Thing::new(kind, ast_kind.span(), hir_id, def_id))
    }

    pub fn lower_fn_decl(&mut self, fndecl: &FnDecl) -> node::ThingKind<'hir> {
        let FnDecl {
            sig,
            block,
            span,
            id,
        } = fndecl;

        let FnSig {
            name,
            args,
            ret_type,
            span: _,
            id: _,
        } = sig;

        let hir_id = self.lower_ast_id(*id);
        let def_id = self.get_def_id(id);

        let expr_body = node::Expr::new(
            node::ExprKind::Block(self.lower_block(block)),
            *span,
            hir_id,
        );

        let body = self.session.arena().alloc(expr_body);

        let sig = node::FnSig::new(
            *span,
            self.lower_ty(ret_type),
            self.session.arena().alloc_from_iter(
                args.iter()
                    .map(|arg| Param::new(arg.ident, self.lower_ty(&arg.ty))),
            ),
            self.session.associate_body(def_id, body),
        );

        node::ThingKind::Fn {
            name: *name,
            sig: self.session.arena().alloc(sig),
        }
    }

    pub fn lower_resolved(&mut self, res: Resolved<AstId>) -> Resolved<HirId> {
        match res {
            Resolved::Local(astid) => Resolved::Local(self.lower_ast_id(astid)),
            Resolved::Def(id, deftype) => Resolved::Def(id, deftype),
            Resolved::Prim(ty) => Resolved::Prim(ty),
            Resolved::Err => Resolved::Err,
        }
    }
}

impl<'v, 'hir> Visitor<'v> for AstLowerer<'hir>
where
    'hir: 'v,
{
    type Result = ();
}

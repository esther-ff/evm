use std::{collections::HashMap, hash::Hash};

type BindingList<'a> = &'a [(SymbolId, Resolved<AstId>)];

use crate::{
    ast::{
        self, Arg, AstId, Block, ExprType, Field, FnDecl, FnSig, Instance, Name, Stmt, StmtKind,
        Thing, ThingKind, TyKind, VarMode, VariableStmt, Visitor, VisitorResult,
    },
    hir::def::{DefId, DefType, Definitions, IntTy, PrimTy, Resolved},
    lexer::Span,
    session::{Session, SymbolId},
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum AstErrorKind {
    // todo: the name
    // refers to the situation when
    // the block associated with the visited
    // instance contains something more than
    // function decls or const declarations
    OverfilledInstanceBlock {
        instance: String,
        span_of_instance: Span,
    },

    NotConstInInstance {
        instance: String,
        span_of_const: Span,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct AstError {
    span: Span,
    kind: AstErrorKind,
}

impl AstError {
    pub fn new(kind: AstErrorKind, span: Span) -> Self {
        Self { span, kind }
    }
}

pub struct Validator<'a> {
    errors: Vec<AstError>,
    sess: &'a Session,
}

impl<'a> Visitor<'a> for Validator<'a> {
    type Result = ();

    fn visit_instance(&mut self, val: &'a crate::ast::Instance) -> Self::Result {
        let Instance {
            name,
            span,
            fields: _,
            assoc,
            generics: _,
            id: _,
        } = val;

        let Some(Block {
            stmts,
            span: _,
            id: _,
        }) = assoc
        else {
            return Self::Result::normal();
        };

        for Stmt {
            kind,
            span: _,
            id: _,
        } in stmts
        {
            match kind {
                StmtKind::LocalVar(local) if local.mode != VarMode::Const => {
                    self.errors.push(AstError::new(
                        AstErrorKind::NotConstInInstance {
                            instance: self.sess.get_string(name.interned).to_string(),
                            span_of_const: local.name.span,
                        },
                        local.name.span,
                    ))
                }

                StmtKind::Thing(def) if !matches!(def.kind, ThingKind::Function(..)) => {
                    self.errors.push(AstError::new(
                        AstErrorKind::OverfilledInstanceBlock {
                            instance: self.sess.get_string(name.interned).to_string(),
                            span_of_instance: *span,
                        },
                        def.kind.span(),
                    ))
                }

                _ => (),
            }
        }
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct ScopeId(u32);

#[derive(Debug)]
pub struct Scope {
    parent: Option<ScopeId>,
    bindings: HashMap<SymbolId, Resolved<AstId>>,
    types: HashMap<SymbolId, Resolved<AstId>>,
}

#[derive(Debug, Clone, Copy)]
pub enum Space {
    Types,
    Values,
}

impl Scope {
    pub fn new(parent: Option<ScopeId>) -> Self {
        Self {
            parent,
            bindings: HashMap::new(),
            types: HashMap::new(),
        }
    }

    pub fn new_with<F, R>(parent: Option<ScopeId>, f: F) -> Self
    where
        F: FnOnce(&mut Scope) -> R,
    {
        let mut scope = Scope::new(parent);
        f(&mut scope);
        scope
    }

    pub fn get(&self, name: SymbolId, ns: Space) -> Option<Resolved<AstId>> {
        match ns {
            Space::Types => self.types.get(&name),
            Space::Values => self.bindings.get(&name),
        }
        .copied()
    }

    pub fn add(&mut self, name: Name, res: Resolved<AstId>, ns: Space) {
        match ns {
            Space::Types => self.types.insert(name.interned, res),
            Space::Values => self.bindings.insert(name.interned, res),
        };
    }
}

const PRIMITIVES: [(SymbolId, Resolved<AstId>); 10] = [
    (SymbolId::u8(), Resolved::Prim(PrimTy::Uint(IntTy::N8))),
    (SymbolId::u16(), Resolved::Prim(PrimTy::Uint(IntTy::N16))),
    (SymbolId::u32(), Resolved::Prim(PrimTy::Uint(IntTy::N32))),
    (SymbolId::u64(), Resolved::Prim(PrimTy::Uint(IntTy::N64))),
    (SymbolId::i8(), Resolved::Prim(PrimTy::Int(IntTy::N8))),
    (SymbolId::i16(), Resolved::Prim(PrimTy::Int(IntTy::N16))),
    (SymbolId::i32(), Resolved::Prim(PrimTy::Int(IntTy::N32))),
    (SymbolId::i64(), Resolved::Prim(PrimTy::Int(IntTy::N64))),
    (SymbolId::f32(), Resolved::Prim(PrimTy::Float)),
    (SymbolId::f64(), Resolved::Prim(PrimTy::Double)),
];

pub struct FirstPassResolver {
    definitions: HashMap<SymbolId, DefId>,

    top_scope: Scope,
}

impl FirstPassResolver {
    pub fn new() -> Self {
        let f = |scope: &mut Scope| {
            for (id, prim) in PRIMITIVES {
                scope.types.insert(id, prim);
            }
        };

        Self {
            definitions: HashMap::new(),
            top_scope: Scope::new_with(None, f),
        }
    }
}

impl<'a> Visitor<'a> for FirstPassResolver {
    type Result = ();

    fn visit_interface(&mut self, _val: &'a crate::ast::Interface) -> Self::Result {
        todo!("interfaces: resolving")
    }

    fn visit_fn_decl(&mut self, val: &'a crate::ast::FnDecl) -> Self::Result {
        self.top_scope.bindings.insert(
            val.sig.name.interned,
            Resolved::Def(DefId::DUMMY, DefType::Instance),
        );
    }

    fn visit_instance(&mut self, val: &'a Instance) -> Self::Result {
        self.top_scope.bindings.insert(
            val.name.interned,
            Resolved::Def(DefId::DUMMY, DefType::Instance),
        );
    }
}

pub struct ThingDefResolver {
    // mapping names to definitions,
    definitions: Definitions,

    // top scope
    top: Scope,

    // state
    in_top_scope: bool,

    // mapping ast ids to def ids
    ast_id_to_def_id: HashMap<AstId, DefId>,
}

impl ThingDefResolver {
    pub fn new() -> Self {
        let f = |s: &mut Scope| {
            for (k, v) in PRIMITIVES {
                s.types.insert(k, v);
            }
        };
        Self {
            definitions: Definitions::new(),
            top: Scope::new_with(None, f),
            in_top_scope: true,
            ast_id_to_def_id: HashMap::new(),
        }
    }
}

impl<'a> Visitor<'a> for ThingDefResolver {
    type Result = ();

    fn visit_fn_decl(&mut self, val: &'a crate::ast::FnDecl) -> Self::Result {
        let FnDecl {
            sig,
            block,
            span: _,
            id,
        } = val;
        let def_id = self.definitions.new_id();
        self.ast_id_to_def_id.insert(*id, def_id);

        if self.in_top_scope {
            self.top
                .add(sig.name, Resolved::Def(def_id, DefType::Fun), Space::Values);
        }

        self.in_top_scope = false;
        self.visit_block(block);
        self.in_top_scope = true;
    }

    fn visit_instance(&mut self, val: &'a Instance) -> Self::Result {
        let Instance {
            name,
            span: _,
            fields,
            assoc,
            generics: _,
            id,
        } = val;

        let def_id = self.definitions.new_id();
        self.ast_id_to_def_id.insert(*id, def_id);

        if self.in_top_scope {
            self.top.add(
                *name,
                Resolved::Def(def_id, DefType::Instance),
                Space::Types,
            );
        }

        self.in_top_scope = false;
        if let Some(b) = assoc {
            self.visit_block(b)
        }
        self.in_top_scope = true;

        fields.iter().for_each(|x| self.visit_field(x))
    }

    fn visit_field(&mut self, val: &'a ast::Field) -> Self::Result {
        let Field {
            constant: _,
            name: _,
            ty: _,
            span: _,
            id,
        } = val;

        let def_id = self.definitions.new_id();
        self.ast_id_to_def_id.insert(*id, def_id);
    }

    fn visit_block(&mut self, val: &'a Block) -> Self::Result {
        let Block {
            stmts,
            span: _,
            id: _,
        } = val;

        stmts.iter().for_each(|st| self.visit_stmt(st))
    }
}

pub struct LateResolver {
    // scope bullshit
    scopes: HashMap<ScopeId, Scope>,
    current_scope: ScopeId,
    scope_id_gen: u32,

    // mapping node ids to their resolutions
    res_map: HashMap<AstId, Resolved<AstId>>,

    // mapping names to definitions,
    definitions: Definitions,

    // mapping ast ids to def ids
    ast_id_to_def_id: HashMap<AstId, DefId>,
}

impl LateResolver {
    pub fn new(old: ThingDefResolver) -> Self {
        Self {
            res_map: HashMap::new(),
            scope_id_gen: 1,
            definitions: old.definitions,
            scopes: HashMap::from([(ScopeId(0), old.top)]),
            current_scope: ScopeId(0),
            ast_id_to_def_id: old.ast_id_to_def_id,
        }
    }

    fn new_scope(&mut self) -> ScopeId {
        let scope = Scope::new(Some(self.current_scope));
        self.add_scope(scope)
    }

    fn add_scope(&mut self, scope: Scope) -> ScopeId {
        let new_id = self.scope_id_gen;
        self.scope_id_gen += 1;
        self.scopes.insert(ScopeId(new_id), scope);
        let old = self.current_scope;

        self.current_scope = ScopeId(new_id);
        old
    }

    fn with_new_scope<'b, F>(&mut self, f: F, bindings: Option<BindingList<'b>>)
    where
        F: FnOnce(&mut Self),
    {
        let old_id = match bindings {
            None => self.new_scope(),
            Some(list) => {
                let f = |scope: &mut Scope| {
                    for (name, res) in list {
                        scope.bindings.insert(*name, *res);
                    }
                };

                let scope = Scope::new_with(Some(self.current_scope), f);

                self.add_scope(scope)
            }
        };

        f(self);
        self.current_scope = old_id;
    }

    fn with_current_scope_mut<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Scope) -> R,
    {
        f(self
            .scopes
            .get_mut(&self.current_scope)
            .expect("bug: no scope id like that"))
    }

    fn with_current_scope<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&Scope) -> R,
    {
        f(self
            .scopes
            .get(&self.current_scope)
            .expect("bug: no scope id like that"))
    }

    fn make_local_binding(&mut self, name: Name, res: AstId) {
        let local = Resolved::Local(res);

        self.with_current_scope_mut(|scope| scope.add(name, local, Space::Values));
    }

    fn get_name(&self, symbol: SymbolId, ns: Space) -> Resolved<AstId> {
        if let Some(v) = self.with_current_scope(|scope| {
            if let Some(ret) = scope.get(symbol, ns) {
                Some(ret)
            } else {
                traverse_scopes(scope.parent, &self.scopes, symbol, ns)
            }
        }) {
            v
        } else {
            println!("missing symbol: {symbol:?}");
            Resolved::Err
        }
    }

    #[cfg(debug_assertions)]
    pub fn res_map(&self) -> &HashMap<AstId, Resolved<AstId>> {
        &self.res_map
    }
}

fn traverse_scopes(
    mut cursor: Option<ScopeId>,
    scopes: &HashMap<ScopeId, Scope>,
    symbol: SymbolId,
    ns: Space,
) -> Option<Resolved<AstId>> {
    while let Some(ref id) = cursor {
        let scope = scopes.get(id).expect("invalid scope id");
        let Some(binding) = scope.get(symbol, ns) else {
            cursor = scope.parent;
            continue;
        };

        return Some(binding);
    }

    None
}

impl<'a> Visitor<'a> for LateResolver {
    type Result = ();

    fn visit_interface(&mut self, _val: &'a crate::ast::Interface) -> Self::Result {
        todo!("interfaces: resolving")
    }

    fn visit_fn_decl(&mut self, val: &'a crate::ast::FnDecl) -> Self::Result {
        let FnDecl {
            sig,
            block,
            span: _,
            id,
        } = val;

        let FnSig {
            name,
            args,
            ret_type,
            span: _,
            id: _,
        } = sig;

        let bindings: Vec<_> = args
            .iter()
            .map(|Arg { ident, ty, id }| {
                self.visit_ty(ty);
                (ident.interned, Resolved::Local(*id))
            })
            .collect();

        self.visit_ty(ret_type);

        if self
            .scopes
            .get(&ScopeId(0))
            .expect("first scope must be here")
            .get(name.interned, Space::Values)
            .is_none()
        {
            let new_def_id = self.definitions.new_id();
            self.ast_id_to_def_id.insert(*id, new_def_id);

            let res = Resolved::Def(new_def_id, DefType::Fun);

            self.with_current_scope_mut(|s| s.add(*name, res, Space::Values));
        };

        self.with_new_scope(|visitor| visitor.visit_block(block), Some(&bindings));
    }

    fn visit_instance(&mut self, val: &'a Instance) -> Self::Result {
        let ast::Instance {
            name: _,
            span: _,
            id: _,
            fields: _,
            assoc: _,
            generics: _,
        } = val;

        // if self
        //     .scopes
        //     .get(&ScopeId(0))
        //     .expect("first scope must be here")
        //     .get(name.interned, Space::Values)
        //     .is_none()
        // {
        //     let new_def_id = self.definitions.new_id();
        //     self.ast_id_to_def_id.insert(*id, new_def_id);

        //     let res = Resolved::Def(new_def_id, DefType::Fun);

        //     self.with_current_scope_mut(|s| s.add(*name, res, Space::Values));
        // };

        println!("later");
    }

    fn visit_stmt(&mut self, val: &'a Stmt) -> Self::Result {
        let Stmt {
            kind,
            span: _,
            id: _,
        } = val;
        match kind {
            StmtKind::Block(block) => {
                self.with_new_scope(|v| v.visit_block(block), None);
            }

            StmtKind::LocalVar(VariableStmt {
                mode: _,
                name,
                initializer,
                ty,
                id,
            }) => {
                self.visit_ty(ty);

                if let Some(init) = initializer {
                    self.visit_expr(init)
                }
                self.make_local_binding(*name, *id);
            }

            StmtKind::Expr(expr) => {
                self.visit_expr(expr);
            }

            StmtKind::Thing(def) => self.visit_thing(def),
        }
    }

    fn visit_expr(&mut self, val: &'a ast::Expr) -> Self::Result {
        let ast::Expr { ty, span: _, id } = val;
        match ty {
            ExprType::Variable { name } => {
                // whatever

                match self.get_name(name.interned, Space::Values) {
                    Resolved::Local(local_id) => {
                        self.res_map.insert(*id, Resolved::Local(local_id));
                    }

                    Resolved::Def(def_id, DefType::Fun) => {
                        self.res_map
                            .insert(*id, Resolved::Def(def_id, DefType::Fun));
                    }

                    any => todo!("ehh... {any:#?}"),
                };
            }

            ExprType::FunCall { callee, args } => {
                self.visit_expr(callee);

                for arg in args {
                    self.visit_expr(arg);
                }
            }

            ExprType::BinaryExpr { lhs, rhs, op: _ } => {
                self.visit_expr(lhs);
                self.visit_expr(rhs);
            }

            ExprType::UnaryExpr { op: _, target } => self.visit_expr(target),

            ExprType::Group(expr) => self.visit_expr(expr),

            ExprType::CommaGroup(exprs) => {
                for e in exprs {
                    self.visit_expr(e)
                }
            }

            ExprType::Assign {
                lvalue,
                rvalue,
                mode: _,
            } => {
                let ExprType::Variable { .. } = lvalue.ty else {
                    todo!("error, can't assign to anything other than variable")
                };

                self.visit_expr(lvalue);
                self.visit_expr(rvalue);
            }

            ExprType::MethodCall {
                receiver,
                args,
                name: _,
            } => {
                self.visit_expr(receiver);
                for arg in args {
                    self.visit_expr(arg)
                }
            }

            ExprType::Return { ret } if matches!(ret, Some(..)) => {
                self.visit_expr(ret.as_ref().unwrap())
            }

            ExprType::For {
                iterable: _,
                pat: _,
                body: _,
            } => {
                todo!("for loop")
            }

            ExprType::Loop { body } => self.visit_block(body),

            ExprType::While { cond, body } => {
                self.visit_expr(cond);
                self.visit_block(body)
            }

            ExprType::Until { cond, body } => {
                self.visit_expr(cond);
                self.visit_block(body)
            }

            ExprType::ArrayDecl {
                ty,
                size,
                initialize,
            } => {
                self.visit_ty(ty);
                self.visit_expr(size);
                initialize.iter().for_each(|expr| self.visit_expr(expr))
            }

            ExprType::FieldAccess { source, field: _ } => self.visit_expr(source),

            ExprType::Lambda { args: _, body: _ } => {
                todo!("lambda")
            }

            ExprType::Make {
                created: _,
                ctor_args: _,
            } => {
                todo!("make")
            }

            ExprType::Constant(..) => (),

            any => todo!("to-do expression kinds: {any:#?}"),
        }
    }

    fn visit_ty(&mut self, val: &'a ast::Ty) -> Self::Result {
        let ast::Ty {
            kind,
            span: _,
            id: _,
        } = val;

        match kind {
            TyKind::Fn { args, ret } => {
                for arg in args {
                    self.visit_ty(arg)
                }

                if let Some(ret) = ret {
                    self.visit_ty(ret)
                }
            }

            TyKind::Array(ty) => self.visit_ty(ty),

            TyKind::Regular(id) => {
                match self.get_name(id.interned, Space::Types) {
                    Resolved::Err => println!("error: type not found, symbol id: {id:?}"),
                    test => println!("type was correct!!! {test:#?}"), // just to silence clippy
                }
            }

            TyKind::Params {
                base: _,
                generics: _,
            } => todo!("generics"),

            TyKind::MethodSelf => (),
        }
    }

    fn visit_block(&mut self, val: &'a Block) -> Self::Result {
        let Block {
            stmts,
            span: _,
            id: _,
        } = val;

        for stmt in stmts {
            if let StmtKind::Thing(item) = &stmt.kind {
                self.visit_thing(item)
            }
        }

        for stmt in stmts {
            match &stmt.kind {
                StmtKind::Block(block) => {
                    self.with_new_scope(|v| v.visit_block(block), None);
                }

                StmtKind::LocalVar(VariableStmt {
                    mode: _,
                    name,
                    initializer,
                    ty,
                    id,
                }) => {
                    self.visit_ty(ty);

                    if let Some(init) = initializer {
                        self.visit_expr(init)
                    }
                    self.make_local_binding(*name, *id);
                }

                StmtKind::Expr(expr) => {
                    self.visit_expr(expr);
                }

                // explicitly here so i can track if i add something
                // new
                //
                // ignored because we did this earlier
                StmtKind::Thing(..) => (),
            }
        }
    }
}

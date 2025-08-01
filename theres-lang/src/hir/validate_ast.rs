use std::{collections::HashMap, mem};

type BindingList<'a> = &'a [(SymbolId, Resolved<AstId>)];

use crate::{
    ast::{
        self, Arg, AstId, Block, ExprType, Field, FnDecl, FnSig, Instance, Name, Path, Realm, Stmt,
        StmtKind, Thing, ThingKind, TyKind, VarMode, VariableStmt, Visitor, VisitorResult,
    },
    hir::def::{DefId, DefMap, DefType, Definitions, IntTy, PrimTy, Resolved},
    lexer::Span,
    parser::AstIdMap,
    session::{Session, SymbolId},
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum NotFoundCulprit {
    Ty,
    Realm,
    Value,
}

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

    NotFound {
        offender: SymbolId,
        culprit: NotFoundCulprit,
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

impl<'a> Validator<'a> {
    pub fn new(sess: &'a Session) -> Self {
        Self {
            errors: vec![],
            sess,
        }
    }
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
            expr: _, // use it
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

crate::newtyped_index!(ScopeId, ScopeIdMap, ScopeIdVec);

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

    pub fn add(&mut self, name: &Name, res: Resolved<AstId>, ns: Space) {
        match ns {
            Space::Types => self.types.insert(name.interned, res),
            Space::Values => self.bindings.insert(name.interned, res),
        };
    }
}

const PRIMITIVES: [(SymbolId, Resolved<AstId>); 11] = [
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
    (SymbolId::nil(), Resolved::Prim(PrimTy::Nil)),
];

pub struct ThingDefResolver {
    // mapping names to definitions,
    definitions: Definitions,

    // top scope
    top: Scope,

    // state
    in_top_scope: bool,

    // ast id of top root module
    root: AstId,

    // module scopes
    module_scopes: AstIdMap<Scope>,

    // mapping ast ids to def ids
    ast_id_to_def_id: AstIdMap<DefId>,
    def_id_to_ast_id: DefMap<AstId>,
}

impl ThingDefResolver {
    pub fn new(root: &Realm) -> Self {
        let f = |s: &mut Scope| {
            for (k, v) in PRIMITIVES {
                s.types.insert(k, v);
            }
        };
        Self {
            definitions: Definitions::new(),
            module_scopes: HashMap::new(),
            top: Scope::new_with(None, f),
            in_top_scope: true,
            ast_id_to_def_id: HashMap::new(),
            def_id_to_ast_id: HashMap::new(),
            root: root.id,
        }
    }
}

impl<'a> Visitor<'a> for ThingDefResolver {
    type Result = ();

    fn visit_realm(&mut self, val: &'a ast::Realm) -> Self::Result {
        let old_scope = mem::replace(&mut self.top, Scope::new(None));

        let Realm {
            items,
            id,
            span: _,
            name,
        } = val;

        for thing in items {
            self.visit_thing(thing)
        }

        let def_id = self.definitions.new_id();
        self.ast_id_to_def_id.insert(*id, def_id);

        let scope = mem::replace(&mut self.top, old_scope);
        self.top
            .add(name, Resolved::Def(def_id, DefType::Realm), Space::Types);

        self.module_scopes.insert(*id, scope);
    }

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
            self.top.add(
                &sig.name,
                Resolved::Def(def_id, DefType::Fun),
                Space::Values,
            );
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
            self.top
                .add(name, Resolved::Def(def_id, DefType::Instance), Space::Types);
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
            expr,
        } = val;

        stmts.iter().for_each(|st| self.visit_stmt(st));
        if let Some(e) = expr {
            self.visit_expr(e)
        }
    }
}

pub struct ScopeStack {
    scopes: ScopeIdVec<Scope>,
    current_scope: ScopeId,
    scope_id_gen: u32,
}

impl ScopeStack {
    fn new_with_prims() -> Self {
        let f = |s: &mut Scope| {
            for (k, v) in PRIMITIVES {
                s.types.insert(k, v);
            }
        };

        let mut scopes = ScopeIdVec::new();
        scopes.push(Scope::new_with(None, f));

        Self {
            scope_id_gen: 1,
            current_scope: ScopeId::ZERO,
            scopes,
        }
    }

    fn current(&self) -> ScopeId {
        self.current_scope
    }

    fn insert(&mut self, scope: Scope) -> ScopeId {
        let new_id = self.scope_id_gen;
        self.scope_id_gen += 1;
        self.scopes.push(scope);
        let old = self.current_scope;

        self.current_scope = ScopeId::new(new_id);
        old
    }

    fn get_scope(&self, id: ScopeId) -> &Scope {
        self.scopes.get(id).expect("invalid scope id")
    }

    fn get_scope_mut(&mut self, id: ScopeId) -> &mut Scope {
        self.scopes.get_mut(id).expect("invalid scope id")
    }
}

pub struct LateResolver<'a> {
    sess: &'a Session,

    // ast id -> scope stack
    current_scope: AstId,
    module_scopes: AstIdMap<ScopeStack>,

    // mapping node ids to their resolutions
    res_map: AstIdMap<Resolved<AstId>>,

    // mapping names to definitions,
    definitions: Definitions,

    // mapping ast ids to def ids
    ast_id_to_def_id: AstIdMap<DefId>,
    def_id_to_ast_id: DefMap<AstId>,

    // instance to fields
    instance_to_fields: AstIdMap<Vec<AstId>>,
    fields_to_instance: AstIdMap<AstId>,
    instance_to_scope: AstIdMap<Scope>,
}

impl<'a> LateResolver<'a> {
    pub fn new(old: ThingDefResolver, sess: &'a Session) -> Self {
        let mut scopes = ScopeIdVec::new_with_capacity(8);
        scopes.push(old.top);
        let sc = ScopeStack {
            scope_id_gen: 1,
            scopes,
            current_scope: ScopeId::ZERO,
        };

        Self {
            sess,
            current_scope: old.root,
            module_scopes: HashMap::from([(old.root, sc)]),
            definitions: old.definitions,

            ast_id_to_def_id: old.ast_id_to_def_id,
            def_id_to_ast_id: old.def_id_to_ast_id,

            res_map: HashMap::new(),

            instance_to_fields: HashMap::new(),
            fields_to_instance: HashMap::new(),
            instance_to_scope: HashMap::new(),
        }
    }

    fn current_scope_stack(&self) -> &ScopeStack {
        self.module_scopes
            .get(&self.current_scope)
            .expect("invalid id")
    }

    fn current_scope_stack_mut(&mut self) -> &mut ScopeStack {
        self.module_scopes
            .get_mut(&self.current_scope)
            .expect("invalid id")
    }

    fn new_scope(&mut self) -> ScopeId {
        let scope = Scope::new(Some(self.current_scope_stack().current()));
        self.current_scope_stack_mut().insert(scope)
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

                let scope = Scope::new_with(Some(self.current_scope_stack().current()), f);

                self.current_scope_stack_mut().insert(scope)
            }
        };

        f(self);
        self.current_scope_stack_mut().current_scope = old_id;
    }

    fn with_current_scope_mut<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Scope) -> R,
    {
        let id = self.current_scope_stack().current();
        f(self.current_scope_stack_mut().get_scope_mut(id))
    }

    fn with_current_scope<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&Scope) -> R,
    {
        f(self
            .current_scope_stack()
            .get_scope(self.current_scope_stack().current()))
    }

    fn make_local_binding(&mut self, name: Name, res: AstId) {
        let local = Resolved::Local(res);

        self.with_current_scope_mut(|scope| scope.add(&name, local, Space::Values));
    }

    fn get_name(&self, symbol: SymbolId, ns: Space) -> Resolved<AstId> {
        let f = |s: &Scope| {
            if let Some(ret) = s.get(symbol, ns) {
                Some(ret)
            } else {
                traverse_scopes(s.parent, self.current_scope_stack(), symbol, ns)
            }
        };

        self.with_current_scope(f).unwrap_or(Resolved::Err)
    }

    fn gen_def_id(&mut self, id: AstId) -> DefId {
        let def_id = self.definitions.new_id();

        self.ast_id_to_def_id.insert(id, def_id);
        self.def_id_to_ast_id.insert(def_id, id);

        def_id
    }

    #[cfg(debug_assertions)]
    pub fn res_map(&self) -> &HashMap<AstId, Resolved<AstId>> {
        &self.res_map
    }

    fn resolve_path(&mut self, arg_path: &Path, last_space: Space) -> Resolved<AstId> {
        let Path {
            path,
            span: _,
            id: _,
        } = arg_path;

        let amount_of_segments = path.len().saturating_sub(1);
        let old_scope = self.current_scope;
        let mut ret = None;

        for (ix, seg) in path.iter().enumerate() {
            let name = seg.name.interned;

            if ix == amount_of_segments {
                ret = Some(self.get_name(name, last_space))
            } else {
                match self.get_name(name, Space::Types) {
                    Resolved::Local(..) => todo!("locals don't have assoc items"),
                    Resolved::Prim(..) => todo!("how to handle builtin types with paths..."),
                    Resolved::Err => todo!("error while resolving path"),
                    Resolved::Def(ref id, DefType::Instance) => {
                        let scope_id = self
                            .def_id_to_ast_id
                            .get(id)
                            .expect("instance def id -> ast id mapping is invalid");

                        let instance_scope = self
                            .instance_to_scope
                            .get(scope_id)
                            .expect("ast id -> instance scope mapping is invalid");

                        self.current_scope = old_scope;

                        let Some(val_name) = path.get(ix + 1) else {
                            return Resolved::Err;
                        };

                        if ix + 1 != amount_of_segments {
                            todo!(
                                "somehow error out due to trying to access an assoc item as a module"
                            );
                        }

                        let res = instance_scope.get(val_name.name.interned, Space::Values);

                        return res.unwrap_or(Resolved::Err);
                    }

                    Resolved::Def(ref id, DefType::Realm) => {
                        let scope = self
                            .def_id_to_ast_id
                            .get(id)
                            .copied()
                            .expect("realm ast id is invalid");
                        self.current_scope = scope;
                    }

                    _ => todo!("handle getting wrong definitions"),
                }
            }
        }

        self.current_scope = old_scope;

        ret.unwrap_or(Resolved::Err)
    }
}

fn traverse_scopes(
    mut cursor: Option<ScopeId>,
    scopes: &ScopeStack,
    symbol: SymbolId,
    ns: Space,
) -> Option<Resolved<AstId>> {
    while let Some(ref id) = cursor {
        let scope = scopes.get_scope(*id);
        let Some(binding) = scope.get(symbol, ns) else {
            cursor = scope.parent;
            continue;
        };

        return Some(binding);
    }

    None
}

impl<'a, 'v> Visitor<'a> for LateResolver<'v>
where
    'v: 'a,
{
    type Result = ();

    fn visit_realm(&mut self, val: &'a Realm) -> Self::Result {
        let Realm {
            items,
            id,
            span: _,
            name,
        } = val;

        let old_stack = mem::replace(&mut self.current_scope, *id);
        self.module_scopes.insert(*id, ScopeStack::new_with_prims());

        for thing in items {
            self.visit_thing(thing)
        }

        let realm_visited_stack = mem::replace(&mut self.current_scope, old_stack);
        let def_id = self.gen_def_id(realm_visited_stack);

        self.with_current_scope_mut(|s| {
            s.add(name, Resolved::Def(def_id, DefType::Realm), Space::Types)
        })
    }

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
            .current_scope_stack()
            .get_scope(ScopeId::ZERO)
            .get(name.interned, Space::Values)
            .is_none()
        {
            let new_def_id = self.definitions.new_id();
            self.ast_id_to_def_id.insert(*id, new_def_id);

            let res = Resolved::Def(new_def_id, DefType::Fun);

            self.with_current_scope_mut(|s| s.add(name, res, Space::Values));
        };

        self.with_new_scope(|visitor| visitor.visit_block(block), Some(&bindings));
    }

    fn visit_instance(&mut self, val: &'a Instance) -> Self::Result {
        let ast::Instance {
            name,
            span: _,
            id: instance_id,
            fields,
            assoc,
            generics: _,
        } = val;

        let instance_def_id = self.gen_def_id(*instance_id);

        self.with_current_scope_mut(|s| {
            s.add(
                name,
                Resolved::Def(instance_def_id, DefType::Instance),
                Space::Types,
            )
        });

        let mut instance_fields = Vec::new();

        for f in fields {
            let _field_def_id = self.gen_def_id(f.id);
            self.fields_to_instance.insert(f.id, *instance_id);
            instance_fields.push(f.id);
        }

        self.instance_to_fields
            .insert(*instance_id, instance_fields);

        let Some(block) = assoc else { return };

        let mut scope = Scope::new(None);

        for s in &block.stmts {
            match &s.kind {
                StmtKind::LocalVar(l) => {
                    debug_assert!(l.mode == VarMode::Const);
                    debug_assert!(l.initializer.is_some());

                    let def_id = self.gen_def_id(l.id);
                    scope.add(
                        &l.name,
                        Resolved::Def(def_id, DefType::Const),
                        Space::Values,
                    );

                    self.visit_var_stmt(l);
                }

                StmtKind::Thing(Thing {
                    id: fun_id,
                    kind: ThingKind::Function(fun),
                }) => {
                    let def_id = self.gen_def_id(*fun_id);
                    scope.add(
                        &fun.sig.name,
                        Resolved::Def(def_id, DefType::Fun),
                        Space::Values,
                    );

                    self.visit_fn_decl(fun);
                }

                _ => unreachable!(),
            }
        }

        self.instance_to_scope.insert(*instance_id, scope);
    }

    fn visit_stmt(&mut self, val: &'a Stmt) -> Self::Result {
        let Stmt {
            kind,
            span: _,
            id: _,
        } = val;
        match kind {
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
            ExprType::Path(path) => {
                let res = self.resolve_path(path, Space::Values);

                self.res_map.insert(*id, res);
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
                let ExprType::Path(ref _path) = lvalue.ty else {
                    todo!("error, can't assign to anything other than a variable")
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

            ExprType::Block(b) => {
                self.with_new_scope(|x| x.visit_block(b), None);
            }

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
            expr,
        } = val;

        for stmt in stmts {
            if let StmtKind::Thing(item) = &stmt.kind {
                self.visit_thing(item)
            }
        }

        for stmt in stmts {
            match &stmt.kind {
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

                StmtKind::Thing(..) => (),
            }
        }

        if let Some(e) = expr {
            self.visit_expr(e)
        }
    }
}

use super::def::{DefId, DefMap, DefType, Definitions, IntTy, PrimTy, Resolved};
use crate::ast::{
    AstId, Bind, BindItem, BindItemKind, Block, Expr, ExprType, Field, FnDecl, FnSig, Instance,
    Name, Path, Realm, Stmt, StmtKind, Thing, ThingKind, Ty, TyKind, Universe, VariableStmt,
    Visitor, VisitorResult,
};
use crate::hir::lowering_ast::Mappings;
use crate::parser::AstIdMap;
use crate::session::{SymbolId, SymbolMap};
use crate::{maybe_visit, try_visit};
use std::collections::HashMap;
use std::mem;

type BindingList<'a> = &'a [(SymbolId, Resolved<AstId>)];

crate::newtyped_index!(ScopeId, ScopeIdMap, ScopeIdVec);

const PRIMITIVES: [(SymbolId, Resolved<AstId>); 12] = [
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
    (SymbolId::bool(), Resolved::Prim(PrimTy::Bool)),
];

#[derive(Debug, Clone, Copy)]
pub enum Space {
    Types,
    Values,
}

#[derive(Debug)]
pub struct Scope {
    parent: Option<ScopeId>,
    bindings: SymbolMap<Resolved<AstId>>,
    types: SymbolMap<Resolved<AstId>>,
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
        // log::trace!(
        //     "Scope::add name={} res={res:?} ns={ns:?}",
        //     name.interned.get_interned()
        // );
        match ns {
            Space::Types => self.types.insert(name.interned, res),
            Space::Values => self.bindings.insert(name.interned, res),
        };
    }
}

pub struct ThingDefResolver<'a> {
    thing_ast_id: Option<AstId>,
    // mapping names to definitions,
    definitions: Definitions<'a>,

    // def scope
    defs_scope: Scope,

    // mapping ast ids to def ids
    ast_id_to_def_id: AstIdMap<DefId>,
    def_id_to_ast_id: DefMap<AstId>,
}

impl ThingDefResolver<'_> {
    pub fn new() -> Self {
        Self {
            defs_scope: Scope::new(None),
            thing_ast_id: None,
            definitions: Definitions::new(),
            ast_id_to_def_id: HashMap::new(),
            def_id_to_ast_id: HashMap::new(),
        }
    }

    pub fn debug(&self) -> &Scope {
        &self.defs_scope
    }

    fn register_defn(&mut self, id: AstId, kind: DefType, name: Name) -> DefId {
        let def_id = self.definitions.register_defn(kind, name.interned);

        log::trace!("register_defn id={id} kind={kind:?} def_id={def_id}");
        self.ast_id_to_def_id.insert(id, def_id);
        self.def_id_to_ast_id.insert(def_id, id);

        def_id
    }
}

impl<'a, 'b> Visitor<'a> for ThingDefResolver<'b>
where
    'b: 'a,
{
    type Result = ();

    fn visit_thing(&mut self, val: &'a Thing) -> Self::Result {
        log::trace!("visit_thing val.id={}", val.id);

        self.thing_ast_id = Some(val.id);
        match &val.kind {
            ThingKind::Function(fndecl) => {
                self.visit_fn_decl(fndecl);
            }
            ThingKind::Realm(realm) => self.visit_realm(realm),
            ThingKind::Instance(instance) => self.visit_instance(instance),

            ThingKind::Bind(bind) => self.visit_bind(bind),
        }
        self.thing_ast_id.take();
    }

    fn visit_realm(&mut self, val: &'a Realm) -> Self::Result {
        let id = self.register_defn(
            self.thing_ast_id.as_ref().copied().unwrap(),
            DefType::Realm,
            val.name,
        );

        self.defs_scope
            .add(&val.name, Resolved::Def(id, DefType::Realm), Space::Types);
        for thing in &val.items {
            self.visit_thing(thing);
        }
    }

    fn visit_bind(&mut self, val: &'a Bind) -> Self::Result {
        let id = self.register_defn(
            self.thing_ast_id.as_ref().copied().unwrap(),
            DefType::Bind,
            Name::DUMMY,
        );

        self.defs_scope.add(
            &Name::DUMMY,
            Resolved::Def(id, DefType::Realm),
            Space::Types,
        );

        for item in &val.items {
            self.visit_bind_item(item);
        }
    }

    fn visit_bind_item(&mut self, val: &'a BindItem) -> Self::Result {
        self.register_defn(val.id, DefType::BindItem, Name::DUMMY);

        match val.kind {
            BindItemKind::Const(ref stmt) => {
                let id = self.register_defn(val.id, DefType::Const, stmt.name);

                self.defs_scope
                    .add(&stmt.name, Resolved::Def(id, DefType::Const), Space::Values);
            }
            BindItemKind::Fun(ref f) => self.visit_fn_decl(f),
        }
    }

    #[track_caller]
    fn visit_fn_decl(&mut self, val: &'a FnDecl) -> Self::Result {
        let id = self.register_defn(
            self.thing_ast_id.as_ref().copied().unwrap(),
            DefType::Fun,
            val.sig.name,
        );

        self.defs_scope.add(
            &val.sig.name,
            Resolved::Def(id, DefType::Fun),
            Space::Values,
        );

        self.visit_block(&val.block);
    }

    fn visit_instance(&mut self, val: &'a Instance) -> Self::Result {
        let id = self.register_defn(
            self.thing_ast_id.as_ref().copied().unwrap(),
            DefType::Instance,
            val.name,
        );

        self.defs_scope.add(
            &val.name,
            Resolved::Def(id, DefType::Instance),
            Space::Types,
        );

        let ctor_def_id = self.register_defn(val.ctor_id, DefType::AdtCtor, val.name);

        self.defs_scope.add(
            &val.name,
            Resolved::Def(ctor_def_id, DefType::AdtCtor),
            Space::Values,
        );

        for field in &val.fields {
            self.visit_field(field);
        }
    }

    fn visit_field(&mut self, val: &'a Field) -> Self::Result {
        let _ = self.register_defn(val.id, DefType::Field, val.name);
    }

    fn visit_block(&mut self, val: &'a Block) -> Self::Result {
        for st in &val.stmts {
            self.visit_stmt(st);
        }

        if let Some(e) = &val.expr {
            self.visit_expr(e);
        }
    }
}

pub struct ScopeStack {
    scopes: ScopeIdVec<Scope>,
    current_scope: ScopeId,
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
            current_scope: ScopeId::ZERO,
            scopes,
        }
    }

    fn current(&self) -> ScopeId {
        self.current_scope
    }

    fn insert(&mut self, scope: Scope) -> ScopeId {
        let new_id = self.scopes.push(scope);
        let old = self.current_scope;

        self.current_scope = new_id;
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
    def_scope: Scope,
    current_item: Option<AstId>,

    // ast id -> scope stack
    current_scope: AstId,
    module_scopes: AstIdMap<ScopeStack>,

    current_instance: Option<AstId>,
    current_bind_item: Option<AstId>,
    current_bind_ty: Option<AstId>,

    // mapping names to definitions,
    pub definitions: Definitions<'a>,

    // mapping ast ids to def ids
    pub bind_to_scope: AstIdMap<ScopeId>,

    pub maps: Mappings,
}

impl<'a> LateResolver<'a> {
    pub fn new(old: ThingDefResolver<'a>, root: &Universe) -> Self {
        Self {
            def_scope: old.defs_scope,
            current_item: None,
            current_instance: None,
            current_bind_ty: None,

            current_bind_item: None,

            current_scope: root.id,
            module_scopes: HashMap::from([(root.id, ScopeStack::new_with_prims())]),

            definitions: old.definitions,

            bind_to_scope: HashMap::new(),

            maps: Mappings::new(old.ast_id_to_def_id, old.def_id_to_ast_id),
        }
    }

    pub fn into_mappings(self) -> Mappings {
        self.maps
    }

    #[track_caller]
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

    fn with_new_scope<F>(&mut self, f: F, bindings: Option<BindingList<'_>>)
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

    #[track_caller]
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

    #[track_caller]
    fn get_name(&self, symbol: SymbolId, ns: Space) -> Resolved<AstId> {
        let f = |s: &Scope| {
            if let Some(ret) = s.get(symbol, ns) {
                Some(ret)
            } else {
                traverse_scopes(s.parent, self.current_scope_stack(), symbol, ns)
            }
        };

        match self.with_current_scope(f) {
            Some(val) => val,
            None => self.def_scope.get(symbol, ns).unwrap_or(Resolved::Err),
        }
    }

    #[track_caller]
    fn resolve_path(&mut self, arg_path: &Path, last_space: Space) -> Resolved<AstId> {
        log::trace!(
            "resolve path arg_path={:?} last_space={last_space:?}",
            arg_path
                .path
                .iter()
                .map(|seg| seg.name.interned.get_interned())
                .collect::<Vec<_>>()
        );

        let amount_of_segments = arg_path.path.len().saturating_sub(1);
        let old_scope = self.current_scope;
        let mut ret = Resolved::Err;

        for (ix, seg) in arg_path.path.iter().enumerate() {
            let name = seg.name.interned;

            if ix == amount_of_segments {
                let ret = self.get_name(name, last_space);
                log::trace!(
                    "resolve_path exited at if guard resolved={ret:?} with ns={last_space:?}"
                );
                return ret;
            }

            ret = match self.get_name(name, Space::Types) {
                cap @ Resolved::Def(.., DefType::Instance) => cap,

                Resolved::Def(id, DefType::Realm) => {
                    self.current_scope = self.maps.ast_id_of(id);
                    continue;
                }

                _ => todo!("Path couldn't be resolved: {arg_path:#?}"),
            }
        }

        self.current_scope = old_scope;
        log::trace!("resolve_path resolved={ret:?}");
        ret
    }

    #[track_caller]
    #[inline]
    fn current_item(&self) -> AstId {
        self.current_item.expect("not inside of an item!")
    }

    #[track_caller]
    #[inline]
    fn get_def_id(&self, ast_id: AstId) -> DefId {
        self.maps.def_id_of(ast_id)
    }
}

fn traverse_scopes(
    mut cursor: Option<ScopeId>,
    scopes: &ScopeStack,
    symbol: SymbolId,
    ns: Space,
) -> Option<Resolved<AstId>> {
    log::trace!("traverse_scopes sym={} ns={ns:?}", symbol.get_interned());
    while let Some(ref id) = cursor {
        let scope = scopes.get_scope(*id);
        let Some(binding) = scope.get(symbol, ns) else {
            cursor = scope.parent;
            continue;
        };

        return Some(binding);
    }

    log::trace!(
        "traverse_scopes loop ended sym={} ns={ns:?}",
        symbol.get_interned()
    );

    None
}

impl<'a> Visitor<'a> for LateResolver<'_> {
    type Result = ();

    fn visit_thing(&mut self, val: &'a Thing) -> Self::Result {
        let old = self.current_item.replace(val.id);
        match &val.kind {
            ThingKind::Function(f) => self.visit_fn_decl(f),
            ThingKind::Realm(r) => self.visit_realm(r),
            ThingKind::Instance(i) => self.visit_instance(i),
            ThingKind::Bind(a) => self.visit_bind(a),
        }

        self.current_item = old;
    }

    fn visit_realm(&mut self, val: &'a Realm) -> Self::Result {
        let Realm {
            items,
            id: _,
            span: _,
            name,
        } = val;

        let current_item = self.current_item();
        let old_stack = mem::replace(&mut self.current_scope, current_item);

        self.module_scopes
            .insert(current_item, ScopeStack::new_with_prims());

        for thing in items {
            self.visit_thing(thing);
        }

        let realm_visited_stack = mem::replace(&mut self.current_scope, old_stack);
        let def_id = self.get_def_id(realm_visited_stack);

        self.with_current_scope_mut(|s| {
            s.add(name, Resolved::Def(def_id, DefType::Realm), Space::Types);
        });
    }

    fn visit_bind(&mut self, bind: &'a Bind) -> Self::Result {
        if bind.mask.is_some() {
            unimplemented!("interfaces!")
        }

        self.current_bind_ty = Some(bind.victim.id);

        self.visit_ty(&bind.victim);

        if let TyKind::Path(path) = &bind.victim.kind {
            let resolved = self.resolve_path(path, Space::Types);

            if let Resolved::Def(def_id, DefType::Instance) = resolved {
                self.maps
                    .insert_instance_to_bind(def_id, self.current_item());
            }
        }

        let scope_id = self.current_scope_stack().scopes.future_id();

        let res = self.maps.resolve(bind.victim.id);
        self.with_new_scope(
            |this| {
                for item in &bind.items {
                    this.visit_bind_item(item);
                }
            },
            Some(&[(SymbolId::self_(), res)]),
        );

        self.current_bind_ty.take();
        self.bind_to_scope.insert(bind.id, scope_id);
    }

    fn visit_bind_item(&mut self, val: &'a BindItem) -> Self::Result {
        self.current_bind_item = Some(val.id);
        match val.kind {
            BindItemKind::Const(ref var_stmt) => {
                let def_id = self.get_def_id(val.id);
                self.with_current_scope_mut(|scope| {
                    scope.add(
                        &var_stmt.name,
                        Resolved::Def(def_id, DefType::Const),
                        Space::Values,
                    );
                });
                self.visit_var_stmt(var_stmt);
            }

            BindItemKind::Fun(ref f) => self.visit_fn_decl(f),
        }
        self.current_bind_item.take();
    }

    fn visit_fn_decl(&mut self, val: &'a crate::ast::FnDecl) -> Self::Result {
        let FnSig {
            name,
            args,
            ret_type,
            span: _,
            id: _,
        } = &val.sig;

        let bindings: Vec<_> = args
            .iter()
            .map(|arg| {
                self.visit_ty(&arg.ty);
                (arg.ident.interned, Resolved::Local(arg.id))
            })
            .collect();

        self.visit_ty(ret_type);

        let thing_ast_id = self
            .current_bind_item
            .unwrap_or_else(|| self.current_item());

        let def_id = self.get_def_id(thing_ast_id);

        if self.current_scope == AstId::ZERO && name.interned == SymbolId::main() {
            self.maps.set_entry_point(def_id);
        }

        self.with_current_scope_mut(|scope| {
            scope.add(name, Resolved::Def(def_id, DefType::Fun), Space::Values);
        });

        self.with_new_scope(|visitor| visitor.visit_block(&val.block), Some(&bindings));
    }

    fn visit_instance(&mut self, val: &'a Instance) -> Self::Result {
        let instance_def_id = self.get_def_id(self.current_item());

        self.current_instance.replace(val.id);

        self.with_current_scope_mut(|scope| {
            // Redundant?
            scope.add(
                &val.name,
                Resolved::Def(instance_def_id, DefType::Instance),
                Space::Types,
            );
        });

        for f in &val.fields {
            self.visit_field(f);
        }

        self.current_instance.take();
    }

    fn visit_field(&mut self, field: &'a Field) -> Self::Result {
        let field_def_id = self.get_def_id(field.id);

        self.maps
            .map_to_resolved(field.id, Resolved::Def(field_def_id, DefType::Field));

        let current_instance_id = self
            .current_instance
            .expect("visited a field outside an instance?");

        self.maps
            .insert_instance_field(current_instance_id, field_def_id);

        self.visit_ty(&field.ty);
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
                    self.visit_expr(init);
                }
                self.make_local_binding(*name, *id);
            }

            StmtKind::Expr(expr) => {
                self.visit_expr(expr);
            }

            StmtKind::Thing(def) => self.visit_thing(def),
        }
    }

    fn visit_expr(&mut self, val: &'a Expr) -> Self::Result {
        let Expr { ty, span: _, id: _ } = val;
        match ty {
            ExprType::Path(path) => {
                let res = self.resolve_path(path, Space::Values);

                self.maps.map_to_resolved(path.id, res);
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

            ExprType::CommaGroup(exprs) | ExprType::List(exprs) => {
                for e in exprs {
                    self.visit_expr(e);
                }
            }

            ExprType::Assign {
                lvalue,
                rvalue,
                mode: _,
            } => {
                let (ExprType::Path(..) | ExprType::FieldAccess { .. }) = lvalue.ty else {
                    todo!("error, can't assign to anything other than a variable or field access")
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
                    self.visit_expr(arg);
                }
            }

            ExprType::Return { ret: Some(expr) } => {
                self.visit_expr(expr);
            }

            ExprType::For {
                iterable: _,
                pat: _,
                body: _,
            } => {
                todo!("for loop")
            }

            ExprType::Loop { body } => self.visit_block(body),

            ExprType::While { cond, body } | ExprType::Until { cond, body } => {
                self.visit_expr(cond);
                self.visit_block(body);
            }

            ExprType::FieldAccess { source, field: _ } => self.visit_expr(source),

            ExprType::Lambda { args: _, body: _ } => {
                todo!("lambda")
            }

            ExprType::Constant(..) => (),

            ExprType::Block(b) => {
                self.with_new_scope(|x| x.visit_block(b), None);
            }

            ExprType::Index { indexed, index } => {
                self.visit_expr(indexed);
                self.visit_expr(index);
            }

            ExprType::If {
                cond,
                if_block,
                else_ifs,
                otherwise,
            } => {
                try_visit!(self.visit_expr(cond), self.visit_block(if_block));

                for elsif in else_ifs {
                    self.visit_expr(&elsif.cond);
                    self.visit_block(&elsif.body);
                }

                maybe_visit!(v: self, m: visit_block, otherwise);
            }

            any => todo!("to-do expression kinds: {any:#?}"),
        }
    }

    fn visit_ty(&mut self, val: &'a Ty) -> Self::Result {
        let Ty {
            kind,
            span: _,
            id: _,
        } = val;

        match kind {
            TyKind::Fn { args, ret } => {
                for arg in args {
                    self.visit_ty(arg);
                }

                if let Some(ret) = ret {
                    self.visit_ty(ret);
                }
            }

            TyKind::Array(ty) => self.visit_ty(ty),

            TyKind::Path(path) => {
                let res = self.resolve_path(path, Space::Types);
                self.maps.map_to_resolved(val.id, res);
                self.maps.map_to_resolved(path.id, res);
            }

            TyKind::MethodSelf => {
                let Some(_cur) = self.current_bind_item else {
                    todo!("self ty outside bind!");
                };
            }

            TyKind::Err => (), // explicit matching in case i add smth new
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
                self.visit_thing(item);
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
                        self.visit_expr(init);
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
            self.visit_expr(e);
        }
    }
}

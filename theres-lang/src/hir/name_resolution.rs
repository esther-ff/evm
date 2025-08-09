use super::def::{DefId, DefMap, DefType, Definitions, IntTy, PrimTy, Resolved};
use crate::ast::{
    Arg, AstId, Block, Expr, ExprType, Field, FnDecl, FnSig, Instance, Name, Path, Realm, Stmt,
    StmtKind, Ty, TyKind, Universe, VariableStmt, Visitor,
};

use crate::hir::lowering_ast::Mappings;
use crate::parser::AstIdMap;
use crate::session::{SymbolId, SymbolMap};
use std::collections::HashMap;
use std::mem;

type BindingList<'a> = &'a [(SymbolId, Resolved<AstId>)];

crate::newtyped_index!(ScopeId, ScopeIdMap, ScopeIdVec);

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
        match ns {
            Space::Types => self.types.insert(name.interned, res),
            Space::Values => self.bindings.insert(name.interned, res),
        };
    }
}

pub struct ThingDefResolver<'a> {
    // mapping names to definitions,
    definitions: Definitions<'a>,

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

impl ThingDefResolver<'_> {
    pub fn new(root: &Universe) -> Self {
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

impl<'a, 'b> Visitor<'a> for ThingDefResolver<'b>
where
    'b: 'a,
{
    type Result = ();

    fn visit_realm(&mut self, val: &'a Realm) -> Self::Result {
        let old_scope = mem::replace(&mut self.top, Scope::new(None));

        let Realm {
            items,
            id,
            span: _,
            name,
        } = val;

        for thing in items {
            self.visit_thing(thing);
        }

        let def_id = self.definitions.new_id();
        self.ast_id_to_def_id.insert(*id, def_id);

        let scope = mem::replace(&mut self.top, old_scope);
        self.top
            .add(name, Resolved::Def(def_id, DefType::Realm), Space::Types);

        self.module_scopes.insert(*id, scope);
    }

    fn visit_fn_decl(&mut self, val: &'a FnDecl) -> Self::Result {
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
            generics: _,
            id,
        } = val;

        let def_id = self.definitions.new_id();
        self.ast_id_to_def_id.insert(*id, def_id);

        if self.in_top_scope {
            self.top
                .add(name, Resolved::Def(def_id, DefType::Instance), Space::Types);
        }

        for field in fields {
            self.visit_field(field);
        }
    }

    fn visit_field(&mut self, val: &'a Field) -> Self::Result {
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

        for st in stmts {
            self.visit_stmt(st);
        }

        if let Some(e) = expr {
            self.visit_expr(e);
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
    // ast id -> scope stack
    current_scope: AstId,
    module_scopes: AstIdMap<ScopeStack>,

    // current instance
    current_instance: Option<DefId>,
    instance_field_stack: Vec<DefId>,

    // mapping node ids to their resolutions
    pub res_map: AstIdMap<Resolved<AstId>>,

    // mapping names to definitions,
    pub definitions: Definitions<'a>,

    // mapping ast ids to def ids
    pub ast_id_to_def_id: AstIdMap<DefId>,
    pub def_id_to_ast_id: DefMap<AstId>,

    // instance to fields
    pub instance_to_fields: AstIdMap<Vec<DefId>>,
    pub fields_to_instance: AstIdMap<DefId>,
    pub instance_to_scope: AstIdMap<Scope>,
}

impl<'a> LateResolver<'a> {
    pub fn new(old: ThingDefResolver<'a>) -> Self {
        let mut scopes = ScopeIdVec::new_with_capacity(8);
        scopes.push(old.top);
        let sc = ScopeStack {
            scope_id_gen: 1,
            scopes,
            current_scope: ScopeId::ZERO,
        };

        Self {
            current_scope: old.root,
            current_instance: None,
            module_scopes: HashMap::from([(old.root, sc)]),
            definitions: old.definitions,
            instance_field_stack: Vec::new(),

            ast_id_to_def_id: old.ast_id_to_def_id,
            def_id_to_ast_id: old.def_id_to_ast_id,

            res_map: HashMap::new(),

            instance_to_fields: HashMap::new(),
            fields_to_instance: HashMap::new(),
            instance_to_scope: HashMap::new(),
        }
    }

    pub fn into_mappings(self) -> Mappings {
        Mappings::new(
            self.instance_to_fields,
            self.fields_to_instance,
            self.res_map,
            self.ast_id_to_def_id,
        )
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
                ret = Some(self.get_name(name, last_space));
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

                        return instance_scope
                            .get(val_name.name.interned, Space::Values)
                            .unwrap_or(Resolved::Err);
                    }

                    Resolved::Def(ref id, DefType::Realm) => {
                        let scope = self
                            .def_id_to_ast_id
                            .get(id)
                            .copied()
                            .expect("realm ast id is invalid");
                        self.current_scope = scope;
                    }

                    Resolved::Def(_, _) => todo!("handle getting wrong definitions"),
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

impl<'a> Visitor<'a> for LateResolver<'_> {
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
            self.visit_thing(thing);
        }

        let realm_visited_stack = mem::replace(&mut self.current_scope, old_stack);
        let def_id = self.gen_def_id(realm_visited_stack);

        self.with_current_scope_mut(|s| {
            s.add(name, Resolved::Def(def_id, DefType::Realm), Space::Types);
        });
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
        }

        self.with_new_scope(|visitor| visitor.visit_block(block), Some(&bindings));
    }

    fn visit_instance(&mut self, val: &'a Instance) -> Self::Result {
        let Instance {
            name,
            span: _,
            id,
            fields,
            generics: _,
        } = val;

        let instance_id = *id;
        let instance_def_id = self.gen_def_id(instance_id);

        self.current_instance.replace(instance_def_id);

        self.with_current_scope_mut(|s| {
            s.add(
                name,
                Resolved::Def(instance_def_id, DefType::Instance),
                Space::Types,
            );
        });

        for f in fields {
            self.visit_field(f);
        }

        self.instance_to_fields
            .insert(instance_id, mem::take(&mut self.instance_field_stack));
    }

    fn visit_field(&mut self, field: &'a Field) -> Self::Result {
        let field_def_id = self.gen_def_id(field.id);

        self.res_map
            .insert(field.id, Resolved::Def(field_def_id, DefType::Field));

        let current_instance = self
            .current_instance
            .expect("visited a field outside an instance?");

        self.fields_to_instance.insert(field.id, current_instance);
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
        let Expr { ty, span: _, id } = val;
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
                    self.visit_expr(e);
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

            ExprType::ArrayDecl {
                ty,
                size,
                initialize,
            } => {
                self.visit_ty(ty);
                self.visit_expr(size);

                for inits in initialize {
                    self.visit_expr(inits);
                }
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
                match self.resolve_path(path, Space::Types) {
                    Resolved::Err => println!("error: type not found, path: {path:?}"),
                    test => println!("type was correct!!! {test:#?}"), // just to silence clippy
                }
            }

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

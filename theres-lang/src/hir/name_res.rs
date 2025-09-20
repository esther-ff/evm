use std::collections::HashMap;
use std::mem;
use std::ops::Sub;

#[allow(clippy::wildcard_imports)]
use crate::ast::*;
use crate::errors::TheresError;
use crate::hir::def::{DefId, DefMap, DefType, DefVec, IntTy, PrimTy, Resolved};
use crate::hir::lowering_ast::Mappings;
use crate::id::IdxVec;
use crate::session::{Session, SymbolId};

crate::newtyped_index!(Scope, ScopeMap, ScopeVec, ScopeSlice);

pub enum ResError {
    DefinedAlready {
        name: SymbolId,
    },

    NotFound {
        name: SymbolId,
        namespace: Namespace,
    },
}

impl TheresError for ResError {
    fn phase() -> &'static str {
        "resolving"
    }

    fn message(&self) -> std::borrow::Cow<'static, str> {
        match self {
            Self::DefinedAlready { name } => format!(
                "the name '{name}' is already defined",
                name = name.get_interned()
            ),
            Self::NotFound { name, namespace } => format!(
                "the {name_of} '{binding}' hasn't been found in this scope",
                binding = name.get_interned(),
                name_of = namespace.word()
            ),
        }
        .into()
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Namespace {
    Types,
    Values,
}

impl Namespace {
    fn word(self) -> &'static str {
        match self {
            Self::Types => "type",
            Self::Values => "value",
        }
    }
}

const PRIMITIVES: &[(SymbolId, Resolved<AstId>)] = &[
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

#[derive(Debug)]
struct ScopeData {
    values: HashMap<SymbolId, Resolved<AstId>>,
    types: HashMap<SymbolId, Resolved<AstId>>,
    anchor: Option<Scope>,
}

impl ScopeData {
    fn new(anchor: Option<Scope>) -> Self {
        Self {
            values: HashMap::new(),
            types: PRIMITIVES.iter().copied().collect(),
            anchor,
        }
    }

    fn add(&mut self, ns: Namespace, sym: SymbolId, res: Resolved<AstId>) {
        match ns {
            Namespace::Types => self.types.insert(sym, res),
            Namespace::Values => self.values.insert(sym, res),
        };
    }

    fn get(&self, ns: Namespace, name: SymbolId) -> Option<Resolved<AstId>> {
        match ns {
            Namespace::Types => self.types.get(&name),
            Namespace::Values => self.values.get(&name),
        }
        .copied()
    }
}

pub struct FirstPass<'cx> {
    cx: &'cx Session<'cx>,
    scopes: ScopeVec<ScopeData>,
    path: Vec<Scope>,
    current_scope: Scope,
    // sym_defs: SymbolMap<DefId>,
    did_defs: DefVec<DefType>,
    realm_scopes: DefMap<(ScopeVec<ScopeData>, Vec<Scope>)>,

    ast_id_did: HashMap<AstId, DefId>,
    did_ast_id: HashMap<DefId, AstId>,

    thing_ast_id: Option<AstId>,
}

impl<'cx> FirstPass<'cx> {
    pub fn new(cx: &'cx Session<'cx>) -> Self {
        let mut scopes = IdxVec::new();
        let current_scope = scopes.push(ScopeData::new(None));

        Self {
            cx,
            thing_ast_id: None,
            path: vec![current_scope],
            scopes,
            current_scope,
            // sym_defs: HashMap::default(),
            did_defs: IdxVec::new(),
            realm_scopes: HashMap::default(),
            did_ast_id: HashMap::default(),
            ast_id_did: HashMap::default(),
        }
    }

    #[track_caller]
    fn define(&mut self, ast_id: AstId, ty: DefType, _name: Name) -> DefId {
        let did = self.did_defs.push(ty);

        dbg!(ast_id);

        assert!(self.ast_id_did.insert(ast_id, did).is_none());
        assert!(self.did_ast_id.insert(did, ast_id).is_none());

        // if self.sym_defs.insert(name.interned, did).is_some() {
        //     self.cx.diag().emit_err(
        //         ResError::DefinedAlready {
        //             name: name.interned,
        //         },
        //         name.span,
        //     );
        // }

        did
    }

    fn add_to_scope(&mut self, ns: Namespace, sym: SymbolId, res: Resolved<AstId>) {
        self.scopes[self.current_scope].add(ns, sym, res);
    }

    fn with_new_scope<F>(&mut self, work: F)
    where
        F: FnOnce(&mut Self),
    {
        let new = self.scopes.push(ScopeData::new(self.current_scope.into()));
        self.path.push(new);
        let old = mem::replace(&mut self.current_scope, new);
        work(self);
        self.path.push(old);
        self.current_scope = old;
    }

    fn in_realm<F>(&mut self, work: F, realm_did: DefId)
    where
        F: FnOnce(&mut Self),
    {
        self.realm_scopes.entry(realm_did).or_insert_with(|| {
            let mut data = ScopeVec::new();
            let path = data.push(ScopeData::new(None));

            (data, vec![path])
        });

        if let Some((realm_scope_data, realm_path)) = self.realm_scopes.get_mut(&realm_did) {
            mem::swap(&mut self.scopes, realm_scope_data);
            mem::swap(&mut self.path, realm_path);
        }

        work(self);

        if let Some((realm_scope_data, realm_path)) = self.realm_scopes.get_mut(&realm_did) {
            mem::swap(&mut self.scopes, realm_scope_data);
            mem::swap(&mut self.path, realm_path);
        }
    }
}

impl<'vis> Visitor<'vis> for FirstPass<'_> {
    type Result = ();

    fn visit_thing(&mut self, val: &'vis Thing) -> Self::Result {
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

    fn visit_realm(&mut self, val: &'vis Realm) -> Self::Result {
        let id = self.define(
            self.thing_ast_id.as_ref().copied().unwrap(),
            DefType::Realm,
            val.name,
        );

        self.add_to_scope(
            Namespace::Types,
            val.name.interned,
            Resolved::Def(id, DefType::Realm),
        );

        self.in_realm(
            |this| {
                for thing in &val.items {
                    this.visit_thing(thing);
                }
            },
            id,
        );
    }

    fn visit_bind(&mut self, val: &'vis Bind) -> Self::Result {
        let id = self.define(
            self.thing_ast_id.as_ref().copied().unwrap(),
            DefType::Bind,
            Name::DUMMY,
        );

        self.add_to_scope(
            Namespace::Types,
            SymbolId::DUMMY,
            Resolved::Def(id, DefType::Realm),
        );

        for item in &val.items {
            self.visit_bind_item(item);
        }
    }

    #[track_caller]
    fn visit_bind_item(&mut self, val: &'vis BindItem) -> Self::Result {
        // self.define(val.id, DefType::BindItem, Name::DUMMY);
        let old = self.thing_ast_id.replace(val.id);
        self.with_new_scope(|this| match val.kind {
            BindItemKind::Const(ref stmt) => {
                let id = this.define(val.id, DefType::Const, stmt.name);

                this.add_to_scope(
                    Namespace::Values,
                    stmt.name.interned,
                    Resolved::Def(id, DefType::Const),
                );
            }
            BindItemKind::Fun(ref f) => this.visit_fn_decl(f),
        });
        self.thing_ast_id = old;
    }

    #[track_caller]
    fn visit_fn_decl(&mut self, val: &'vis FnDecl) -> Self::Result {
        let id = self.define(
            self.thing_ast_id.as_ref().copied().unwrap(),
            DefType::Fun,
            val.sig.name,
        );

        self.add_to_scope(
            Namespace::Values,
            val.sig.name.interned,
            Resolved::Def(id, DefType::Fun),
        );

        self.visit_block(&val.block);
    }

    fn visit_instance(&mut self, val: &'vis Instance) -> Self::Result {
        let id = self.define(
            self.thing_ast_id.as_ref().copied().unwrap(),
            DefType::Instance,
            val.name,
        );

        self.add_to_scope(
            Namespace::Types,
            val.name.interned,
            Resolved::Def(id, DefType::Instance),
        );

        let ctor_def_id = self.define(val.ctor_id, DefType::AdtCtor, val.name);

        self.add_to_scope(
            Namespace::Values,
            val.name.interned,
            Resolved::Def(ctor_def_id, DefType::AdtCtor),
        );

        for field in &val.fields {
            self.visit_field(field);
        }
    }

    fn visit_field(&mut self, val: &'vis Field) -> Self::Result {
        let _ = self.define(val.id, DefType::Field, val.name);
    }

    fn visit_block(&mut self, val: &'vis Block) -> Self::Result {
        self.with_new_scope(|this| {
            for st in &val.stmts {
                this.visit_stmt(st);
            }

            if let Some(e) = &val.expr {
                this.visit_expr(e);
            }
        });
    }
}

struct SecondPass<'cx> {
    cx: &'cx Session<'cx>,
    maps: Mappings,

    current_instance: Option<AstId>,
    current_bind_ty: Option<AstId>,
    current_bind_item: Option<AstId>,

    path: std::vec::IntoIter<Scope>,
    current_scope: Scope,
    scopes: ScopeVec<ScopeData>,

    realm_scopes: DefMap<(ScopeVec<ScopeData>, std::vec::IntoIter<Scope>)>,

    current_item: Option<AstId>,

    arg_stack: Vec<(SymbolId, Resolved<AstId>)>,
}

impl<'cx> SecondPass<'cx> {
    fn new(resolver: FirstPass<'cx>) -> Self {
        let FirstPass {
            cx,
            scopes,
            path,
            current_scope,
            did_defs: _,
            realm_scopes,
            ast_id_did,
            did_ast_id,
            thing_ast_id: _,
        } = resolver;

        Self {
            cx,
            maps: Mappings::new(ast_id_did, did_ast_id),
            current_instance: None,
            current_bind_ty: None,
            current_bind_item: None,
            scopes,
            arg_stack: vec![],
            current_item: None,
            // unironically, stupid
            // (reallocates an entire hashmap)
            realm_scopes: realm_scopes
                .into_iter()
                .map(|(k, (data, path))| (k, (data, path.into_iter())))
                .collect(),
            path: path.into_iter(),
            current_scope,
        }
    }

    fn current_scope_mut(&mut self) -> &mut ScopeData {
        &mut self.scopes[self.current_scope]
    }

    fn current_scope(&self) -> &ScopeData {
        &self.scopes[self.current_scope]
    }

    fn make_local_binding(&mut self, name: Name, res: AstId) {
        let local = Resolved::Local(res);

        self.current_scope_mut()
            .add(Namespace::Values, name.interned, local);
    }

    #[track_caller]
    fn get_name(&self, symbol: SymbolId, ns: Namespace) -> Resolved<AstId> {
        let scope = self.current_scope();

        if let Some(found) = scope.get(ns, symbol) {
            found
        } else {
            let mut cursor = scope.anchor;

            while let Some(scope_id) = cursor {
                match self.scopes[scope_id].get(ns, symbol) {
                    None => cursor = self.scopes[scope_id].anchor,
                    Some(found) => return found,
                }
            }

            Resolved::Err
        }
    }

    fn process_path(&mut self, ast_path: &Path, last: Namespace) -> Resolved<AstId> {
        debug_assert!(!ast_path.path.is_empty());

        let segments = &ast_path.path;
        let mut scope = self.current_scope;
        let mut explored = &self.scopes;
        let mut ret = Resolved::Err;

        if segments.len() == 1 {
            let ret = self.get_name(segments[0].name.interned, last);
            if ret.is_err() {
                self.emit_not_found(ast_path, 0, last);
            }
            return ret;
        }

        for (segment_ix, segment) in segments.iter().enumerate() {
            let seg_name = segment.name.interned;

            if segment_ix == segments.len().sub(1) {
                // println!("Exiting here");
                // dbg!(&explored[scope]);
                ret = explored[scope].get(last, seg_name).unwrap_or(Resolved::Err);

                dbg!(ret);
                if ret.is_err() {
                    self.emit_not_found(ast_path, segment_ix, last);
                }
                break;
            }

            match explored[scope]
                .get(Namespace::Types, seg_name)
                .unwrap_or(Resolved::Err)
            {
                Resolved::Def(did, DefType::Realm) => {
                    explored = &self.realm_scopes[&did].0;
                    scope = Scope::ZERO;
                }

                Resolved::Local(..) => unreachable!("locals shouldn't be referenced by paths"),

                Resolved::Err => {
                    self.cx.diag().emit_err(
                        ResError::NotFound {
                            name: seg_name,
                            namespace: Namespace::Types,
                        },
                        segment.span,
                    );

                    break;
                }

                any => {
                    ret = any;
                    break;
                }
            }
        }

        ret
    }

    #[track_caller]
    fn path_forward(&mut self) {
        self.current_scope = self.path.next().unwrap();
    }

    #[track_caller]
    #[inline]
    fn current_item(&self) -> AstId {
        self.current_item.expect("not inside of an item!")
    }

    #[track_caller]
    #[inline]
    fn get_def_id(&self, ast_id: AstId) -> DefId {
        dbg!(ast_id);
        self.maps.def_id_of(ast_id)
    }

    fn switch_scope_paths<F>(&mut self, realm_did: DefId, work: F)
    where
        F: FnOnce(&mut Self),
    {
        if let Some((realm_scope_data, realm_path)) = self.realm_scopes.get_mut(&realm_did) {
            mem::swap(&mut self.scopes, realm_scope_data);
            mem::swap(&mut self.path, realm_path);
        }

        work(self);

        if let Some((realm_scope_data, realm_path)) = self.realm_scopes.get_mut(&realm_did) {
            mem::swap(&mut self.scopes, realm_scope_data);
            mem::swap(&mut self.path, realm_path);
        }
    }

    fn emit_not_found(&self, path: &Path, idx: usize, namespace: Namespace) {
        let name = path.path[idx].name.interned;
        let span = path.path[idx].span;

        self.cx
            .diag()
            .emit_err(ResError::NotFound { name, namespace }, span);
    }
}

impl<'vis> Visitor<'vis> for SecondPass<'_> {
    type Result = ();

    fn visit_thing(&mut self, val: &'vis Thing) -> Self::Result {
        let old = self.current_item.replace(val.id);
        match &val.kind {
            ThingKind::Function(f) => self.visit_fn_decl(f),
            ThingKind::Realm(r) => self.visit_realm(r),
            ThingKind::Instance(i) => self.visit_instance(i),
            ThingKind::Bind(a) => self.visit_bind(a),
        }

        self.current_item = old;
    }

    fn visit_realm(&mut self, val: &'vis Realm) -> Self::Result {
        let Realm {
            items,
            span: _,
            name: _,
        } = val;

        let current_item = self.current_item();
        let realm_did = self.get_def_id(current_item);

        self.switch_scope_paths(realm_did, |this| {
            for thing in items {
                this.visit_thing(thing);
            }
        });
    }

    fn visit_bind(&mut self, bind: &'vis Bind) -> Self::Result {
        if bind.mask.is_some() {
            unimplemented!("interfaces!")
        }

        self.current_bind_ty = Some(bind.victim.id);

        self.visit_ty(&bind.victim);

        if let TyKind::Path(path) = &bind.victim.kind {
            let resolved = self.process_path(path, Namespace::Types);

            if let Resolved::Def(def_id, DefType::Instance) = resolved {
                self.maps
                    .insert_instance_to_bind(def_id, self.current_item());
            }
        }

        let res = self.maps.resolve(bind.victim.id);

        self.path_forward();
        self.current_scope_mut()
            .add(Namespace::Values, SymbolId::self_(), res);

        for item in &bind.items {
            self.visit_bind_item(item);
        }

        self.current_bind_ty.take();
    }

    fn visit_bind_item(&mut self, val: &'vis BindItem) -> Self::Result {
        self.current_bind_item = Some(val.id);
        match val.kind {
            BindItemKind::Const(ref var_stmt) => {
                let def_id = self.get_def_id(val.id);
                self.current_scope_mut().add(
                    Namespace::Values,
                    var_stmt.name.interned,
                    Resolved::Def(def_id, DefType::Const),
                );
                self.visit_var_stmt(var_stmt);
            }

            BindItemKind::Fun(ref f) => self.visit_fn_decl(f),
        }
        self.current_bind_item.take();
    }

    fn visit_fn_decl(&mut self, val: &'vis crate::ast::FnDecl) -> Self::Result {
        let FnSig {
            name,
            args,
            ret_type,
            span: _,
            id: _,
        } = &val.sig;

        for arg in args {
            self.visit_ty(&arg.ty);
        }

        self.arg_stack.extend(
            args.iter()
                .map(|arg| (arg.ident.interned, Resolved::Local(arg.id))),
        );

        self.visit_ty(ret_type);

        let thing_ast_id = self
            .current_bind_item
            .unwrap_or_else(|| self.current_item());

        let def_id = self.get_def_id(thing_ast_id);

        self.current_scope_mut().add(
            Namespace::Values,
            name.interned,
            Resolved::Def(def_id, DefType::Fun),
        );

        self.visit_block(&val.block);
    }

    fn visit_instance(&mut self, val: &'vis Instance) -> Self::Result {
        let instance_def_id = self.get_def_id(self.current_item());

        self.current_instance.replace(val.id);

        // Redundant?
        self.current_scope_mut().add(
            Namespace::Types,
            val.name.interned,
            Resolved::Def(instance_def_id, DefType::Instance),
        );

        for f in &val.fields {
            self.visit_field(f);
        }

        self.current_instance.take();
    }

    fn visit_field(&mut self, field: &'vis Field) -> Self::Result {
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

    fn visit_stmt(&mut self, val: &'vis Stmt) -> Self::Result {
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

    fn visit_expr(&mut self, val: &'vis Expr) -> Self::Result {
        let ty = &val.ty;
        match ty {
            ExprType::Path(path) => {
                let res = self.process_path(path, Namespace::Values);

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

            ExprType::Block(b) => self.visit_block(b),

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
                crate::try_visit!(self.visit_expr(cond), self.visit_block(if_block));

                for elsif in else_ifs {
                    self.visit_expr(&elsif.cond);
                    self.visit_block(&elsif.body);
                }

                crate::maybe_visit!(v: self, m: visit_block, otherwise);
            }

            any => todo!("to-do expression kinds: {any:#?}"),
        }
    }

    fn visit_ty(&mut self, val: &'vis Ty) -> Self::Result {
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
                let res = self.process_path(path, Namespace::Types);

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

    fn visit_block(&mut self, val: &'vis Block) -> Self::Result {
        self.path_forward();

        // TODO: find a better way
        if !self.arg_stack.is_empty() {
            let args: Vec<_> = self.arg_stack.drain(..).collect();
            for (sym, res) in args {
                self.current_scope_mut().add(Namespace::Values, sym, res);
            }
        }

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

        self.path_forward();
    }
}

pub fn resolve<'cx>(cx: &'cx Session<'cx>, universe: &Universe) {
    let mut first = FirstPass::new(cx);
    for thing in &universe.thingies {
        first.visit_thing(thing);
    }

    let mut second = SecondPass::new(first);
    for thing in &universe.thingies {
        second.visit_thing(thing);
    }
}

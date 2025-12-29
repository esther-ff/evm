use std::collections::HashMap;
use std::mem;
use std::ops::{Deref, DerefMut};

use crate::lowering_ast::Mappings;
use lychee_ast::Visibility;
use lychee_util::def::{DefId, DefMap, DefPath, DefType, DefVec, IntTy, PrimTy, Resolved};

#[allow(clippy::wildcard_imports)]
use lychee_ast::*;
use lychee_util::errors::{DiagEmitter, TheresError};
use lychee_util::id::IdxVec;
use lychee_util::symbols::SymbolId;
use lychee_util::visitor_common::VisitorResult as _;
use lychee_util::{maybe_visit, try_visit};

lychee_util::newtyped_index!(Scope, ScopeMap, ScopeVec, ScopeSlice);

#[derive(Debug, Clone, Copy)]
enum ResError {
    DefinedAlready {
        name: SymbolId,
    },

    NotFound {
        name: SymbolId,
        namespace: Namespace,
    },

    PrivateItem {
        name: SymbolId,
    },
}

impl TheresError for ResError {
    fn message(&self) -> std::borrow::Cow<'static, str> {
        match self {
            Self::PrivateItem { name } => {
                format!("`{name}` is private", name = name.get_interned())
            }
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum AirVisibility {
    UserPublic,
    Private,
    Ignored,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Namespace {
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

#[derive(Debug, Clone, Copy)]
struct ScopeItem {
    data: Resolved<AstId>,
    from_realm: DefId,
    vis: AirVisibility,
    name: SymbolId,
}

impl ScopeItem {
    pub fn new(
        data: Resolved<AstId>,
        from_realm: DefId,
        vis: AirVisibility,
        name: SymbolId,
    ) -> Self {
        Self {
            data,
            from_realm,
            vis,
            name,
        }
    }

    fn visible_from(&self, from_realm: DefId) -> bool {
        match self.vis {
            AirVisibility::Private => from_realm == self.from_realm,
            AirVisibility::UserPublic | AirVisibility::Ignored => true,
        }
    }
}

#[derive(Debug)]
struct ScopeData {
    values: HashMap<SymbolId, ScopeItem>,
    types: HashMap<SymbolId, ScopeItem>,
    anchor: Option<Scope>,
}

impl ScopeData {
    fn new(anchor: Option<Scope>) -> Self {
        Self {
            values: HashMap::new(),
            types: HashMap::new(),
            anchor,
        }
    }

    fn add(
        &mut self,
        ns: Namespace,
        sym: SymbolId,
        res: Resolved<AstId>,
        defined_in_def_id: DefId,
        vis: AirVisibility,
    ) {
        let data = ScopeItem::new(res, defined_in_def_id, vis, sym);
        match ns {
            Namespace::Types => self.types.insert(sym, data),
            Namespace::Values => self.values.insert(sym, data),
        };
    }

    /// This should only be used on local variables!
    fn local_add(&mut self, ns: Namespace, sym: SymbolId, res: Resolved<AstId>) {
        self.add(ns, sym, res, DefId::DUMMY, AirVisibility::Ignored);
    }

    fn get(&self, ns: Namespace, name: SymbolId) -> Option<&ScopeItem> {
        match ns {
            Namespace::Types => self.types.get(&name),
            Namespace::Values => self.values.get(&name),
        }
    }
}

#[derive(Debug)]
struct Scopes {
    storage: Vec<Scope>,
    cursor: usize,
}

impl Scopes {
    fn new(storage: Vec<Scope>) -> Self {
        Self { storage, cursor: 0 }
    }

    fn vec_mut(&mut self) -> &mut Vec<Scope> {
        &mut self.storage
    }

    fn next_scope(&mut self) -> Option<Scope> {
        if self.cursor >= self.storage.len() {
            return None;
        }

        let scope = self.storage[self.cursor];
        self.cursor += 1;
        Some(scope)
    }
}

struct FirstPass<'cx> {
    diag: &'cx DiagEmitter<'cx>,
    scopes: ScopeVec<ScopeData>,
    path: Scopes,

    current_scope: Scope,
    current_realm: Option<DefId>,
    current_vis: AirVisibility,

    did_defs: DefVec<(DefType, DefPath)>,
    realm_scopes: DefMap<(ScopeVec<ScopeData>, Scopes)>,

    ast_id_did: HashMap<AstId, DefId>,
    did_ast_id: HashMap<DefId, AstId>,

    thing_ast_id: Option<AstId>,

    defs: DefPath,
}

struct Guard<'a, T, F: FnMut(&mut T) + Copy> {
    this: &'a mut T,
    fun: F,
}

impl<'a, T, F: FnMut(&mut T) + Copy> Guard<'a, T, F> {
    pub fn new(this: &'a mut T, fun: F) -> Self {
        Self { fun, this }
    }
}

impl<'a, T, F: FnMut(&mut T) + Copy> Deref for Guard<'a, T, F> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.this
    }
}

impl<'a, T, F: FnMut(&mut T) + Copy> DerefMut for Guard<'a, T, F> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.this
    }
}

impl<'a, T, F: FnMut(&mut T) + Copy> Drop for Guard<'a, T, F> {
    fn drop(&mut self) {
        (self.fun)(self.this)
    }
}

impl<'cx> FirstPass<'cx> {
    fn define(&mut self, ast_id: AstId, ty: DefType, name: Name, ns: Namespace) -> DefId {
        let mut path = self.defs.clone();

        match ns {
            Namespace::Types => path.push_type_ns(name.interned),
            Namespace::Values => path.push_value_ns(name.interned),
        }
        let did = self.did_defs.push((ty, path));

        assert!(self.ast_id_did.insert(ast_id, did).is_none());
        assert!(self.did_ast_id.insert(did, ast_id).is_none());

        if self
            .path
            .storage
            .last()
            .is_some_and(|&id| id == Scope::ZERO)
            && self
                .scopes
                .get(Scope::ZERO)
                .is_some_and(|data| data.get(ns, name.interned).is_some())
            && name != Name::DUMMY
        {
            self.diag.emit_err(
                ResError::DefinedAlready {
                    name: name.interned,
                },
                name.span,
            );
        }

        did
    }

    fn add_to_scope(&mut self, ns: Namespace, sym: SymbolId, res: Resolved<AstId>) {
        self.scopes[self.current_scope].add(
            ns,
            sym,
            res,
            self.current_realm
                .expect("every ast starts with a top level realm"),
            self.current_vis,
        );
    }

    fn with_new_scope<F>(&mut self, work: F)
    where
        F: FnOnce(&mut Self),
    {
        let new = self.scopes.push(ScopeData::new(self.current_scope.into()));
        self.path.vec_mut().push(new);
        let old = mem::replace(&mut self.current_scope, new);

        work(self);

        self.path.vec_mut().push(old);
        self.current_scope = old;
    }

    fn in_realm<F>(&mut self, work: F, realm_did: DefId, name: SymbolId)
    where
        F: FnOnce(&mut Self),
    {
        self.defs.push_type_ns(name);
        self.realm_scopes.entry(realm_did).or_insert_with(|| {
            let mut data = ScopeVec::new();
            let path = data.push(ScopeData::new(None));

            (data, Scopes::new(vec![path]))
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
        self.defs.pop();
    }
}

impl<'vis> Visitor<'vis> for FirstPass<'_> {
    type Result = ();

    fn visit_thing(&mut self, val: &'vis Thing) -> Self::Result {
        let old = self.current_vis;
        eprintln!("old vis: {old:?}");
        let mut this = Guard::new(self, |this| {
            this.thing_ast_id.take();
            this.current_vis = old;
        });

        this.thing_ast_id = Some(val.id);
        this.current_vis = match val.vis {
            Visibility::None => AirVisibility::Private,
            Visibility::Public(..) => AirVisibility::UserPublic,
        };
        eprintln!("new vis: {:?}", this.current_vis);

        match &val.kind {
            ThingKind::Function(fndecl) => this.visit_fn_decl(fndecl),
            ThingKind::Realm(realm) => this.visit_realm(realm),
            ThingKind::Instance(instance) => this.visit_instance(instance),
            ThingKind::Bind(bind) => this.visit_bind(bind),
            ThingKind::NativeBlock(nat) => this.visit_native_block(nat),
        }
    }

    fn visit_realm(&mut self, val: &'vis Realm) -> Self::Result {
        let ast_id = self.thing_ast_id.unwrap_or(AstId::DUMMY);
        let id = self.define(ast_id, DefType::Realm, val.name, Namespace::Types);
        self.add_to_scope(
            Namespace::Types,
            val.name.interned,
            Resolved::Def(id, DefType::Realm),
        );

        let old = self.current_realm;
        let mut this = Guard::new(self, |this| this.current_realm = old);
        this.current_realm = Some(id);
        this.in_realm(
            |this| {
                for thing in &val.items {
                    this.visit_thing(thing);
                }
            },
            id,
            val.name.interned,
        );
    }

    fn visit_native_block(&mut self, val: &'vis NativeBlock) -> Self::Result {
        let _ = self.define(
            self.thing_ast_id.as_ref().copied().unwrap(),
            DefType::Realm,
            Name::DUMMY,
            Namespace::Types,
        );

        for ele in &val.item {
            self.visit_native_import(ele);
        }
    }

    fn visit_native_import(&mut self, val: &'vis NativeImport) -> Self::Result {
        let id = self.define(val.ast_id, DefType::NativeFn, val.name, Namespace::Values);
        self.add_to_scope(
            Namespace::Values,
            val.name.interned,
            Resolved::Def(id, DefType::Fun),
        );
    }

    fn visit_bind(&mut self, val: &'vis Bind) -> Self::Result {
        let id = self.define(
            self.thing_ast_id.as_ref().copied().unwrap(),
            DefType::Bind,
            Name::DUMMY,
            Namespace::Types,
        );

        self.add_to_scope(
            Namespace::Types,
            SymbolId::DUMMY,
            Resolved::Def(id, DefType::Realm),
        );

        self.defs.push_bind();
        self.with_new_scope(|this| {
            for item in &val.items {
                this.visit_bind_item(item);
            }
        });
        self.defs.pop();
    }

    #[track_caller]
    fn visit_bind_item(&mut self, val: &'vis BindItem) -> Self::Result {
        let old = self.thing_ast_id.replace(val.id);
        match val.kind {
            // BindItemKind::Const(ref stmt) => {
            //     let id = self.define(val.id, DefType::Const, stmt.name);

            //     self.add_to_scope(
            //         Namespace::Values,
            //         stmt.name.interned,
            //         Resolved::Def(id, DefType::Const),
            //     );
            // }
            BindItemKind::Fun(ref f) => self.visit_fn_decl(f),
        }
        self.thing_ast_id = old;
    }

    #[track_caller]
    fn visit_fn_decl(&mut self, val: &'vis FnDecl) -> Self::Result {
        eprintln!("visit_fn_decl -> name: {:?}", val.sig.name);
        let id = self.define(
            self.thing_ast_id.as_ref().copied().unwrap(),
            DefType::Fun,
            val.sig.name,
            Namespace::Values,
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
            Namespace::Types,
        );

        self.add_to_scope(
            Namespace::Types,
            val.name.interned,
            Resolved::Def(id, DefType::Instance),
        );

        let ctor_def_id = self.define(val.ctor_id, DefType::AdtCtor, val.name, Namespace::Values);

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
        let _ = self.define(val.id, DefType::Field, val.name, Namespace::Types);
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

    fn visit_expr(&mut self, val: &'vis Expr) -> Self::Result {
        if let ExprType::Lambda { body, .. } = &val.ty {
            self.defs.push_lambda();
            self.define(val.id, DefType::Lambda, Name::DUMMY, Namespace::Values);
            match body {
                LambdaBody::Block(bl) => self.visit_block(bl),
                LambdaBody::Expr(expr) => self.with_new_scope(|this| this.visit_expr(expr)),
            }
            self.defs.pop();
        }

        walk_expr(self, val);
    }
}

struct SecondPass<'res> {
    diag: &'res DiagEmitter<'res>,
    maps: Mappings,

    current_instance: Option<AstId>,
    current_bind_ty: Option<AstId>,
    current_bind_item: Option<AstId>,
    current_realm: Option<DefId>,

    path: Scopes,
    current_scope: Scope,
    scopes: ScopeVec<ScopeData>,

    realm_scopes: DefMap<(ScopeVec<ScopeData>, Scopes)>,

    current_item: AstId,

    current_loop_label: Option<AstId>,

    arg_stack: Vec<(SymbolId, Resolved<AstId>)>,
}

impl<'res> SecondPass<'res> {
    fn current_scope_mut(&mut self) -> &mut ScopeData {
        &mut self.scopes[self.current_scope]
    }

    fn make_local_binding(&mut self, name: Name, res: AstId) {
        let local = Resolved::Local(res);

        self.current_scope_mut()
            .local_add(Namespace::Values, name.interned, local);
    }

    fn get_name(&self, symbol: SymbolId, ns: Namespace) -> Option<ScopeItem> {
        self.get_name_from(self.current_scope, symbol, ns)
    }

    fn get_name_from(&self, scope: Scope, symbol: SymbolId, ns: Namespace) -> Option<ScopeItem> {
        let scope = &self.scopes[scope];
        if let Some(found) = scope.get(ns, symbol) {
            return Some(*found);
        }

        let mut cursor = scope.anchor;

        while let Some(scope_id) = cursor {
            match self.scopes[scope_id].get(ns, symbol) {
                None => cursor = self.scopes[scope_id].anchor,
                Some(found) => return Some(*found),
            }
        }

        if ns != Namespace::Types {
            return None;
        }

        PRIMITIVES
            .iter()
            .find(|(sym, _)| *sym == symbol && ns == Namespace::Types)
            .map(|(sym, res)| ScopeItem::new(*res, DefId::DUMMY, AirVisibility::Ignored, *sym))
    }

    fn private_lookup(
        &mut self,
        sym: SymbolId,
        ns: Namespace,
        state: Option<DefId>,
    ) -> Option<ScopeItem> {
        match state {
            None => self.get_name(sym, ns),
            Some(did) => self.lookup_in_realm(did, sym, ns),
        }
    }

    fn process_path(&mut self, path: &Path, ns: Namespace) -> Option<ScopeItem> {
        // if path.path.len() == 1 {
        //     let found = self.get_name(path.path[0].name.interned, ns);
        //     self.maps.map_to_resolved(path.path[0].id, found?.data);
        //     return found;
        // }

        let mut ret = None;
        let mut finish = None;

        /*
            None => we are in the default realm
            Some(def_id) => we are in another realm!
        */
        let mut current_or_diff_realm = None;
        let mut iter = path
            .path
            .iter()
            .map(|seg| (seg, seg.name.interned))
            .enumerate()
            .peekable();

        while let Some((ix, (segment, name))) = iter.next() {
            let namespace = if iter.peek().is_none() {
                ns
            } else {
                Namespace::Types
            };

            let Some(res) = self.private_lookup(name, namespace, current_or_diff_realm) else {
                self.maps.map_to_resolved(segment.id, Resolved::Err);
                self.emit_not_found(path, ix, namespace);
                break;
            };

            if !res.visible_from(self.current_realm.unwrap()) {
                self.diag
                    .emit_err(ResError::PrivateItem { name: res.name }, segment.span);
            }

            self.maps.map_to_resolved(segment.id, res.data);

            match res.data {
                Resolved::Def(did, DefType::Realm) => current_or_diff_realm = Some(did),

                Resolved::Err => {
                    self.diag.emit_err(
                        ResError::NotFound {
                            name,
                            namespace: Namespace::Types,
                        },
                        segment.span,
                    );

                    finish = Some(ix);
                    break;
                }

                _ => {
                    ret = Some(res);
                    finish = Some(ix);
                    break;
                }
            }
        }

        if let Some(finish) = finish {
            for seg in &path.path[finish + 1..] {
                self.maps.map_to_resolved(seg.id, Resolved::Err);
            }
        }

        ret
    }

    fn lookup_in_realm(
        &mut self,
        realm_did: DefId,
        name: SymbolId,
        ns: Namespace,
    ) -> Option<ScopeItem> {
        let mut ret = None;
        self.switch_scope_paths(realm_did, |this| {
            ret = this.get_name_from(Scope::ZERO, name, ns);
        });

        ret
    }

    #[track_caller]
    fn path_forward(&mut self) {
        self.current_scope = self.path.next_scope().expect("went beyond the path");
    }

    fn current_item(&self) -> AstId {
        self.current_item
    }

    #[track_caller]
    fn get_def_id(&self, ast_id: AstId) -> DefId {
        self.maps.def_id_of(ast_id)
    }

    fn switch_scope_paths<F>(&mut self, realm_did: DefId, work: F)
    where
        F: FnOnce(&mut Self),
    {
        let (realm_scope_data, realm_path) = self
            .realm_scopes
            .get_mut(&realm_did)
            .expect("realm defid was invalid");
        mem::swap(&mut self.scopes, realm_scope_data);
        mem::swap(&mut self.path, realm_path);

        work(self);

        let (realm_scope_data, realm_path) = self
            .realm_scopes
            .get_mut(&realm_did)
            .expect("realm defid was invalid");
        mem::swap(&mut self.scopes, realm_scope_data);
        mem::swap(&mut self.path, realm_path);
    }

    fn emit_not_found(&self, path: &Path, idx: usize, namespace: Namespace) {
        let name = path.path[idx].name.interned;
        let span = path.path[idx].span;

        self.diag
            .emit_err(ResError::NotFound { name, namespace }, span);
    }
}

impl<'vis> Visitor<'vis> for SecondPass<'_> {
    type Result = ();

    fn visit_thing(&mut self, val: &'vis Thing) -> Self::Result {
        let old = self.current_item;
        self.current_item = val.id;
        match &val.kind {
            ThingKind::Function(f) => self.visit_fn_decl(f),
            ThingKind::Realm(r) => self.visit_realm(r),
            ThingKind::Instance(i) => self.visit_instance(i),
            ThingKind::Bind(a) => self.visit_bind(a),
            ThingKind::NativeBlock(nat) => self.visit_native_block(nat),
        }

        self.current_item = old;
    }

    fn visit_native_import(&mut self, val: &'vis NativeImport) -> Self::Result {
        match &val.kind {
            NativeImportKind::Fun { args, ret_ty } => {
                for arg in args {
                    self.visit_ty(&arg.ty);
                }

                self.visit_ty(ret_ty);
            }
        }

        let def_id = self.get_def_id(val.ast_id);
        self.current_scope_mut().local_add(
            Namespace::Values,
            val.name.interned,
            Resolved::Def(def_id, DefType::Fun),
        );
    }

    fn visit_realm(&mut self, val: &'vis Realm) -> Self::Result {
        let Realm {
            items,
            span: _,
            name: _,
        } = val;

        let current_item = self.current_item();
        let realm_did = self.get_def_id(current_item);
        let old = self.current_realm.replace(realm_did);

        self.switch_scope_paths(realm_did, |this| {
            for thing in items {
                this.visit_thing(thing);
            }
        });

        self.current_realm = old;
    }

    fn visit_bind(&mut self, bind: &'vis Bind) -> Self::Result {
        self.current_bind_ty = Some(bind.victim.id);
        self.visit_ty(&bind.victim);

        if let TyKind::Path(path) = &bind.victim.kind {
            let _resolved = self.process_path(path, Namespace::Types);

            // if let Resolved::Def(def_id, DefType::Instance) = resolved {
            //     self.maps
            //         .insert_instance_to_bind(def_id, self.current_item());
            // }
        }

        self.path_forward();
        for item in &bind.items {
            self.visit_bind_item(item);
        }
        self.path_forward();

        self.current_bind_ty.take();
    }

    fn visit_bind_item(&mut self, val: &'vis BindItem) -> Self::Result {
        self.current_bind_item = Some(val.id);

        match val.kind {
            // BindItemKind::Const(ref var_stmt) => {
            //     let def_id = self.get_def_id(val.id);
            //     self.current_scope_mut().add(
            //         Namespace::Values,
            //         var_stmt.name.interned,
            //         Resolved::Def(def_id, DefType::Const),
            //     );
            //     self.visit_var_stmt(var_stmt);
            // }
            BindItemKind::Fun(ref f) => self.visit_fn_decl(f),
        }

        self.current_bind_item.take();
    }

    fn visit_fn_decl(&mut self, val: &'vis FnDecl) -> Self::Result {
        let FnSig {
            name: _,
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

        let _def_id = self.get_def_id(thing_ast_id);

        // self.current_scope_mut().local_add(
        //     Namespace::Values,
        //     name.interned,
        //     Resolved::Def(def_id, DefType::Fun),
        // );

        self.visit_block(&val.block);
    }

    fn visit_instance(&mut self, val: &'vis Instance) -> Self::Result {
        let _instance_def_id = self.get_def_id(self.current_item());

        self.current_instance.replace(val.id);

        // Redundant?
        // self.current_scope_mut().add(
        //     Namespace::Types,
        //     val.name.interned,
        //     Resolved::Def(instance_def_id, DefType::Instance),
        // );

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
                init,
                ty,
                id,
            }) => {
                maybe_visit!(v:self, m:visit_ty, ty);
                maybe_visit!(v:self, m:visit_expr, init);
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
            ExprType::Return { ret } => maybe_visit!(v: self, m: visit_expr, ret),
            ExprType::Path(path) => {
                let res = self
                    .process_path(path, Namespace::Values)
                    .map_or(Resolved::Err, |x| x.data);

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

            ExprType::List(exprs) => {
                for e in exprs {
                    self.visit_expr(e);
                }
            }

            ExprType::Assign {
                lvalue,
                rvalue,
                mode: _,
            } => {
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

            ExprType::For {
                iterable,
                pat: _,
                body,
            } => {
                try_visit!(self.visit_expr(iterable), self.visit_block(body));

                todo!("patterns?");
            }

            ExprType::Loop { body, label } => {
                if label.name != Name::DUMMY {
                    self.current_scope_mut().local_add(
                        Namespace::Values,
                        label.name.interned,
                        Resolved::Label {
                            id: label.id,
                            was_error: false,
                        },
                    );
                }

                self.current_loop_label.replace(label.id);
                self.visit_block(body);
                self.current_loop_label.take();
            }

            ExprType::While {
                cond,
                body,
                label: _,
            }
            | ExprType::Until {
                cond,
                body,
                label: _,
            } => {
                self.visit_expr(cond);
                self.visit_block(body);
            }

            ExprType::FieldAccess { source, field: _ } => self.visit_expr(source),

            ExprType::Lambda { args, body } => {
                for arg in args {
                    self.visit_ty(&arg.ty);
                }

                self.arg_stack.extend(
                    args.iter()
                        .map(|arg| (arg.ident.interned, Resolved::Local(arg.id))),
                );

                // dbg!(&self.arg_stack);

                match body {
                    LambdaBody::Block(bl) => self.visit_block(bl),
                    LambdaBody::Expr(expr) => {
                        self.path_forward();

                        // TODO: find a better way
                        if !self.arg_stack.is_empty() {
                            let args: Vec<_> = self.arg_stack.drain(..).collect();
                            for (sym, res) in args {
                                self.current_scope_mut()
                                    .local_add(Namespace::Values, sym, res);
                            }
                        }

                        self.visit_expr(expr);
                        self.path_forward();
                    }
                }
            }

            ExprType::Constant(..) | ExprType::Err => (),

            ExprType::Break { label } => {
                if let Some(label) = *label {
                    let Some(res) = self.get_name(label, Namespace::Values) else {
                        self.maps.map_to_resolved(val.id, Resolved::Err);
                        return;
                    };

                    if let Resolved::Label { .. } = res.data {
                        self.maps.map_to_resolved(val.id, res.data);
                    } else {
                        todo!("not-label in resolution for a break")
                    }
                } else {
                    self.maps.map_to_resolved(
                        val.id,
                        Resolved::Label {
                            id: AstId::DUMMY,
                            was_error: true,
                        },
                    );
                };
            }

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
                try_visit!(self.visit_expr(cond), self.visit_block(if_block));

                for elsif in else_ifs {
                    self.visit_expr(&elsif.cond);
                    self.visit_block(&elsif.body);
                }

                maybe_visit!(v: self, m: visit_block, otherwise);
            }
        }
    }

    fn visit_ty(&mut self, val: &'vis Ty) -> Self::Result {
        match &val.kind {
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
                let res = self
                    .process_path(path, Namespace::Types)
                    .map_or(Resolved::Err, |x| x.data);

                self.maps.map_to_resolved(val.id, res);
                self.maps.map_to_resolved(path.id, res);
            }

            TyKind::MethodSelf => {
                // just not to fail silenty
                let Some(..) = self.current_bind_item else {
                    unreachable!("self ty outside bind!");
                };
            }

            TyKind::Err | TyKind::Infer => (), // explicit matching in case i add smth new
        }
    }

    fn visit_block(&mut self, val: &'vis Block) -> Self::Result {
        self.path_forward();

        // TODO: find a better way
        if !self.arg_stack.is_empty() {
            let args: Vec<_> = self.arg_stack.drain(..).collect();
            for (sym, res) in args {
                self.current_scope_mut()
                    .local_add(Namespace::Values, sym, res);
            }
        }

        let Block {
            stmts,
            span: _,
            id: _,
            expr,
            label: _,
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
                    init,
                    ty,
                    id,
                }) => {
                    maybe_visit!(v:self, m:visit_ty, ty);
                    maybe_visit!(v:self, m:visit_expr, init);
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

pub fn resolve<'cx>(diag: &'cx DiagEmitter<'cx>, universe: &Universe) -> Mappings {
    let mut scopes = IdxVec::new();
    let current_scope = scopes.push(ScopeData::new(None));
    let mut first = FirstPass {
        diag,
        // First insert will be the realm
        // which will start at DefId#0
        current_realm: Some(DefId::ZERO),
        thing_ast_id: None,
        current_vis: AirVisibility::Private,
        path: Scopes::new(vec![current_scope]),
        scopes,
        current_scope,
        did_defs: IdxVec::new(),
        realm_scopes: HashMap::default(),
        did_ast_id: HashMap::default(),
        ast_id_did: HashMap::default(),
        defs: DefPath::new(),
    };

    first.visit_realm(&universe.realm);
    let FirstPass {
        diag,
        current_realm: _,
        current_vis: _,
        scopes,
        mut path,
        current_scope,
        did_defs,
        mut realm_scopes,
        ast_id_did,
        did_ast_id: _,
        thing_ast_id: _,
        defs: _,
    } = first;

    // Get rid of first scope OK!
    //
    // Why?
    // Because we conceptually start in the first scope (#0)
    // and without this we skip a scope!
    //
    // Which fucking breaks everything!
    //
    // Una bandiera tutta nera!
    //
    // This is a fucking horrible implementation
    // because of the O(n) reallocation of the vector
    //
    // Please! Change this somehow!
    path.storage.remove(0);
    for path in realm_scopes.values_mut() {
        path.1.storage.remove(0);
    }

    let mut second = SecondPass {
        diag,
        current_realm: None,
        maps: Mappings::new(ast_id_did, did_defs),
        current_instance: None,
        current_bind_ty: None,
        current_bind_item: None,
        scopes,
        arg_stack: vec![],
        current_item: AstId::DUMMY,
        realm_scopes,
        path,
        current_scope,
        current_loop_label: None,
    };

    second.visit_realm(&universe.realm);
    second.maps
}

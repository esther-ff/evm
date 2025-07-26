use std::collections::HashMap;

use crate::{
    ast::{
        self, Block, FnDecl, Instance, Stmt, StmtKind, ThingKind, VarMode, VariableStmt, Visitor,
        VisitorResult,
    },
    ctx::Context,
    hir::def::{DefId, Resolved},
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

pub struct Scope {
    parent: Option<ScopeId>,
    bindings: HashMap<SymbolId, Resolved>,
}

pub struct Pass1Resolver<'a> {
    cx: &'a mut Context,
    definitions: HashMap<SymbolId, DefId>,
}

impl<'a> Visitor<'a> for Pass1Resolver<'a> {
    type Result = ();

    fn visit_interface(&mut self, val: &'a crate::ast::Interface) -> Self::Result {
        todo!("interfaces: resolving")
    }

    fn visit_fn_decl(&mut self, val: &'a crate::ast::FnDecl) -> Self::Result {
        let id = self.cx.defs.insert_fn(val);
        self.definitions.insert(val.sig.name.interned, id);
    }

    fn visit_instance(&mut self, val: &'a Instance) -> Self::Result {
        let id = self.cx.defs.insert_instance(val);
        self.definitions.insert(val.name.interned, id);
    }
}

pub struct InnerResolver<'a> {
    cx: &'a mut Context,
    scopes: HashMap<ScopeId, Scope>,
    scope_id_gen: u32,
    current_scope: Option<ScopeId>,
    definitions: HashMap<SymbolId, DefId>,

    // context
    current_fn: Option<DefId>,
    current_instance: Option<DefId>,
    current_interface: Option<DefId>,
}

impl<'a> InnerResolver<'a> {
    pub fn new() -> Self {
        todo!()
    }

    pub fn new_scope(&mut self) -> Option<ScopeId> {
        let new_id = self.scope_id_gen;

        self.scope_id_gen += 1;

        let new = Scope {
            parent: self.current_scope,
            bindings: HashMap::new(),
        };

        self.scopes.insert(ScopeId(new_id), new);

        self.current_scope.replace(ScopeId(new_id))
    }

    pub fn with_new_scope<'b, F, R>(&'b mut self, f: F)
    where
        F: FnOnce(&mut InnerResolver) -> R,
        'a: 'b,
    {
        let old_scope_id = self.new_scope();
        f(self);
        self.current_scope = old_scope_id;
    }
}

impl<'a, 'b> Visitor<'a> for InnerResolver<'b>
where
    'b: 'a,
{
    type Result = ();

    fn visit_interface(&mut self, val: &'a crate::ast::Interface) -> Self::Result {
        todo!("interfaces: resolving")
    }

    fn visit_fn_decl(&mut self, val: &'a crate::ast::FnDecl) -> Self::Result {
        let FnDecl {
            sig,
            block,
            span: _,
            id: _,
        } = val;

        let old = self.current_fn;

        let id = self
            .definitions
            .get(&sig.name.interned)
            .copied()
            .expect("function wasn't registered");

        self.current_fn.replace(id);

        self.with_new_scope(|visitor| visitor.visit_block(block));

        self.current_fn = old;
    }

    fn visit_instance(&mut self, val: &'a Instance) -> Self::Result {
        todo!()
    }

    fn visit_stmt(&mut self, val: &'a Stmt) -> Self::Result {
        let Stmt {
            kind,
            span: _,
            id: _,
        } = val;
        match kind {
            StmtKind::Block(block) => {
                self.with_new_scope(|v| v.visit_block(block));
            }

            StmtKind::LocalVar(VariableStmt {
                mode,
                name,
                initializer,
                ty,
                id: _,
            }) => {
                todo!();
            }

            StmtKind::Expr(expr) => {
                self.visit_expr(expr);
            }

            StmtKind::Thing(def) => self.visit_thing(def),
        }
    }

    fn visit_expr(&mut self, val: &'a ast::Expr) -> Self::Result {
        todo!()
    }
}

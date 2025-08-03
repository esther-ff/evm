use crate::{
    ast::{
        AstError, AstErrorKind, Block, Instance, Stmt, StmtKind, ThingKind, VarMode, Visitor,
        VisitorResult,
    },
    session::Session,
};

pub struct Validator<'a> {
    errors: Vec<AstError>,
    sess: &'a Session<'a>,
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
                            instance: name.interned.get_interned().to_string(),
                            span_of_const: local.name.span,
                        },
                        local.name.span,
                    ))
                }

                StmtKind::Thing(def) if !matches!(def.kind, ThingKind::Function(..)) => {
                    self.errors.push(AstError::new(
                        AstErrorKind::OverfilledInstanceBlock {
                            instance: name.interned.get_interned().to_string(),
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

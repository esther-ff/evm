use std::{io, path::Path};

use crate::{
    ast::{Realm, Visitor},
    errors::Errors,
    hir::{LateResolver, ThingDefResolver, Validator, lowering_ast::AstLowerer},
    lexer::{Lexemes, Lexer},
    parser::Parser,
    session::{DIAG_CTXT, Session},
    sources::{FileManager, SourceFile, Sources},
};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Compilation {
    Error,
    Ok,
}

pub struct Compiler<T: FileManager> {
    sources: Sources<T>,

    state: Compilation,
}

impl<T: FileManager> Compiler<T> {
    pub fn new(manager: T) -> Self {
        Self {
            sources: Sources::new(manager),
            state: Compilation::Ok,
        }
    }

    pub fn start<A>(&mut self, main: A)
    where
        A: AsRef<Path>,
    {
        let src = self
            .sources
            .open(main.as_ref())
            .expect("failed to open main file");

        let mut session = Session::new();
        let lexemes = self.lex(&src);
        let ast = self.parse_to_ast(lexemes);

        session.enter(|session| {
            let mut v = Validator::new(session);
            v.visit_realm(&ast);

            let mut first_pass = ThingDefResolver::new(&ast);
            for decl in &ast.items {
                first_pass.visit_thing(decl)
            }

            let mut inner = LateResolver::new(first_pass);
            for decl in &ast.items {
                inner.visit_thing(decl)
            }

            for (id, res) in inner.res_map().iter() {
                println!("ast id of res: {id:?} -> resolved as: {res:?}",);
            }

            let mappings = inner.into_mappings();

            let ast_lowerer = AstLowerer::new(mappings, session);

            self.emit_errors(&src).unwrap();
        });
    }

    fn lex(&mut self, src: &SourceFile) -> Lexemes {
        let lexemes = {
            let lexer = Lexer::new(src.data(), src.source_id());
            lexer.lex()
        };

        if DIAG_CTXT.lock().unwrap().errored() {
            self.state = Compilation::Error;
        };

        lexemes
    }

    fn parse_to_ast(&mut self, lexemes: Lexemes) -> Realm {
        let decls = Parser::new(lexemes).parse();

        if DIAG_CTXT.lock().unwrap().errored() {
            self.state = Compilation::Error;
        }

        if self.state == Compilation::Ok {
            dbg!(&decls);
        }

        decls
    }

    pub fn emit_errors(&mut self, src: &SourceFile) -> io::Result<()> {
        let mut stdout = io::stdout();

        let diag = DIAG_CTXT.lock().unwrap();
        let mut errs = Errors::new(diag.lex_errors(), &mut stdout);

        errs.print_all(src)?;
        let mut errs = Errors::new(diag.parse_errors(), &mut stdout);

        errs.print_all(src)?;

        Ok(())
    }
}

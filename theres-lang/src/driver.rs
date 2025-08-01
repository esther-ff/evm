use std::{io, path::Path};

use crate::{
    ast::{Realm, Visitor},
    errors::Errors,
    hir::validate_ast::{LateResolver, ThingDefResolver},
    lexer::{LexError, Lexemes, Lexer},
    parser::{ParseError, Parser},
    session::Session,
    sources::{FileManager, SourceFile, Sources},
};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Compilation {
    Error,
    Ok,
}

pub struct Compiler<T: FileManager> {
    session: Session,
    sources: Sources<T>,

    lex_errors: Vec<LexError>,
    parse_errors: Vec<ParseError>,

    state: Compilation,
}

impl<T: FileManager> Compiler<T> {
    pub fn new(manager: T) -> Self {
        Self {
            sources: Sources::new(manager),
            parse_errors: Vec::new(),
            lex_errors: Vec::new(),
            session: Session::new(),
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

        let lexemes = self.lex(&src);
        let ast = self.parse_to_ast(lexemes);

        self.resolvers(&ast);

        self.emit_errors(&src).unwrap();
    }

    fn lex(&mut self, src: &SourceFile) -> Lexemes {
        let lexemes =
            Lexer::new(src.data(), src.source_id(), &mut self.lex_errors).lex(&mut self.session);

        if !self.lex_errors.is_empty() {
            self.state = Compilation::Error;
        };

        lexemes
    }

    fn parse_to_ast(&mut self, lexemes: Lexemes) -> Realm {
        let decls = Parser::new(lexemes, &mut self.parse_errors).parse();

        if !self.parse_errors.is_empty() {
            self.state = Compilation::Error;
        }

        dbg!(&self.parse_errors);

        if self.state == Compilation::Ok {
            dbg!(&decls);
        }

        decls
    }

    fn resolvers(&mut self, ast: &Realm) {
        let mut first_pass = ThingDefResolver::new(ast);
        for decl in &ast.items {
            first_pass.visit_thing(decl)
        }
        let mut inner = LateResolver::new(first_pass, &self.session);
        for decl in &ast.items {
            inner.visit_thing(decl)
        }

        #[cfg(debug_assertions)]
        {
            for (id, res) in inner.res_map().iter() {
                println!("ast id of res: {id:?} -> resolved as: {res:?}",);
            }

            self.session
                .debug_symbol_id_string()
                .iter()
                .for_each(|(name, id)| {
                    println!("{id:?} -> {name:?}");
                })
        }
    }

    pub fn emit_errors(&mut self, src: &SourceFile) -> io::Result<()> {
        let mut stdout = io::stdout();
        let mut errs = Errors::new(&self.lex_errors, &mut stdout);

        errs.print_all(src)?;
        let mut errs = Errors::new(&self.parse_errors, &mut stdout);

        errs.print_all(src)?;

        Ok(())
    }
}

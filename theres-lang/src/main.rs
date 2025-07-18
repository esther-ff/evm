mod arena;
mod ast;
mod lexer;
mod parser;
mod session;

use std::{
    fs::File,
    io::{self, Read, Stdout, Write, stdin, stdout},
};

use crate::{lexer::Lexer, parser::Parser, session::Session};
fn main() -> io::Result<()> {
    println!("welcome to the queen evm complier!");
    println!("puppygirl :3");
    let stdout = stdout();

    let mut args = std::env::args().skip(1);

    match args.next() {
        None => {
            println!("error: didn't provide the action");
            println!("current actions are: `repl` or `parse`")
        }

        Some(txt) => match txt.as_str() {
            "repl" => repl(stdout)?,
            "parse" => {
                let mut session = Session::new();
                let Some(filepath) = args.next() else {
                    println!("error: no file path provided for parsing :(");
                    return Ok(());
                };

                let mut data = File::open(filepath)?;
                let mut buf = Vec::new();
                data.read_to_end(&mut buf)?;

                let parser = match parse(&buf, &mut session) {
                    Ok(parser) => parser,

                    Err(lexer) => {
                        println!("error: lexing failed");
                        print_lines(lexer.errors());

                        return Ok(());
                    }
                };

                if parser.has_errored() {
                    println!("error: parsing failed!");
                    let errors = parser
                        .errors()
                        .iter()
                        .map(|err| {
                            let span = err.token_span;
                            let str = buf
                                .get(span.start()..span.end())
                                .map(core::str::from_utf8)
                                .and_then(Result::ok)
                                .map(ToOwned::to_owned);

                            (*err, str)
                        })
                        .collect::<Vec<_>>();
                    print_lines(&errors);

                    return Ok(());
                }

                println!("parsed: \n{:#?}", parser.decls())
            }

            any => {
                println!("error: invalid mode chosen: {any}");
                return Ok(());
            }
        },
    }

    Ok(())
}

fn repl(mut stdout: Stdout) -> Result<(), io::Error> {
    let mut buf = String::new();
    loop {
        let mut session = Session::new();
        stdout.write_all(b"repl> ")?;
        stdout.flush()?;

        let _ = stdin().read_line(&mut buf)?;

        let mut lexer = Lexer::new(buf.clone());
        lexer.lex(&mut session);

        if lexer.errored() {
            writeln!(stdout, "lex errors: \n {:?}", lexer.errors())?;
        } else {
            writeln!(stdout, "Lexed!")?;
            writeln!(stdout, "lexemes: \n {:#?}", lexer.tokens())?;
        };

        let mut parser = Parser::new(lexer);
        parser.parse();

        dbg!(parser.errors());
        if parser.has_errored() {
            writeln!(stdout, "parse errors: \n {:#?}", parser.errors())?;
        } else {
            writeln!(stdout, "Parsed!")?;
            // writeln!(stdout, "tree: \n {:#?}", expr.unwrap())?;
            writeln!(stdout, "definitions: {:#?}", parser.decls())?;
        }

        stdout.flush()?;
        buf.clear();
    }
}

fn parse(data: &[u8], session: &mut Session) -> Result<Parser, Lexer> {
    let mut lexer = Lexer::new(data.to_vec());
    lexer.lex(session);

    if lexer.errored() {
        return Err(lexer);
    } else {
        print_lines(lexer.tokens());
    }

    let mut parser = Parser::new(lexer);

    parser.parse();

    Ok(parser)
}

fn print_lines<T: std::fmt::Debug>(items: &[T]) {
    for item in items {
        println!("{item:?}")
    }
}

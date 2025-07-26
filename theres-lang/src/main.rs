#![warn(clippy::all)]

mod arena;
mod ast;
mod ctx;
mod driver;
mod errors;
mod hir;
mod lexer;
mod parser;
mod session;
mod sources;

use std::{
    fs::File,
    io::{self, Read},
};

use crate::{driver::Compiler, sources::FileManager};

fn main() -> io::Result<()> {
    println!("welcome to the theres evm compiler!");
    println!("puppygirl :3");

    let mut args = std::env::args().skip(1);

    match args.next() {
        None => {
            println!("error: didn't provide the action");
            println!("current actions are: `repl` or `parse`")
        }

        Some(txt) => match txt.as_str() {
            "parse" => {
                let Some(filepath) = args.next() else {
                    println!("error: no file path provided for parsing :(");
                    return Ok(());
                };

                parse(filepath)
            }

            any => {
                println!("error: invalid mode chosen: {any}");
                return Ok(());
            }
        },
    }

    Ok(())
}

pub struct FileOpener;

impl FileManager for FileOpener {
    fn open_file(&mut self, path: &std::path::Path) -> io::Result<Vec<u8>> {
        let mut file = File::open(path)?;
        let mut vec = Vec::new();

        let _ = file.read_to_end(&mut vec)?;

        Ok(vec)
    }
}
fn parse(path: String) {
    let mut compiler = Compiler::new(FileOpener);

    compiler.start(&path);
}

fn print_lines<T: std::fmt::Debug>(items: &[T]) {
    for item in items {
        println!("{item:?}")
    }
}

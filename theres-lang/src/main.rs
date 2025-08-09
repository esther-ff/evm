#![warn(clippy::pedantic)]
#![warn(clippy::style)]
#![warn(clippy::complexity)]
#![warn(clippy::perf)]
#![warn(clippy::suspicious)]
#![warn(clippy::correctness)]

mod arena;
mod ast;
mod ast_pretty_printer;
mod driver;
mod errors;
mod hir;
mod id;
mod lexer;
mod parser;
mod session;
mod sources;
use std::{
    fs::File,
    io::{self, Read as _},
};

use crate::{driver::Compiler, sources::FileManager};

fn main() {
    println!("welcome to the theres compiler!");
    println!("puppygirl :3");

    let mut args = std::env::args().skip(1);

    match args.next() {
        None => {
            println!("error: didn't provide the action");
            println!("current actions are: `parse`");
        }

        Some(txt) => match txt.as_str() {
            "parse" => {
                let Some(filepath) = args.next() else {
                    println!("error: no file path provided for parsing :(");
                    return;
                };

                parse(&filepath);
            }

            any => {
                println!("error: invalid mode chosen: {any}");
            }
        },
    }
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
fn parse(path: &str) {
    let mut compiler = Compiler::new(FileOpener);

    compiler.start(path);
}

#![feature(allocator_api)]
#![feature(ptr_metadata)]
#![feature(iter_intersperse)]
#![warn(clippy::style)]
#![warn(clippy::complexity)]
#![warn(clippy::perf)]
#![warn(clippy::suspicious)]
#![warn(clippy::correctness)]
#![warn(clippy::pedantic)]
#![allow(dead_code)]

mod air;
mod arena;
mod ast;
mod driver;
mod eair;
mod errors;
mod id;
mod lexer;
mod parser;
mod pill;
mod pooled;
mod session;
mod sources;
mod span;
mod symbols;
mod types;
mod visitor_common;

use std::fs::File;
use std::io::{self, Read as _};
use std::path::{Path, PathBuf};
use std::str::FromStr;

use sap::Argument;

use crate::driver::{Compiler, Flags, HirDump};
use crate::sources::FileManager;

fn main() -> sap::Result<()> {
    println!("woof :3");
    let (flags, path) = opts()?;

    parse(&path, flags, FileOpener);

    Ok(())
}

fn opts() -> sap::Result<(Flags, PathBuf)> {
    let mut args = sap::Parser::from_env()?;

    let mut path = None;

    let mut flags = Flags {
        dump_hir: HirDump::None,
        dump_ast: false,
        dump_types: false,
        log_level: log::Level::Error,
    };

    while let Some(cmd_arg) = args.forward()? {
        match cmd_arg {
            Argument::Long("logging") => {
                let Some(value) = args.value() else {
                    flags.log_level = log::Level::Debug;
                    continue;
                };

                flags.log_level = match value.as_str() {
                    "debug" => log::Level::Debug,
                    "trace" => log::Level::Trace,
                    "warn" => log::Level::Warn,
                    "info" => log::Level::Info,
                    "error" => log::Level::Error,

                    _ => {
                        let err = sap::ParsingError::UnexpectedArg {
                            offender: String::from("logging"),
                            value: Some(value),
                            format: "",
                            prefix: "--",
                        };

                        return Err(err);
                    }
                }
            }
            Argument::Long("dump") => {
                let Some(value) = args.value() else {
                    return Err(sap::ParsingError::InvalidOption {
                        reason: "provided `--dump` with no arguments",
                        offender: None,
                    });
                };

                let options = value.split(',');

                for dump_opt in options {
                    match dump_opt {
                        "air_items" => flags.dump_hir = HirDump::OnlyItems,
                        "air" => flags.dump_hir = HirDump::All,
                        "ast" => flags.dump_ast = true,
                        "types" => flags.dump_types = true,

                        any => {
                            let err = sap::ParsingError::UnexpectedArg {
                                offender: String::from("dump"),
                                value: Some(any.into()),
                                format: "",
                                prefix: "--",
                            };

                            return Err(err);
                        }
                    }
                }
            }

            Argument::Long("file") => {
                let Some(value) = args.value() else {
                    return Err(sap::ParsingError::InvalidOption {
                        reason: "provided `--file` with no arguments",
                        offender: None,
                    });
                };

                path = Some(value);
            }

            any => {
                return Err(any.into_error(None));
            }
        }
    }

    Ok((
        flags,
        path.map_or(
            PathBuf::from_str("main.th").expect("infallible"),
            Into::into,
        ),
    ))
}

fn parse(path: &Path, flags: Flags, opener: impl FileManager + 'static) {
    let mut compiler = Compiler::new(opener, flags);

    compiler.start(path);
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

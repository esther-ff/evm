//! The Puppygirl Intermediate Lowering Language
pub mod access;
pub mod body;
mod cfg;
pub(crate) mod dataflow;
pub mod op;
pub mod scalar;
pub mod visitor;

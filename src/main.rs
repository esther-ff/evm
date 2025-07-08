// #![warn(clippy::pedantic)]
#![allow(dead_code)]

mod bytecode;
mod call_stack;
mod gc;
mod globals;
mod instruction;
mod objects;
mod stack;
mod vm;

fn main() -> vm::Result<()> {
    let mut bytecode: Vec<u8> = vec![101, 118, 109, 32, 58, 51];
    let fn_instructions: &[u8] = &[255];

    bytecode::testing::create_fn_bytecode(&mut bytecode, "main", fn_instructions, 0);

    let mut vm = vm::Vm::new(&bytecode)?;

    vm.interpret_all()?;
    Ok(())
}

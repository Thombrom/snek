#![feature(array_windows)]

use interpreter::{builtin_frame, evaluate, Frame};
use parser::parser;

mod error;
mod interpreter;
mod parser;

#[cfg(test)]
mod test_utils;

fn main() -> anyhow::Result<()> {
    let frame = Frame::new(builtin_frame());
    let program = vec![
        "(define (spam) (* eggs 3))",
        "(spam)",
        "(define eggs 20)",
        "(spam)",
    ].into_iter().map(|line| parser(line)).collect::<Result<Vec<_>, _>>()?;

    for (lineno, line) in program.iter().enumerate() {
        println!("{}: {:?}", lineno, evaluate(line, &frame));
    }

    Ok(())
}

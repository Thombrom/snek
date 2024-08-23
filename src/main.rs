#![feature(array_windows)]

use interpreter::{builtin_frame, EvaluationContext, Frame};
use parser::parser;

mod error;
mod interpreter;
mod parser;

#[cfg(test)]
mod test_utils;

fn main() -> anyhow::Result<()> {
    let program = vec![
        "(define (spam) (* eggs 3))",
        "(spam)",
        "(define eggs 20)",
        "(spam)",
    ];

    let mut context = EvaluationContext::new();
    for (lineno, line) in program.into_iter().enumerate() {
        println!("{}: {:?}", lineno, context.evaluate_str(line));
    }

    Ok(())
}

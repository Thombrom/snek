#![feature(array_windows)]

use interpreter::{builtin_frame, Frame, EvaluationContext};
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
    ].into_iter().map(|line| parser(line)).collect::<Result<Vec<_>, _>>()?;

    let mut context = EvaluationContext::new();
    for (lineno, line) in program.iter().enumerate() {
        println!("{}: {:?}", lineno, context.evaluate_sexp(line));
    }

    Ok(())
}

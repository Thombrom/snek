
use snek::{parse, BorrowedEvaluationContext, Sexp, SnekError};

fn main() {
    let sexps = vec![
        "(define (spam) (* eggs 3))",
        "(spam)",
        "(define eggs 20)",
        "(spam)",
    ].into_iter()
        .map(|line| parse(line).map(|sexp| (line, sexp)))
        .collect::<Result<Vec<(&str, Sexp)>, SnekError>>()
        .unwrap();

    let mut context = BorrowedEvaluationContext::new();
    for (source, sexp) in &sexps {
        match context.evaluate_sexp(sexp) {
            Ok(value) => println!("{}: {}", source, value),
            Err(err) => println!("{}: {}", source, err)
        }
    }
}
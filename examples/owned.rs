use snek::EvaluationContext;

fn main() {
    let program = vec![
        "(define (spam) (* eggs 3))",
        "(spam)",
        "(define eggs 20)",
        "(spam)",
    ];

    let mut context = EvaluationContext::new();
    for source in program {
        match context.evaluate_str(source) {
            Ok(value) => println!("{}: {}", source, value),
            Err(err) => println!("{}: {}", source, err)
        }
    }
}
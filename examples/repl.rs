use tokio::io::{self, AsyncBufReadExt, AsyncWriteExt};
use snek::OwnedEvaluationContext;

async fn query(stdout: &mut io::Stdout, lines: &mut io::Lines<io::BufReader<io::Stdin>>) -> io::Result<Option<String>> {
    stdout.write_all("> ".as_bytes()).await.unwrap();
    stdout.flush().await.unwrap();
    lines.next_line().await
}

#[tokio::main]
async fn main() {
    let mut context = OwnedEvaluationContext::new();
    let mut lines = io::BufReader::new(io::stdin()).lines();
    let mut stdout = io::stdout();
    
    while let Ok(Some(line)) = query(&mut stdout, &mut lines).await {
        match context.evaluate(line) {
            Ok(value) => println!("{}", value),
            Err(err) => println!("Error: {}", err),
        }
    }
}

use tokio::io::{self, AsyncBufReadExt, AsyncWriteExt};
use snek::{OwnedEvaluationContext, AllocationContext};

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
    
    // We need to keep the lines around due to the fact that we 
    // borrow the strings in the input in the context
    let mut storage = AllocationContext::new();

    while let Ok(Some(line)) = query(&mut stdout, &mut lines).await {
        let ptr = storage.as_ptr(line);

        match context.evaluate_str(unsafe { &*ptr }) {
            Ok(value) => println!("{}", value),
            Err(err) => println!("Error: {}", err),
        }
    }

    unsafe { storage.drop(); }
}

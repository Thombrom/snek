use parser::parser;

mod parser;
mod interpreter;

#[cfg(test)]
mod test_utils;

fn main() {
    println!("Hello, world!");

    println!("Sexp: {:?}", parser("(test a (deeper 2 3 v) -1.5)"));
    println!("Sexp: {:?}", parser("atom"));
}

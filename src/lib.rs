
mod builtin;
mod context;
mod error;
mod interpreter;
mod parser;

#[cfg(test)]
mod test_utils;

pub use error::SnekError;
pub use context::{OwnedEvaluationContext, BorrowedEvaluationContext, AllocationContext};
pub use interpreter::SnekValue;
pub use parser::{parse, Sexp};
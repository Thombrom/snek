use core::{error::Error, fmt};



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SnekError {
    SnekSyntaxError,
    SnekNameError,
    SnekEvaluationError,
}

impl fmt::Display for SnekError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

impl Error for SnekError {
    fn description(&self) -> &str {
        match self {
            Self::SnekEvaluationError => "SnekEvaluationError",
            Self::SnekNameError => "SnekNameError",
            Self::SnekSyntaxError => "SnekSyntaxError"
        }
    }
}
#![no_main]

use core::fmt;

use itertools::Itertools;
use libfuzzer_sys::{arbitrary::Arbitrary, fuzz_target};

// Builtins and load from variables
#[derive(Arbitrary, Debug)]
enum SnekAtom {
    Add, Sub, Mul, Div,
    True, False, Nil,
    Greater, GreaterEq,
    Less, LessEq, Eq,

    List, Car, Cdr, Length,
    EltAtIndex, Concat, Map,
    Filter, Reduce,
    
    Identifier(String),
    Number(f64),
}

impl fmt::Display for SnekAtom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", match self {
            SnekAtom::Add => "+",
            SnekAtom::Sub => "-",
            SnekAtom::Mul => "*",
            SnekAtom::Div => "/",
            SnekAtom::True => "#t",
            SnekAtom::False => "#f",
            SnekAtom::Nil => "nil",
            SnekAtom::Greater => ">",
            SnekAtom::GreaterEq => ">=",
            SnekAtom::Less => "<",
            SnekAtom::LessEq => "<=",
            SnekAtom::Eq => "==",
            SnekAtom::List => "list",
            SnekAtom::Car => "car",
            SnekAtom::Cdr => "cdr",
            SnekAtom::Length => "length",
            SnekAtom::EltAtIndex => "elt-at-index",
            SnekAtom::Concat => "concat",
            SnekAtom::Map => "map",
            SnekAtom::Filter => "filter",
            SnekAtom::Reduce => "reduce",
            SnekAtom::Identifier(identifier) => identifier,
            SnekAtom::Number(value) => return write!(f, "{}", value),
        })
    }
}

#[derive(Arbitrary, Debug)]
enum SnekCommand {
    // Definitive commands
    Lambda(Vec<SnekCommand>),
    Define(Vec<SnekCommand>),
    If(Vec<SnekCommand>),
    And(Vec<SnekCommand>),
    Or(Vec<SnekCommand>),
    Not(Vec<SnekCommand>),
    Cons(Vec<SnekCommand>),
    Begin(Vec<SnekCommand>),
    Let(Vec<SnekCommand>),
    Set(Vec<SnekCommand>),

    Atom(SnekAtom),
}

fn stringify_arguments(values: &[SnekCommand]) -> String {
    values.into_iter()
        .map(SnekCommand::to_string)
        .join(" ")
}

impl fmt::Display for SnekCommand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Self::Atom(atom) = self {
            return atom.fmt(f)
        }

        let argument_str = match self {
            SnekCommand::Lambda(args) |
            SnekCommand::Define(args) |
            SnekCommand::If(args) |
            SnekCommand::And(args) |
            SnekCommand::Or(args) |
            SnekCommand::Not(args) |
            SnekCommand::Cons(args) |
            SnekCommand::Begin(args) |
            SnekCommand::Let(args) |
            SnekCommand::Set(args) 
                => stringify_arguments(&args),
            SnekCommand::Atom(_) => unreachable!("Handled separately at the start")
        };

        write!(f, "({} {})", match self {
            SnekCommand::Lambda(_) => "lambda",
            SnekCommand::Define(_) => "define",
            SnekCommand::If(_) => "if",
            SnekCommand::And(_) => "and",
            SnekCommand::Or(_) => "or",
            SnekCommand::Not(_) => "not",
            SnekCommand::Cons(_) => "cons",
            SnekCommand::Begin(_) => "begin",
            SnekCommand::Let(_) => "let",
            SnekCommand::Set(_) => "set!",
            SnekCommand::Atom(_) => unreachable!("Handled separately at the start")
        }, argument_str)
    }
}

fuzz_target!(|commands: Vec<SnekCommand>| {
    {
        let mut context = snek::OwnedEvaluationContext::new();

        for command in commands {
            let command = command.to_string();
            let _ = context.evaluate(command);
        }
    }
});


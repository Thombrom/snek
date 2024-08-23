use core::fmt;
use std::{cell::RefCell, collections::HashMap, ops::Deref, rc::Rc};

use itertools::Itertools;

use crate::{error::SnekError, parser::{parser, Literal, Sexp}};

type EvaluationResult<'a, 'b> = Result<SnekValue<'a, 'b>, SnekError>;

fn snek_value_list_to_numbers<'a, 'b>(values: Vec<SnekValue<'a, 'b>>) -> Result<Vec<f64>, SnekError> {
    values.into_iter()
        .map(|value| match value {
            SnekValue::Number(number) => Ok(number),
            _ => Err(SnekError::SnekEvaluationError)
        }).collect()
}

fn builtin_add<'a, 'b>(values: Vec<SnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if values.len() == 0 { return Err(SnekError::SnekEvaluationError); }

    // We can only add integers together
    let values = snek_value_list_to_numbers(values)?;
    Ok(SnekValue::Number(values.into_iter().sum()))
}

fn builtin_sub<'a, 'b>(values: Vec<SnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if values.len() == 0 { return Err(SnekError::SnekEvaluationError); }

    let values = snek_value_list_to_numbers(values)?;
    if values.len() == 1 { return Ok(SnekValue::Number(values[0] * -1.0)) }
    Ok(SnekValue::Number(values[0] - values[1..].into_iter().sum::<f64>()))
}

fn builtin_mul<'a, 'b>(values: Vec<SnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if values.len() == 0 { return Err(SnekError::SnekEvaluationError); }

    let values = snek_value_list_to_numbers(values)?;
    Ok(SnekValue::Number(values.into_iter().reduce(|a, b| a * b).unwrap()))
}

fn builtin_div<'a, 'b>(values: Vec<SnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if values.len() == 0 { return Err(SnekError::SnekEvaluationError); }

    let values = snek_value_list_to_numbers(values)?;
    Ok(SnekValue::Number(values[1..].into_iter().fold(values[0], |a, b| a / b)))
}

fn builtin_compare_impl<F: Fn(&f64, &f64) -> bool>(values: &[f64], f: F) -> Result<bool, SnekError> {
    if values.len() < 2 { return Ok(true) }
    Ok(f(&values[0], &values[1]) && builtin_compare_impl(&values[1..], f)?)
}

fn builtin_compare<'a, 'b, F: Fn(&f64, &f64) -> bool>(values: Vec<SnekValue<'a, 'b>>, f: F) -> EvaluationResult<'a, 'b> {
    let values = snek_value_list_to_numbers(values)?;
    Ok(SnekValue::Boolean(builtin_compare_impl(&values, f)?))
}

fn builtin_greater<'a, 'b>(values: Vec<SnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    builtin_compare(values, |a, b| a > b)
}

fn builtin_greater_eq<'a, 'b>(values: Vec<SnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    builtin_compare(values, |a, b| a >= b)
}

fn builtin_less<'a, 'b>(values: Vec<SnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    builtin_compare(values, |a, b| a < b)
}

fn builtin_less_eq<'a, 'b>(values: Vec<SnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    builtin_compare(values, |a, b| a <= b)
}

fn builtin_eq<'a, 'b>(values: Vec<SnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    builtin_compare(values, |a, b| (a - b).abs() < 1.0e-5)
}

fn builtin_list<'a, 'b>(mut values: Vec<SnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    let mut cond = SnekValue::Cons(Cons::nil());

    while let Some(value) = values.pop() {
        cond = SnekValue::Cons(Cons::new(value, cond));
    }

    Ok(cond)
}

fn builtin_car<'a, 'b>(values: Vec<SnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if values.len() != 1 { return Err(SnekError::SnekSyntaxError); }

    match &values[0] {
        SnekValue::Cons(Cons(Some(value))) => Ok(value.0.clone()),
        _ => Err(SnekError::SnekEvaluationError)
    }
}   

fn builtin_cdr<'a, 'b>(values: Vec<SnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if values.len() != 1 { return Err(SnekError::SnekSyntaxError); }

    match &values[0] {
        SnekValue::Cons(Cons(Some(value))) => Ok(value.1.clone()),
        _ => Err(SnekError::SnekEvaluationError)
    }
}   

fn builtin_length_impl<'a, 'b>(value: &SnekValue<'a, 'b>) -> Result<usize, SnekError> {
    match value {
        SnekValue::Cons(Cons(None)) => Ok(0),
        SnekValue::Cons(Cons(Some(value))) => Ok(1 + builtin_length_impl(&value.1)?),
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn builtin_length<'a, 'b>(values: Vec<SnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if values.len() != 1 { return Err(SnekError::SnekSyntaxError); }
    Ok(SnekValue::Number(builtin_length_impl(&values[0])? as f64))
}

fn builtin_elt_at_index_impl<'a, 'b>(value: &SnekValue<'a, 'b>, index: usize) -> EvaluationResult<'a, 'b> {
    match (value, index) {
        (SnekValue::Cons(Cons(Some(value))), 0) => Ok(value.0.clone()),
        (SnekValue::Cons(Cons(Some(value))), _) => builtin_elt_at_index_impl(&value.1, index - 1),
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn builtin_elt_at_index<'a, 'b>(values: Vec<SnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if values.len() != 2 { return Err(SnekError::SnekSyntaxError); }
    match (&values[0], &values[1]) {
        (value, SnekValue::Number(index)) => builtin_elt_at_index_impl(&value, index.round() as usize),
        _ => Err(SnekError::SnekEvaluationError)
    }    
}

fn builtin_concat_impl<'a, 'b>(current: &SnekValue<'a, 'b>, lists: &[SnekValue<'a, 'b>]) -> EvaluationResult<'a, 'b> {
    match current {
        SnekValue::Cons(Cons(None)) => {
            if lists.len() == 0 { return Ok(SnekValue::Cons(Cons::nil())); }
            builtin_concat_impl(&lists[0], &lists[1..])
        }
        SnekValue::Cons(Cons(Some(cons))) => {
            let cdr = builtin_concat_impl(&cons.1, lists)?;
            Ok(SnekValue::Cons(Cons::new(cons.0.clone(), cdr)))
        },
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn builtin_concat<'a, 'b>(values: Vec<SnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if values.len() == 0 { return Ok(SnekValue::Cons(Cons::nil())); }
    builtin_concat_impl(&values[0], &values[1..])
}

fn builtin_map_impl<'a, 'b>(function: &Function<'a, 'b>, list: &SnekValue<'a, 'b>) -> EvaluationResult<'a, 'b> {
    match list {
        SnekValue::Cons(Cons(None)) => Ok(list.clone()),
        SnekValue::Cons(Cons(Some(value))) => {
            let cdr = builtin_map_impl(function, &value.1)?;
            let car = function.evaluate(vec![value.0.clone()])?;
            Ok(SnekValue::Cons(Cons::new(car, cdr)))
        },
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn builtin_map<'a, 'b>(values: Vec<SnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if values.len() != 2 { return Err(SnekError::SnekSyntaxError); }

    match &values[0] {
        SnekValue::Function(function) => builtin_map_impl(function, &values[1]),
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn builtin_filter_impl<'a, 'b>(function: &Function<'a, 'b>, list: &SnekValue<'a, 'b>) -> EvaluationResult<'a, 'b> {
    match list {
        SnekValue::Cons(Cons(None)) => Ok(SnekValue::Cons(Cons::nil())),
        SnekValue::Cons(Cons(Some(value))) => {
            let cdr = builtin_filter_impl(function, &value.1)?;
            match function.evaluate(vec![value.0.clone()])? {
                SnekValue::Boolean(true) => Ok(SnekValue::Cons(Cons::new(value.0.clone(), cdr))),
                SnekValue::Boolean(false) => Ok(cdr),
                _ => Err(SnekError::SnekEvaluationError)
            }
        },
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn builtin_filter<'a, 'b>(values: Vec<SnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if values.len() != 2 { return Err(SnekError::SnekSyntaxError); }

    match &values[0] {
        SnekValue::Function(function) => builtin_filter_impl(function, &values[1]),
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn builtin_reduce_impl<'a, 'b>(function: &Function<'a, 'b>, list: &SnekValue<'a, 'b>, acc: SnekValue<'a, 'b>) -> EvaluationResult<'a, 'b> {
    match list {
        SnekValue::Cons(Cons(None)) => Ok(acc),
        SnekValue::Cons(Cons(Some(value))) 
            => builtin_reduce_impl(function, &value.1, function.evaluate(vec![acc, value.0.clone()])?),
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn builtin_reduce<'a, 'b>(values: Vec<SnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if values.len() != 3 { return Err(SnekError::SnekSyntaxError); }

    match &values[0] {
        SnekValue::Function(function) => builtin_reduce_impl(function, &values[1], values[2].clone()),
        _ => Err(SnekError::SnekEvaluationError)
    }
}

pub fn builtin_frame<'a, 'b: 'a>() -> Rc<Frame<'a, 'b>> {
    Frame::root(HashMap::from([
        ("+", SnekValue::Function(Function::Builtin(&builtin_add))),
        ("-", SnekValue::Function(Function::Builtin(&builtin_sub))),
        ("*", SnekValue::Function(Function::Builtin(&builtin_mul))),
        ("/", SnekValue::Function(Function::Builtin(&builtin_div))),

        ("#t", SnekValue::Boolean(true)),
        ("#f", SnekValue::Boolean(false)),
        ("nil", SnekValue::Cons(Cons::nil())),

        (">", SnekValue::Function(Function::Builtin(&builtin_greater))),
        (">=", SnekValue::Function(Function::Builtin(&builtin_greater_eq))),
        ("<", SnekValue::Function(Function::Builtin(&builtin_less))),
        ("<=", SnekValue::Function(Function::Builtin(&builtin_less_eq))),
        ("=?", SnekValue::Function(Function::Builtin(&builtin_eq))),
        
        ("list", SnekValue::Function(Function::Builtin(&builtin_list))),
        ("car", SnekValue::Function(Function::Builtin(&builtin_car))),
        ("cdr", SnekValue::Function(Function::Builtin(&builtin_cdr))),
        ("length", SnekValue::Function(Function::Builtin(&builtin_length))),
        ("elt-at-index", SnekValue::Function(Function::Builtin(&builtin_elt_at_index))),
        ("concat", SnekValue::Function(Function::Builtin(&builtin_concat))),
        ("map", SnekValue::Function(Function::Builtin(&builtin_map))),
        ("filter", SnekValue::Function(Function::Builtin(&builtin_filter))),
        ("reduce", SnekValue::Function(Function::Builtin(&builtin_reduce))),
    ]))
}

#[derive(Clone)]
struct Cons<'a, 'b>(Option<Rc<(SnekValue<'a, 'b>, SnekValue<'a, 'b>)>>);

impl<'a, 'b> fmt::Debug for Cons<'a, 'b> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<'a, 'b> Cons<'a, 'b> {
    pub fn new(a: SnekValue<'a, 'b>, b: SnekValue<'a, 'b>) -> Self {
        Self(Some(Rc::new((a, b))))
    }

    pub fn nil() -> Self {
        Self(None)
    }

    pub fn car(&self) -> EvaluationResult<'a, 'b> {
        match &self.0 {
            Some(v) => Ok(v.0.clone()),
            None => Err(SnekError::SnekEvaluationError)
        }
    }

    pub fn cdr(&self) -> EvaluationResult<'a, 'b> {
        match &self.0 {
            Some(v) => Ok(v.1.clone()),
            None => Err(SnekError::SnekEvaluationError)
        }
    }
}

// Value type that can be produced by expressions
#[derive(Clone)]
pub enum SnekValue<'a, 'b: 'a> {
    Boolean(bool),
    Number(f64),
    Function(Function<'a, 'b>),
    Cons(Cons<'a, 'b>),
}

impl<'a, 'b> fmt::Display for SnekValue<'a, 'b> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Boolean(value) => write!(f, "{}", value),
            Self::Number(value) => write!(f, "{}", value),
            Self::Function(_) => write!(f, "FUNCTION"),
            Self::Cons(cons) => write!(f, "{:?}", cons),
        }
    }
}

impl<'a, 'b> fmt::Debug for SnekValue<'a, 'b> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        (self as &dyn fmt::Display).fmt(f)
    }
}

#[derive(Debug, Clone)]
pub struct Frame<'a, 'b: 'a> {
    bindings: RefCell<HashMap<&'b str, SnekValue<'a, 'b>>>,
    parent: Option<Rc<Frame<'a, 'b>>>,
}

impl<'a, 'b> Frame<'a, 'b> {
    fn root(bindings: HashMap<&'b str, SnekValue<'a, 'b>>) -> Rc<Self> {
        Rc::new(Self {
                    parent: None,
                    bindings: RefCell::from(bindings)
                })
    }

    pub fn new(parent: Rc<Frame<'a, 'b>>) -> Rc<Self> {
        Rc::new(Self {
                    parent: Some(parent),
                    bindings: RefCell::new(HashMap::new())
                })
    }

    fn insert(&self, key: &'b str, value: SnekValue<'a, 'b>) {
        self.bindings.borrow_mut().insert(key, value);
    }

    fn get(&self, key: &'b str) -> EvaluationResult<'a, 'b> {
        if let Some(value) = self.bindings.borrow_mut().get(key) {
            return Ok(value.clone())
        }
        match self.parent.as_ref() {
            Some(parent) => parent.get(key),
            None => Err(SnekError::SnekNameError)
        }
    }

    fn update(&self, key: &'b str, value: SnekValue<'a, 'b>) -> EvaluationResult<'a, 'b> {
        if self.bindings.borrow().contains_key(key) {
            self.bindings.borrow_mut().insert(key, value.clone());
            return Ok(value)
        } else {
            match &self.parent {
                Some(parent) => parent.update(key, value),
                None => Err(SnekError::SnekNameError)
            }
        }
    } 
}

#[derive(Clone)]
enum Function<'a, 'b: 'a> {
    Builtin(&'b dyn Fn(Vec<SnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b>),
    Lisp(LispFunction<'a, 'b>)
}

impl<'a, 'b> fmt::Debug for Function<'a, 'b> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Builtin(_) => write!(f, "BUILTIN"),
            Self::Lisp(lisp_function) => write!(f, "Lisp({:?})", lisp_function)
        }
    }
}

impl<'a, 'b: 'a> Function<'a, 'b> {
    fn evaluate(&self, values: Vec<SnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
        match self {
            Self::Builtin(builtin) => builtin(values),
            Self::Lisp(lisp_function) => lisp_function.evaluate(values)
        }
    }
}

#[derive(Debug, Clone)]
struct LispFunction<'a, 'b: 'a> {
    parameters: Vec<&'b str>,
    expression: &'a Sexp<'b>,
    environment: Rc<Frame<'a, 'b>>
}

impl<'a, 'b: 'a> LispFunction<'a, 'b> {
    fn evaluate(&self, values: Vec<SnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
        // To evaluate a lisp function, it must receive the correct number of variables
        if values.len() != self.parameters.len() { return Err(SnekError::SnekEvaluationError) }

        let environment = Frame::new(self.environment.clone());
        for (variable, value) in self.parameters.iter().zip(values.into_iter()) {
            environment.insert(variable, value);
        }

        evaluate(self.expression, &environment)
    }
}

fn evaluate_atom<'a, 'b>(literal: &'a Literal<'b>, environment: &Rc<Frame<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    // An atom is interpreted by looking up the identifier, if it is an identifier, or returning the numerical value
    // it represents

    match literal {
        Literal::Identifier(identifier) => environment.get(identifier),
        Literal::Number(number) => Ok(SnekValue::Number(*number))
    }
}

fn evaluate_expression<'a, 'b: 'a>(expression: &'a [Sexp<'b>], environment: &Rc<Frame<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    // To interpret an expression, all values in the expression are interpreted in the environment. The first value
    // must be a function, which is then called with the remainder of the arguments. 
    // There are a few special function exceptions that are checked first

    if expression.len() == 0 { return Err(SnekError::SnekEvaluationError) }
    match expression[0] {
        Sexp::Atom(Literal::Identifier(identifier)) => {
            match identifier {
                "lambda" => return evaluate_lambda(&expression[1..], environment),
                "define" => return evaluate_define(&expression[1..], environment),
                "if" => return evaluate_if(&expression[1..], environment),
                "and" => return evaluate_and(&expression[1..], environment),
                "or" => return evaluate_or(&expression[1..], environment),
                "not" => return evaluate_not(&expression[1..], environment),
                "cons" => return evaluate_cons(&expression[1..], environment),
                "begin" => return evaluate_begin(&expression[1..], environment),
                "let" => return evaluate_let(&expression[1..], environment),
                "set!" => return evaluate_set_bang(&expression[1..], environment),
                _ => {}
            }
        },
        _ => {}
    }

    let function = match evaluate(&expression[0], environment)? {
        SnekValue::Function(function) => function,
        _ => return Err(SnekError::SnekEvaluationError)
    };

    function.evaluate(evaulate_list(&expression[1..], environment)?)
}

fn sexp_list_to_identifiers<'a, 'b: 'a>(list: &'a [Sexp<'b>]) -> Result<Vec<&'b str>, SnekError> {
    list.into_iter()
        .map(|sexp| match sexp {
            Sexp::Atom(Literal::Identifier(identifier)) => Ok(*identifier),
            _ => Err(SnekError::SnekSyntaxError)
        }).collect()
}

fn evaluate_let_parameter<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: &Rc<Frame<'a, 'b>>) -> Result<(&'b str, SnekValue<'a, 'b>), SnekError> {
    // A let parameter is a sexp of two elements, the first being an atom with the name of the parameter,
    // and the second evalutes to a value for the parameter

    if list.len() != 2 { return Err(SnekError::SnekSyntaxError); }

    let name = match list[0] {
        Sexp::Atom(Literal::Identifier(identifier)) => identifier,
        _ => return Err(SnekError::SnekSyntaxError)
    };

    evaluate(&list[1], environment)
        .map(|value| (name, value))
}

fn evaluate_let_parameter_list<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: &Rc<Frame<'a, 'b>>) -> Result<Vec<(&'b str, SnekValue<'a, 'b>)>, SnekError> {
    list.into_iter().map(|sexp| {
        match sexp { 
            Sexp::Expression(expression) => evaluate_let_parameter(&expression, environment),
            _ => Err(SnekError::SnekSyntaxError)
        }
    }).collect()
}

fn evaluate_let<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: &Rc<Frame<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    // Let statements has two parts. The parameters and the body. The paremeters is an expression in the first
    // element of list, which is a list of two-length sexp expressions, the first being the name (a literal),
    // and the second being a value (to be evaluated). These are set in a new environment where the second index
    // of list is evaluated

    if list.len() != 2 { return Err(SnekError::SnekSyntaxError); }

    let parameters = match &list[0] {
        Sexp::Expression(expression) => evaluate_let_parameter_list(&expression, environment)?,
        _ => return Err(SnekError::SnekSyntaxError)
    };

    let sub_environment = Frame::new(environment.clone());
    for (name, value) in parameters {
        sub_environment.insert(name, value);
    }

    evaluate(&list[1], &sub_environment)
}

fn evaluate_set_bang<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: &Rc<Frame<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if list.len() != 2 { return Err(SnekError::SnekSyntaxError); }
    
    let name = match list[0] {
        Sexp::Atom(Literal::Identifier(name)) => name,
        _ => return Err(SnekError::SnekSyntaxError),
    };

    let value = evaluate(&list[1], environment)?;
    environment.update(name, value)
}

fn evaluate_begin<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: &Rc<Frame<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    // Begin evaluates all sexps in the list and returns the result of the last evaluation

    if list.len() == 0 { return Err(SnekError::SnekSyntaxError); }

    Ok(list.into_iter()
        .map(|sexp| evaluate(sexp, environment))
        .collect::<Result<Vec<_>, _>>()?
        .pop()
        .unwrap())
}

fn evaluate_if<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: &Rc<Frame<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    // An if expression evaluates the first value, and if it is true, evaluates the second value, if it is false,
    // evalutes the third value

    if list.len() != 3 { return Err(SnekError::SnekEvaluationError); }

    match evaluate(&list[0], environment)? {
        SnekValue::Boolean(true) => evaluate(&list[1], environment),
        SnekValue::Boolean(false) => evaluate(&list[2], environment),
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn evaluate_and<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: &Rc<Frame<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    // Evalutes an and-expression. If all values in the expression evalutes to true, it returns true, 
    // but if a single value evalutes to false, it returns false. It is an error to have an expression evaluate
    // to a non-boolean value

    for expression in list {
        match evaluate(expression, environment)? 
        { 
            SnekValue::Boolean(false) => return Ok(SnekValue::Boolean(false)),
            SnekValue::Boolean(true) => {},
            _ => return Err(SnekError::SnekEvaluationError)
        }
    }

    Ok(SnekValue::Boolean(true))
}

fn evaluate_or<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: &Rc<Frame<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    // Evalutes an or-expression. If all values in the expression evalutes to false, it returns false, 
    // but if a single value evalutes to true, it returns true. It is an error to have an expression evaluate
    // to a non-boolean value

    for expression in list {
        match evaluate(expression, environment)? 
        { 
            SnekValue::Boolean(true) => return Ok(SnekValue::Boolean(true)),
            SnekValue::Boolean(false) => {},
            _ => return Err(SnekError::SnekEvaluationError)
        }
    }

    Ok(SnekValue::Boolean(false))
}

fn evaluate_not<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: &Rc<Frame<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    // Evalutes a not-expression. It has a single parameter which should evalute to a boolean expression

    if list.len() != 1 { return Err(SnekError::SnekSyntaxError); }
    match evaluate(&list[0], environment)? {
        SnekValue::Boolean(value) => Ok(SnekValue::Boolean(!value)),
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn evaluate_define<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: &Rc<Frame<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    // A define can be either a shorthand lambda or an instruction to associate a variable
    // with a value. 
    //
    // A shorthand lambda has two elements in the list, the first must be a non-empty expression of all literals, 
    // where the first value is the name to be defined as the lambda, and the rest is the parameters
    //
    // The second option is a definition of a value, where the first element is an atom of a literal, and the second
    // value is evaluated to the value
    if list.len() != 2 { return Err(SnekError::SnekSyntaxError); }

    let parameter_expression = match &list[0] {
        Sexp::Atom(Literal::Identifier(key)) => {
            let value = evaluate(&list[1], environment)?;
            environment.insert(key, value.clone());
            return Ok(value)
        },
        Sexp::Expression(expression) => expression,
        _ => return Err(SnekError::SnekSyntaxError)
    };

    if parameter_expression.len() == 0 { return Err(SnekError::SnekSyntaxError); }
    let identifier_list = sexp_list_to_identifiers(&parameter_expression)?;
    let (name, parameters) = identifier_list.split_at(1);

    let function = SnekValue::Function(Function::Lisp(LispFunction { 
        parameters: parameters.to_vec(), 
        expression: &list[1], 
        environment: environment.clone()
    }));

    environment.insert(name[0], function.clone());
    Ok(function)    
}

fn evaluate_lambda<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: &Rc<Frame<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    // A lambda is a function declaration. The list must have two elements, the first being an expression with all
    // literal atoms in them, and the second element is the body of the function

    if list.len() != 2 { return Err(SnekError::SnekSyntaxError); }
    let parameter_expression = match &list[0] {
        Sexp::Expression(parameter_list) => parameter_list,
        _ => return Err(SnekError::SnekSyntaxError)
    };

    let parameters = sexp_list_to_identifiers(&parameter_expression)?;
    Ok(SnekValue::Function(Function::Lisp(LispFunction {
        parameters,
        expression: &list[1],
        environment: environment.clone()
    })))
}

fn evaluate_cons<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: &Rc<Frame<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    // A cons expression builds a cons cell of the two parameters

    if list.len() != 2 { return Err(SnekError::SnekSyntaxError); }
    Ok(SnekValue::Cons(Cons::new(
        evaluate(&list[0], environment)?,
        evaluate(&list[1], environment)?
    )))
}

fn evaulate_list<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: &Rc<Frame<'a, 'b>>) -> Result<Vec<SnekValue<'a, 'b>>, SnekError> {
    list.into_iter()
        .map(|sexp| evaluate(sexp, environment))
        .collect::<Result<Vec<SnekValue<'a, 'b>>, SnekError>>()
}

pub fn evaluate<'a, 'b: 'a>(sexp: &'a Sexp<'b>, environment: &Rc<Frame<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    match sexp {
        Sexp::Atom(atom) => evaluate_atom(atom, environment),
        Sexp::Expression(expression) => evaluate_expression(expression, environment)
    }
}

pub struct EvaluationContext<'a, 'b> {
    frame: Rc<Frame<'a, 'b>>
}

impl<'a, 'b> EvaluationContext<'a, 'b> {
    pub fn new() -> Self {
        Self {
            frame: Frame::new(builtin_frame())
        }
    }

    pub fn evaluate_sexp(&mut self, sexp: &'b Sexp<'a>) -> EvaluationResult<'a, 'b> {
        let result = evaluate(sexp, &self.frame);
        result
    }
}

#[cfg(test)]
mod tests {
    use anyhow::bail;
    use itertools::Itertools;

    use crate::test_utils::{all_testcases, load_test_pair, TestEvaluationResult, TestOutput};

    use super::*;

    fn compare_lists<'a, 'b>(a: &Cons<'a, 'b>, b: &[TestOutput]) -> bool {
        match &a.0 {
            None => b.len() == 0,
            Some(a) => {
                let (car, cdr) = a.deref();
                if b.len() == 0 { return false; }
                if !compare(car, &b[0]) { return false }

                match cdr {
                    SnekValue::Cons(cons) => compare_lists(cons, &b[1..]),
                    _ => false
                }
            }
        }
    }

    fn compare<'a, 'b>(a: &SnekValue<'a, 'b>, b: &TestOutput) -> bool {
        match (a, b) {
            (_, TestOutput::Something(_)) => true,
            (SnekValue::Number(a), TestOutput::Number(b)) => (a - b).abs() < 1.0e-5,
            (SnekValue::Cons(cons), TestOutput::List(list)) => compare_lists(cons, &list),
            _ => false
        }
    }

    fn assert_run(testcase: usize, entries: Vec<(String, TestEvaluationResult)>) -> anyhow::Result<()> {
        let mut evaluation_context = EvaluationContext::new();
        let sexps = entries
            .iter()
            .enumerate()
            .filter_map(|(line_no, (source, result))| {
                // Parser testing is done separately
                parser(&source).ok().map(move |sexp| (line_no, source, sexp, result.clone().into()))
            })
            .collect_vec();

        for (lineno, source, sexp, expected) in &sexps {
            let result = evaluation_context.evaluate_sexp(sexp);
            println!("{}:\n{:?}", source, result);
            match (&result, expected) {
                (Ok(a), Ok(b)) => assert!(compare(a, b), "Testcase({}, {}): Got {:?}, expected {:?}", testcase, lineno, result, expected),
                (Err(result), Err(expected)) 
                    => assert_eq!(result, expected, "Testcase({}, {}): Got {:?}, expected {:?}", testcase, lineno, result, expected),
                _ => bail!("Testcase({}, {}): Got {:?}, expected {:?}", testcase, lineno, result, expected),
            }
        }

        Ok(())
    }

    #[test]
    fn evaluate_testcase() -> anyhow::Result<()> {
        for testcase in all_testcases() {
            println!("Running testcase {}", testcase);
            let entries = load_test_pair(testcase)?;
            assert_run(testcase, entries)?;
        }

        Ok(())
    }
}
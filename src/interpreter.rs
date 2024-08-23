use core::fmt;
use std::{cell::RefCell, collections::HashMap, ops::Deref, rc::Rc};

use itertools::Itertools;

use crate::{error::SnekError, parser::{parser, Literal, Sexp}};

type EvaluationResult<'a, 'b> = Result<InternalSnekValue<'a, 'b>, SnekError>;

fn snek_value_list_to_numbers<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>) -> Result<Vec<f64>, SnekError> {
    values.into_iter()
        .map(|value| match value {
            InternalSnekValue::Number(number) => Ok(number),
            _ => Err(SnekError::SnekEvaluationError)
        }).collect()
}

fn builtin_add<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if values.len() == 0 { return Err(SnekError::SnekEvaluationError); }

    // We can only add integers together
    let values = snek_value_list_to_numbers(values)?;
    Ok(InternalSnekValue::Number(values.into_iter().sum()))
}

fn builtin_sub<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if values.len() == 0 { return Err(SnekError::SnekEvaluationError); }

    let values = snek_value_list_to_numbers(values)?;
    if values.len() == 1 { return Ok(InternalSnekValue::Number(values[0] * -1.0)) }
    Ok(InternalSnekValue::Number(values[0] - values[1..].into_iter().sum::<f64>()))
}

fn builtin_mul<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if values.len() == 0 { return Err(SnekError::SnekEvaluationError); }

    let values = snek_value_list_to_numbers(values)?;
    Ok(InternalSnekValue::Number(values.into_iter().reduce(|a, b| a * b).unwrap()))
}

fn builtin_div<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if values.len() == 0 { return Err(SnekError::SnekEvaluationError); }

    let values = snek_value_list_to_numbers(values)?;
    Ok(InternalSnekValue::Number(values[1..].into_iter().fold(values[0], |a, b| a / b)))
}

fn builtin_compare_impl<F: Fn(&f64, &f64) -> bool>(values: &[f64], f: F) -> Result<bool, SnekError> {
    if values.len() < 2 { return Ok(true) }
    Ok(f(&values[0], &values[1]) && builtin_compare_impl(&values[1..], f)?)
}

fn builtin_compare<'a, 'b, F: Fn(&f64, &f64) -> bool>(values: Vec<InternalSnekValue<'a, 'b>>, f: F) -> EvaluationResult<'a, 'b> {
    let values = snek_value_list_to_numbers(values)?;
    Ok(InternalSnekValue::Boolean(builtin_compare_impl(&values, f)?))
}

fn builtin_greater<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    builtin_compare(values, |a, b| a > b)
}

fn builtin_greater_eq<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    builtin_compare(values, |a, b| a >= b)
}

fn builtin_less<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    builtin_compare(values, |a, b| a < b)
}

fn builtin_less_eq<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    builtin_compare(values, |a, b| a <= b)
}

fn builtin_eq<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    builtin_compare(values, |a, b| (a - b).abs() < 1.0e-5)
}

fn builtin_list<'a, 'b>(mut values: Vec<InternalSnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    let mut cond = InternalSnekValue::Cons(Cons::nil());

    while let Some(value) = values.pop() {
        cond = InternalSnekValue::Cons(Cons::new(value, cond));
    }

    Ok(cond)
}

fn builtin_car<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if values.len() != 1 { return Err(SnekError::SnekSyntaxError); }

    match &values[0] {
        InternalSnekValue::Cons(Cons(Some(value))) => Ok(value.0.clone()),
        _ => Err(SnekError::SnekEvaluationError)
    }
}   

fn builtin_cdr<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if values.len() != 1 { return Err(SnekError::SnekSyntaxError); }

    match &values[0] {
        InternalSnekValue::Cons(Cons(Some(value))) => Ok(value.1.clone()),
        _ => Err(SnekError::SnekEvaluationError)
    }
}   

fn builtin_length_impl<'a, 'b>(value: &InternalSnekValue<'a, 'b>) -> Result<usize, SnekError> {
    match value {
        InternalSnekValue::Cons(Cons(None)) => Ok(0),
        InternalSnekValue::Cons(Cons(Some(value))) => Ok(1 + builtin_length_impl(&value.1)?),
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn builtin_length<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if values.len() != 1 { return Err(SnekError::SnekSyntaxError); }
    Ok(InternalSnekValue::Number(builtin_length_impl(&values[0])? as f64))
}

fn builtin_elt_at_index_impl<'a, 'b>(value: &InternalSnekValue<'a, 'b>, index: usize) -> EvaluationResult<'a, 'b> {
    match (value, index) {
        (InternalSnekValue::Cons(Cons(Some(value))), 0) => Ok(value.0.clone()),
        (InternalSnekValue::Cons(Cons(Some(value))), _) => builtin_elt_at_index_impl(&value.1, index - 1),
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn builtin_elt_at_index<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if values.len() != 2 { return Err(SnekError::SnekSyntaxError); }
    match (&values[0], &values[1]) {
        (value, InternalSnekValue::Number(index)) => builtin_elt_at_index_impl(&value, index.round() as usize),
        _ => Err(SnekError::SnekEvaluationError)
    }    
}

fn builtin_concat_impl<'a, 'b>(current: &InternalSnekValue<'a, 'b>, lists: &[InternalSnekValue<'a, 'b>]) -> EvaluationResult<'a, 'b> {
    match current {
        InternalSnekValue::Cons(Cons(None)) => {
            if lists.len() == 0 { return Ok(InternalSnekValue::Cons(Cons::nil())); }
            builtin_concat_impl(&lists[0], &lists[1..])
        }
        InternalSnekValue::Cons(Cons(Some(cons))) => {
            let cdr = builtin_concat_impl(&cons.1, lists)?;
            Ok(InternalSnekValue::Cons(Cons::new(cons.0.clone(), cdr)))
        },
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn builtin_concat<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if values.len() == 0 { return Ok(InternalSnekValue::Cons(Cons::nil())); }
    builtin_concat_impl(&values[0], &values[1..])
}

fn builtin_map_impl<'a, 'b>(function: &Function<'a, 'b>, list: &InternalSnekValue<'a, 'b>) -> EvaluationResult<'a, 'b> {
    match list {
        InternalSnekValue::Cons(Cons(None)) => Ok(list.clone()),
        InternalSnekValue::Cons(Cons(Some(value))) => {
            let cdr = builtin_map_impl(function, &value.1)?;
            let car = function.evaluate(vec![value.0.clone()])?;
            Ok(InternalSnekValue::Cons(Cons::new(car, cdr)))
        },
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn builtin_map<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if values.len() != 2 { return Err(SnekError::SnekSyntaxError); }

    match &values[0] {
        InternalSnekValue::Function(function) => builtin_map_impl(function, &values[1]),
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn builtin_filter_impl<'a, 'b>(function: &Function<'a, 'b>, list: &InternalSnekValue<'a, 'b>) -> EvaluationResult<'a, 'b> {
    match list {
        InternalSnekValue::Cons(Cons(None)) => Ok(InternalSnekValue::Cons(Cons::nil())),
        InternalSnekValue::Cons(Cons(Some(value))) => {
            let cdr = builtin_filter_impl(function, &value.1)?;
            match function.evaluate(vec![value.0.clone()])? {
                InternalSnekValue::Boolean(true) => Ok(InternalSnekValue::Cons(Cons::new(value.0.clone(), cdr))),
                InternalSnekValue::Boolean(false) => Ok(cdr),
                _ => Err(SnekError::SnekEvaluationError)
            }
        },
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn builtin_filter<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if values.len() != 2 { return Err(SnekError::SnekSyntaxError); }

    match &values[0] {
        InternalSnekValue::Function(function) => builtin_filter_impl(function, &values[1]),
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn builtin_reduce_impl<'a, 'b>(function: &Function<'a, 'b>, list: &InternalSnekValue<'a, 'b>, acc: InternalSnekValue<'a, 'b>) -> EvaluationResult<'a, 'b> {
    match list {
        InternalSnekValue::Cons(Cons(None)) => Ok(acc),
        InternalSnekValue::Cons(Cons(Some(value))) 
            => builtin_reduce_impl(function, &value.1, function.evaluate(vec![acc, value.0.clone()])?),
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn builtin_reduce<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    if values.len() != 3 { return Err(SnekError::SnekSyntaxError); }

    match &values[0] {
        InternalSnekValue::Function(function) => builtin_reduce_impl(function, &values[1], values[2].clone()),
        _ => Err(SnekError::SnekEvaluationError)
    }
}

pub fn builtin_frame<'a, 'b: 'a>() -> Rc<Frame<'a, 'b>> {
    Frame::root(HashMap::from([
        ("+", InternalSnekValue::Function(Function::Builtin(&builtin_add))),
        ("-", InternalSnekValue::Function(Function::Builtin(&builtin_sub))),
        ("*", InternalSnekValue::Function(Function::Builtin(&builtin_mul))),
        ("/", InternalSnekValue::Function(Function::Builtin(&builtin_div))),

        ("#t", InternalSnekValue::Boolean(true)),
        ("#f", InternalSnekValue::Boolean(false)),
        ("nil", InternalSnekValue::Cons(Cons::nil())),

        (">", InternalSnekValue::Function(Function::Builtin(&builtin_greater))),
        (">=", InternalSnekValue::Function(Function::Builtin(&builtin_greater_eq))),
        ("<", InternalSnekValue::Function(Function::Builtin(&builtin_less))),
        ("<=", InternalSnekValue::Function(Function::Builtin(&builtin_less_eq))),
        ("=?", InternalSnekValue::Function(Function::Builtin(&builtin_eq))),
        
        ("list", InternalSnekValue::Function(Function::Builtin(&builtin_list))),
        ("car", InternalSnekValue::Function(Function::Builtin(&builtin_car))),
        ("cdr", InternalSnekValue::Function(Function::Builtin(&builtin_cdr))),
        ("length", InternalSnekValue::Function(Function::Builtin(&builtin_length))),
        ("elt-at-index", InternalSnekValue::Function(Function::Builtin(&builtin_elt_at_index))),
        ("concat", InternalSnekValue::Function(Function::Builtin(&builtin_concat))),
        ("map", InternalSnekValue::Function(Function::Builtin(&builtin_map))),
        ("filter", InternalSnekValue::Function(Function::Builtin(&builtin_filter))),
        ("reduce", InternalSnekValue::Function(Function::Builtin(&builtin_reduce))),
    ]))
}

#[derive(Clone)]
struct Cons<'a, 'b>(Option<Rc<(InternalSnekValue<'a, 'b>, InternalSnekValue<'a, 'b>)>>);

impl<'a, 'b> fmt::Debug for Cons<'a, 'b> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<'a, 'b> Cons<'a, 'b> {
    pub fn new(a: InternalSnekValue<'a, 'b>, b: InternalSnekValue<'a, 'b>) -> Self {
        Self(Some(Rc::new((a, b))))
    }

    pub fn nil() -> Self {
        Self(None)
    }
}

// Value type that can be produced by expressions, this is
// a value that is internal to the module. Any values that are
// exposed to the outside world are converted to [SnekValue]
#[derive(Clone)]
enum InternalSnekValue<'a, 'b: 'a> {
    Boolean(bool),
    Number(f64),
    Function(Function<'a, 'b>),
    Cons(Cons<'a, 'b>),
}

impl<'a, 'b> fmt::Display for InternalSnekValue<'a, 'b> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Boolean(value) => write!(f, "{}", value),
            Self::Number(value) => write!(f, "{}", value),
            Self::Function(_) => write!(f, "FUNCTION"),
            Self::Cons(cons) => write!(f, "{:?}", cons),
        }
    }
}

impl<'a, 'b> fmt::Debug for InternalSnekValue<'a, 'b> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        (self as &dyn fmt::Display).fmt(f)
    }
}

#[derive(Debug, Clone)]
pub enum SnekValue {
    Boolean(bool),
    Number(f64),
    Function,
    List(Vec<SnekValue>)
}

impl fmt::Display for SnekValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Boolean(bool) => bool.fmt(f),
            Self::Number(number) => number.fmt(f),
            Self::Function => write!(f, "FUNCTION"),
            Self::List(list) => {
                let list_display = list.iter().map(|v| v.to_string())
                    .join(", ");
                write!(f, "[{}]", list_display)
            }
        }
    }
}

fn collect_cons_to_vec<'a, 'b>(value: &InternalSnekValue<'a, 'b>, vector: &mut Vec<SnekValue>) {
    match value {
        InternalSnekValue::Cons(Cons(Some(value))) => {
            vector.push(value.0.clone().into());
            collect_cons_to_vec(&value.1, vector);
        },
        InternalSnekValue::Cons(Cons(None)) => {},
        non_cons => { vector.push(non_cons.clone().into()); }
    }
}

impl<'a, 'b> From<InternalSnekValue<'a, 'b>> for SnekValue {
    fn from(value: InternalSnekValue<'a, 'b>) -> Self {
        match value {
            InternalSnekValue::Boolean(bool) => Self::Boolean(bool),
            InternalSnekValue::Number(number) => Self::Number(number),
            InternalSnekValue::Function(_) => Self::Function,
            value @ InternalSnekValue::Cons(_) => {
                let mut vector = Vec::new();
                collect_cons_to_vec(&value, &mut vector);
                Self::List(vector)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Frame<'a, 'b: 'a> {
    bindings: RefCell<HashMap<&'b str, InternalSnekValue<'a, 'b>>>,
    parent: Option<Rc<Frame<'a, 'b>>>,
}

impl<'a, 'b> Frame<'a, 'b> {
    fn root(bindings: HashMap<&'b str, InternalSnekValue<'a, 'b>>) -> Rc<Self> {
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

    fn insert(&self, key: &'b str, value: InternalSnekValue<'a, 'b>) {
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

    fn update(&self, key: &'b str, value: InternalSnekValue<'a, 'b>) -> EvaluationResult<'a, 'b> {
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
    Builtin(&'b dyn Fn(Vec<InternalSnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b>),
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
    fn evaluate(&self, values: Vec<InternalSnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
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
    fn evaluate(&self, values: Vec<InternalSnekValue<'a, 'b>>) -> EvaluationResult<'a, 'b> {
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
        Literal::Number(number) => Ok(InternalSnekValue::Number(*number))
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
        InternalSnekValue::Function(function) => function,
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

fn evaluate_let_parameter<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: &Rc<Frame<'a, 'b>>) -> Result<(&'b str, InternalSnekValue<'a, 'b>), SnekError> {
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

fn evaluate_let_parameter_list<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: &Rc<Frame<'a, 'b>>) -> Result<Vec<(&'b str, InternalSnekValue<'a, 'b>)>, SnekError> {
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
        InternalSnekValue::Boolean(true) => evaluate(&list[1], environment),
        InternalSnekValue::Boolean(false) => evaluate(&list[2], environment),
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
            InternalSnekValue::Boolean(false) => return Ok(InternalSnekValue::Boolean(false)),
            InternalSnekValue::Boolean(true) => {},
            _ => return Err(SnekError::SnekEvaluationError)
        }
    }

    Ok(InternalSnekValue::Boolean(true))
}

fn evaluate_or<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: &Rc<Frame<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    // Evalutes an or-expression. If all values in the expression evalutes to false, it returns false, 
    // but if a single value evalutes to true, it returns true. It is an error to have an expression evaluate
    // to a non-boolean value

    for expression in list {
        match evaluate(expression, environment)? 
        { 
            InternalSnekValue::Boolean(true) => return Ok(InternalSnekValue::Boolean(true)),
            InternalSnekValue::Boolean(false) => {},
            _ => return Err(SnekError::SnekEvaluationError)
        }
    }

    Ok(InternalSnekValue::Boolean(false))
}

fn evaluate_not<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: &Rc<Frame<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    // Evalutes a not-expression. It has a single parameter which should evalute to a boolean expression

    if list.len() != 1 { return Err(SnekError::SnekSyntaxError); }
    match evaluate(&list[0], environment)? {
        InternalSnekValue::Boolean(value) => Ok(InternalSnekValue::Boolean(!value)),
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

    let function = InternalSnekValue::Function(Function::Lisp(LispFunction { 
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
    Ok(InternalSnekValue::Function(Function::Lisp(LispFunction {
        parameters,
        expression: &list[1],
        environment: environment.clone()
    })))
}

fn evaluate_cons<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: &Rc<Frame<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    // A cons expression builds a cons cell of the two parameters

    if list.len() != 2 { return Err(SnekError::SnekSyntaxError); }
    Ok(InternalSnekValue::Cons(Cons::new(
        evaluate(&list[0], environment)?,
        evaluate(&list[1], environment)?
    )))
}

fn evaulate_list<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: &Rc<Frame<'a, 'b>>) -> Result<Vec<InternalSnekValue<'a, 'b>>, SnekError> {
    list.into_iter()
        .map(|sexp| evaluate(sexp, environment))
        .collect::<Result<Vec<InternalSnekValue<'a, 'b>>, SnekError>>()
}

fn evaluate<'a, 'b: 'a>(sexp: &'a Sexp<'b>, environment: &Rc<Frame<'a, 'b>>) -> EvaluationResult<'a, 'b> {
    match sexp {
        Sexp::Atom(atom) => evaluate_atom(atom, environment),
        Sexp::Expression(expression) => evaluate_expression(expression, environment)
    }
}

/// An evaluation context that takes sexps and evaluates them to give
/// values. 
/// 
/// It uses a zero-copy approach for sexps, which means the sexps must remain alive as
/// long as the evaluation context is alive, which does pose some restrictions on the user.
/// 
/// If this is too much of a restriction, consider the regular evaluation context
pub struct SexpEvaluationContext<'a, 'b> {
    frame: Rc<Frame<'a, 'b>>
}

impl<'a, 'b> SexpEvaluationContext<'a, 'b> {
    pub fn new() -> Self {
        Self {
            frame: Frame::new(builtin_frame())
        }
    }

    pub fn evaluate_sexp(&mut self, sexp: &'b Sexp<'a>) -> Result<SnekValue, SnekError> {
        let result = evaluate(sexp, &self.frame);
        result.map(|v| v.into())
    }
}

pub struct EvaluationContext<'a, 'b> {
    sexps: Vec<* const Sexp<'a>>,
    frame: Rc<Frame<'a, 'b>>,
}

impl<'a> EvaluationContext<'a, 'static> {
    pub fn new() -> Self {
        Self {
            sexps: Vec::new(),
            frame: Frame::new(builtin_frame())
        }
    }

    pub fn evaluate_str(&mut self, input: &'a str) -> Result<SnekValue, SnekError> {
        let sexp = parser(input)?;
        let ptr = Box::into_raw(Box::new(sexp));
        self.sexps.push(ptr);

        // Safety:
        // The pointer will be alive for as long as the evaluation context is alive,
        // since we never pop from the sexps until we drop
        evaluate(unsafe { &*ptr }, &self.frame)
            .map(|value| value.into())
    }
}

impl<'a, 'b> Drop for EvaluationContext<'a, 'b> {
    fn drop(&mut self) {
        // Safety:
        // All pointers in the vector comes from box
        self.sexps.drain(..).for_each(|ptr| unsafe { Box::from_raw(ptr as *mut Sexp<'a>); });
    }
}

#[cfg(test)]
mod tests {
    use anyhow::bail;
    use itertools::Itertools;

    use crate::test_utils::{all_testcases, load_test_pair, TestEvaluationResult, TestOutput};

    use super::*;

    fn compare_lists(a: &[SnekValue], b: &[TestOutput]) -> bool {
        if a.len() != b.len() { return false; }

        a.into_iter().zip(b.into_iter())
            .all(|(a, b)| compare(a, b))
    }

    fn compare<'a, 'b>(a: &SnekValue, b: &TestOutput) -> bool {
        match (a, b) {
            (_, TestOutput::Something(_)) => true,
            (SnekValue::Number(a), TestOutput::Number(b)) => (a - b).abs() < 1.0e-5,
            (SnekValue::List(a), TestOutput::List(b)) => compare_lists(a, b),
            _ => false
        }
    }

    fn assert_run(testcase: usize, entries: Vec<(String, TestEvaluationResult)>) -> anyhow::Result<()> {
        let mut evaluation_context = SexpEvaluationContext::new();
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
use core::fmt;
use std::{cell::RefCell, collections::HashMap, rc::Rc};

use itertools::Itertools;

use crate::{context::AllocationContext, error::SnekError, parser::{Literal, Sexp}};

pub(crate) type EvaluationResult<'a, 'b> = Result<InternalSnekValue<'a, 'b>, SnekError>;



#[derive(Clone)]
pub(crate) struct Cons<'a, 'b>(pub(crate) Option<Rc<(InternalSnekValue<'a, 'b>, InternalSnekValue<'a, 'b>)>>);

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
pub(crate) enum InternalSnekValue<'a, 'b: 'a> {
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
pub(crate) struct Frame<'a, 'b: 'a> {
    bindings: RefCell<HashMap<&'b str, InternalSnekValue<'a, 'b>>>,
    parent: Option<* const Frame<'a, 'b>>,
}

impl<'a, 'b> Drop for Frame<'a, 'b> {
    fn drop(&mut self) {
        let _  = &mut self.bindings;
        let _ = &mut self.parent;
    }
}

impl<'a, 'b> Frame<'a, 'b> {
    pub(crate) fn root(bindings: HashMap<&'b str, InternalSnekValue<'a, 'b>>, ctx: &mut AllocationContext) -> *const Self {
        ctx.as_ptr(Self {
            parent: None,
            bindings: RefCell::from(bindings)
        })
    }

    pub fn new(parent: *const Frame<'a, 'b>, ctx: &mut AllocationContext) -> *const Self {
        ctx.as_ptr(Self {
            parent: Some(parent),
            bindings: RefCell::new(HashMap::new())
        })
    }

    fn insert(self_: *const Self, key: &'b str, value: InternalSnekValue<'a, 'b>) {
        unsafe { &*self_ }.bindings.borrow_mut().insert(key, value);
    }

    fn get(self_: *const Self, key: &'b str) -> EvaluationResult<'a, 'b> {
        if let Some(value) = unsafe { &*self_ }.bindings.borrow_mut().get(key) {
            return Ok(value.clone())
        }
        match unsafe { &*self_ }.parent.as_ref() {
            Some(parent) => Self::get(*parent, key),
            None => Err(SnekError::SnekNameError)
        }
    }

    fn update(self_: *const Self, key: &'b str, value: InternalSnekValue<'a, 'b>) -> EvaluationResult<'a, 'b> {
        if unsafe { &*self_ }.bindings.borrow().contains_key(key) {
            unsafe { &*self_ }.bindings.borrow_mut().insert(key, value.clone());
            return Ok(value)
        } else {
            match unsafe { &*self_ }.parent {
                Some(parent) => Self::update(parent, key, value),
                None => Err(SnekError::SnekNameError)
            }
        }
    } 
}

#[derive(Clone)]
pub(crate) enum Function<'a, 'b: 'a> {
    Builtin(&'b dyn Fn(Vec<InternalSnekValue<'a, 'b>>, &mut AllocationContext) -> EvaluationResult<'a, 'b>),
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
    pub(crate) fn evaluate(&self, values: Vec<InternalSnekValue<'a, 'b>>, ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
        match self {
            Self::Builtin(builtin) => builtin(values, ctx),
            Self::Lisp(lisp_function) => lisp_function.evaluate(values, ctx)
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct LispFunction<'a, 'b: 'a> {
    parameters: Vec<&'b str>,
    expression: &'a Sexp<'b>,
    environment: *const Frame<'a, 'b>
}

impl<'a, 'b: 'a> LispFunction<'a, 'b> {
    fn evaluate(&self, values: Vec<InternalSnekValue<'a, 'b>>, ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
        // To evaluate a lisp function, it must receive the correct number of variables
        if values.len() != self.parameters.len() { return Err(SnekError::SnekEvaluationError) }

        let environment = Frame::new(self.environment.clone(), ctx);
        for (variable, value) in self.parameters.iter().zip(values.into_iter()) {
            Frame::insert(environment, variable, value);
        }

        evaluate(self.expression, environment, ctx)
    }
}

fn evaluate_atom<'a, 'b>(literal: &'a Literal<'b>, environment: *const Frame<'a, 'b>) -> EvaluationResult<'a, 'b> {
    // An atom is interpreted by looking up the identifier, if it is an identifier, or returning the numerical value
    // it represents

    match literal {
        Literal::Identifier(identifier) => Frame::get(environment, identifier),
        Literal::Number(number) => Ok(InternalSnekValue::Number(*number))
    }
}

fn evaluate_expression<'a, 'b: 'a>(expression: &'a [Sexp<'b>], environment: *const Frame<'a, 'b>, ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    // To interpret an expression, all values in the expression are interpreted in the environment. The first value
    // must be a function, which is then called with the remainder of the arguments. 
    // There are a few special function exceptions that are checked first

    if expression.len() == 0 { return Err(SnekError::SnekEvaluationError) }
    match expression[0] {
        Sexp::Atom(Literal::Identifier(identifier)) => {
            match identifier {
                "lambda" => return evaluate_lambda(&expression[1..], environment, ctx),
                "define" => return evaluate_define(&expression[1..], environment, ctx),
                "if" => return evaluate_if(&expression[1..], environment, ctx),
                "and" => return evaluate_and(&expression[1..], environment, ctx),
                "or" => return evaluate_or(&expression[1..], environment, ctx),
                "not" => return evaluate_not(&expression[1..], environment, ctx),
                "cons" => return evaluate_cons(&expression[1..], environment, ctx),
                "begin" => return evaluate_begin(&expression[1..], environment, ctx),
                "let" => return evaluate_let(&expression[1..], environment, ctx),
                "set!" => return evaluate_set_bang(&expression[1..], environment, ctx),
                _ => {}
            }
        },
        _ => {}
    }

    let function = match evaluate(&expression[0], environment, ctx)? {
        InternalSnekValue::Function(function) => function,
        _ => return Err(SnekError::SnekEvaluationError)
    };

    function.evaluate(evaulate_list(&expression[1..], environment, ctx)?, ctx)
}

fn sexp_list_to_identifiers<'a, 'b: 'a>(list: &'a [Sexp<'b>]) -> Result<Vec<&'b str>, SnekError> {
    list.into_iter()
        .map(|sexp| match sexp {
            Sexp::Atom(Literal::Identifier(identifier)) => Ok(*identifier),
            _ => Err(SnekError::SnekSyntaxError)
        }).collect()
}

fn evaluate_let_parameter<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: *const Frame<'a, 'b>, ctx: &mut AllocationContext) -> Result<(&'b str, InternalSnekValue<'a, 'b>), SnekError> {
    // A let parameter is a sexp of two elements, the first being an atom with the name of the parameter,
    // and the second evalutes to a value for the parameter

    if list.len() != 2 { return Err(SnekError::SnekSyntaxError); }

    let name = match list[0] {
        Sexp::Atom(Literal::Identifier(identifier)) => identifier,
        _ => return Err(SnekError::SnekSyntaxError)
    };

    evaluate(&list[1], environment, ctx)
        .map(|value| (name, value))
}

fn evaluate_let_parameter_list<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: *const Frame<'a, 'b>, ctx: &mut AllocationContext) -> Result<Vec<(&'b str, InternalSnekValue<'a, 'b>)>, SnekError> {
    list.into_iter().map(|sexp| {
        match sexp { 
            Sexp::Expression(expression) => evaluate_let_parameter(&expression, environment, ctx),
            _ => Err(SnekError::SnekSyntaxError)
        }
    }).collect()
}

fn evaluate_let<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: *const Frame<'a, 'b>, ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    // Let statements has two parts. The parameters and the body. The paremeters is an expression in the first
    // element of list, which is a list of two-length sexp expressions, the first being the name (a literal),
    // and the second being a value (to be evaluated). These are set in a new environment where the second index
    // of list is evaluated

    if list.len() != 2 { return Err(SnekError::SnekSyntaxError); }

    let parameters = match &list[0] {
        Sexp::Expression(expression) => evaluate_let_parameter_list(&expression, environment, ctx)?,
        _ => return Err(SnekError::SnekSyntaxError)
    };

    let sub_environment = Frame::new(environment.clone(), ctx);
    for (name, value) in parameters {
        Frame::insert(sub_environment, name, value);
    }

    evaluate(&list[1], sub_environment, ctx)
}

fn evaluate_set_bang<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: *const Frame<'a, 'b>, ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    if list.len() != 2 { return Err(SnekError::SnekSyntaxError); }
    
    let name = match list[0] {
        Sexp::Atom(Literal::Identifier(name)) => name,
        _ => return Err(SnekError::SnekSyntaxError),
    };

    let value = evaluate(&list[1], environment, ctx)?;
    Frame::update(environment, name, value)
}

fn evaluate_begin<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: *const Frame<'a, 'b>, ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    // Begin evaluates all sexps in the list and returns the result of the last evaluation

    if list.len() == 0 { return Err(SnekError::SnekSyntaxError); }

    Ok(list.into_iter()
        .map(|sexp| evaluate(sexp, environment, ctx))
        .collect::<Result<Vec<_>, _>>()?
        .pop()
        .unwrap())
}

fn evaluate_if<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: *const Frame<'a, 'b>, ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    // An if expression evaluates the first value, and if it is true, evaluates the second value, if it is false,
    // evalutes the third value

    if list.len() != 3 { return Err(SnekError::SnekEvaluationError); }

    match evaluate(&list[0], environment, ctx)? {
        InternalSnekValue::Boolean(true) => evaluate(&list[1], environment, ctx),
        InternalSnekValue::Boolean(false) => evaluate(&list[2], environment, ctx),
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn evaluate_and<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: *const Frame<'a, 'b>, ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    // Evalutes an and-expression. If all values in the expression evalutes to true, it returns true, 
    // but if a single value evalutes to false, it returns false. It is an error to have an expression evaluate
    // to a non-boolean value

    for expression in list {
        match evaluate(expression, environment, ctx)? 
        { 
            InternalSnekValue::Boolean(false) => return Ok(InternalSnekValue::Boolean(false)),
            InternalSnekValue::Boolean(true) => {},
            _ => return Err(SnekError::SnekEvaluationError)
        }
    }

    Ok(InternalSnekValue::Boolean(true))
}

fn evaluate_or<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: *const Frame<'a, 'b>, ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    // Evalutes an or-expression. If all values in the expression evalutes to false, it returns false, 
    // but if a single value evalutes to true, it returns true. It is an error to have an expression evaluate
    // to a non-boolean value

    for expression in list {
        match evaluate(expression, environment, ctx)? 
        { 
            InternalSnekValue::Boolean(true) => return Ok(InternalSnekValue::Boolean(true)),
            InternalSnekValue::Boolean(false) => {},
            _ => return Err(SnekError::SnekEvaluationError)
        }
    }

    Ok(InternalSnekValue::Boolean(false))
}

fn evaluate_not<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: *const Frame<'a, 'b>, ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    // Evalutes a not-expression. It has a single parameter which should evalute to a boolean expression

    if list.len() != 1 { return Err(SnekError::SnekSyntaxError); }
    match evaluate(&list[0], environment, ctx)? {
        InternalSnekValue::Boolean(value) => Ok(InternalSnekValue::Boolean(!value)),
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn evaluate_define<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: *const Frame<'a, 'b>, ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
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
            let value = evaluate(&list[1], environment, ctx)?;
            Frame::insert(environment, key, value.clone());
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

    Frame::insert(environment, name[0], function.clone());
    Ok(function)    
}

fn evaluate_lambda<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: *const Frame<'a, 'b>, _ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
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

fn evaluate_cons<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: *const Frame<'a, 'b>, ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    // A cons expression builds a cons cell of the two parameters

    if list.len() != 2 { return Err(SnekError::SnekSyntaxError); }
    Ok(InternalSnekValue::Cons(Cons::new(
        evaluate(&list[0], environment, ctx)?,
        evaluate(&list[1], environment, ctx)?
    )))
}

fn evaulate_list<'a, 'b: 'a>(list: &'a [Sexp<'b>], environment: *const Frame<'a, 'b>, ctx: &mut AllocationContext) -> Result<Vec<InternalSnekValue<'a, 'b>>, SnekError> {
    list.into_iter()
        .map(|sexp| evaluate(sexp, environment, ctx))
        .collect::<Result<Vec<InternalSnekValue<'a, 'b>>, SnekError>>()
}

pub(crate) fn evaluate<'a, 'b: 'a>(sexp: &'a Sexp<'b>, environment: *const Frame<'a, 'b>, ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    match sexp {
        Sexp::Atom(atom) => evaluate_atom(atom, environment),
        Sexp::Expression(expression) => evaluate_expression(expression, environment, ctx)
    }
}



#[cfg(test)]
mod tests {
    use anyhow::bail;

    use crate::{context::EvaluationContext, test_utils::{all_testcases, load_test_pair, TestEvaluationResult, TestOutput}};

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

    fn assert_run(testcase: usize, entries: &[(String, TestEvaluationResult)]) -> anyhow::Result<()> {
        let mut evaluation_context = EvaluationContext::new();
        for (lineno, (source, expected)) in entries.iter().enumerate() {
            let result = evaluation_context.evaluate_str(source.as_str());
            let expected: Result<_, _> = expected.clone().into();

            println!("{}:\n{:?}", source, result);
            match (&result, &expected) {
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
            assert_run(testcase, &entries)?;
        }

        Ok(())
    }
}
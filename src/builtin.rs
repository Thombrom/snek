use std::collections::HashMap;

use crate::{context::AllocationContext, error::SnekError, interpreter::{Cons, EvaluationResult, Frame, Function, InternalSnekValue}};


fn snek_value_list_to_numbers<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>) -> Result<Vec<f64>, SnekError> {
    values.into_iter()
        .map(|value| match value {
            InternalSnekValue::Number(number) => Ok(number),
            _ => Err(SnekError::SnekEvaluationError)
        }).collect()
}

fn builtin_add<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>, _ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    if values.len() == 0 { return Err(SnekError::SnekEvaluationError); }

    // We can only add integers together
    let values = snek_value_list_to_numbers(values)?;
    Ok(InternalSnekValue::Number(values.into_iter().sum()))
}

fn builtin_sub<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>, _ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    if values.len() == 0 { return Err(SnekError::SnekEvaluationError); }

    let values = snek_value_list_to_numbers(values)?;
    if values.len() == 1 { return Ok(InternalSnekValue::Number(values[0] * -1.0)) }
    Ok(InternalSnekValue::Number(values[0] - values[1..].into_iter().sum::<f64>()))
}

fn builtin_mul<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>, _ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    if values.len() == 0 { return Err(SnekError::SnekEvaluationError); }

    let values = snek_value_list_to_numbers(values)?;
    Ok(InternalSnekValue::Number(values.into_iter().reduce(|a, b| a * b).unwrap()))
}

fn builtin_div<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>, _ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
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

fn builtin_greater<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>, _ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    builtin_compare(values, |a, b| a > b)
}

fn builtin_greater_eq<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>, _ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    builtin_compare(values, |a, b| a >= b)
}

fn builtin_less<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>, _ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    builtin_compare(values, |a, b| a < b)
}

fn builtin_less_eq<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>, _ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    builtin_compare(values, |a, b| a <= b)
}

fn builtin_eq<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>, _ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    builtin_compare(values, |a, b| (a - b).abs() < 1.0e-5)
}

fn builtin_list<'a, 'b>(mut values: Vec<InternalSnekValue<'a, 'b>>, _ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    let mut cond = InternalSnekValue::Cons(Cons::nil());

    while let Some(value) = values.pop() {
        cond = InternalSnekValue::Cons(Cons::new(value, cond));
    }

    Ok(cond)
}

fn builtin_car<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>, _ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    if values.len() != 1 { return Err(SnekError::SnekSyntaxError); }

    match &values[0] {
        InternalSnekValue::Cons(Cons(Some(value))) => Ok(value.0.clone()),
        _ => Err(SnekError::SnekEvaluationError)
    }
}   

fn builtin_cdr<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>, _ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
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

fn builtin_length<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>, _ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
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

fn builtin_elt_at_index<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>, _ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    if values.len() != 2 { return Err(SnekError::SnekSyntaxError); }
    match (&values[0], &values[1]) {
        (value, InternalSnekValue::Number(index)) => builtin_elt_at_index_impl(&value, index.round() as usize),
        _ => Err(SnekError::SnekEvaluationError)
    }    
}

fn builtin_concat_impl<'a, 'b>(current: &InternalSnekValue<'a, 'b>, lists: &[InternalSnekValue<'a, 'b>], ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    match current {
        InternalSnekValue::Cons(Cons(None)) => {
            if lists.len() == 0 { return Ok(InternalSnekValue::Cons(Cons::nil())); }
            builtin_concat_impl(&lists[0], &lists[1..], ctx)
        }
        InternalSnekValue::Cons(Cons(Some(cons))) => {
            let cdr = builtin_concat_impl(&cons.1, lists, ctx)?;
            Ok(InternalSnekValue::Cons(Cons::new(cons.0.clone(), cdr)))
        },
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn builtin_concat<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>, ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    if values.len() == 0 { return Ok(InternalSnekValue::Cons(Cons::nil())); }
    builtin_concat_impl(&values[0], &values[1..], ctx)
}

fn builtin_map_impl<'a, 'b>(function: &Function<'a, 'b>, list: &InternalSnekValue<'a, 'b>, ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    match list {
        InternalSnekValue::Cons(Cons(None)) => Ok(list.clone()),
        InternalSnekValue::Cons(Cons(Some(value))) => {
            let cdr = builtin_map_impl(function, &value.1, ctx)?;
            let car = function.evaluate(vec![value.0.clone()], ctx)?;
            Ok(InternalSnekValue::Cons(Cons::new(car, cdr)))
        },
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn builtin_map<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>, ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    if values.len() != 2 { return Err(SnekError::SnekSyntaxError); }

    match &values[0] {
        InternalSnekValue::Function(function) => builtin_map_impl(function, &values[1], ctx),
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn builtin_filter_impl<'a, 'b>(function: &Function<'a, 'b>, list: &InternalSnekValue<'a, 'b>, ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    match list {
        InternalSnekValue::Cons(Cons(None)) => Ok(InternalSnekValue::Cons(Cons::nil())),
        InternalSnekValue::Cons(Cons(Some(value))) => {
            let cdr = builtin_filter_impl(function, &value.1, ctx)?;
            match function.evaluate(vec![value.0.clone()], ctx)? {
                InternalSnekValue::Boolean(true) => Ok(InternalSnekValue::Cons(Cons::new(value.0.clone(), cdr))),
                InternalSnekValue::Boolean(false) => Ok(cdr),
                _ => Err(SnekError::SnekEvaluationError)
            }
        },
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn builtin_filter<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>, ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    if values.len() != 2 { return Err(SnekError::SnekSyntaxError); }

    match &values[0] {
        InternalSnekValue::Function(function) => builtin_filter_impl(function, &values[1], ctx),
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn builtin_reduce_impl<'a, 'b>(function: &Function<'a, 'b>, list: &InternalSnekValue<'a, 'b>, acc: InternalSnekValue<'a, 'b>, ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    match list {
        InternalSnekValue::Cons(Cons(None)) => Ok(acc),
        InternalSnekValue::Cons(Cons(Some(value))) 
            => builtin_reduce_impl(function, &value.1, function.evaluate(vec![acc, value.0.clone()], ctx)?, ctx),
        _ => Err(SnekError::SnekEvaluationError)
    }
}

fn builtin_reduce<'a, 'b>(values: Vec<InternalSnekValue<'a, 'b>>, ctx: &mut AllocationContext) -> EvaluationResult<'a, 'b> {
    if values.len() != 3 { return Err(SnekError::SnekSyntaxError); }

    match &values[0] {
        InternalSnekValue::Function(function) => builtin_reduce_impl(function, &values[1], values[2].clone(), ctx),
        _ => Err(SnekError::SnekEvaluationError)
    }
}

pub(crate) fn builtin_frame<'a, 'b: 'a>(ctx: &mut AllocationContext) -> *const Frame<'a, 'b> {
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
    ]), ctx)
}
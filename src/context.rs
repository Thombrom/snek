use crate::{builtin::builtin_frame, error::SnekError, interpreter::{evaluate, Frame, SnekValue}, parser::{parse, Sexp}};


/// An evaluation context that takes sexps and evaluates them to give
/// values. 
/// 
/// It uses a zero-copy approach for sexps, which means the sexps must remain alive as
/// long as the evaluation context is alive, which does pose some restrictions on the user.
/// 
/// If this is too much of a restriction, consider the regular evaluation context
pub struct BorrowedEvaluationContext<'a, 'b> {
    allocations: AllocationContext,
    frame: *const Frame<'a, 'b>
}

pub struct AllocationContext {
    allocations: Vec<*const ()> 
}

impl AllocationContext {
    pub fn new() -> Self {
        Self { allocations: Vec::new() }
    }

    #[allow(dyn_drop)]
    pub fn as_ptr<T>(&mut self, value: T) -> *const T {
        let ptr = Box::into_raw(Box::new(value));
        self.allocations.push(ptr as *const ());
        ptr
    }

    #[allow(dyn_drop)]
    pub unsafe fn drop(&mut self) {
        self.allocations.drain(..).for_each(|ptr| {
            drop(unsafe { Box::from_raw(ptr as *mut ()) })
        })
    }
}

impl<'a, 'b> BorrowedEvaluationContext<'a, 'b> {
    pub fn new() -> Self {
        let mut ctx = AllocationContext::new();
        let frame = Frame::new(builtin_frame(&mut ctx), &mut ctx);

        Self {
            allocations: ctx,
            frame
        }
    }

    pub fn evaluate_sexp(&mut self, sexp: &'b Sexp<'a>) -> Result<SnekValue, SnekError> {
        let result = evaluate(sexp, self.frame, &mut self.allocations);
        result.map(|v| v.into())
    }
}

impl<'a, 'b> Drop for BorrowedEvaluationContext<'a, 'b> {
    fn drop(&mut self) {
        unsafe { self.allocations.drop() }
    }
}

pub struct OwnedEvaluationContext<'a, 'b> {
    allocations: AllocationContext,
    sexps: Vec<* const Sexp<'a>>,
    frame: *const Frame<'a, 'b>,
}

impl<'a, 'b> OwnedEvaluationContext<'a, 'b> {
    pub fn new() -> Self {
        let mut ctx = AllocationContext::new();
        let frame = Frame::new(builtin_frame(&mut ctx), &mut ctx);

        Self {
            allocations: ctx,
            sexps: Vec::new(),
            frame: frame
        }
    }

    pub fn evaluate_str(&mut self, input: &'a str) -> Result<SnekValue, SnekError> {
        let sexp = parse(input)?;
        let ptr = Box::into_raw(Box::new(sexp));
        self.sexps.push(ptr);

        // Safety:
        // The pointer will be alive for as long as the evaluation context is alive,
        // since we never pop from the sexps until we drop
        evaluate(unsafe { &*ptr }, self.frame, &mut self.allocations)
            .map(|value| value.into())
    }

    // TODO: Define trait that will allow us to accept &str and String in 
    // the same method
    pub fn evaluate_string(&mut self, input: String) -> Result<SnekValue, SnekError> {
        let string_ref = self.allocations.as_ptr(input);
        self.evaluate_str(unsafe { &*string_ref }.as_str())
    }
}

impl<'a, 'b> Drop for OwnedEvaluationContext<'a, 'b> {
    fn drop(&mut self) {
        // Safety:
        // All pointers in the vector comes from box
        self.sexps.drain(..).for_each(|ptr| unsafe { drop(Box::from_raw(ptr as *mut Sexp<'a>)); });
        unsafe { self.allocations.drop() }
    }
}
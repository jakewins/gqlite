use crate::{Cursor, Error};
use crate::frontend::{LogicalPlan, Tokenizer};
use std::fmt::Debug;
use std::rc::Rc;

pub trait PreparedStatement: Debug {
    fn run(&mut self, cursor: &mut Cursor) -> Result<(), Error>;
}

// I don't know if any of this makes any sense, but the thoughts here is like.. lets make it
// easy to build experimental backends, that can convert a logical plan tree into something that
// can be executed. I've tried really hard to avoid making this trait have generics on it,
// though I'm not sure it's possible to maintain that invariant.. It does simplify a lot of stuff
// in the planning side and in the API to not have to deal with different backends having different
// generics. Much of that difficulty is likely my poor Rust skills tho.
pub trait Backend: Debug {
    fn tokenizer(&self) -> Rc<dyn Tokenizer>;

    // Convert a logical plan into something executable
    fn prepare(&self, plan: LogicalPlan) -> Result<Box<dyn PreparedStatement>, Error>;
}

pub(crate) mod gram;
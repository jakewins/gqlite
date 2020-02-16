//
// Backends implement the actual storage of graphs, and provide implementations of the
// logical operators the frontend emits that can act on that storage.
//
use crate::{Cursor, Error};
use crate::frontend::{LogicalPlan};
use std::fmt::Debug;
use std::rc::Rc;
use std::cell::RefCell;
use std::collections::HashMap;

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
    fn tokens(&self) -> Rc<RefCell<Tokens>>;

    // Convert a logical plan into something executable
    fn prepare(&self, plan: Box<LogicalPlan>) -> Result<Box<dyn PreparedStatement>, Error>;
}


// gql databases are filled with short string keys. Both things stored in the graph, like property
// keys, labels and relationship types. But also strings used for identifiers in queries, like
// "n" in `MATCH (n)`.
// These are easier for the database to work with, since they are fixed size stack allocated values.
pub type Token = usize;

// Simple in-memory string-to-token mapper.
#[derive(Debug)]
pub struct Tokens {
    table: HashMap<String, Token>,
}

impl Tokens {
    pub fn new() -> Tokens {
        Tokens{ table: Default::default() }
    }
    pub fn lookup(&self, tok: usize) -> Option<&str> {
        for (content, candidate) in self.table.iter() {
            if *candidate == tok {
                return Some(&content);
            }
        }
        return None
    }

    pub fn tokenize(&mut self, content: &str) -> usize {
        match self.table.get(content) {
            Some(tok) => { return *tok }
            None => {
                let tok = self.table.len();
                self.table.insert(content.to_string(), tok);
                return tok
            }
        }
    }
}

#[cfg(feature = "gram")]
pub(crate) mod gram;

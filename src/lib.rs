extern crate pest;
#[macro_use]
extern crate pest_derive;

mod backend;
mod frontend;

use std::fmt::{Display, Formatter, Debug};
use std::fmt;

use backend::Backend;
use crate::frontend::Frontend;

#[derive(Debug)]
pub struct Database {
    backend: Box<dyn Backend>,
    frontend: Frontend,
}

impl Database {
    pub fn open(path: &str) -> Result<Database, Error> {
        let backend = backend::gram::GramBackend::open(path)?;
        let frontend = Frontend{ tokens: backend.tokens() };
        return Ok(Database {
            backend: Box::new(backend),
            frontend,
        })
    }

    // TODO obviously the query string shouldn't be static
    pub fn run(&mut self, query_str: &'static str, cursor: &mut Cursor) -> Result<(), Error> {
        let plan = self.frontend.plan(query_str)?;

        println!("plan: {:?}", plan);

        let mut row = Row{ slots: vec![] };
        let mut prepped = self.backend.prepare(Box::new(plan))?;

        // The API then allows us to modify this to reuse existing CursorState if we like
        prepped.run(cursor)
    }
}

// Backends provide this
pub trait CursorState : Debug {
    fn next(&mut self, row:  &mut Row) -> Result<bool, Error>;
}

// Cursors are like iterators, except they don't require malloc for each row; the row you read is
// valid until next time you call "next", or until the transaction you are in is closed.
#[derive(Debug)]
pub struct Cursor {
    state: Option<Box<dyn CursorState>>,
    row: Row,
}

impl Cursor {
    pub fn new() -> Cursor {
        return Cursor {
            state: None,
            row: Row { slots: vec![] }
        }
    }
    pub fn next(&mut self) -> Result<bool, Error> {
        match &mut self.state {
            Some(state) => {
                return state.next(&mut self.row)
            }
            None => {
                panic!("Use of uninitialized cursor")
            }
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Dir {
    Out, In
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Error {
    // TODO I think maybe this should be &str?
    msg: String,
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        f.write_str(&self.msg)
    }
}

impl std::convert::From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Error{ msg: format!("from io.error: {:?}", e) }
    }
}

impl std::convert::From<pest::error::Error<frontend::Rule>> for Error {
    fn from(e: pest::error::Error<frontend::Rule>) -> Self {
        Error{ msg: format!("{}", e)}
    }
}

#[derive(Debug)]
pub struct Row {
    slots: Vec<Val>
}

// Pointer to a Val in a row
pub type Slot = usize;

#[derive(Debug,Clone,PartialEq)]
pub enum Val {
    Null,
    String(String),
    Node(usize),
    Rel{ node: usize, rel_index: usize },
}

impl Val {
    fn as_node_id(&self) -> usize {
        match self {
            Val::Node(id) => *id,
            _ => panic!("invalid execution plan, non-node value feeds into thing expecting node value")
        }
    }
}

impl Display for Val {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Val::Null=> f.write_str("NULL"),
            Val::String(s) => f.write_str(&s),
            Val::Node(id) => f.write_str(&format!("Node({})", id)),
            Val::Rel{node, rel_index} => f.write_str(&format!("Rel({}/{})", node, rel_index))
        }
    }
}

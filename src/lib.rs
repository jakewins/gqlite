extern crate pest;
#[macro_use]
extern crate pest_derive;
#[macro_use]
extern crate anyhow;
extern crate rand;

pub mod backend;
pub mod frontend;

pub use anyhow::{Error, Result};
use std::fmt::{self, Debug, Display, Formatter};
#[cfg(feature = "gram")]
use std::fs::File;

use crate::frontend::Frontend;
use backend::Backend;

#[derive(Debug)]
pub struct Database {
    backend: Box<dyn Backend>,
    frontend: Frontend,
}

impl Database {
    #[cfg(feature = "gram")]
    pub fn open(file: File) -> Result<Database> {
        let backend = backend::gram::GramBackend::open(file)?;
        Database::with_backend(Box::new(backend))
    }

    pub fn with_backend(backend: Box<dyn Backend>) -> Result<Database, Error> {
        let frontend = Frontend {
            tokens: backend.tokens(),
            backend_desc: backend.describe()?,
        };
        Ok(Database { backend, frontend })
    }

    pub fn run(&mut self, query_str: &str, cursor: &mut Cursor) -> Result<(), Error> {
        let plan = self.frontend.plan(query_str)?;
        let mut prepped = self.backend.prepare(Box::new(plan))?;

        // The API then allows us to modify this to reuse existing CursorState if we like
        prepped.run(cursor)
    }
}

// Backends provide this
pub trait CursorState: Debug {
    fn next(&mut self, row: &mut Row) -> Result<bool>;
}

// Cursors are like iterators, except they don't require malloc for each row; the row you read is
// valid until next time you call "next", or until the transaction you are in is closed.
#[derive(Debug, Default)]
pub struct Cursor {
    pub state: Option<Box<dyn CursorState>>,
    pub row: Row,
}

impl Cursor {
    pub fn new() -> Cursor {
        Cursor::default()
    }

    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Result<bool> {
        match &mut self.state {
            Some(state) => state.next(&mut self.row),
            None => panic!("Use of uninitialized cursor"),
        }
    }
}

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum Dir {
    Out,
    In,
}
impl Dir {
    fn reverse(self) -> Self {
        match self {
            Dir::Out => Dir::In,
            Dir::In => Dir::Out,
        }
    }
}

#[derive(Debug, Default)]
pub struct Row {
    pub slots: Vec<Val>,
}

// Pointer to a Val in a row
pub type Slot = usize;

// openCypher 9 enumeration of types
#[derive(Debug)]
pub enum Type {
    // This is not a documented part of the openCypher type system, but.. well I'm not sure how
    // else we represent the arguments to a function like count(..).
    Any,

    // Integers and floats are both Numbers
    Number,
    // The spec does not specify a maximum bit size, it just says "exact number without decimal"
    Integer,
    // IEEE-754 64-bit float
    Float,

    // Unicode string
    String,
    Boolean,

    Node,
    Relationship,
    Path,

    List(Box<Type>),
    Map,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Val {
    Null,
    String(String),
    Node(usize),
    Rel { node: usize, rel_index: usize },
}

impl Val {
    pub fn as_node_id(&self) -> usize {
        match self {
            Val::Node(id) => *id,
            _ => panic!(
                "invalid execution plan, non-node value feeds into thing expecting node value"
            ),
        }
    }
    pub fn as_string_literal(&self) -> &str {
        match self {
            Val::String(string) => &**string, // TODO: not clone
            _ => panic!(
                "invalid execution plan, non-property value feeds into thing expecting node value"
            ),
        }
    }
}

impl Display for Val {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Val::Null => f.write_str("NULL"),
            Val::String(s) => f.write_str(&s),
            Val::Node(id) => f.write_str(&format!("Node({})", id)),
            Val::Rel { node, rel_index } => f.write_str(&format!("Rel({}/{})", node, rel_index)),
        }
    }
}

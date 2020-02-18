extern crate pest;
#[macro_use]
extern crate pest_derive;
#[macro_use]
extern crate anyhow;

pub mod backend;
pub mod frontend;

pub use anyhow::{Error, Result};
use std::fmt::{self, Debug, Display, Formatter};
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
    pub fn open(file: &mut File) -> Result<Database> {
        let backend = backend::gram::GramBackend::open(file)?;
        let frontend = Frontend {
            tokens: backend.tokens(),
        };
        Ok(Database {
            backend: Box::new(backend),
            frontend,
        })
    }

    pub fn with_backend(backend: Box<dyn Backend>) -> Result<Database> {
        let frontend = Frontend {
            tokens: backend.tokens(),
        };
        Ok(Database { backend, frontend })
    }

    pub fn run(&mut self, query_str: &str, cursor: &mut Cursor) -> Result<()> {
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

#[derive(Debug, PartialEq)]
pub enum Dir {
    Out,
    In,
}

#[derive(Debug, Default)]
pub struct Row {
    pub slots: Vec<Val>,
}

// Pointer to a Val in a row
pub type Slot = usize;

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

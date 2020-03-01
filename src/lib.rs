extern crate pest;
#[macro_use]
extern crate pest_derive;
#[macro_use]
extern crate anyhow;

pub mod backend;
pub mod frontend;

pub use anyhow::{Error, Result};
use std::fmt::{self, Debug, Display, Formatter};
#[cfg(feature = "gram")]
use std::fs::File;

use crate::frontend::Frontend;
use backend::{Backend, PreparedStatement};
use std::cmp::Ordering;

#[derive(Debug)]
pub struct Database<T: Backend> {
    backend: T,
    frontend: Frontend,
}

type BackendState<T> = <<T as Backend>::Statement as PreparedStatement>::State;

impl<T: Backend> Database<T> {
    pub fn with_backend(backend: T) -> Result<Database<T>> {
        let frontend = Frontend {
            tokens: backend.tokens(),
            backend_desc: backend.describe()?,
        };
        Ok(Database { backend, frontend })
    }

    pub fn run(
        &mut self,
        query_str: &str,
        cursor: &mut Cursor<BackendState<T>>,
    ) -> Result<(), Error> {
        let plan = self.frontend.plan(query_str)?;
        let prepped = self.backend.prepare(plan)?;

        // The API then allows us to modify this to reuse existing CursorState if we like
        PreparedStatement::run(prepped, cursor)
    }
}

#[cfg(feature = "gram")]
pub type GramDatabase = Database<backend::gram::GramBackend>;

#[cfg(feature = "gram")]
pub type GramCursor = Cursor<backend::gram::GramCursorState>;

#[cfg(feature = "gram")]
impl Database<backend::gram::GramBackend> {
    pub fn open(file: File) -> Result<Database<backend::gram::GramBackend>> {
        let backend = backend::gram::GramBackend::open(file)?;
        Database::with_backend(backend)
    }
}

// Backends provide this
pub trait CursorState: Debug {
    fn next(&mut self, row: &mut Row) -> Result<bool>;
    // Convert a column index (as specified by the ordering in RETURN ..) to a slot in row;
    // this is a side-effect of us also keeping temporary values in the row struct, so the
    // mapping is not (currently) 1-1. You could make an argument that we should fix this
    // by reorganizing slot assignments in the planner once it plans RETURN, so those outputs
    // go in the right places. That also ties into the planner being smart enough to reuse
    // slots that are no longer needed in different parts of the pipeline..
    //
    // Another alternative is to have each operator own it's own Row instance, copying values out
    // to an output row?
    fn slot_index(&self, index: usize) -> usize;
}

// Cursors are like iterators, except they don't require malloc for each row; the row you read is
// valid until next time you call "next", or until the transaction you are in is closed.
#[derive(Debug)]
pub struct Cursor<S: CursorState> {
    pub state: Option<S>,
    pub row: Row,
}

impl<S: CursorState> Cursor<S> {
    pub fn new() -> Cursor<S> {
        Cursor {
            state: None,
            row: Row::default(),
        }
    }

    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Result<bool> {
        match &mut self.state {
            Some(state) => state.next(&mut self.row),
            None => panic!("Use of uninitialized cursor"),
        }
    }

    pub fn get(&self, index: usize) -> &Val {
        // Sorry this is a giant mess lol
        let slot = self.state.as_ref().unwrap().slot_index(index);
        &self.row.slots[slot]
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
#[derive(Debug, Clone)]
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
    List(Vec<Val>),
    Int(i64),
    Float(f64),
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

impl PartialOrd for Val {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self {
            Val::Int(self_v) => match other {
                Val::String(_) => Some(Ordering::Greater),
                Val::Int(other_v) => self_v.partial_cmp(other_v),
                Val::Float(other_v) => self_v.partial_cmp(&&(*other_v as i64)),
                Val::List(_) => Some(Ordering::Greater),
                Val::Null => None,
                _ => panic!("Don't know how to compare {:?} to {:?}", self, other),
            },
            Val::Float(self_v) => match other {
                Val::String(_) => Some(Ordering::Greater),
                Val::Int(other_v) => (*self_v).partial_cmp(&(*other_v as f64)),
                Val::Float(other_v) => (*self_v).partial_cmp(other_v),
                Val::List(_) => Some(Ordering::Greater),
                Val::Null => None,
                _ => panic!("Don't know how to compare {:?} to {:?}", self, other),
            },
            Val::String(self_v) => match other {
                Val::Int(_) => Some(Ordering::Less),
                Val::Float(_) => Some(Ordering::Less),
                Val::String(other_v) => self_v.partial_cmp(other_v),
                Val::List(_) => Some(Ordering::Greater),
                Val::Null => None,
                _ => panic!("Don't know how to compare {:?} to {:?}", self, other),
            },
            Val::List(self_v) => match other {
                Val::String(_) => Some(Ordering::Less),
                Val::Int(_) => Some(Ordering::Less),
                Val::Float(_) => Some(Ordering::Less),
                Val::List(other_v) => self_v.partial_cmp(&other_v),
                Val::Null => None,
                _ => panic!("Don't know how to compare {:?} to {:?}", self, other),
            },
            Val::Null => match other {
                _ => None,
            },
            _ => panic!("Don't know how to compare {:?} to {:?}", self, other),
        }
    }
}

impl Display for Val {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Val::Null => f.write_str("NULL"),
            Val::String(s) => f.write_str(&s),
            Val::List(vs) => f.write_str(&format!("{:?}", vs)),
            Val::Node(id) => f.write_str(&format!("Node({})", id)),
            Val::Rel { node, rel_index } => f.write_str(&format!("Rel({}/{})", node, rel_index)),
            Val::Int(v) => f.write_str(&format!("{}", v)),
            Val::Float(v) => f.write_str(&format!("{}", v)),
        }
    }
}

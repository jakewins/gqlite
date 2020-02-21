//
// Backends implement the actual storage of graphs, and provide implementations of the
// logical operators the frontend emits that can act on that storage.
//
use crate::frontend::LogicalPlan;
use crate::{Cursor, Error, Type};
use anyhow::Result;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::rc::Rc;

pub trait PreparedStatement: Debug {
    fn run(&mut self, cursor: &mut Cursor) -> Result<()>;
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

    // Describe this backend for the frontends benefit
    fn describe(&self) -> Result<BackendDesc, Error>;
}

// Describes, for the frontend, the layout of the backend. This is intended to include things
// like schema (which the planner can take advantage of to perform optimizations), but also
// type signatures of functions and perhaps listings of available special features for the planner
// to use.
#[derive(Debug)]
pub struct BackendDesc {
    pub functions: Vec<FuncSignature>,
    // Fast lookup of functions that aggregate
    pub aggregates: HashSet<Token>,
}

impl BackendDesc {
    pub fn new(functions: Vec<FuncSignature>) -> BackendDesc {
        let mut aggregates = HashSet::new();
        for f in &functions {
            if let FuncType::Aggregating = f.func_type {
                aggregates.insert(f.name);
            }
        }
        return BackendDesc {
            functions,
            aggregates,
        };
    }
}

#[derive(Debug)]
pub enum FuncType {
    // If you imagine cypher as a stream processing system, each operator consumes one or more
    // input streams and yields an output stream. In expressions with scalar functions, each
    // input row maps to one output row.
    //
    // For example, the following query involves a scalar function:
    //
    //   MATCH (n) RETURN id(n)
    //
    // The MATCH (n) part yields a stream of every node in the graph, and the RETURN id(n) part
    // operates on one row at a time, yielding an output row with the node id for each input row.
    Scalar,
    // Aggregating functions change the operator cardinality - an operator with aggregating functions
    // may yield output rows than it consumed. For instance, this query:
    //
    //   MATCH (n) RETURN count(n)
    //
    // Here, the "MATCH (n)" part yields a stream of every node in the graph. The "RETURN count(n)"
    // part consumes that stream, and yields exactly one row with the count. The "count" function
    // is aggregating rows.
    //
    // There are examples of aggregations yielding more than one row, when grouping is involved:
    //
    //   MATCH (n) RETURN n.age, count(n)
    //
    Aggregating,
}

// See the "functions" section in the openCypher spec https://s3.amazonaws.com/artifacts.opencypher.org/openCypher9.pdf
#[derive(Debug)]
pub struct FuncSignature {
    // Aggregate or scalar?
    pub func_type: FuncType,
    // Name of this function
    pub name: Token,
    // Return type
    pub returns: Type,
    // Named arguments
    pub args: Vec<(Token, Type)>,
}

// gql databases are filled with short string keys. Both things stored in the graph, like property
// keys, labels and relationship types. But also strings used for identifiers in queries, like
// "n" in `MATCH (n)`.
// These are easier for the database to work with, since they are fixed size stack allocated values.
pub type Token = usize;

// Simple in-memory string-to-token mapper.
#[derive(Debug, Default)]
pub struct Tokens {
    pub table: HashMap<String, Token>,
}

impl Tokens {
    pub fn new() -> Tokens {
        Tokens::default()
    }

    pub fn lookup(&self, tok: usize) -> Option<&str> {
        for (content, candidate) in self.table.iter() {
            if *candidate == tok {
                return Some(&content);
            }
        }
        None
    }

    pub fn tokenize(&mut self, content: &str) -> usize {
        match self.table.get(content) {
            Some(tok) => *tok,
            None => {
                let tok = self.table.len();
                self.table.insert(content.to_string(), tok);
                tok
            }
        }
    }
}

#[cfg(feature = "gram")]
pub(crate) mod gram;

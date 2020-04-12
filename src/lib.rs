extern crate pest;
#[macro_use]
extern crate pest_derive;
#[macro_use]
extern crate anyhow;

pub mod backend;
pub mod frontend;

pub use anyhow::{Error, Result};
use std::fmt::{Debug};

use frontend::Frontend;
use backend::{Backend, BackendCursor};

#[derive(Debug)]
pub struct Database<T: Backend> {
    backend: T,
    frontend: Frontend,
}

impl<T: Backend> Database<T> {
    pub fn with_backend(backend: T) -> Result<Database<T>> {
        let frontend = Frontend {
            tokens: backend.tokens(),
            backend_desc: backend.describe()?,
        };
        Ok(Database { backend, frontend })
    }

    // TODO this is a side-effect, presumably, of me being bad at rust.
    //      I'd like the public API to not require end-users to specify
    //      generics everywhere, so they do not have them rewrite their
    //      code if they swap backend.. but *at the same time* I don't
    //      want to pay for dynamic dispatch in the hot loop of cursor
    //      next and accessor methods.
    //      So.. for now we lose the part where users can change backends
    //      without rewriting their code. Benchmarking and exploration to
    //      follow!
    pub fn new_cursor(&mut self) -> Cursor<T> {
        let bc = self.backend.new_cursor();
        Cursor{
            inner: bc
        }
    }

    pub fn run(&mut self, query_str: &str, cursor: &mut Cursor<T>) -> Result<()> {
        let plan = self.frontend.plan(query_str)?;
        self.backend.eval(plan, &mut cursor.inner)
    }
}

// A result cursor; the cursor, when in use, points to a current record and lets you access it.
// It is approximately the same thing as an iterator, except it doesn't need to allocate on each
// iteration.
//
// We are kind of having the same issue as discussed here:
// https://www.reddit.com/r/rust/comments/303a09/looking_for_more_information_on_streaming/cpoysog/
//
// Eg. this is efficient, but very unergonomic. I think the solution - for now, at least? -
// is to have a "sugared" version where you can get an iterator out of a cursor, so if you are
// ok to pay a small performance penalty you get back the regular Rust iteration API.
//
// In fact, the sugared version should probably be the default thing you interact with, with an
// option to drop down to a non-allocating core API if you like.
//
// If this could return a borrow on next(..), then you may have an API that both feels ergonomic
// and is efficient.. we could at least do this with a try_fold version, which is likely faster
// as well.
//
// TL;DR: This is all up in the air. Design goals are to make zero-allocation *possible* and the
//        default API *easy*, potentially by having two APIs.
pub struct Cursor<B: Backend> {
    inner: B::Cursor
}

impl<B: Backend> Cursor<B> {
    pub fn next(&mut self) -> Result<bool> {
        self.inner.next()
    }
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

#[cfg(feature = "gram")]
pub mod gramdb {
    use super::{Database, Cursor, Result};
    use crate::backend::gram;
    use std::fs::File;

    pub type GramDatabase = Database<gram::GramBackend>;
    pub type GramCursor = Cursor<gram::GramBackend>;

    impl GramDatabase {
        pub fn open(file: File) -> Result<GramDatabase> {
            let backend = gram::GramBackend::open(file)?;
            Database::with_backend(backend)
        }
    }
}
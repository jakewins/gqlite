
## Structure

gqlite exposes three main API surfaces

- the `gqlite` rust library, at [src/lib.rs]
- the `g` program, at [src/main.rs] 
- the libgqlite c bindings to the rust library, at [gqlite-capi/src/lib.rs]

The `g` program and the libgqlite c bindings are both wrappers around the gqlite rust library.

### Internal structure

gqlite is organized into a "frontend" and a "backend". The frontend contains the parser and planner. 
Backends contain storage and provides executable implementations of the logical operators emitted by the frontend.

# Getting Started

To build everything, ensure that you have Cargo and Rust installed.

## Build

```
cargo build
```

## Run

The repo comes with a small graph in gram file format, representing the characters in Les Miserables.
To run a "hello world" example, let's apply a simple cypher query that pulls out character names.

```
$ ./target/debug/g -f miserables.gram 'MATCH (n:Person) RETURN n.name'
built pg: PatternGraph { e: {8: PatternNode { identifier: 8, labels: [0], props: [], solved: false }}, e_order: [8], v: [] }
plan: Return { src: NodeScan { src: Argument, slot: 0, labels: Some(0) }, projections: [Projection { expr: Prop(Slot(0), [2]), alias: 9, dst: 1 }] }
----
9
----
"Napoleon"
"Myriel"
"Mlle.Baptistine"
"Mme.Magloire"
"CountessdeLo"
"Geborand"
```

## Test

```
$ cargo test
(...)
test result: ok. 14 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out
```

# Limitations

This code is currently under development and only supports a small subset of the Cypher language.  Trying certain
cypher queries may result in errors about "The gram backend does not support this expression type yet" or other syntax
errors.

The subset of Cypher that is currently supported is best described by the grammar found in `src/backend`, and should
expand over time.

# License

This is not (yet) available under an open source license, the source is simply available for reading.

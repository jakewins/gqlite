
## Structure

gqlite exposes three main API surfaces

- the gqlite rust library, at [src/lib.rs]
- the gqlite program, at [src/main.rs] 
- the libgqlite c bindings to the rust library, at [gqlite-capi/src/lib.rs]

The `gqlite` program and the libgqlite c bindings are both wrappers around the gqlite rust library.

### Internal structure

gqlite is organized into a "frontend" and a "backend". The frontend contains the parser and planner. 
Backends take logical plans from the frontend and convert them to an executable form. 
There is wide leeway for how backends go about their business.

# License

This is not (yet) available under an open source license, the source is simply available for reading.
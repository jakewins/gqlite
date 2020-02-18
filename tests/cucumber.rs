use cucumber::{after, before, cucumber, Step, steps};
use gqlite::{Cursor, Database};
use tempfile::tempfile;

pub struct GraphProperties {
    node_count: i32,
    relationship_count: i32,
}

fn empty_db() -> Database {
    Database::open(&mut tempfile().unwrap()).unwrap()
}

pub struct MyWorld {
    // You can use this struct for mutable context in scenarios.
    graph: Database,
    starting_graph_properties: GraphProperties,
    result: Cursor,
}

impl cucumber::World for MyWorld {}

impl std::default::Default for MyWorld {

    fn default() -> MyWorld {

        // This function is called every time a new scenario is started
        MyWorld {
            graph: empty_db(),
            result: Cursor::new(),
            starting_graph_properties: GraphProperties {
                node_count: 0,
                relationship_count: 0,
            },
        }
    }
}


mod example_steps {
    use cucumber::{Step, steps};
    use gqlite::{Cursor, Database, Error};
    use super::{MyWorld, empty_db};

    // TODO: The reason for this is that the cursor borrows part of the query string when you
    //       run a query, and rather than deal with setting proper lifetimes for that I think we can
    //       get rid of that memory sharing entirely, maybe? Although maybe the borrow is actually
    //       kind of sensible; it'd mean queries with large string properties don't need to copy those
    //       strings in, for instance..
    fn string_to_static_str(s: &str) -> &'static str {
        Box::leak(s.to_string().into_boxed_str())
    }

    fn run_preparatory_query(world: &mut MyWorld, step: &Step) -> Result<(), Error> {
        let mut cursor = Cursor::new();
        let result = world.graph.run(string_to_static_str(&step.docstring().unwrap()), &mut cursor);
        while cursor.next()? {
            // consume
        }
        return result;
    }

    fn start_query(world: &mut MyWorld, step: &Step) {
        world.graph.run(string_to_static_str(&step.docstring().unwrap()), &mut world.result).expect("Should not fail")
    }

    fn count_rows(result: &mut Cursor) -> Result<i32, Error> {
        let mut ct = 0;
        while result.next()? {
            ct += 1
        }
        return Ok(ct);
    }

    fn count_nodes(world: &mut MyWorld) -> i32 {
        let mut cursor = Cursor::new();
        world.graph.run(string_to_static_str(&"MATCH (n) RETURN n"), &mut cursor).expect("should succeed");
        return count_rows(&mut cursor).unwrap();
    }

    fn assert_side_effect(world: &mut MyWorld, kind: &str, val: &str) {
        match kind {
            "+nodes" => assert_eq!(count_nodes(world) - world.starting_graph_properties.node_count, val.parse::<i32>().unwrap()),
            _ => panic!(format!("unknown side effect: '{}'", kind))
        }
    }

    // Any type that implements cucumber::World + Default can be the world
    steps!(crate::MyWorld => {
        given "any graph" |world, step| {
            // Don't need to do anything
        };

        given "an empty graph" |world, step| {
            world.graph = empty_db();
        };

        given "having executed:" |world, step| {
            run_preparatory_query(world, step);
        };

        when "executing query:" |world, step| {
            // Take actions
            start_query(world, step)
        };

        then "the result should be empty" |world, step| {
            // Check that the outcomes to be observed have occurred
            assert_eq!(0, count_rows(&mut world.result).unwrap());
        };

        then "the side effects should be:" |world, step| {
            // Check that the outcomes to be observed have occurred
            let table = step.table().unwrap().clone();
            table.rows.iter().for_each(|row| assert_side_effect(world, &row[0], &row[1]));
        };
    });
}

// Declares a before handler function named `a_before_fn`
before!(a_before_fn => |scenario| {

});

// Declares an after handler function named `an_after_fn`
after!(an_after_fn => |scenario| {

});

// A setup function to be called before everything else
fn setup() {}

cucumber! {
    features: "./features/supported", // Path to our feature files
    world: crate::MyWorld, // The world needs to be the same for steps and the main cucumber call
    steps: &[
        example_steps::steps // the `steps!` macro creates a `steps` function in a module
    ],
    setup: setup, // Optional; called once before everything
    before: &[
        a_before_fn // Optional; called before each scenario
    ],
    after: &[
        an_after_fn // Optional; called after each scenario
    ]
}
use cucumber::{after, before, cucumber};
use gqlite::{Cursor, Database};
use tempfile::tempfile;

pub struct GraphProperties {
    node_count: i32,
    _relationship_count: i32,
}

fn empty_db() -> Database {
    Database::open(tempfile().unwrap()).unwrap()
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
                _relationship_count: 0,
            },
        }
    }
}

mod example_steps {
    use super::{empty_db, MyWorld};
    use cucumber::{steps, Step};
    use gqlite::{Cursor, Error};

    fn run_preparatory_query(world: &mut MyWorld, step: &Step) -> Result<(), Error> {
        let mut cursor = Cursor::new();
        let result = world.graph.run(&step.docstring().unwrap(), &mut cursor);
        while cursor.next()? {
            // consume
        }
        result
    }

    fn start_query(world: &mut MyWorld, step: &Step) {
        world
            .graph
            .run(&step.docstring().unwrap(), &mut world.result)
            .expect("Should not fail")
    }

    fn count_rows(result: &mut Cursor) -> Result<i32, Error> {
        let mut ct = 0;
        while result.next()? {
            ct += 1
        }
        Ok(ct)
    }

    fn count_nodes(world: &mut MyWorld) -> i32 {
        let mut cursor = Cursor::new();
        world
            .graph
            .run("MATCH (n) RETURN n", &mut cursor)
            .expect("should succeed");
        count_rows(&mut cursor).unwrap()
    }

    fn assert_side_effect(world: &mut MyWorld, kind: &str, val: &str) {
        match kind {
            "+nodes" => assert_eq!(
                count_nodes(world) - world.starting_graph_properties.node_count,
                val.parse::<i32>().unwrap()
            ),
            _ => panic!(format!("unknown side effect: '{}'", kind)),
        }
    }

    // Any type that implements cucumber::World + Default can be the world
    steps!(crate::MyWorld => {
        given "any graph" |_world, _step| {
            // Don't need to do anything
        };

        given "an empty graph" |world, _step| {
            world.graph = empty_db();
        };

        given "having executed:" |world, step| {
            run_preparatory_query(world, step).unwrap();
        };

        when "executing query:" |world, step| {
            // Take actions
            start_query(world, step)
        };

        then "the result should be empty" |world, _step| {
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
before!(a_before_fn => |_scenario| {

});

// Declares an after handler function named `an_after_fn`
after!(an_after_fn => |_scenario| {

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

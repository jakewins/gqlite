use cucumber::{after, before, cucumber};
use gqlite::gramdb::{GramCursor, GramDatabase};
use gqlite::Database;
use tempfile::tempfile;

pub struct GraphProperties {
    node_count: i32,
    _relationship_count: i32,
}

fn empty_db() -> GramDatabase {
    Database::open(tempfile().unwrap()).unwrap()
}

pub struct MyWorld {
    // You can use this struct for mutable context in scenarios.
    graph: GramDatabase,
    starting_graph_properties: GraphProperties,
    result: GramCursor,
}

impl cucumber::World for MyWorld {}

impl std::default::Default for MyWorld {
    fn default() -> MyWorld {
        // This function is called every time a new scenario is started
        let mut db = empty_db();
        let cursor = db.new_cursor();
        MyWorld {
            graph: db,
            result: cursor,
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
    use gqlite::gramdb::GramCursor;
    use gqlite::{Error, Val};

    use std::iter::Peekable;
    use std::str::Chars;

    // The OpenCypher spec contains an unspecified language to describe assertions;
    // we have an informal parser for that language which yields these matchers

    #[derive(Debug, PartialEq, Clone)]
    pub enum ValMatcher {
        String(String),
        List(Vec<ValMatcher>),
        Map(Vec<(String, ValMatcher)>),
        Int(i64),
        Float(f64),
        Node { props: Vec<(String, ValMatcher)> },
    }

    impl ValMatcher {
        pub fn assert_eq(&self, v: Val) {
            match self {
                ValMatcher::Int(e) => assert_eq!(Val::Int(*e), v),
                ValMatcher::Float(e) => assert_eq!(Val::Float(*e), v),
                ValMatcher::String(e) => assert_eq!(Val::String(e.clone()), v),
                ValMatcher::Map(_) => panic!(".."),
                ValMatcher::List(expected) => match v {
                    Val::List(actual) => {
                        if expected.len() != actual.len() {
                            panic!(
                                "Expected {:?}, got {:?} (not same length)",
                                expected, actual
                            )
                        }
                        for i in 0..expected.len() {
                            expected[i].assert_eq(actual[i].clone())
                        }
                    }
                    _ => panic!("Expected a list, found {:?}", v),
                },
                ValMatcher::Node { props } => {
                    if let Val::Node(n) = v {
                        if n.props.len() != props.len() {
                            panic!("Node has different number of properties from spec, expected {:?}, got {:?}",
                                   props, n.props);
                        }
                        for (k, prop_val) in &n.props {
                            let mut found = false;
                            for (ek, ev) in props {
                                if ek == k {
                                    found = true;
                                    ev.assert_eq(prop_val.clone());
                                }
                            }
                            if !found {
                                panic!("Node has unspecified property {}", k);
                            }
                        }
                    } else {
                        panic!("Expected a node, found {:?}", v);
                    }
                }
            }
        }
    }

    fn run_preparatory_query(world: &mut MyWorld, step: &Step) -> Result<(), Error> {
        let mut cursor = world.graph.new_cursor();
        let result = world.graph.run(&step.docstring().unwrap(), &mut cursor);
        while let Some(_) = cursor.next()? {
            // consume
        }
        world.starting_graph_properties.node_count = count_nodes(world);
        result
    }

    fn start_query(world: &mut MyWorld, step: &Step) {
        world
            .graph
            .run(&step.docstring().unwrap(), &mut world.result)
            .expect("Should not fail")
    }

    fn count_rows(result: &mut GramCursor) -> Result<i32, Error> {
        let mut ct = 0;
        while let Some(_) = result.next()? {
            ct += 1
        }
        Ok(ct)
    }

    fn count_nodes(world: &mut MyWorld) -> i32 {
        let mut cursor = world.graph.new_cursor();
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

    fn assert_no_side_effects(world: &mut MyWorld) {
        assert_eq!(
            0,
            count_nodes(world) - world.starting_graph_properties.node_count
        )
    }

    fn assert_result(world: &mut MyWorld, step: &Step) {
        let table = step.table().unwrap().clone();
        for mut row in table.rows {
            if let Ok(Some(actual)) = world.result.next() {
                for slot in 0..row.len() {
                    str_to_val(&mut row[slot].chars().peekable())
                        .assert_eq(actual.slots[slot].clone());
                }
            } else {
                assert_eq!(false, true, "Expected more results");
            }
        }
    }

    fn str_to_val(mut chars: &mut Peekable<Chars>) -> ValMatcher {
        fn parse_number(chars: &mut Peekable<Chars>) -> ValMatcher {
            let mut val = String::new();
            let mut is_float = false;
            val.push(chars.next().unwrap());
            loop {
                match chars.peek() {
                    Some('0'..='9') => val.push(chars.next().unwrap()),
                    Some('-') => val.push(chars.next().unwrap()),
                    Some(' ') => break,
                    Some(']') => break,
                    Some('}') => break,
                    Some(',') => break,
                    Some('.') => {
                        is_float = true;
                        val.push(chars.next().unwrap());
                    }
                    None => break,
                    _ => panic!(format!("unknown integer portion: '{:?}'", chars.peek())),
                }
            }
            if is_float {
                return ValMatcher::Float(val.parse().unwrap());
            }
            return ValMatcher::Int(val.parse().unwrap());
        }
        fn parse_identifier(chars: &mut Peekable<Chars>) -> String {
            let mut id = String::new();
            id.push(chars.next().unwrap());
            loop {
                match chars.peek() {
                    Some('0'..='9') => id.push(chars.next().unwrap()),
                    Some('-') => id.push(chars.next().unwrap()),
                    Some('_') => id.push(chars.next().unwrap()),
                    Some('a'..='z') => id.push(chars.next().unwrap()),
                    Some('A'..='Z') => id.push(chars.next().unwrap()),
                    _ => break,
                }
            }
            return id;
        }

        loop {
            match chars.peek().unwrap() {
                '0'..='9' => return parse_number(chars),
                '-' => return parse_number(chars),
                '\'' => {
                    let mut val = String::new();
                    chars.next().unwrap();
                    loop {
                        match chars.next() {
                            Some('\'') => return ValMatcher::String(val),
                            None => return ValMatcher::String(val),
                            Some(v) => val.push(v),
                        }
                    }
                }
                ' ' => {
                    chars.next().unwrap();
                    ()
                }
                '[' => {
                    let mut items = Vec::new();
                    chars.next().unwrap();
                    loop {
                        match chars.peek() {
                            Some(']') => return ValMatcher::List(items),
                            None => return ValMatcher::List(items),
                            Some(',') => {
                                chars.next().unwrap();
                                ()
                            }
                            Some(' ') => {
                                chars.next().unwrap();
                                ()
                            }
                            _ => items.push(str_to_val(&mut chars)),
                        }
                    }
                }
                '{' => {
                    chars.next().unwrap();
                    let mut entries = Vec::new();
                    loop {
                        // Parse entry identifier..
                        let mut identifier = None;
                        loop {
                            match chars.peek() {
                                Some('}') => {
                                    chars.next().unwrap();
                                    return ValMatcher::Map(entries);
                                }
                                Some('a'..='z') => identifier = Some(parse_identifier(chars)),
                                Some(':') => {
                                    chars.next().unwrap();
                                    break;
                                }
                                Some(' ') => {
                                    chars.next().unwrap();
                                    ()
                                }
                                _ => panic!(format!("unknown map portion: '{:?}'", chars)),
                            }
                        }

                        // Parse entry value..
                        let value = str_to_val(chars);
                        entries.push((identifier.unwrap(), value))
                    }
                }
                '(' => {
                    chars.next().unwrap();
                    let mut props = Vec::new();
                    loop {
                        match chars.peek() {
                            Some(')') => return ValMatcher::Node { props },
                            None => return ValMatcher::Node { props },
                            Some('{') => {
                                match str_to_val(&mut chars) {
                                    ValMatcher::Map(e) => {
                                        props = e;
                                    }
                                    v => panic!("Expected property map, got {:?}", v),
                                }
                                ()
                            }
                            Some(' ') => {
                                chars.next().unwrap();
                                ()
                            }
                            _ => panic!(format!("unknown node spec portion: '{:?}'", chars.peek())),
                        }
                    }
                }
                _ => panic!(format!("unknown value: '{:?}'", chars)),
            }
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

        then "the result should be, in any order:" |mut world, step| {
            assert_result(&mut world, &step)
        };

        then "the side effects should be:" |world, step| {
            // Check that the outcomes to be observed have occurred
            let table = step.table().unwrap().clone();
            table.rows.iter().for_each(|row| assert_side_effect(world, &row[0], &row[1]));
        };

        then "no side effects" |world, _step| {
            assert_no_side_effects(world);
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

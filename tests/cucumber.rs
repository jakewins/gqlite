use cucumber::{after, before, cucumber};
use gqlite::gramdb::{GramCursor, GramDatabase};
use gqlite::{Database, Val};
use tempfile::tempfile;

#[macro_use]
extern crate anyhow;

pub struct GraphProperties {
    node_count: i32,
    relationship_count: i32,
    labels_count: i32,
    properties_count: i32,
}

fn empty_db() -> GramDatabase {
    Database::open(tempfile().unwrap()).unwrap()
}

pub struct MyWorld {
    graph: GramDatabase,
    starting_graph_properties: GraphProperties,
    parameters: Vec<(String, Val)>,
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
            parameters: Vec::new(),
            starting_graph_properties: GraphProperties {
                node_count: 0,
                relationship_count: 0,
                labels_count: 0,
                properties_count: 0,
            },
        }
    }
}

mod example_steps {
    use super::{empty_db, MyWorld};
    use anyhow::Result;
    use cucumber::{steps, Step};
    use gqlite::gramdb::GramCursor;
    use gqlite::{Error, Val};

    use std::iter::Peekable;
    use std::str::Chars;

    macro_rules! ensure_eq {
        ($left:expr, $right:expr) => {{
            match (&$left, &$right) {
                (left_val, right_val) => {
                    if !(*left_val == *right_val) {
                        bail!(
                            r#"assertion failed: `(left == right)`
      left: `{:?}`,
     right: `{:?}`"#,
                            &*left_val,
                            &*right_val
                        )
                    } else {
                        Ok(())
                    }
                }
            }
        }};
        ($left:expr, $right:expr,) => {{
            $crate::assert_eq!($left, $right)
        }};
    }

    // The OpenCypher spec contains an unspecified language to describe assertions;
    // we have an informal parser for that language which yields these matchers

    #[derive(Debug, PartialEq, Clone)]
    pub enum ValMatcher {
        String(String),
        Bool(bool),
        Null,
        List(Vec<ValMatcher>),
        Map(Vec<(String, ValMatcher)>),
        Int(i64),
        Float(f64),
        Node {
            props: Vec<(String, ValMatcher)>,
            labels: Vec<String>,
        },
        Rel {
            reltype: String,
        },
    }

    impl ValMatcher {
        pub fn to_val(&self) -> Val {
            match self {
                ValMatcher::Int(v) => Val::Int(*v),
                v => panic!("Don't know how to convert {:?} to val", v),
            }
        }
        pub fn test_eq(&self, v: Val) -> Result<()> {
            match self {
                ValMatcher::Int(e) => {
                    // The TCK writes float results in a way that doesn't let us distinguish
                    // them from int results.. so we allow ints that are strictly equal here
                    // as well
                    if let Val::Float(av) = v {
                        ensure_eq!(*e as f64, av)
                    } else {
                        ensure_eq!(Val::Int(*e), v)
                    }
                }
                ValMatcher::Float(e) => ensure_eq!(Val::Float(*e), v),
                ValMatcher::Bool(b) => ensure_eq!(Val::Bool(*b), v),
                ValMatcher::Null => ensure_eq!(Val::Null, v),
                ValMatcher::String(e) => ensure_eq!(Val::String(e.clone()), v),
                ValMatcher::Map(es) => {
                    if let Val::Map(actual) = v {
                        if es.len() != actual.len() {
                            bail!("Expected {:?}, got {:?} (not same length)", es, actual)
                        }
                        for (k, ev) in es {
                            let mut found = false;
                            for (ak, av) in &actual {
                                if ak == k {
                                    found = true;
                                    ev.test_eq(av.clone())?;
                                }
                            }
                            if !found {
                                bail!("map has unspecified property {}", k);
                            }
                        }
                        Ok(())
                    } else {
                        bail!("Expected a map, found {:?}", v)
                    }
                }
                ValMatcher::List(expected) => match v {
                    Val::List(actual) => {
                        if expected.len() != actual.len() {
                            bail!(
                                "Expected {:?}, got {:?} (not same length)",
                                expected,
                                actual
                            )
                        }
                        for i in 0..expected.len() {
                            expected[i].test_eq(actual[i].clone())?;
                        }
                        Ok(())
                    }
                    _ => bail!("Expected a list, found {:?}", v),
                },
                ValMatcher::Node { props, labels } => {
                    if let Val::Node(n) = v {
                        if n.props.len() != props.len() {
                            bail!("Node has different number of properties from spec, expected {:?}, got {:?}",
                                   props, n.props);
                        }
                        for (k, prop_val) in &n.props {
                            let mut found = false;
                            for (ek, ev) in props {
                                if ek == k {
                                    found = true;
                                    ev.test_eq(prop_val.clone())?;
                                }
                            }
                            if !found {
                                bail!("Node has unspecified property {}", k);
                            }
                        }

                        if n.labels.len() != labels.len() {
                            bail!("Node has different number of labels from spec, expected {:?}, got {:?}", labels, n.labels);
                        }
                        for l in labels {
                            let mut found = false;
                            for actual in &n.labels {
                                if actual == l {
                                    found = true;
                                    break;
                                }
                            }
                            if !found {
                                bail!(
                                    "Missing expected labels. Expected {:?}, got {:?}",
                                    labels,
                                    n.labels
                                );
                            }
                        }
                        Ok(())
                    } else {
                        bail!("Expected a node, found {:?}", v);
                    }
                }
                ValMatcher::Rel { reltype } => {
                    if let Val::Rel(r) = v {
                        ensure_eq!(reltype, &r.rel_type)
                    } else {
                        bail!("Expected a rel, found {:?}", v);
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
        world.starting_graph_properties.relationship_count = count_rels(world);
        world.starting_graph_properties.labels_count = count_labels(world);
        world.starting_graph_properties.properties_count = count_properties(world);
        result
    }

    fn set_parameters(world: &mut MyWorld, step: &Step) -> Result<(), Error> {
        let mut table = step.table().unwrap().clone();
        let pkey = table.header[0].to_string();
        let pval = str_to_val(&mut table.header[1].chars().peekable()).to_val();
        world.parameters.push((pkey, pval));
        for mut row in table.rows {
            let pkey = row[0].to_string();
            let pval = str_to_val(&mut row[1].chars().peekable()).to_val();
            world.parameters.push((pkey, pval));
        }
        Ok(())
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

    fn count_labels(world: &mut MyWorld) -> i32 {
        let mut cursor = world.graph.new_cursor();
        world
            .graph
            .run("MATCH (n) RETURN n", &mut cursor)
            .expect("should succeed");
        let mut ct = 0;
        while let Some(r) = cursor.next().unwrap() {
            if let Val::Node(n) = &r.slots[0] {
                ct += n.labels.len()
            } else {
                panic!("Query requesting nodes returned something else: {:?}", r)
            }
        }
        ct as i32
    }

    fn count_properties(world: &mut MyWorld) -> i32 {
        let mut cursor = world.graph.new_cursor();
        world
            .graph
            .run("MATCH (n) RETURN n", &mut cursor)
            .expect("should succeed");
        let mut ct = 0;
        while let Some(r) = cursor.next().unwrap() {
            if let Val::Node(n) = &r.slots[0] {
                ct += n.props.len()
            } else {
                panic!("Query requesting nodes returned something else: {:?}", r)
            }
        }

        world
            .graph
            .run("MATCH ()-[r]->() RETURN r", &mut cursor)
            .expect("should succeed");
        while let Some(r) = cursor.next().unwrap() {
            if let Val::Rel(n) = &r.slots[0] {
                ct += n.props.len()
            } else {
                panic!("Query requesting rels returned something else: {:?}", r)
            }
        }
        ct as i32
    }

    fn count_nodes(world: &mut MyWorld) -> i32 {
        let mut cursor = world.graph.new_cursor();
        world
            .graph
            .run("MATCH (n) RETURN n", &mut cursor)
            .expect("should succeed");
        count_rows(&mut cursor).unwrap()
    }

    fn count_rels(world: &mut MyWorld) -> i32 {
        let mut cursor = world.graph.new_cursor();
        world
            .graph
            .run("MATCH (n)-->() RETURN n", &mut cursor)
            .expect("should succeed");
        count_rows(&mut cursor).unwrap()
    }

    fn assert_side_effect(world: &mut MyWorld, kind: &str, val: &str) {
        match kind {
            "+nodes" => assert_eq!(
                count_nodes(world) - world.starting_graph_properties.node_count,
                val.parse::<i32>().unwrap()
            ),
            "+relationships" => assert_eq!(
                count_rels(world) - world.starting_graph_properties.relationship_count,
                val.parse::<i32>().unwrap()
            ),
            "+labels" => assert_eq!(
                count_labels(world) - world.starting_graph_properties.labels_count,
                val.parse::<i32>().unwrap()
            ),
            "+properties" => assert_eq!(
                count_properties(world) - world.starting_graph_properties.properties_count,
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

        // So.. the rust cucumber parser treats one-row tables as having empty headers
        // but the TCK uses headers in empty tables, to specify the column names.. so this
        // is to detect that case
        let mut empty = table.rows.len() == 1;
        for c in &table.header {
            empty = empty && c.is_empty();
        }

        if empty {
            let row = world.result.next().unwrap();
            assert_eq!(true, row.is_none(), "expected empty result");
            assert_eq!(world.result.fields(), table.rows[0]);
            return;
        } else {
            assert_eq!(world.result.fields(), table.header);
        }

        for mut row in table.rows {
            if let Some(actual) = world.result.next().unwrap() {
                for slot in 0..row.len() {
                    str_to_val(&mut row[slot].chars().peekable())
                        .test_eq(actual.slots[slot].clone())
                        .unwrap();
                }
            } else {
                assert_eq!(false, true, "Expected more results");
            }
        }
    }

    fn assert_result_in_any_order(world: &mut MyWorld, step: &Step) {
        let table = step.table().unwrap().clone();

        // So.. the rust cucumber parser treats one-row tables as having empty headers
        // but the TCK uses headers in empty tables, to specify the column names.. so this
        // is to detect that case
        let mut empty = table.rows.len() == 1;
        for c in &table.header {
            empty = empty && c.is_empty();
        }

        if empty {
            let row = world.result.next().unwrap();
            assert_eq!(true, row.is_none(), "expected empty result");
            assert_eq!(world.result.fields(), table.rows[0]);
            return;
        } else {
            assert_eq!(world.result.fields(), table.header);
        }

        // It makes debugging way easier for the cases where there is just one result row
        // if we use the ordered assertion
        if table.rows.len() == 1 {
            assert_result(world, step);
            return;
        }

        let mut expected_rows = table.rows;

        while let Some(actual) = world.result.next().unwrap() {
            // Find any row in the remaining result that matches
            let mut matching_row = None;
            let mut row_equal = Ok(());
            for (index, row) in expected_rows.iter().enumerate() {
                row_equal = Ok(());
                let mut row_copy = row.clone();
                for slot in 0..row.len() {
                    let slot_equal = str_to_val(&mut row_copy[slot].chars().peekable())
                        .test_eq(actual.slots[slot].clone());
                    if slot_equal.is_err() {
                        row_equal = slot_equal;
                        break;
                    }
                }
                if row_equal.is_ok() {
                    // Found matching row
                    matching_row = Some(index);
                    break;
                }
            }

            // If we found a row that matched, remove it from the set of expected rows..
            if let Some(index) = matching_row {
                expected_rows.remove(index);
            } else {
                // Found no matching row; are there any expected rows left?
                if expected_rows.is_empty() {
                    panic!("Expected no more rows, got {:?}", actual)
                } else {
                    panic!("Got row that does not match any expected rows: {:?}. Expected rows are: {:?}, last error was {:?}", actual, expected_rows, row_equal)
                }
            }
        }

        // And then there should be no desired rows left
        assert_eq!(0, expected_rows.len(), "{:?}", expected_rows)
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

        fn parse_rel(chars: &mut Peekable<Chars>) -> ValMatcher {
            let mut reltype = None;
            loop {
                match chars.peek() {
                    Some(':') => {
                        chars.next().unwrap();
                        reltype = Some(parse_identifier(chars));
                    }
                    Some(']') => {
                        chars.next().unwrap();
                        return ValMatcher::Rel {
                            reltype: reltype.unwrap(),
                        };
                    }
                    _ => panic!("unknown rel part: {:?}", chars),
                }
            }
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
                't' | 'f' | 'n' => {
                    let literal = parse_identifier(chars);
                    match literal.as_str() {
                        "true" => return ValMatcher::Bool(true),
                        "false" => return ValMatcher::Bool(false),
                        "null" => return ValMatcher::Null,
                        _ => panic!("Unknown literal: {:?}"),
                    }
                }
                ' ' => {
                    chars.next().unwrap();
                    ()
                }
                '[' => {
                    chars.next().unwrap();
                    // this can either be a list, or a relationship
                    // need to differentiate [:REL] from [1]..

                    match chars.peek() {
                        Some(':') => {
                            return parse_rel(chars);
                        }
                        _ => (),
                    }

                    // List
                    let mut items = Vec::new();
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
                                Some(',') => {
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
                    let mut labels: Vec<String> = Vec::new();
                    loop {
                        match chars.peek() {
                            Some(')') => return ValMatcher::Node { props, labels },
                            None => return ValMatcher::Node { props, labels },
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
                            Some(':') => {
                                chars.next().unwrap();
                                labels.push(parse_identifier(chars))
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

        given "parameters are:" |world, step| {
            set_parameters(world, step).unwrap();
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
            assert_result_in_any_order(&mut world, &step)
        };

        then "the result should be, in order:" |mut world, step| {
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

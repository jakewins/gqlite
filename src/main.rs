use gqlite::{Error, Tokens, Database, Cursor};

use clap::{App, SubCommand, AppSettings, Arg};

use pest::Parser;

use pest::iterators::{Pair};
use std::any::Any;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::fmt::{Display, Formatter, Write};
use std::fmt;

// lol
fn string_to_static_str(s: &str) -> &'static str {
    Box::leak(s.to_string().into_boxed_str())
}

fn main() -> Result<(), Error>{
    let matches = App::new("g")
        .version("0.0")
        .about("A graph database in a yaml file!")
        .setting(AppSettings::ArgRequiredElseHelp)
        .args_from_usage(
            "-f, --file=[FILE] @graph.gram 'Sets the gram file to use'
            -h, --help 'Print help information'
            <QUERY> 'Query to execute'")
        .get_matches();

    let query_str = string_to_static_str(matches.value_of("QUERY").unwrap());
    let path = matches.value_of("file").unwrap_or("graph.gram");

    let mut db = Database::open(path)?;
    let mut cursor = Cursor::new();
    db.run(query_str, &mut cursor)?;

    while cursor.next()? {

    }
    Ok(())
}
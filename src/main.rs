extern crate pest;
#[macro_use]
extern crate pest_derive;

extern crate clap;

use clap::{App, SubCommand, AppSettings};

use pest::Parser;

#[derive(Parser)]
#[grammar = "cypher.pest"]
pub struct CypherParser;

fn main() {
    let matches = App::new("graf")
        .version("0.0")
        .author("Jacob Davis-Hansson <jake@davis-hansson.com>")
        .about("A graph database in a yaml file!")
        .setting(AppSettings::ArgRequiredElseHelp)
        .args_from_usage(
            "-f, --file=[FILE] @graf.yaml 'Sets the db file to use'\
            -h, --help 'Print help information'")
        .subcommand(SubCommand::with_name("query")
            .about("executes a query against the database")
            .arg_from_usage(
                "<QUERY> 'Query to execute'"))
        .get_matches();

    if let Some(matches) = matches.subcommand_matches("query") {
        let query_str = matches.value_of("QUERY").unwrap();

        let query = CypherParser::parse(Rule::query, &query_str)
            .expect("unsuccessful parse") // unwrap the parse result
            .next().unwrap(); // get and unwrap the `file` rule; never fails

        let mut statement_count: u64 = 0;

        for statement in query.into_inner() {
            match statement.as_rule() {
                Rule::statement => {
                    statement_count += 1;
                }
                Rule::EOI => (),
                _ => unreachable!(),
            }
        }

        println!("Number of statements: {}", statement_count);
    }
}

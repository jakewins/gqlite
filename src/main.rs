use gqlite::{Error, Tokens};

use clap::{App, SubCommand, AppSettings, Arg};

use pest::Parser;

use pest::iterators::{Pair};
use std::any::Any;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use crate::Val::Null;
use std::fmt::{Display, Formatter, Write};
use std::fmt;

use steps::*;

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

    let query_str = matches.value_of("QUERY").unwrap();

    let path = matches.value_of("file").unwrap_or("graph.gram");

    let query = CypherParser::parse(Rule::query, &query_str)
        .expect("unsuccessful parse") // unwrap the parse result
        .next().unwrap(); // get and unwrap the `file` rule; never fails

    let mut statement_count: u64 = 0;

    let mut tokens = Tokens { table: Default::default() };
    let lbl_note = tokens.tokenize("Note");
    let lbl_reference = tokens.tokenize("Reference");
    let key_message = tokens.tokenize("message");
    let mut g = gram::load(&mut tokens, path)?;
    let mut pc = PlanningContext{ g: Rc::new(g), slots: Default::default(), anon_rel_seq:0, anon_node_seq: 0, tokens: tokens, };
    let mut plan: Box<dyn Step> = Box::new(Leaf{});

    for stmt in query.into_inner() {
        match stmt.as_rule() {
            Rule::match_stmt => {
                plan = plan_match(&mut pc, plan, stmt);
            }
            Rule::create_stmt => {
                plan = plan_create(&mut pc, plan, stmt);
            }
            Rule::return_stmt => {
                plan = plan_return(&mut pc, plan, stmt);
            }
            Rule::EOI => (),
            _ => unreachable!(),
        }
    }

    println!("plan: {:?}", plan);

    let mut ctx = pc.new_execution_ctx();
    let mut row = pc.new_row();
    loop {
        match plan.next(&mut ctx, &mut row) {
            Ok(true) => {
                // Keep going
            }
            Ok(false) => {
                return Ok(())
            }
            Err(e) => {
                panic!(e.msg)
            }
        }
    }
}
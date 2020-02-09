extern crate pest;
#[macro_use]
extern crate pest_derive;

extern crate clap;

use clap::{App, SubCommand, AppSettings};

use pest::Parser;

use pest::iterators::{Pair};
use std::any::Any;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

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

        let g = Rc::new(Graph{ nodes: vec![
            Node{ labels: [ String::from("Note") ].iter().cloned().collect(), properties: Default::default() },
            Node{ labels: [ String::from("Note") ].iter().cloned().collect(), properties: Default::default() },
            Node{ labels: [ String::from("Reference") ].iter().cloned().collect(), properties: Default::default() },
        ] });
        let mut pc = PlanningContext{ g, slots: Default::default() };
        let mut plan: Box<dyn Step> = Box::new(Leaf{});

        for stmt in query.into_inner() {
            match stmt.as_rule() {
                Rule::match_stmt => {
                    plan = plan_match(&mut pc, plan, stmt)
                }
                Rule::create_stmt => {
                    let create_stmt = stmt.into_inner();
                    println!("{}", create_stmt.as_str())
                }
                Rule::return_stmt => {
                    plan = plan_return(&mut pc, plan, stmt)
                }
                Rule::EOI => (),
                _ => unreachable!(),
            }
        }

        println!("Plan: {:?}", plan);

        let mut ctx = pc.new_execution_ctx();
        let mut row = pc.new_row();
        loop {
            match plan.next(&mut ctx, &mut row) {
                Ok(true) => {
                    // Keep going
                    println!("{:?}", row)
                }
                Ok(false) => {
                    return
                }
                Err(e) => {
                    panic!(e.msg)
                }
            }
        }
    }
}

// For a given plan, each step that has runtime state uas one of these to get their state
// out of the runtime context.
type StepStateKey = u32;

struct PlanningContext {
    g: Rc<Graph>,
    // slot assignments by name in output row
    slots: HashMap<String, usize>,
}

impl PlanningContext {

    pub fn get_or_alloc_slot(&mut self, identifier: &str) -> usize {
        match self.slots.get(identifier) {
            Some(slot) => { return *slot },
            None => {
                let slot = self.slots.len();
                let string= String::from(identifier);
                self.slots.insert(string, slot);
                return slot
            }
        }
    }

    pub fn new_row(&self) -> Row {
        return Row{ slots: vec![Val::Null;self.slots.len()] }
    }

    pub fn new_execution_ctx(&self) -> Context {
        return Context{ g: self.g.clone() }
    }
}

fn plan_return<'i, 'p>(pc: &'p mut PlanningContext, src: Box<dyn Step + 'i>, return_stmt: Pair<'i, Rule>) -> Box<dyn Step + 'i> {
    let mut plan: Box<dyn Step + 'i> = src;
    for part in return_stmt.into_inner() {
        match part.as_rule() {
            Rule::projections => {
                plan = plan_return_projections(pc, plan, part)
            }
            _ => unreachable!(),
        }
    }
    return plan;
}

fn plan_return_projections<'i, 'p>(pc: &'p mut PlanningContext, src: Box<dyn Step + 'i>, projections: Pair<'i, Rule>) -> Box<dyn Step + 'i> {
    let mut plan: Box<dyn Step + 'i> = src;
    for part in projections.into_inner() {
        match part.as_rule() {
            Rule::projection => {

            }
            _ => unreachable!(),
        }
    }
    return plan;
}

fn plan_match<'i, 'p>(pc: &'p mut PlanningContext, src: Box<dyn Step + 'i>, match_stmt: Pair<'i, Rule>) -> Box<dyn Step + 'i> {
    let mut plan: Box<dyn Step + 'i> = src;
    for part in match_stmt.into_inner() {
        match part.as_rule() {
            Rule::pattern => {
                // For each node and rel segment of eg: (n:Message)-[:KNOWS]->()
                for segment in part.into_inner() {
                    match segment.as_rule() {
                        Rule::node => {
                            plan = plan_match_node(pc,plan, segment);
                        }
                        Rule::rel => {
                            println!("rel: {}", segment.as_str());
                        }
                        _ => unreachable!(),
                    }
                }
            }
            _ => unreachable!(),
        }
    }
    return plan
}

// Figures out what step we need to find the specified node
fn plan_match_node<'i, 'p>(pc: &'p mut PlanningContext, src: Box<dyn Step + 'i>, pattern_node: Pair<'i, Rule>) -> Box<dyn Step + 'i> {
    let mut identifier = "";
    let mut label = "";
    for part in pattern_node.into_inner() {
        match part.as_rule() {
            Rule::id => {
                identifier = part.as_str()
            }
            Rule::label => {
                label = part.as_str()
            }
            _ => unreachable!(),
        }
    }

    let slot = pc.get_or_alloc_slot(identifier);

    let out: Box<dyn Step> = Box::new(NodeScan {
        src,
        slot,
        label,
        next_node: 0,
    });

    return out
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Error {
    msg: String,
}

#[derive(Debug)]
pub struct Context {
    g: Rc<Graph>
}

#[derive(Debug)]
pub struct Row {
    slots: Vec<Val>
}

pub trait Step: std::fmt::Debug {
    // Produce the next row
    fn next(&mut self, ctx: &mut Context, out: &mut Row) -> Result<bool, Error>;
}

#[derive(Debug)]
pub struct Expand;

impl Step for Expand {
    fn next(&mut self, ctx: &mut Context, out: &mut Row) -> Result<bool, Error> {
        unimplemented!()
    }
}


#[derive(Debug)]
pub struct Filter;

impl Step for Filter {
    fn next(&mut self, ctx: &mut Context, out: &mut Row) -> Result<bool, Error> {
        unimplemented!()
    }
}

// For each src row, perform a full node scan with the specified filters
#[derive(Debug)]
pub struct NodeScan<'i> {
    src: Box<dyn Step + 'i>,

    // Next node id in g to return
    next_node: usize,

    // Where should this scan write its output?
    slot: usize,

    // If the empty string, return all nodes, otherwise only nodes with the specified label
    label:  &'i str,
}

impl<'i> Step for NodeScan<'i> {
    fn next(&mut self, ctx: &mut Context, out: &mut Row) -> Result<bool, Error> {
        loop {
            if ctx.g.nodes.len() > self.next_node {
                let node = ctx.g.nodes.get(self.next_node).unwrap();
                self.next_node += 1;
                if self.label != "" && !node.labels.contains(self.label) {
                    continue;
                }

                out.slots[self.slot] = Val::Node(self.next_node);
                return Ok(true)
            }
            return Ok(false)
        }
    }
}

#[derive(Debug)]
pub struct Leaf;

impl Step for Leaf {
    fn next(&mut self, ctx: &mut Context, out: &mut Row) -> Result<bool, Error> {
        unimplemented!()
    }
}


#[derive(Debug)]
pub struct Return;

impl Step for Return {
    fn next(&mut self, ctx: &mut Context, out: &mut Row) -> Result<bool, Error> {
        unimplemented!()
    }
}

#[derive(Debug)]
pub struct Node {
    labels: HashSet<String>,
    properties: HashMap<String, Val>,
}

#[derive(Debug,Clone)]
pub enum Val {
    Null,
    Node(usize),
}

#[derive(Debug)]
pub struct Graph  {
    nodes: Vec<Node>

}
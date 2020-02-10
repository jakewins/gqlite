extern crate pest;
#[macro_use]
extern crate pest_derive;

extern crate clap;

mod steps;

use clap::{App, SubCommand, AppSettings};

use pest::Parser;

use pest::iterators::{Pair};
use std::any::Any;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use crate::Val::Null;
use std::fmt::{Display, Formatter, Write};
use std::fmt;

use steps::*;
use std::iter::Map;

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
            "<QUERY> 'Query to execute'\
            -f, --file=[FILE] @graf.yaml 'Sets the db file to use'\
            -h, --help 'Print help information'")
        .get_matches();

    let query_str = matches.value_of("QUERY").unwrap();

    let query = CypherParser::parse(Rule::query, &query_str)
        .expect("unsuccessful parse") // unwrap the parse result
        .next().unwrap(); // get and unwrap the `file` rule; never fails

    let mut statement_count: u64 = 0;

    let g = Rc::new(Graph{ nodes: vec![
        Node{ labels: [ String::from("Note") ].iter().cloned().collect(), properties: [ (String::from("message"), Val::String(String::from("a message"))) ].iter().cloned().collect() },
        Node{ labels: [ String::from("Note") ].iter().cloned().collect(), properties: [ (String::from("message"), Val::String(String::from("other message.."))) ].iter().cloned().collect() },
        Node{ labels: [ String::from("Reference") ].iter().cloned().collect(), properties: Default::default() },
    ] });
    let mut pc = PlanningContext{ g, slots: Default::default(), anon_rel_seq:0, anon_node_seq: 0 };
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

    let mut ctx = pc.new_execution_ctx();
    let mut row = pc.new_row();
    loop {
        match plan.next(&mut ctx, &mut row) {
            Ok(true) => {
                // Keep going
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

struct PlanningContext {
    g: Rc<Graph>,
    // slot assignments by name in output row
    slots: HashMap<String, usize>,
    anon_rel_seq: u32,
    anon_node_seq: u32,
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

    pub fn new_anon_rel(&mut self) -> Id {
        let seq = self.anon_rel_seq;
        self.anon_rel_seq += 1;
        return format!("AnonRel#{}", seq)
    }

    pub fn new_anon_node(&mut self) -> Id {
        let seq = self.anon_node_seq;
        self.anon_node_seq += 1;
        return format!("AnonNode#{}", seq)
    }

    pub fn new_row(&self) -> Row {
        return Row{ slots: vec![Val::Null;self.slots.len()] }
    }

    pub fn new_execution_ctx(&self) -> Context {
        return Context{ g: self.g.clone() }
    }
}

fn plan_return<'i>(pc: & mut PlanningContext, src: Box<dyn Step + 'i>, return_stmt: Pair<'i, Rule>) -> Box<dyn Step + 'i> {
    let mut parts = return_stmt.into_inner();
    let projections = parts.next().and_then(|p| Some(plan_return_projections(pc, p))).expect("RETURN must start with projections");
    return Box::new(Return{ src, projections });
}

fn plan_return_projections(pc: & mut PlanningContext, projections: Pair<Rule>) -> Vec<Projection> {
    let mut out = Vec::new();
    for projection in projections.into_inner() {
        if let Rule::projection = projection.as_rule() {
            let default_alias = String::from(projection.as_str());
            let mut parts = projection.into_inner();
            let expr = parts.next().and_then(|p| Some(plan_expr(pc, p))).unwrap();
            let alias = parts.next().and_then(|p| match p.as_rule() {
                Rule::id => Some(String::from(p.as_str())),
                _ => None
            }).unwrap_or(default_alias);
            out.push(Projection{expr, alias});
        }
    }
    return out;
}

fn plan_expr(pc: & mut PlanningContext, expression: Pair<Rule>) -> Expr {
    for inner in expression.into_inner() {
        match inner.as_rule() {
            Rule::string => {
                return Expr::Lit(Val::String(String::from(inner.as_str())))
            }
            Rule::id => {
                return Expr::Slot(pc.get_or_alloc_slot(inner.as_str()))
            }
            Rule::prop_lookup => {
                let mut prop_lookup = inner.into_inner();
                let prop_lookup_expr = prop_lookup.next().unwrap();
                let base = match prop_lookup_expr.as_rule() {
                    Rule::id => Expr::Slot(pc.get_or_alloc_slot(prop_lookup_expr.as_str())),
                    _ => unreachable!(),
                };
                let mut props = Vec::new();
                for p_inner in prop_lookup {
                    if let Rule::id = p_inner.as_rule() {
                        props.push(String::from(p_inner.as_str()));
                    }
                }
                return Expr::Prop(Box::new(base), props)
            }
            _ => panic!(String::from(inner.as_str())),
        }
    }
    panic!("Invalid expression from parser.")
}

#[derive(Debug)]
struct PatternNode {
    identifier: Id,
    labels: Vec<String>
}

impl PatternNode {
    fn merge(&mut self, other: &PatternNode) {

    }
}

#[derive(Debug)]
struct PatternRel {
    identifier: Id,
    rel_type: String,
    left_node: String,
    right_node: String,
}

#[derive(Debug)]
struct PatternGraph {
    e: HashMap<String, PatternNode>,
    v: Vec<PatternRel>,
}

impl PatternGraph {
    fn merge_node(&mut self, pc: &mut PlanningContext, mut n: PatternNode) -> String {
        if n.identifier == "" {
            n.identifier = pc.new_anon_node();
        }

        let id = n.identifier.clone();
        let id2 = id.clone();
        let entry = self.e.entry(id);
        entry.and_modify(|on| on.merge(&n)).or_insert(n);
        return id2;
    }

    fn merge_rel(&mut self, pc: &mut PlanningContext, mut r: PatternRel) {
        if r.identifier == "" {
            r.identifier = pc.new_anon_rel();
        }

        self.v.push(r)
    }
}

fn plan_match<'i>(pc: &mut PlanningContext, src: Box<dyn Step + 'i>, match_stmt: Pair<'i, Rule>) -> Box<dyn Step + 'i> {
    let mut plan: Box<dyn Step + 'i> = src;
    let mut pg: PatternGraph = PatternGraph{ e: HashMap::new(), v: Vec::new()};

    for part in match_stmt.into_inner() {
        match part.as_rule() {
            Rule::pattern => {
                let mut prior_node = None;
                let mut prior_rel: Option<PatternRel> = None;
                // For each node and rel segment of eg: (n:Message)-[:KNOWS]->()
                for segment in part.into_inner() {
                    match segment.as_rule() {
                        Rule::node => {
                            prior_node = Some(pg.merge_node(pc, parse_pattern_node(segment)));
                            if let Some(mut rel) = prior_rel {
                                rel.right_node = prior_node.as_ref().unwrap().clone(); // TODO lol
                                pg.merge_rel(pc, rel);
                                prior_rel = None
                            }
                        }
                        Rule::rel => {
                            prior_rel = Some(parse_pattern_rel(prior_node.expect("pattern rel must be preceded by node"), segment));
                            prior_node = None
                        }
                        _ => unreachable!(),
                    }
                }
            }
            _ => unreachable!(),
        }
    }

    println!("built pg: {:?}", pg);

    return plan
}

// Figures out what step we need to find the specified node
fn parse_pattern_node(pattern_node: Pair<Rule>) -> PatternNode {
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

    return PatternNode{ identifier: identifier.to_string(), labels: vec![label.to_string()] }
}

fn parse_pattern_rel(left_node: String, pattern_rel: Pair<Rule>) -> PatternRel {
    let mut identifier = "";
    let mut rel_type = "";
    for part in pattern_rel.into_inner() {
        match part.as_rule() {
            Rule::id => {
                identifier = part.as_str()
            }
            Rule::rel_type => {
                rel_type = part.as_str()
            }
            _ => unreachable!(),
        }
    }
    // TODO don't use this empty identifier here
    return PatternRel{ left_node, right_node: String::from(""), identifier: identifier.to_string(), rel_type: rel_type.to_string() }
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

// Pointer to a Val in a row
pub type Slot = usize;

#[derive(Debug)]
pub enum Expr {
    Lit(Val),
    // Lookup a property by id
    Prop(Box<Expr>, Vec<Id>),
    Slot(Slot),
}

impl Expr {

    fn eval_prop(ctx: &mut Context, row: &mut Row, expr: &Box<Expr>, props: &Vec<Id>) -> Result<Val, Error> {
        let mut v = expr.eval(ctx, row)?;
        for prop in props {
            v = v.get(ctx, row, prop)?;
        }
        return Ok(v)
    }

    fn eval(&self, ctx: &mut Context, row: &mut Row) -> Result<Val, Error> {
        match self {
            Expr::Prop(expr, props) => Expr::eval_prop(ctx, row, expr, props),
            Expr::Slot(slot) => Ok(row.slots[*slot].clone()), // TODO not this
            Expr::Lit(v) => Ok(v.clone()), // TODO not this
            _ => panic!("{:?}", self)
        }
    }
}

#[derive(Debug)]
pub struct Node {
    labels: HashSet<String>,
    properties: HashMap<String, Val>,
}

pub type Id = String;

#[derive(Debug,Clone)]
pub enum Val {
    Null,
    String(String),
    Node(usize),
}

impl Val {
    fn get(&self, ctx: &mut Context, row: &mut Row, prop: &Id) -> Result<Val, Error>  {
        match self {
            Val::Null=> Err(Error{ msg: format!("NULL has no property {}", prop) }),
            Val::String(_) => Err(Error{ msg: format!("STRING has no property {}", prop) }),
            Val::Node(id) => match ctx.g.get_node_prop(*id, prop) {
                Some(v) => Ok(v),
                None => Ok(Null),
            },
        }
    }
}

impl Display for Val {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Val::Null=> f.write_str("NULL"),
            Val::String(s) => f.write_str(&s),
            Val::Node(id) => f.write_str(&format!("Node({})", id))
        }
    }
}


#[derive(Debug)]
pub struct Graph  {
    nodes: Vec<Node>

}

impl Graph {
    fn get_node_prop(&self, node_id: usize, prop: &Id) -> Option<Val> {
        if let Some(v) = self.nodes[node_id].properties.get(prop) {
            Some(v.clone())
        } else {
            None
        }
    }
}
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

    let mut tokens = Tokens { table: Default::default() };
    let lbl_note = tokens.tokenize("Note");
    let lbl_reference = tokens.tokenize("Reference");
    let key_message = tokens.tokenize("message");
    let mut g = Graph{ nodes: vec![
        Node::new(vec!( lbl_note ), [ (key_message, Val::String(String::from("a message"))) ].iter().cloned().collect()),
        Node::new(vec!( lbl_note ), [ (key_message, Val::String(String::from("other message.."))) ].iter().cloned().collect()),
        Node::new(vec!( lbl_note ), [ (key_message, Val::String(String::from("that other note made me think of this thing"))) ].iter().cloned().collect()),
        Node::new(vec!( lbl_reference ), Default::default() ),
    ] };
    g.add_rel(0, 1, tokens.tokenize("RELATES_TO"));
    g.add_rel(0, 2, tokens.tokenize("RELATES_TO"));
    g.add_rel(1, 3, tokens.tokenize("REFERENCES"));
    let mut pc = PlanningContext{ g: Rc::new(g), slots: Default::default(), anon_rel_seq:0, anon_node_seq: 0, tokens: tokens, };
    let mut plan: Box<dyn Step> = Box::new(Leaf{});

    for stmt in query.into_inner() {
        match stmt.as_rule() {
            Rule::match_stmt => {
                plan = plan_match(&mut pc, plan, stmt);
            }
            Rule::create_stmt => {
                let create_stmt = stmt.into_inner();
                println!("{}", create_stmt.as_str())
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
                return
            }
            Err(e) => {
                panic!(e.msg)
            }
        }
    }
}

type Token = usize;


struct Tokens {
    table: HashMap<String, Token>,
}

impl Tokens {
    fn tokenize(&mut self, contents: &str) -> Token {
        match self.table.get(contents) {
            Some(tok) => { return *tok }
            None => {
                let tok = self.table.len();
                self.table.insert(contents.to_string(), tok);
                return tok
            }
        }
    }

    fn get(&self, tok: Token) -> Option<&str> {
        for (content, candidate) in self.table.iter() {
            if *candidate == tok {
                return Some(&content);
            }
        }
        return None
    }
}

struct PlanningContext {
    g: Rc<Graph>,
    // slot assignments by name in output row
    slots: HashMap<Token, usize>,

    tokens: Tokens,

    anon_rel_seq: u32,
    anon_node_seq: u32,
}

impl PlanningContext {


    pub fn get_or_alloc_slot(&mut self, tok: Token) -> usize {
        match self.slots.get(&tok) {
            Some(slot) => { return *slot },
            None => {
                let slot = self.slots.len();
                self.slots.insert(tok, slot);
                return slot
            }
        }
    }

    pub fn new_anon_rel(&mut self) -> Token {
        let seq = self.anon_rel_seq;
        self.anon_rel_seq += 1;
        return self.tokens.tokenize(&format!("AnonRel#{}", seq))
    }

    pub fn new_anon_node(&mut self) -> Token {
        let seq = self.anon_node_seq;
        self.anon_node_seq += 1;
        return self.tokens.tokenize(&format!("AnonNode#{}", seq))
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
                let tok = pc.tokens.tokenize(inner.as_str());
                return Expr::Slot(pc.get_or_alloc_slot(tok))
            }
            Rule::prop_lookup => {
                let mut prop_lookup = inner.into_inner();
                let prop_lookup_expr = prop_lookup.next().unwrap();
                let base = match prop_lookup_expr.as_rule() {
                    Rule::id => {
                        let tok = pc.tokens.tokenize(prop_lookup_expr.as_str());
                        Expr::Slot(pc.get_or_alloc_slot(tok))
                    }
                    _ => unreachable!(),
                };
                let mut props = Vec::new();
                for p_inner in prop_lookup {
                    if let Rule::id = p_inner.as_rule() {
                        props.push(pc.tokens.tokenize(p_inner.as_str()));
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
    identifier: Token,
    labels: Vec<Token>,
    solved: bool,
}

impl PatternNode {
    fn merge(&mut self, other: &PatternNode) {

    }
}

#[derive(Debug)]
struct PatternRel {
    identifier: Token,
    rel_type: Token,
    left_node: Token,
    right_node: Option<Token>,
    solved: bool,
}

#[derive(Debug)]
struct PatternGraph {
    e: HashMap<Token, PatternNode>,
    v: Vec<PatternRel>,
}

impl PatternGraph {
    fn merge_node(&mut self, pc: &mut PlanningContext, mut n: PatternNode) {
        let entry = self.e.entry(n.identifier);
        entry.and_modify(|on| on.merge(&n)).or_insert(n);
    }

    fn merge_rel(&mut self, pc: &mut PlanningContext, mut r: PatternRel) {
        self.v.push(r)
    }
}

fn plan_match<'i>(pc: &mut PlanningContext, src: Box<dyn Step + 'i>, match_stmt: Pair<'i, Rule>) -> Box<dyn Step + 'i> {
    let mut plan: Box<dyn Step + 'i> = src;
    let mut pg: PatternGraph = PatternGraph{ e: HashMap::new(), v: Vec::new()};

    for part in match_stmt.into_inner() {
        match part.as_rule() {
            Rule::pattern => {
                let mut prior_node_id = None;
                let mut prior_rel: Option<PatternRel> = None;
                // For each node and rel segment of eg: (n:Message)-[:KNOWS]->()
                for segment in part.into_inner() {
                    match segment.as_rule() {
                        Rule::node => {
                            let prior_node = parse_pattern_node(pc, segment);
                            prior_node_id = Some(prior_node.identifier);
                            pg.merge_node(pc, prior_node);
                            if let Some(mut rel) = prior_rel {
                                rel.right_node = prior_node_id;
                                pg.merge_rel(pc, rel);
                                prior_rel = None
                            }
                        }
                        Rule::rel => {
                            prior_rel = Some(parse_pattern_rel(pc,prior_node_id.expect("pattern rel must be preceded by node"), segment));
                            prior_node_id = None
                        }
                        _ => unreachable!(),
                    }
                }
            }
            _ => unreachable!(),
        }
    }

    // Ok, now we have parsed the pattern into a full graph, time to start solving it
    println!("built pg: {:?}", pg);
    // Start by picking one high-selectivity node
    for (id, candidate) in &mut pg.e {
        // Advanced algorithm: Pick first node with a label filter on it and call it an afternoon
        if candidate.labels.len() > 0 {
            plan = Box::new(NodeScan{
                src: plan,
                next_node: 0,
                slot: pc.get_or_alloc_slot(*id),
                labels: candidate.labels.first().cloned(),
            });
            candidate.solved = true;
            break
        }
    }

    // Now we iterate until the whole pattern is solved. The way this works is that "solving"
    // a part of the pattern expands the plan such that when the top-level part of the plan is
    // executed, all the solved identifiers will be present in the output row. That then unlocks
    // the ability to solve other parts of the pattern, and so on.
    loop {
        let mut found_unsolved = false;
        let mut solved_any = false;
        // Look for relationships we can expand
        for mut rel in &mut pg.v {
            if rel.solved {
                continue
            }
            found_unsolved = true;

            let right_id = rel.right_node.unwrap();
            let left_id = rel.left_node;
            let left_solved = pg.e.get(&left_id).unwrap().solved;
            let right_solved = pg.e.get_mut(&right_id).unwrap().solved;

            if left_solved && !right_solved {
                // Left is solved and right isn't, so we can expand to the right
                let mut right_node = pg.e.get_mut(&right_id).unwrap();
                right_node.solved = true;
                rel.solved = true;
                solved_any = true;
                plan = Box::new( Expand::new(
                    plan,  pc.get_or_alloc_slot(left_id), pc.get_or_alloc_slot(right_id), pc.get_or_alloc_slot(rel.identifier), rel.rel_type
                ) );
            } else if !left_solved && right_solved {
                // Right is solved and left isn't, so we can expand to the left
                let mut left_node = pg.e.get_mut(&left_id).unwrap();
                left_node.solved = true;
                rel.solved = true;
                solved_any = true;
                plan = Box::new( Expand::new(
                    plan,  pc.get_or_alloc_slot(right_id), pc.get_or_alloc_slot(left_id), pc.get_or_alloc_slot(rel.identifier), rel.rel_type
                ) );
            }
        }

        if !found_unsolved {
            break
        }

        if !solved_any {
            panic!("Failed to solve pattern: {:?}", pg)
        }
    }

    return plan
}

// Figures out what step we need to find the specified node
fn parse_pattern_node(pc: &mut PlanningContext, pattern_node: Pair<Rule>) -> PatternNode {
    let mut identifier = None;
    let mut label = None;
    for part in pattern_node.into_inner() {
        match part.as_rule() {
            Rule::id => {
                identifier = Some(pc.tokens.tokenize(part.as_str()))
            }
            Rule::label => {
                label = Some(pc.tokens.tokenize(part.as_str()))
            }
            _ => unreachable!(),
        }
    }

    let id = identifier.unwrap_or_else(||pc.new_anon_node());

    return PatternNode{ identifier: id, labels: vec![label.expect("Label currently required")], solved: false }
}

fn parse_pattern_rel(pc: &mut PlanningContext, left_node: Token, pattern_rel: Pair<Rule>) -> PatternRel {
    let mut identifier = None;
    let mut rel_type = None;
    for part in pattern_rel.into_inner() {
        match part.as_rule() {
            Rule::id => {
                identifier = Some(pc.tokens.tokenize(part.as_str()))
            }
            Rule::rel_type => {
                rel_type = Some(pc.tokens.tokenize(part.as_str()))
            }
            _ => unreachable!(),
        }
    }
    // TODO don't use this empty identifier here
    let id = identifier.unwrap_or_else(|| pc.new_anon_rel());
    let rt = rel_type.unwrap_or_else(||pc.new_anon_rel());
    return PatternRel{ left_node, right_node: None, identifier: id, rel_type: rt, solved: false }
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
    Prop(Box<Expr>, Vec<Token>),
    Slot(Slot),
}

impl Expr {

    fn eval_prop(ctx: &mut Context, row: &mut Row, expr: &Box<Expr>, props: &Vec<Token>) -> Result<Val, Error> {
        let mut v = expr.eval(ctx, row)?;
        for prop in props {
            v = v.get(ctx, row, *prop)?;
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
    labels: HashSet<Token>,
    properties: HashMap<Token, Val>,
    rels: Vec<RelHalf>,
}

impl Node {
    pub fn new(labels: Vec<Token>, properties: HashMap<Token, Val>) -> Node {
        return Node {
            labels: labels.iter().cloned().collect(),
            properties,
            rels: vec![]
        }
    }
}

#[derive(Debug)]
pub struct RelHalf {
    rel_type: Token,
    dir: Dir,
    other_node: usize,
    properties: Rc<HashMap<Token, Val>>,
}

#[derive(Debug)]
pub enum Dir {
    Out, In
}

// TODO poorly named, "Identifier", not "Node Id", probably just replace this with "Token", or a dedicated "SlotIdentifier"?
pub type Id = String;

#[derive(Debug,Clone)]
pub enum Val {
    Null,
    String(String),
    Node(usize),
    Rel{ node: usize, rel_index: usize },
}

impl Val {
    fn get(&self, ctx: &mut Context, row: &mut Row, prop: Token) -> Result<Val, Error>  {
        match self {
            Val::Null=> Err(Error{ msg: format!("NULL has no property {}", prop) }),
            Val::String(_) => Err(Error{ msg: format!("STRING has no property {}", prop) }),
            Val::Node(id) => match ctx.g.get_node_prop(*id, prop) {
                Some(v) => Ok(v),
                None => Ok(Null),
            },
            Val::Rel{node, rel_index} => match ctx.g.get_rel_prop(*node, *rel_index, prop) {
                Some(v) => Ok(v),
                None => Ok(Null),
            },
        }
    }

    fn as_node_id(&self) -> usize {
        match self {
            Val::Node(id) => *id,
            _ => panic!("invalid execution plan, non-node value feeds into thing expecting node value")
        }
    }
}

impl Display for Val {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Val::Null=> f.write_str("NULL"),
            Val::String(s) => f.write_str(&s),
            Val::Node(id) => f.write_str(&format!("Node({})", id)),
            Val::Rel{node, rel_index} => f.write_str(&format!("Rel({}/{})", node, rel_index))
        }
    }
}


#[derive(Debug)]
pub struct Graph  {
    nodes: Vec<Node>

}

impl Graph {
    fn get_node_prop(&self, node_id: usize, prop: Token) -> Option<Val> {
        if let Some(v) = self.nodes[node_id].properties.get(&prop) {
            Some(v.clone())
        } else {
            None
        }
    }

    fn get_rel_prop(&self, node_id: usize, rel_index: usize, prop: Token) -> Option<Val> {
        if let Some(v) = self.nodes[node_id].rels[rel_index].properties.get(&prop) {
            Some(v.clone())
        } else {
            None
        }
    }

    fn add_rel(&mut self, from: usize, to: usize, rel_type: Token) {
        let props = Rc::new(Default::default());
        self.nodes[from].rels.push(RelHalf{
            rel_type,
            dir: Dir::Out,
            other_node: to,
            properties: Rc::clone(&props)
        });
        self.nodes[to].rels.push(RelHalf{
            rel_type,
            dir: Dir::In,
            other_node: from,
            properties: props,
        })
    }
}
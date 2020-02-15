//
// The gqlite frontend contains the gql parser and logical planner.
// It produces a LogicalPlan, describing what needs to occur to fulfill the input query.
//

use pest::Parser;

use std::fmt::{Debug};
use pest::iterators::Pair;
use crate::{Token, Slot, Val, Error, Row};
use std::collections::HashMap;
use std::rc::Rc;
use crate::backend::Tokens;
use std::cell::RefCell;

#[derive(Parser)]
#[grammar = "cypher.pest"]
pub struct CypherParser;

#[derive(Debug)]
pub struct Frontend {
    pub tokens: Rc<RefCell<Tokens>>,
}

impl Frontend {
    // TODO obviously the query string shouldn't be static
    pub fn plan(&self, query_str: &'static str) -> Result<LogicalPlan, Error> {
        let query = CypherParser::parse(Rule::query, query_str)
            .expect("unsuccessful parse") // unwrap the parse result
            .next().unwrap(); // get and unwrap the `file` rule; never fails

        let mut statement_count: u64 = 0;

        let mut pc = PlanningContext{
            slots: Default::default(),
            anon_rel_seq:0, anon_node_seq: 0,
            tokens: Rc::clone(&self.tokens), };
        let mut plan = LogicalPlan::Argument;

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

        return Ok(plan)
    }
}

#[derive(Debug)]
pub enum LogicalPlan {
    Argument,
    NodeScan{
        src: Box<Self>,
        slot: usize,
        labels: Option<Token>,
    },
    Expand{
        src: Box<Self>,
        src_slot: usize,
        rel_slot: usize,
        dst_slot: usize,
        rel_type: Token,
    },
    Return{
        src: Box<Self>,
        projections: Vec<Projection>,
    }
}

#[derive(Debug)]
pub struct Projection {
    pub expr: Expr,
    pub alias: String, // TODO this should be Token
}


struct PlanningContext {
    // slot assignments by name in output row
    slots: HashMap<Token, usize>,

    // TODO is there some nicer way to do this than Rc+RefCell?
    tokens: Rc<RefCell<Tokens>>,

    anon_rel_seq: u32,
    anon_node_seq: u32,
}

impl PlanningContext {

    fn tokenize(&mut self, contents: &str) -> Token {
        self.tokens.borrow_mut().tokenize(contents)
    }

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
        return self.tokenize(&format!("AnonRel#{}", seq))
    }

    pub fn new_anon_node(&mut self) -> Token {
        let seq = self.anon_node_seq;
        self.anon_node_seq += 1;
        return self.tokenize(&format!("AnonNode#{}", seq))
    }

    pub fn new_row(&self) -> Row {
        return Row{ slots: vec![Val::Null;self.slots.len()] }
    }
}

fn plan_create(pc: &mut PlanningContext, src: LogicalPlan, create_stmt: Pair<Rule>) -> LogicalPlan {
    let mut pg = parse_pattern_graph(pc,create_stmt);

    println!("pg: {:?}", pg);

    // So.. just create all unsolved parts of the pattern?


    return src;
}

fn plan_return(pc: &mut PlanningContext, src: LogicalPlan, return_stmt: Pair<Rule>) -> LogicalPlan {
    let mut parts = return_stmt.into_inner();
    let projections = parts.next().and_then(|p| Some(plan_return_projections(pc, p))).expect("RETURN must start with projections");
    return LogicalPlan::Return{ src: Box::new(src), projections };
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
                let tok = pc.tokenize(inner.as_str());
                return Expr::Slot(pc.get_or_alloc_slot(tok))
            }
            Rule::prop_lookup => {
                let mut prop_lookup = inner.into_inner();
                let prop_lookup_expr = prop_lookup.next().unwrap();
                let base = match prop_lookup_expr.as_rule() {
                    Rule::id => {
                        let tok = pc.tokenize(prop_lookup_expr.as_str());
                        Expr::Slot(pc.get_or_alloc_slot(tok))
                    }
                    _ => unreachable!(),
                };
                let mut props = Vec::new();
                for p_inner in prop_lookup {
                    if let Rule::id = p_inner.as_rule() {
                        props.push(pc.tokenize(p_inner.as_str()));
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
pub struct PatternNode {
    identifier: Token,
    labels: Vec<Token>,
    solved: bool,
}

impl PatternNode {
    fn merge(&mut self, other: &PatternNode) {

    }
}

#[derive(Debug)]
pub struct PatternRel {
    identifier: Token,
    rel_type: Token,
    left_node: Token,
    right_node: Option<Token>,
    solved: bool,
}

#[derive(Debug)]
pub struct PatternGraph {
    e: HashMap<Token, PatternNode>,
    v: Vec<PatternRel>,
}

impl PatternGraph {
    fn merge_node(&mut self, pc: &mut PlanningContext, n: PatternNode) {
        let entry = self.e.entry(n.identifier);
        entry.and_modify(|on| on.merge(&n)).or_insert(n);
    }

    fn merge_rel(&mut self, pc: &mut PlanningContext, r: PatternRel) {
        self.v.push(r)
    }
}

fn plan_match<'i>(pc: &mut PlanningContext, src: LogicalPlan, match_stmt: Pair<'i, Rule>) -> LogicalPlan {
    let mut plan = src;
    let mut pg = parse_pattern_graph(pc, match_stmt);

    // Ok, now we have parsed the pattern into a full graph, time to start solving it
    println!("built pg: {:?}", pg);
    // Start by picking one high-selectivity node
    for (id, candidate) in &mut pg.e {
        // Advanced algorithm: Pick first node with a label filter on it and call it an afternoon
        if candidate.labels.len() > 0 {
            plan = LogicalPlan::NodeScan{
                src: Box::new(plan),
                slot: pc.get_or_alloc_slot(*id),
                labels: candidate.labels.first().cloned(),
            };
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
                plan = LogicalPlan::Expand {
                    src: Box::new(plan),
                    src_slot: pc.get_or_alloc_slot(left_id),
                    rel_slot: pc.get_or_alloc_slot(rel.identifier),
                    dst_slot:  pc.get_or_alloc_slot(right_id),
                    rel_type: rel.rel_type,
                };
            } else if !left_solved && right_solved {
                // Right is solved and left isn't, so we can expand to the left
                let mut left_node = pg.e.get_mut(&left_id).unwrap();
                left_node.solved = true;
                rel.solved = true;
                solved_any = true;
                plan = LogicalPlan::Expand {
                    src: Box::new(plan),
                    src_slot: pc.get_or_alloc_slot(right_id),
                    rel_slot: pc.get_or_alloc_slot(rel.identifier),
                    dst_slot:  pc.get_or_alloc_slot(left_id),
                    rel_type: rel.rel_type,
                };
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

fn parse_pattern_graph(pc: &mut PlanningContext, patterns: Pair<Rule>) -> PatternGraph {
    let mut pg: PatternGraph = PatternGraph{ e: HashMap::new(), v: Vec::new()};

    for part in patterns.into_inner() {
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

    return pg;
}

// Figures out what step we need to find the specified node
fn parse_pattern_node(pc: &mut PlanningContext, pattern_node: Pair<Rule>) -> PatternNode {
    let mut identifier = None;
    let mut label = None;
    for part in pattern_node.into_inner() {
        match part.as_rule() {
            Rule::id => {
                identifier = Some(pc.tokenize(part.as_str()))
            }
            Rule::label => {
                label = Some(pc.tokenize(part.as_str()))
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
                identifier = Some(pc.tokenize(part.as_str()))
            }
            Rule::rel_type => {
                rel_type = Some(pc.tokenize(part.as_str()))
            }
            _ => unreachable!(),
        }
    }
    // TODO don't use this empty identifier here
    let id = identifier.unwrap_or_else(|| pc.new_anon_rel());
    let rt = rel_type.unwrap_or_else(||pc.new_anon_rel());
    return PatternRel{ left_node, right_node: None, identifier: id, rel_type: rt, solved: false }
}

#[derive(Debug)]
pub enum Expr {
    Lit(Val),
    // Lookup a property by id
    Prop(Box<Self>, Vec<Token>),
    Slot(Slot),
}

// TODO poorly named, "Identifier", not "Node Id", probably just replace this with "Token", or a dedicated "SlotIdentifier"?
pub type Id = String;

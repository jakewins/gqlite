
// The Gram backend is a backend implementation that acts on a Gram file.
// It is currently single threaded, and provides no data durability guarantees.

use crate::{Error, Val, Dir, Slot, Row, Cursor, frontend, CursorState};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::cell::RefCell;
use super::PreparedStatement;
use crate::frontend::{LogicalPlan};
use std::fmt::Debug;
use crate::backend::{Tokens, Token};

#[derive(Debug)]
pub struct GramBackend {
    tokens: Rc<RefCell<Tokens>>,
    g: Rc<Graph>,
}

impl GramBackend {
    pub fn open(path: &str) -> Result<GramBackend, Error> {
        let mut tokens = Tokens { table: Default::default() };
        let mut g = parser::load(&mut tokens, path)?;

        return Ok(GramBackend {
            tokens: Rc::new(RefCell::new(tokens)), g: Rc::new(g)
        })
    }

    fn convert(&self, plan: Box<LogicalPlan>) -> Result<Box<dyn Operator>, Error> {
        match *plan {
            LogicalPlan::Argument => Ok(Box::new(Argument{})),
            LogicalPlan::NodeScan { src, slot, labels } => Ok(Box::new(NodeScan{
                src: self.convert(src)?,
                next_node: 0,
                slot,
                labels
            })),
            LogicalPlan::Expand { src, src_slot, rel_slot, dst_slot, rel_type } => Ok(Box::new(Expand{
                src: self.convert(src)?,
                src_slot,
                rel_slot,
                dst_slot,
                rel_type,
                next_rel_index: 0,
                state: ExpandState::NextNode
            })),
            LogicalPlan::Create { .. } => {
                panic!("The gram backend does not yet support CREATE statements")
            }
            LogicalPlan::Return { src, projections } => {
                let mut converted_projections = Vec::new();
                for projection in projections {
                    converted_projections.push(Projection{
                        expr: self.convert_expr(projection.expr),
                        alias: projection.alias })
                }

                Ok(Box::new(Return{
                    src: self.convert(src)?,
                    projections: converted_projections }))
            },
        }
    }

    fn convert_expr(&self, expr: frontend::Expr) -> Expr {
        match expr {
            frontend::Expr::Lit(v) => Expr::Lit(v),
            frontend::Expr::Prop(e, props) => Expr::Prop(Box::new(self.convert_expr(*e)), props),
            frontend::Expr::Slot(s) => Expr::Slot(s),
        }
    }
}

impl super::Backend for GramBackend {
    fn tokens(&self) -> Rc<RefCell<Tokens>> {
        Rc::clone(&self.tokens)
    }

    fn prepare(&self, logical_plan: Box<LogicalPlan>) -> Result<Box<dyn PreparedStatement>, Error> {
        let plan = self.convert(logical_plan)?;
        return Ok(Box::new(Statement{ g: Rc::clone(&self.g), plan,
            // TODO: pipe this knowledge through from logial plan
            num_slots: 16 }))
    }
}

#[derive(Debug)]
struct Statement {
    g: Rc<Graph>,
    plan: Box<dyn Operator>,
    num_slots: usize,
}

impl PreparedStatement for Statement {
    fn run(&mut self, cursor: &mut Cursor) -> Result<(), Error> {
        cursor.state = Some(Box::new(GramCursorState{
            ctx: Context{ g: Rc::clone(&self.g)},
            plan: self.plan.clone(),
        }));
        if cursor.row.slots.len() < self.num_slots {
            cursor.row.slots.resize(self.num_slots, Val::Null);
        }
        return Ok(())
    }
}

#[derive(Debug)]
struct GramCursorState {
    ctx: Context,
    plan: Box<dyn Operator>
}

impl CursorState for GramCursorState {
    fn next(&mut self, row: &mut Row) -> Result<bool, Error> {
        self.plan.next(&mut self.ctx, row)
    }
}

#[derive(Debug)]
struct Context {
    g: Rc<Graph>,
}

#[derive(Debug, Clone)]
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
            v = match v {
                Val::Null=> Err(Error{ msg: format!("NULL has no property {}", prop) }),
                Val::String(_) => Err(Error{ msg: format!("STRING has no property {}", prop) }),
                Val::Node(id) => match ctx.g.get_node_prop(id, *prop) {
                    Some(v) => Ok(v),
                    None => Ok(Val::Null),
                },
                Val::Rel{node, rel_index} => match ctx.g.get_rel_prop(node, rel_index, *prop) {
                    Some(v) => Ok(v),
                    None => Ok(Val::Null),
                },
            }?;
        }
        return Ok(v)
    }

    fn eval(&self, ctx: &mut Context, row: &mut Row) -> Result<Val, Error> {
        match self {
            Expr::Prop(expr, props) => Expr::eval_prop(ctx, row, expr, props),
            Expr::Slot(slot) => Ok(row.slots[*slot].clone()), // TODO not this
            Expr::Lit(v) => Ok(v.clone()), // TODO not this
        }
    }
}

// Physical operator. We have one of these for each Logical operator the frontend emits.
trait Operator: Debug {
    fn next(&mut self, ctx: &mut Context, row: &mut Row) -> Result<bool, Error>;

    // I can't figure out how do implement the normal "Clone" trait for this trait..
    fn clone(&self) -> Box<dyn Operator>;
}

#[derive(Debug)]
pub enum ExpandState {
    NextNode,
    InNode,
}

#[derive(Debug)]
struct Expand {
    pub src: Box<dyn Operator>,

    pub src_slot: usize,

    pub rel_slot: usize,

    pub dst_slot: usize,

    pub rel_type: Token,

    // In the current adjacency list, what is the next index we should return?
    pub next_rel_index: usize,

    pub state: ExpandState,
}

impl Expand {
    pub fn new (src: Box<dyn Operator>, src_slot: usize, dst_slot: usize, rel_slot: usize, rel_type: Token) -> Expand {
        return Expand{
            src,
            src_slot,
            rel_slot,
            dst_slot,
            rel_type,
            next_rel_index: 0,
            state: ExpandState::NextNode
        }
    }
}

impl Operator for Expand {
    fn next(&mut self, ctx: &mut Context, out: &mut Row) -> Result<bool, Error> {
        loop {
            match &self.state {
                ExpandState::NextNode => {
                    // Pull in the next node
                    if ! self.src.next(ctx, out)? {
                        return Ok(false)
                    }
                    self.state = ExpandState::InNode;
                },
                ExpandState::InNode => {
                    let node = out.slots[self.src_slot].as_node_id();
                    let rels = &ctx.g.nodes[node].rels;
                    if self.next_rel_index >= rels.len() {
                        // No more rels on this node
                        self.state = ExpandState::NextNode;
                        self.next_rel_index = 0;
                        continue
                    }

                    let rel = &rels[self.next_rel_index];
                    self.next_rel_index += 1;

                    if rel.rel_type == self.rel_type {
                        out.slots[self.rel_slot] = Val::Rel{ node, rel_index: self.next_rel_index-1 };
                        out.slots[self.dst_slot] = Val::Node( rel.other_node );
                        return Ok(true);
                    }
                },
            }
        }
    }

    fn clone(&self) -> Box<dyn Operator> {
        Box::new(Expand{
            src: self.src.clone(),
            src_slot: self.src_slot,
            rel_slot: self.rel_slot,
            dst_slot: self.dst_slot,
            rel_type: self.rel_type,
            next_rel_index: 0,
            state: ExpandState::NextNode,
        })
    }
}

// For each src row, perform a full no de scan with the specified filters
#[derive(Debug)]
struct NodeScan {
    pub src: Box<dyn Operator>,

    // Next node id in g to return
    pub next_node: usize,

    // Where should this scan write its output?
    pub slot: usize,

    // If the empty string, return all nodes, otherwise only nodes with the specified label
    pub labels: Option<Token>,
}

impl Operator for NodeScan {
    fn next(&mut self, ctx: &mut Context, out: &mut Row) -> Result<bool, Error> {
        loop {
            if ctx.g.nodes.len() > self.next_node {
                let node = ctx.g.nodes.get(self.next_node).unwrap();
                if let Some(tok) = self.labels {
                    if !node.labels.contains(&tok) {
                        self.next_node += 1;
                        continue;
                    }
                }

                out.slots[self.slot] = Val::Node(self.next_node);
                self.next_node += 1;
                return Ok(true)
            }
            return Ok(false)
        }
    }

    fn clone(&self) -> Box<dyn Operator> {
        Box::new(NodeScan{
            src: self.src.clone(),
            next_node: 0,
            slot: self.slot,
            labels: self.labels,
        })
    }
}

#[derive(Debug, Clone)]
struct Argument;

impl Operator for Argument {
    fn next(&mut self, ctx: &mut Context, out: &mut Row) -> Result<bool, Error> {
        unimplemented!()
    }

    fn clone(&self) -> Box<dyn Operator> {
        Box::new(Argument{})
    }
}

#[derive(Debug, Clone)]
struct Projection {
    pub expr: Expr,
    pub alias: String,
}

#[derive(Debug)]
struct Return {
    pub src: Box<dyn Operator>,
    pub projections: Vec<Projection>,
}

impl Operator for Return {
    fn next(&mut self, ctx: &mut Context, out: &mut Row) -> Result<bool, Error> {
        println!("----");
        let mut first = true;
        for cell in &self.projections {
            if first {
                print!("{}", cell.alias);
                first = false
            } else {
                print!(", {}", cell.alias)
            }
        }
        println!();
        println!("----");
        while self.src.next(ctx, out)? {
            first = true;
            for cell in &self.projections {
                let v = cell.expr.eval(ctx, out)?;
                if first {
                    print!("{}", v);
                    first = false
                } else {
                    print!(", {}", v)
                }
            }
            println!();
        }
        Ok(false)
    }

    fn clone(&self) -> Box<dyn Operator> {
        Box::new(Return{
            src: self.src.clone(),
            projections: self.projections.clone(),
        })
    }
}

mod parser {
    use std::collections::{HashMap};
    use crate::pest::Parser;
    use crate::backend::gram::{Node, Graph};
    use crate::{Error, Val};
    use crate::backend::{Tokens, Token};

    #[derive(Parser)]
    #[grammar = "backend/gram.pest"]
    pub struct GramParser;

    pub fn load(tokens: &mut Tokens, path: &str) -> Result<Graph, Error> {
        let mut g = Graph{ nodes: vec![] };


        let query_str = std::fs::read_to_string(path).unwrap();
        let maybe_parse = GramParser::parse(Rule::gram, &query_str);

        let gram = maybe_parse
            .expect("unsuccessful parse") // unwrap the parse result
            .next().unwrap(); // get and unwrap the `file` rule; never fails

//    let id_map = HashMap::new();
        let mut node_ids = Tokens{ table: Default::default() };

        for item in gram.into_inner() {
            match item.as_rule() {
                Rule::path => {
                    let mut start_identifier : Option<Token> = None;
                    let mut end_identifier : Option<Token> = None;
                    let mut props : HashMap<Token, Val> = HashMap::new();

                    for part in item.into_inner() {
                        match part.as_rule() {
                            Rule::node => {
                                let identifier = part.into_inner().next().unwrap().as_str();
                                if start_identifier == None {
                                    start_identifier = Some(node_ids.tokenize(identifier));
                                } else {
                                    end_identifier = Some(node_ids.tokenize(identifier));
                                }
                            }
                            Rule::rel => {
                                for rel_part in part.into_inner() {
                                    match rel_part.as_rule() {
                                        Rule::map => {

                                        }
                                        _ => panic!("what? {:?} / {}", rel_part.as_rule(), rel_part.as_str())
                                    }
                                }
                            }
                            _ => panic!("what? {:?} / {}", part.as_rule(), part.as_str())
                        }
                    }

                    g.add_rel(start_identifier.unwrap(), end_identifier.unwrap(), tokens.tokenize("KNOWS"));
                }
                Rule::node => {
                    let mut identifier : Option<String> = None;
                    let mut props : HashMap<Token, Val> = HashMap::new();

                    for part in item.into_inner() {
                        match part.as_rule() {
                            Rule::id => identifier = Some(part.as_str().to_string()),
                            Rule::map => {
                                for pair in part.into_inner() {
                                    let mut key: Option<String> = None;
                                    let mut val = None;
                                    match pair.as_rule() {
                                        Rule::map_pair => {
                                            for pair_part in pair.into_inner() {
                                                match pair_part.as_rule() {
                                                    Rule::id => key = Some(pair_part.as_str().to_string()),
                                                    Rule::expr => val = Some(pair_part.as_str().to_string()),
                                                    _ => panic!("what? {:?} / {}", pair_part.as_rule(), pair_part.as_str())
                                                }
                                            }
                                        }
                                        _ => panic!("what? {:?} / {}", pair.as_rule(), pair.as_str())
                                    }
                                    let key_str = key.unwrap();
                                    props.insert(tokens.tokenize(&key_str), Val::String(val.unwrap()) );
                                }
                            },
                            _ => panic!("what? {:?} / {}", part.as_rule(), part.as_str())
                        }
                    }

                    g.add_node(node_ids.tokenize(&identifier.unwrap()), Node{
                        labels: vec![tokens.tokenize("Person")].iter().cloned().collect(),
                        properties: props,
                        rels: vec![]
                    });
                },
                _ => ()
            }
        }

        return Ok(g)
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

    fn add_node(&mut self, id: usize, n: Node) {
        self.nodes.insert(id,n);
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
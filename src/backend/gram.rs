use crate::{Error, Token, Val, Dir, Slot, Row};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::cell::RefCell;
use super::PreparedStatement;
use crate::frontend::{LogicalPlan, Tokenizer};
use std::fmt::Debug;

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
}

impl super::Backend for GramBackend {
    fn tokenizer(&self) -> Rc<dyn Tokenizer> {
        unimplemented!()
    }

    fn prepare(&self, plan: LogicalPlan) -> Result<Box<dyn PreparedStatement>, Error> {
        unimplemented!()
    }
}

#[derive(Debug)]
pub struct Tokens {
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

struct Context {
    g: Rc<Graph>
}


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
            _ => panic!("{:?}", self)
        }
    }
}


trait PlanStep: Debug {
    fn next(&mut self, ctx: &mut Context, row: &mut Row) -> Result<bool, Error>;
}

#[derive(Debug)]
pub enum ExpandState {
    NextNode,
    InNode,
}

#[derive(Debug)]
struct Expand {
    pub src: Box<dyn PlanStep>,

    pub src_slot: usize,

    pub rel_slot: usize,

    pub dst_slot: usize,

    pub rel_type: Token,

    // In the current adjacency list, what is the next index we should return?
    pub next_rel_index: usize,

    pub state: ExpandState,
}

impl Expand {
    pub fn new (src: Box<dyn PlanStep>, src_slot: usize, dst_slot: usize, rel_slot: usize, rel_type: Token) -> Expand {
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
}

// For each src row, perform a full no de scan with the specified filters
#[derive(Debug)]
struct NodeScan {
    pub src: Box<dyn PlanStep>,

    // Next node id in g to return
    pub next_node: usize,

    // Where should this scan write its output?
    pub slot: usize,

    // If the empty string, return all nodes, otherwise only nodes with the specified label
    pub labels: Option<Token>,
}

impl PlanStep for NodeScan {
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
}

#[derive(Debug)]
struct Argument;

impl PlanStep for Argument {
    fn next(&mut self, ctx: &mut Context, out: &mut Row) -> Result<bool, Error> {
        unimplemented!()
    }
}

#[derive(Debug)]
struct Projection {
    pub expr: Expr,
    pub alias: String,
}

#[derive(Debug)]
struct Return {
    pub src: Box<dyn PlanStep>,
    pub projections: Vec<Projection>,
}

impl PlanStep for Return {
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
}

mod parser {
    use std::collections::{HashMap};
    use crate::pest::Parser;
    use crate::backend::gram::{Tokens, Node, Graph};
    use crate::{Error, Token, Val};

    #[derive(Parser)]
    #[grammar = "gram.pest"]
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
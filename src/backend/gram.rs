// The Gram backend is a backend implementation that acts on a Gram file.
// It is currently single threaded, and provides no data durability guarantees.

use super::PreparedStatement;
use crate::backend::{BackendDesc, FuncSignature, FuncType, Token, Tokens};
use crate::frontend::LogicalPlan;
use crate::{frontend, Cursor, CursorState, Dir, Error, Row, Slot, Type, Val};
use anyhow::Result;
use rand::Rng;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::fs::File;
use std::io::{Seek, SeekFrom, Write};
use std::rc::Rc;
use std::time::SystemTime;
use uuid::v1::{Context as UuidContext, Timestamp};
use uuid::Uuid;

#[derive(Debug)]
pub struct GramBackend {
    tokens: Rc<RefCell<Tokens>>,
    g: Rc<RefCell<Graph>>,
    file: Rc<RefCell<File>>,
}

impl GramBackend {
    pub fn open(mut file: File) -> Result<GramBackend> {
        let mut tokens = Tokens {
            table: Default::default(),
        };
        let g = parser::load(&mut tokens, &mut file)?;

        return Ok(GramBackend {
            tokens: Rc::new(RefCell::new(tokens)),
            g: Rc::new(RefCell::new(g)),
            file: Rc::new(RefCell::new(file)),
        });
    }

    fn convert(&self, plan: Box<LogicalPlan>) -> Result<Rc<RefCell<dyn Operator>>, Error> {
        match *plan {
            LogicalPlan::Argument => Ok(Rc::new(RefCell::new(Argument {}))),
            LogicalPlan::NodeScan { src, slot, labels } => Ok(Rc::new(RefCell::new(NodeScan {
                src: self.convert(src)?,
                next_node: 0,
                slot,
                labels,
            }))),
            LogicalPlan::Create { src, nodes, .. } => {
                let mut out_nodes = Vec::with_capacity(nodes.len());
                let mut i = 0;
                for ns in nodes {
                    let mut props = HashMap::new();
                    for k in ns.props {
                        props.insert(k.key, self.convert_expr(k.val));
                    }
                    out_nodes.insert(
                        i,
                        NodeSpec {
                            slot: ns.slot,
                            labels: ns.labels.iter().copied().collect(),
                            props: props,
                        },
                    );
                    i += 1;
                }
                Ok(Rc::new(RefCell::new(Create {
                    src: self.convert(src)?,
                    nodes: out_nodes,
                    tokens: self.tokens.clone(),
                })))
            }
            LogicalPlan::Expand {
                src,
                src_slot,
                rel_slot,
                dst_slot,
                rel_type,
                ..
            } => Ok(Rc::new(RefCell::new(Expand {
                src: self.convert(src)?,
                src_slot,
                rel_slot,
                dst_slot,
                rel_type,
                next_rel_index: 0,
                state: ExpandState::NextNode,
            }))),
            LogicalPlan::Return { src, projections } => {
                let mut converted_projections = Vec::new();
                for projection in projections {
                    converted_projections.push(Projection {
                        expr: self.convert_expr(projection.expr),
                        alias: projection.alias,
                    })
                }

                Ok(Rc::new(RefCell::new(Return {
                    src: self.convert(src)?,
                    projections: converted_projections,
                    print_header: true,
                })))
            }
            _ => panic!("The gram backend does not yet handle {:?}", plan),
        }
    }

    fn convert_expr(&self, expr: frontend::Expr) -> Expr {
        match expr {
            frontend::Expr::Lit(v) => Expr::Lit(v),
            frontend::Expr::Prop(e, props) => Expr::Prop(Box::new(self.convert_expr(*e)), props),
            frontend::Expr::Slot(s) => Expr::Slot(s),
            _ => panic!(
                "The gram backend does not support this expression type yet: {:?}",
                expr
            ),
        }
    }
}

impl super::Backend for GramBackend {
    fn tokens(&self) -> Rc<RefCell<Tokens>> {
        Rc::clone(&self.tokens)
    }

    fn prepare(&self, logical_plan: Box<LogicalPlan>) -> Result<Box<dyn PreparedStatement>> {
        let plan = self.convert(logical_plan)?;
        return Ok(Box::new(Statement {
            file: Rc::clone(&self.file),
            g: Rc::clone(&self.g),
            plan,
            // TODO: pipe this knowledge through from logial plan
            num_slots: 16,
        }));
    }

    fn describe(&self) -> Result<BackendDesc, Error> {
        let tok_count = self.tokens.borrow_mut().tokenize("count");
        let tok_expr = self.tokens.borrow_mut().tokenize("expr");
        Ok(BackendDesc::new(vec![FuncSignature {
            func_type: FuncType::Scalar,
            name: tok_count,
            returns: Type::Number,
            args: vec![(tok_expr, Type::Any)],
        }]))
    }
}

#[derive(Debug)]
struct Statement {
    g: Rc<RefCell<Graph>>,
    file: Rc<RefCell<File>>,
    plan: Rc<RefCell<dyn Operator>>,
    num_slots: usize,
}

impl PreparedStatement for Statement {
    fn run(&mut self, cursor: &mut Cursor) -> Result<(), Error> {
        cursor.state = Some(Box::new(GramCursorState {
            ctx: Context {
                g: Rc::clone(&self.g),
                file: Rc::clone(&self.file),
            },
            plan: self.plan.clone(),
        }));
        if cursor.row.slots.len() < self.num_slots {
            cursor.row.slots.resize(self.num_slots, Val::Null);
        }
        return Ok(());
    }
}

#[derive(Debug)]
struct GramCursorState {
    ctx: Context,
    plan: Rc<RefCell<dyn Operator>>,
}

impl CursorState for GramCursorState {
    fn next(&mut self, row: &mut Row) -> Result<bool> {
        self.plan.borrow_mut().next(&mut self.ctx, row)
    }
}

#[derive(Debug)]
struct Context {
    g: Rc<RefCell<Graph>>,
    file: Rc<RefCell<File>>,
}

#[derive(Debug, Clone)]
enum Expr {
    Lit(Val),
    // Lookup a property by id
    Prop(Box<Expr>, Vec<Token>),
    Slot(Slot),
}

impl Expr {
    fn eval_prop(ctx: &mut Context, row: &mut Row, expr: &Expr, props: &[Token]) -> Result<Val> {
        let mut v = expr.eval(ctx, row)?;
        for prop in props {
            v = match v {
                Val::Null => bail!("NULL has no property {}", prop),
                Val::String(_) => bail!("STRING has no property {}", prop),
                Val::Node(id) => ctx.g.borrow().get_node_prop(id, *prop).unwrap_or(Val::Null),
                Val::Rel { node, rel_index } => ctx
                    .g
                    .borrow()
                    .get_rel_prop(node, rel_index, *prop)
                    .unwrap_or(Val::Null),
            };
        }
        Ok(v)
    }

    fn eval(&self, ctx: &mut Context, row: &mut Row) -> Result<Val> {
        match self {
            Expr::Prop(expr, props) => Expr::eval_prop(ctx, row, expr, props),
            Expr::Slot(slot) => Ok(row.slots[*slot].clone()), // TODO not this
            Expr::Lit(v) => Ok(v.clone()),                    // TODO not this
        }
    }
}

// Physical operator. We have one of these for each Logical operator the frontend emits.
trait Operator: Debug {
    fn next(&mut self, ctx: &mut Context, row: &mut Row) -> Result<bool>;
}

#[derive(Debug)]
pub enum ExpandState {
    NextNode,
    InNode,
}

#[derive(Debug)]
struct Expand {
    pub src: Rc<RefCell<dyn Operator>>,

    pub src_slot: usize,

    pub rel_slot: usize,

    pub dst_slot: usize,

    pub rel_type: Token,

    // In the current adjacency list, what is the next index we should return?
    pub next_rel_index: usize,

    pub state: ExpandState,
}

impl Operator for Expand {
    fn next(&mut self, ctx: &mut Context, out: &mut Row) -> Result<bool> {
        loop {
            match &self.state {
                ExpandState::NextNode => {
                    // Pull in the next node
                    if !self.src.borrow_mut().next(ctx, out)? {
                        return Ok(false);
                    }
                    self.state = ExpandState::InNode;
                }
                ExpandState::InNode => {
                    let node = out.slots[self.src_slot].as_node_id();
                    let g = ctx.g.borrow();
                    let rels = &g.nodes[node].rels;
                    if self.next_rel_index >= rels.len() {
                        // No more rels on this node
                        self.state = ExpandState::NextNode;
                        self.next_rel_index = 0;
                        continue;
                    }

                    let rel = &rels[self.next_rel_index];
                    self.next_rel_index += 1;

                    if rel.rel_type == self.rel_type {
                        out.slots[self.rel_slot] = Val::Rel {
                            node,
                            rel_index: self.next_rel_index - 1,
                        };
                        out.slots[self.dst_slot] = Val::Node(rel.other_node);
                        return Ok(true);
                    }
                }
            }
        }
    }
}

// For each src row, perform a full no de scan with the specified filters
#[derive(Debug)]
struct NodeScan {
    pub src: Rc<RefCell<dyn Operator>>,

    // Next node id in g to return
    pub next_node: usize,

    // Where should this scan write its output?
    pub slot: usize,

    // If the empty string, return all nodes, otherwise only nodes with the specified label
    pub labels: Option<Token>,
}

impl Operator for NodeScan {
    fn next(&mut self, ctx: &mut Context, out: &mut Row) -> Result<bool> {
        loop {
            let g = ctx.g.borrow();
            if g.nodes.len() > self.next_node {
                let node = g.nodes.get(self.next_node).unwrap();
                if let Some(tok) = self.labels {
                    if !node.labels.contains(&tok) {
                        self.next_node += 1;
                        continue;
                    }
                }

                out.slots[self.slot] = Val::Node(self.next_node);
                self.next_node += 1;
                return Ok(true);
            }
            return Ok(false);
        }
    }
}

#[derive(Debug, Clone)]
struct Argument;

impl Operator for Argument {
    fn next(&mut self, _ctx: &mut Context, _out: &mut Row) -> Result<bool> {
        unimplemented!()
    }
}

#[derive(Debug, Clone)]
struct Projection {
    pub expr: Expr,
    pub alias: Token,
}

#[derive(Debug)]
struct Create {
    pub src: Rc<RefCell<dyn Operator>>,
    nodes: Vec<NodeSpec>,
    tokens: Rc<RefCell<Tokens>>,
}

impl Operator for Create {
    fn next(&mut self, ctx: &mut Context, out: &mut Row) -> Result<bool, Error> {
        for node in &self.nodes {
            let node_properties = node
                .props
                .iter()
                .map(|p| (*p.0, (p.1.eval(ctx, out).unwrap())))
                .collect();
            out.slots[node.slot] = append_node(
                ctx,
                Rc::clone(&self.tokens),
                node.labels.clone(),
                node_properties,
            )?;
        }
        Ok(false)
    }
}

#[derive(Debug)]
struct Return {
    pub src: Rc<RefCell<dyn Operator>>,
    pub projections: Vec<Projection>,
    print_header: bool,
}

impl Operator for Return {
    fn next(&mut self, ctx: &mut Context, out: &mut Row) -> Result<bool> {
        if self.print_header {
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
            self.print_header = false;
        }
        if self.src.borrow_mut().next(ctx, out)? {
            let mut first = true;
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
            // Do this to 'yield' one row at a time to the cursor
            return Ok(true);
        }
        Ok(false)
    }
}

mod parser {
    use crate::backend::gram::{Graph, Node};
    use crate::backend::{Token, Tokens};
    use crate::pest::Parser;
    use crate::Val;
    use anyhow::Result;
    use std::collections::HashMap;
    use std::collections::HashSet;
    use std::fs::File;
    use std::io::Read;

    #[derive(Parser)]
    #[grammar = "backend/gram.pest"]
    pub struct GramParser;

    /// Indicates how large a buffer to pre-allocate before reading the entire file.
    fn initial_buffer_size(file: &File) -> usize {
        // Allocate one extra byte so the buffer doesn't need to grow before the
        // final `read` call at the end of the file.  Don't worry about `usize`
        // overflow because reading will fail regardless in that case.
        file.metadata().map(|m| m.len() as usize + 1).unwrap_or(0)
    }

    fn read_to_string(file: &mut File) -> Result<String> {
        //todo lock this (and other io on the file)
        let mut string = String::with_capacity(initial_buffer_size(&file));
        file.read_to_string(&mut string)?;
        Ok(string)
    }

    pub fn load(tokens: &mut Tokens, file: &mut File) -> Result<Graph> {
        let mut g = Graph { nodes: vec![] };

        let query_str = read_to_string(file).unwrap();
        let maybe_parse = GramParser::parse(Rule::gram, &query_str);

        let gram = maybe_parse
            .expect("unsuccessful parse") // unwrap the parse result
            .next()
            .unwrap(); // get and unwrap the `file` rule; never fails

        //    let id_map = HashMap::new();
        let mut node_ids = Tokens {
            table: Default::default(),
        };

        for item in gram.into_inner() {
            match item.as_rule() {
                Rule::path => {
                    let mut start_identifier: Option<Token> = None;
                    let mut end_identifier: Option<Token> = None;

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
                                        Rule::map => {}
                                        _ => panic!(
                                            "what? {:?} / {}",
                                            rel_part.as_rule(),
                                            rel_part.as_str()
                                        ),
                                    }
                                }
                            }
                            _ => panic!("what? {:?} / {}", part.as_rule(), part.as_str()),
                        }
                    }

                    g.add_rel(
                        start_identifier.unwrap(),
                        end_identifier.unwrap(),
                        tokens.tokenize("KNOWS"),
                    );
                }
                Rule::node => {
                    let mut identifier: Option<String> = None;
                    let mut props: HashMap<Token, Val> = HashMap::new();
                    let mut labels: HashSet<Token> = HashSet::new();

                    for part in item.into_inner() {
                        match part.as_rule() {
                            Rule::id => identifier = Some(part.as_str().to_string()),
                            Rule::label => {
                                for label in part.into_inner() {
                                    labels.insert(tokens.tokenize(label.as_str()));
                                }
                            }
                            Rule::map => {
                                for pair in part.into_inner() {
                                    let mut key: Option<String> = None;
                                    let mut val = None;
                                    match pair.as_rule() {
                                        Rule::map_pair => {
                                            for pair_part in pair.into_inner() {
                                                match pair_part.as_rule() {
                                                    Rule::id => {
                                                        key = Some(pair_part.as_str().to_string())
                                                    }
                                                    Rule::expr => {
                                                        val = Some(pair_part.as_str().to_string())
                                                    }
                                                    _ => panic!(
                                                        "what? {:?} / {}",
                                                        pair_part.as_rule(),
                                                        pair_part.as_str()
                                                    ),
                                                }
                                            }
                                        }
                                        _ => {
                                            panic!("what? {:?} / {}", pair.as_rule(), pair.as_str())
                                        }
                                    }
                                    let key_str = key.unwrap();
                                    props.insert(
                                        tokens.tokenize(&key_str),
                                        Val::String(val.unwrap()),
                                    );
                                }
                            }
                            _ => panic!("what? {:?} / {}", part.as_rule(), part.as_str()),
                        }
                    }

                    g.add_node(
                        node_ids.tokenize(&identifier.unwrap()),
                        Node {
                            labels,
                            properties: props,
                            rels: vec![],
                        },
                    );
                }
                _ => (),
            }
        }

        Ok(g)
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
struct NodeSpec {
    pub slot: usize,
    pub labels: HashSet<Token>,
    pub props: HashMap<Token, Expr>,
}

impl Clone for NodeSpec {
    fn clone(&self) -> Self {
        return NodeSpec {
            slot: self.slot,
            labels: self.labels.iter().cloned().collect(),
            props: self.props.clone(),
        };
    }

    fn clone_from(&mut self, _source: &'_ Self) {
        unimplemented!()
    }
}

#[derive(Debug)]
pub struct Node {
    labels: HashSet<Token>,
    properties: HashMap<Token, Val>,
    rels: Vec<RelHalf>,
}

#[derive(Debug)]
pub struct Graph {
    nodes: Vec<Node>,
}

impl Graph {
    fn get_node_prop(&self, node_id: usize, prop: Token) -> Option<Val> {
        self.nodes[node_id].properties.get(&prop).cloned()
    }

    fn get_rel_prop(&self, node_id: usize, rel_index: usize, prop: Token) -> Option<Val> {
        self.nodes[node_id].rels[rel_index]
            .properties
            .get(&prop)
            .cloned()
    }

    fn add_node(&mut self, id: usize, n: Node) {
        self.nodes.insert(id, n);
    }

    fn add_rel(&mut self, from: usize, to: usize, rel_type: Token) {
        let props = Rc::new(Default::default());
        self.nodes[from].rels.push(RelHalf {
            rel_type,
            dir: Dir::Out,
            other_node: to,
            properties: Rc::clone(&props),
        });
        self.nodes[to].rels.push(RelHalf {
            rel_type,
            dir: Dir::In,
            other_node: from,
            properties: props,
        })
    }
}

fn generate_uuid() -> Uuid {
    // TODO: there should be a single context for the whole backend
    let context = UuidContext::new(42);
    // TODO: there should be a single node id generated per process execution
    let node_id: [u8; 6] = rand::thread_rng().gen();
    let now = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .unwrap();
    let ts = Timestamp::from_unix(&context, now.as_secs(), now.subsec_nanos());
    return Uuid::new_v1(ts, &node_id).expect("failed to generate UUID");
}

fn append_node(
    ctx: &mut Context,
    tokens_in: Rc<RefCell<Tokens>>,
    labels: HashSet<Token>,
    node_properties: HashMap<Token, Val>,
) -> Result<Val, Error> {
    let tokens = tokens_in.borrow();
    let properties_gram_ready: HashMap<&str, &str> = node_properties
        .iter()
        .map(|kvp| (tokens.lookup(*kvp.0).unwrap(), (*kvp.1).as_string_literal()))
        .collect();
    let gram_identifier = generate_uuid().to_hyphenated().to_string();
    let gram_string: String;
    if !labels.is_empty() {
        let labels_gram_ready: Vec<&str> =
            labels.iter().map(|l| tokens.lookup(*l).unwrap()).collect();
        gram_string = format!(
            "(`{}`:{} {})\n",
            gram_identifier,
            labels_gram_ready.join(":"),
            json::stringify(properties_gram_ready)
        );
    } else {
        gram_string = format!(
            "(`{}` {})\n",
            gram_identifier,
            json::stringify(properties_gram_ready)
        );
    }

    let out_node = Node {
        labels: labels,
        properties: node_properties,
        rels: vec![],
    };

    let node_id = ctx.g.borrow().nodes.len();
    ctx.g.borrow_mut().add_node(node_id, out_node);

    println!("--- About to write ---");
    println!("{}", gram_string);
    println!("------");
    // TODO: actually write to the file:

    ctx.file
        .borrow_mut()
        .seek(SeekFrom::End(0))
        .expect("seek error");

    return match ctx.file.borrow_mut().write_all(gram_string.as_bytes()) {
        Ok(_) => Ok(Val::Node(node_id)),
        Err(e) => Err(Error::new(e)),
    };
}

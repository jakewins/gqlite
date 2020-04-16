// The Gram backend is a backend implementation that acts on a Gram file.
// Note that this is primarily a playground currently, there are no tests and
// things are duct-taped together; we're interested in exploration and learning
// not a final product.

// It is currently single threaded, and provides no data durability guarantees.

use crate::backend::gram::functions::AggregatingFuncSpec;
use crate::backend::{Backend, BackendCursor, BackendDesc, Token, Tokens};
use crate::frontend::{Dir, LogicalPlan};
use crate::{frontend, Error, Row, Slot, Val};
use anyhow::Result;
use rand::Rng;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::fmt::{self, Debug, Display, Formatter};
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
    aggregators: HashMap<Token, Box<dyn AggregatingFuncSpec>>,
}

impl GramBackend {
    pub fn open(mut file: File) -> Result<GramBackend> {
        let mut tokens = Tokens {
            table: Default::default(),
        };
        let g = parser::load(&mut tokens, &mut file)?;

        let mut aggregators = HashMap::new();
        for agg in functions::aggregating(&mut tokens) {
            aggregators.insert(agg.signature().name, agg);
        }

        Ok(GramBackend {
            tokens: Rc::new(RefCell::new(tokens)),
            g: Rc::new(RefCell::new(g)),
            file: Rc::new(RefCell::new(file)),
            aggregators,
        })
    }

    fn convert(&self, plan: LogicalPlan) -> Result<Box<dyn Operator>> {
        match plan {
            LogicalPlan::Argument => Ok(Box::new(Argument { consumed: false })),
            LogicalPlan::NodeScan { src, slot, labels } => Ok(Box::new(NodeScan {
                src: self.convert(*src)?,
                slot,
                labels,
                state: NodeScanState::Idle,
            })),
            LogicalPlan::Create { src, nodes, rels } => {
                let mut out_nodes = Vec::with_capacity(nodes.len());
                for (i, ns) in nodes.into_iter().enumerate() {
                    let mut props = HashMap::new();
                    for k in ns.props {
                        props.insert(k.key, self.convert_expr(k.val));
                    }
                    out_nodes.insert(
                        i,
                        NodeSpec {
                            slot: ns.slot,
                            labels: ns.labels.iter().copied().collect(),
                            props,
                        },
                    );
                }
                let mut out_rels = Vec::with_capacity(rels.len());
                for (i, ns) in rels.into_iter().enumerate() {
                    let mut props = HashMap::new();
                    for k in ns.props {
                        props.insert(k.key, self.convert_expr(k.val));
                    }
                    out_rels.insert(
                        i,
                        RelSpec {
                            slot: ns.slot,
                            start_node_slot: ns.start_node_slot,
                            end_node_slot: ns.end_node_slot,
                            rel_type: ns.rel_type,
                            props,
                        },
                    );
                }
                Ok(Box::new(Create {
                    src: self.convert(*src)?,
                    nodes: out_nodes,
                    rels: out_rels,
                    tokens: self.tokens.clone(),
                }))
            }
            LogicalPlan::Expand {
                src,
                src_slot,
                rel_slot,
                dst_slot,
                rel_type,
                ..
            } => Ok(Box::new(Expand {
                src: self.convert(*src)?,
                src_slot,
                rel_slot,
                dst_slot,
                rel_type,
                next_rel_index: 0,
                state: ExpandState::NextNode,
            })),
            // TODO: unwrap selection for now, actually implement
            LogicalPlan::Selection { src, .. } => self.convert(*src),
            LogicalPlan::Aggregate {
                src,
                grouping: _,
                aggregations,
            } => {
                let mut agg_exprs = Vec::new();
                for (expr, slot) in aggregations {
                    agg_exprs.push(AggregateEntry {
                        func: self.convert_aggregating_expr(expr),
                        slot,
                    })
                }
                Ok(Box::new(Aggregate {
                    src: self.convert(*src)?,
                    aggregations: agg_exprs,
                    consumed: false,
                }))
            }
            LogicalPlan::Unwind {
                src,
                list_expr,
                alias,
            } => Ok(Box::new(Unwind {
                src: self.convert(*src)?,
                list_expr: self.convert_expr(list_expr),
                current_list: None,
                next_index: 0,
                dst: alias,
            })),
            LogicalPlan::Return { src, projections } => {
                let mut converted_projections = Vec::new();
                for projection in projections {
                    converted_projections.push(Projection {
                        expr: self.convert_expr(projection.expr),
                        alias: projection.alias,
                        slot: projection.dst,
                    })
                }

                Ok(Box::new(Return {
                    src: self.convert(*src)?,
                    projections: converted_projections,
                    print_header: true,
                }))
            }
            LogicalPlan::Project { src, projections } => {
                let mut converted_projections = Vec::new();
                for projection in projections {
                    converted_projections.push(Projection {
                        expr: self.convert_expr(projection.expr),
                        alias: projection.alias,
                        slot: projection.dst,
                    })
                }

                Ok(Box::new(Project {
                    src: self.convert(*src)?,
                    projections: converted_projections,
                }))
            }
        }
    }

    fn convert_aggregating_expr(
        &self,
        expr: frontend::Expr,
    ) -> Box<dyn functions::AggregatingFunc> {
        match expr {
            frontend::Expr::FuncCall { name, args } => {
                if let Some(f) = self.aggregators.get(&name) {
                    let mut arguments = Vec::new();
                    for a in args {
                        arguments.push(self.convert_expr(a));
                    }
                    return f.init(arguments);
                } else {
                    panic!(
                        "The gram backend doesn't support nesting regular functions with aggregates yet: {:?}",
                        name
                    )
                }
            }
            _ => panic!(
                "The gram backend does not support this expression type yet: {:?}",
                expr
            ),
        }
    }

    fn convert_expr(&self, expr: frontend::Expr) -> Expr {
        match expr {
            frontend::Expr::String(v) => Expr::Lit(Val::String(v)),
            frontend::Expr::Int(v) => Expr::Lit(Val::Int(v)),
            frontend::Expr::Float(v) => Expr::Lit(Val::Float(v)),

            frontend::Expr::Prop(e, props) => Expr::Prop(Box::new(self.convert_expr(*e)), props),
            frontend::Expr::Slot(s) => Expr::Slot(s),
            frontend::Expr::List(es) => {
                let mut items = Vec::with_capacity(es.len());
                for e in es {
                    items.push(self.convert_expr(e));
                }
                Expr::List(items)
            }
            _ => panic!(
                "The gram backend does not support this expression type yet: {:?}",
                expr
            ),
        }
    }
}

impl Backend for GramBackend {
    type Cursor = GramCursor;

    fn new_cursor(&mut self) -> GramCursor {
        GramCursor {
            ctx: Context {
                tokens: Rc::clone(&self.tokens),
                g: Rc::clone(&self.g),
                file: Rc::clone(&self.file),
            },
            plan: None,
            slots: vec![],
            row: GramRow { slots: vec![] },
            projection: Row { slots: vec![] },
        }
    }

    fn tokens(&self) -> Rc<RefCell<Tokens>> {
        Rc::clone(&self.tokens)
    }

    fn eval(&mut self, plan: LogicalPlan, cursor: &mut GramCursor) -> Result<(), Error> {
        let slots = match &plan {
            LogicalPlan::Return { projections, .. } => {
                projections.iter().map(|p| (p.alias, p.dst)).collect()
            }
            _ => Vec::new(),
        };
        if cursor.projection.slots.len() < slots.len() {
            cursor.projection.slots.resize(slots.len(), Val::Null);
        }

        let plan = self.convert(plan)?;
        cursor.ctx = Context {
            tokens: Rc::clone(&self.tokens),
            g: Rc::clone(&self.g),
            file: Rc::clone(&self.file),
        };
        cursor.slots = slots;
        cursor.plan = Some(plan);

        if cursor.row.slots.len() < 16 {
            // TODO derive this from the logical plan
            cursor.row.slots.resize(16, GramVal::Lit(Val::Null));
        }
        Ok(())
    }

    fn describe(&self) -> Result<BackendDesc, Error> {
        let mut functions = Vec::new();
        for agg in self.aggregators.values() {
            functions.push(agg.signature().clone())
        }

        Ok(BackendDesc::new(functions))
    }
}

#[derive(Debug)]
struct GramRow {
    slots: Vec<GramVal>,
}

#[derive(Debug)]
pub struct GramCursor {
    ctx: Context,
    plan: Option<Box<dyn Operator>>,
    // This is the internal data row, each operator in the execution plan acts on this,
    // reading and writing slots. Another model would be that each operator has it's own
    // row, and that we copy the values between each - or that you use "morsels", buffers of
    // multiple rows, like how Neo4j does it.
    row: GramRow,

    // Each time we call next, we project the final result of the execution plan from
    // row into this public projection; hence this is where we'd pay the cost to materialize
    // node values, strings and so on
    projection: Row,
    // This maps from row to projection; each value corresponds to a slot in the projection,
    // the token is the name assigned in the query (eg. RETURN 1 as banana)
    slots: Vec<(Token, Slot)>,
}

impl BackendCursor for GramCursor {
    fn next(&mut self) -> Result<Option<&Row>> {
        if let Some(p) = &mut self.plan {
            if p.next(&mut self.ctx, &mut self.row)? {
                for slot in 0..self.slots.len() {
                    self.projection.slots[slot] =
                        self.row.slots[self.slots[slot].1].project(&mut self.ctx)
                }
                Ok(Some(&self.projection))
            } else {
                Ok(None)
            }
        } else {
            Err(anyhow!("This cursor is not associated with a result, try passing the cursor to the run() function"))
        }
    }
}

#[derive(Debug)]
struct Context {
    tokens: Rc<RefCell<Tokens>>,
    g: Rc<RefCell<Graph>>,
    file: Rc<RefCell<File>>,
}

#[derive(Debug, Clone)]
enum Expr {
    Lit(Val),
    // Lookup a property by id
    Prop(Box<Expr>, Vec<Token>),
    Slot(Slot),
    List(Vec<Expr>),
}

impl Expr {
    fn eval_prop(
        ctx: &mut Context,
        row: &mut GramRow,
        expr: &Expr,
        prop: Token,
    ) -> Result<GramVal> {
        let v = match expr.eval(ctx, row)? {
            GramVal::Node { id } => ctx.g.borrow().get_node_prop(id, prop).unwrap_or(Val::Null),
            GramVal::Rel { node_id, rel_index } => ctx
                .g
                .borrow()
                .get_rel_prop(node_id, rel_index, prop)
                .unwrap_or(Val::Null),
            v => bail!("Gram backend does not yet support {:?}", v),
        };
        Ok(GramVal::Lit(v))
    }

    fn eval(&self, ctx: &mut Context, row: &mut GramRow) -> Result<GramVal> {
        match self {
            Expr::Prop(expr, props) => {
                if props.len() != 1 {
                    panic!("Can't handle property expressions referring to more than one key")
                }
                Expr::eval_prop(ctx, row, expr, props[0])
            }
            Expr::Slot(slot) => Ok(row.slots[*slot].clone()), // TODO not this
            Expr::Lit(v) => Ok(GramVal::Lit(v.clone())),      // TODO not this,
            Expr::List(vs) => {
                let mut out = Vec::new();
                for v in vs {
                    out.push(v.eval(ctx, row)?);
                }
                Ok(GramVal::List(out))
            }
        }
    }
}

// The gram backends representation of values; this is what propagates through the execution plan
// This is different from just Val in that it allows the Gram engine to avoid copying large string
// values around - it can implement special reference types as it sees fit, that point to its
// internal structures, and only in the final projections of the execution plan is the value then
// converted into a (borrowed!) val.
#[derive(Debug, PartialEq, Clone)]
enum GramVal {
    Lit(Val),
    List(Vec<GramVal>),
    Node { id: usize },
    Rel { node_id: usize, rel_index: usize },
}

impl GramVal {
    pub fn project(&self, ctx: &mut Context) -> Val {
        match self {
            GramVal::Lit(v) => v.clone(),
            GramVal::List(vs) => {
                let mut out = Vec::new();
                out.resize(vs.len(), Val::Null);
                for i in 0..vs.len() {
                    out[i] = vs[i].project(ctx);
                }
                return Val::List(out);
            }
            GramVal::Node { id } => {
                let n = &ctx.g.borrow().nodes[*id];
                let mut props = crate::Map::new();
                for (k, v) in &n.properties {
                    props.push((
                        ctx.tokens.borrow().lookup(*k).unwrap().to_string(),
                        v.clone(),
                    ));
                }
                let mut labels = Vec::new();
                for l in &n.labels {
                    labels.push(ctx.tokens.borrow().lookup(*l).unwrap().to_string());
                }
                return Val::Node(crate::Node {
                    id: *id,
                    labels,
                    props,
                });
            }
            _ => panic!("don't know how to project: {:?}", self),
        }
    }

    pub fn as_node_id(&self) -> usize {
        match self {
            GramVal::Node { id } => *id,
            _ => panic!(
                "invalid execution plan, non-node value feeds into thing expecting node value"
            ),
        }
    }
}

impl PartialOrd for GramVal {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self {
            GramVal::Lit(Val::Int(self_v)) => match other {
                GramVal::Lit(Val::Int(other_v)) => self_v.partial_cmp(other_v),
                GramVal::Lit(Val::Float(other_v)) => self_v.partial_cmp(&&(*other_v as i64)),
                GramVal::Lit(Val::String(_)) => Some(Ordering::Greater),
                GramVal::Lit(Val::List(_)) => Some(Ordering::Greater),
                GramVal::List(_) => Some(Ordering::Greater),
                GramVal::Lit(Val::Null) => None,
                _ => panic!("Don't know how to compare {:?} to {:?}", self, other),
            },
            GramVal::Lit(Val::Float(self_v)) => match other {
                GramVal::Lit(Val::Int(other_v)) => (*self_v).partial_cmp(&(*other_v as f64)),
                GramVal::Lit(Val::Float(other_v)) => (*self_v).partial_cmp(other_v),
                GramVal::Lit(Val::String(_)) => Some(Ordering::Greater),
                GramVal::Lit(Val::List(_)) => Some(Ordering::Greater),
                GramVal::List(_) => Some(Ordering::Greater),
                GramVal::Lit(Val::Null) => None,
                _ => panic!("Don't know how to compare {:?} to {:?}", self, other),
            },
            GramVal::Lit(Val::String(self_v)) => match other {
                GramVal::Lit(Val::Int(_)) => Some(Ordering::Less),
                GramVal::Lit(Val::Float(_)) => Some(Ordering::Less),
                GramVal::Lit(Val::String(other_v)) => self_v.partial_cmp(other_v),
                GramVal::Lit(Val::List(_)) => Some(Ordering::Greater),
                GramVal::List(_) => Some(Ordering::Greater),
                GramVal::Lit(Val::Null) => None,
                _ => panic!("Don't know how to compare {:?} to {:?}", self, other),
            },
            GramVal::Lit(Val::List(_self_v)) => match other {
                GramVal::Lit(Val::String(_)) => Some(Ordering::Less),
                GramVal::Lit(Val::Int(_)) => Some(Ordering::Less),
                GramVal::Lit(Val::Float(_)) => Some(Ordering::Less),
                GramVal::Lit(Val::Null) => None,
                _ => panic!("Don't know how to compare {:?} to {:?}", self, other),
            },
            GramVal::List(self_v) => match other {
                GramVal::Lit(Val::String(_)) => Some(Ordering::Less),
                GramVal::Lit(Val::Int(_)) => Some(Ordering::Less),
                GramVal::Lit(Val::Float(_)) => Some(Ordering::Less),
                GramVal::List(other_vs) => {
                    return self_v.partial_cmp(&other_vs);
                }
                GramVal::Lit(Val::Null) => None,
                _ => panic!("Don't know how to compare {:?} to {:?}", self, other),
            },
            GramVal::Lit(Val::Null) => match other {
                _ => None,
            },
            _ => panic!("Don't know how to compare {:?} to {:?}", self, other),
        }
    }
}

impl Display for GramVal {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            GramVal::Lit(v) => std::fmt::Display::fmt(&v, f),
            GramVal::List(vs) => f.write_str(&format!("{:?}", vs)),
            GramVal::Node { id } => f.write_str(&format!("Node({})", id)),
            GramVal::Rel { node_id, rel_index } => {
                f.write_str(&format!("Rel({}/{})", node_id, rel_index))
            }
        }
    }
}

// Physical operator. We have one of these for each Logical operator the frontend emits.
trait Operator: Debug {
    fn next(&mut self, ctx: &mut Context, row: &mut GramRow) -> Result<bool>;
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

    pub rel_type: Option<Token>,

    // In the current adjacency list, what is the next index we should return?
    pub next_rel_index: usize,

    pub state: ExpandState,
}

impl Operator for Expand {
    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool> {
        loop {
            match &self.state {
                ExpandState::NextNode => {
                    // Pull in the next node
                    if !self.src.next(ctx, out)? {
                        return Ok(false);
                    }
                    println!("[expand]  in: {:?}", out);
                    self.state = ExpandState::InNode;
                }
                ExpandState::InNode => {
                    let node = out.slots[self.src_slot].as_node_id();
                    let g = ctx.g.borrow();
                    let rels = &g.nodes[node].rels;
                    println!("[expand]  relcount={}", rels.len());
                    if self.next_rel_index >= rels.len() {
                        // No more rels on this node
                        println!("[expand]  no mas");
                        self.state = ExpandState::NextNode;
                        self.next_rel_index = 0;
                        continue;
                    }

                    let rel = &rels[self.next_rel_index];
                    self.next_rel_index += 1;

                    if self.rel_type == None || rel.rel_type == self.rel_type.unwrap() {
                        out.slots[self.rel_slot] = GramVal::Rel {
                            node_id: node,
                            rel_index: self.next_rel_index - 1,
                        };
                        out.slots[self.dst_slot] = GramVal::Node { id: rel.other_node };
                        println!("[expand]  out: {:?}", out);
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
    pub src: Box<dyn Operator>,

    // Where should this scan write its output?
    pub slot: usize,

    // If None, return all nodes, otherwise only nodes with the specified label
    pub labels: Option<Token>,

    pub state: NodeScanState,
}

#[derive(Debug)]
pub enum NodeScanState {
    // Next call will pull another row from src
    Idle,
    // We're in the middle of a scan, next call will continue scanning
    Scanning{ next_node: usize },
}

impl Operator for NodeScan {
    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool> {
        loop {
            match &self.state {
                NodeScanState::Idle => {
                    if ! self.src.next(ctx, out)? {
                        return Ok(false)
                    }
                    self.state = NodeScanState::Scanning { next_node: 0 }
                },
                NodeScanState::Scanning { next_node } => {
                    let g = ctx.g.borrow();
                    let mut node_id = *next_node;
                    while g.nodes.len() > node_id {
                        let node = g.nodes.get(node_id).unwrap();
                        if let Some(tok) = self.labels {
                            if !node.labels.contains(&tok) {
                                node_id += 1;
                                continue;
                            }
                        }

                        out.slots[self.slot] = GramVal::Node { id: node_id };
                        self.state = NodeScanState::Scanning { next_node: node_id + 1 };
                        return Ok(true);
                    }
                    self.state = NodeScanState::Idle;
                },
            }
        }
    }
}

#[derive(Debug, Clone)]
struct Argument {
    // Eventually this operator would yield one row with user-provided parameters; for now
    // it's simply used as a leaf that yields one "seed" row to set things in motion.
    // This is because other operators perform their action "once per input row", so you
    // need one initial row to start the machinery.
    consumed: bool,
}

impl Operator for Argument {
    fn next(&mut self, _ctx: &mut Context, _out: &mut GramRow) -> Result<bool> {
        if self.consumed {
            return Ok(false);
        }
        self.consumed = true;
        return Ok(true);
    }
}

// Nodespec is used by the CREATE operator, and differs from Node in that its properties are
// expressions rather than materialized values.
#[derive(Debug)]
struct NodeSpec {
    pub slot: usize,
    pub labels: HashSet<Token>,
    pub props: HashMap<Token, Expr>,
}

impl Clone for NodeSpec {
    fn clone(&self) -> Self {
        NodeSpec {
            slot: self.slot,
            labels: self.labels.iter().cloned().collect(),
            props: self.props.clone(),
        }
    }

    fn clone_from(&mut self, _source: &'_ Self) {
        unimplemented!()
    }
}

// Specifies a rel to be created (thought: Could these be implemented as functions?)
#[derive(Debug)]
struct RelSpec {
    pub slot: usize,
    pub start_node_slot: usize,
    pub end_node_slot: usize,
    pub rel_type: Token,
    pub props: HashMap<Token, Expr>,
}

#[derive(Debug)]
struct Create {
    pub src: Box<dyn Operator>,
    nodes: Vec<NodeSpec>,
    rels: Vec<RelSpec>,
    tokens: Rc<RefCell<Tokens>>,
}

impl Operator for Create {
    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool, Error> {
        for node in &self.nodes {
            let node_properties = node
                .props
                .iter()
                .map(|p| {
                    if let Ok(GramVal::Lit(val)) = p.1.eval(ctx, out) {
                        return (*p.0, (val));
                    } else {
                        panic!("Property creation expression yielded non-literal?")
                    }
                })
                .collect();
            out.slots[node.slot] = append_node(
                ctx,
                Rc::clone(&self.tokens),
                node.labels.clone(),
                node_properties,
            )?;
        }
        for rel in &self.rels {
            let rel_properties = rel
                .props
                .iter()
                .map(|p| {
                    if let Ok(GramVal::Lit(val)) = p.1.eval(ctx, out) {
                        return (*p.0, (val));
                    } else {
                        panic!("Property creation expression yielded non-literal?")
                    }
                })
                .collect();

            let start_node = match out.slots[rel.start_node_slot] {
                GramVal::Node { id } => id,
                _ => unreachable!("Start node for rel create must be a node value"),
            };
            let end_node = match out.slots[rel.end_node_slot] {
                GramVal::Node { id } => id,
                _ => unreachable!("End node for rel create must be a node value"),
            };

            out.slots[rel.slot] =
                append_rel(ctx, start_node, end_node, rel.rel_type, rel_properties)?;
        }
        Ok(false)
    }
}

#[derive(Debug)]
struct Return {
    pub src: Box<dyn Operator>,
    pub projections: Vec<Projection>,
    print_header: bool,
}

impl Operator for Return {
    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool> {
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
        if self.src.next(ctx, out)? {
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

#[derive(Debug, Clone)]
struct Projection {
    pub expr: Expr,
    pub alias: Token,
    pub slot: usize,
}

#[derive(Debug)]
struct Project {
    pub src: Box<dyn Operator>,
    pub projections: Vec<Projection>,
}

impl Operator for Project {
    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool> {
        if self.src.next(ctx, out)? {
            for proj in &self.projections {
                out.slots[proj.slot] = proj.expr.eval(ctx, out)?;
            }
            return Ok(true);
        }
        Ok(false)
    }
}

#[derive(Debug)]
struct Aggregate {
    src: Box<dyn Operator>,

    aggregations: Vec<AggregateEntry>,

    consumed: bool,
}

#[derive(Debug)]
struct AggregateEntry {
    func: Box<dyn functions::AggregatingFunc>,
    slot: Slot,
}

impl Operator for Aggregate {
    fn next(&mut self, ctx: &mut Context, row: &mut GramRow) -> Result<bool> {
        if self.consumed {
            return Ok(false);
        }
        let src = &mut *self.src;
        while src.next(ctx, row)? {
            for agge in &mut self.aggregations {
                agge.func.apply(ctx, row)?;
            }
        }

        for agge in &mut self.aggregations {
            row.slots[agge.slot] = agge.func.complete()?.clone();
        }

        self.consumed = true;
        return Ok(true);
    }
}

#[derive(Debug)]
struct Unwind {
    src: Box<dyn Operator>,
    list_expr: Expr,
    dst: Slot,
    // TODO this should use an iterator
    current_list: Option<Vec<GramVal>>,
    next_index: usize,
}

impl Operator for Unwind {
    fn next(&mut self, ctx: &mut Context, row: &mut GramRow) -> Result<bool> {
        loop {
            if self.current_list.is_none() {
                let src = &mut *self.src;
                if !src.next(ctx, row)? {
                    return Ok(false);
                }

                match self.list_expr.eval(ctx, row)? {
                    GramVal::List(items) => self.current_list = Some(items),
                    _ => return Err(anyhow!("UNWIND expression must yield a list")),
                }
                self.next_index = 0;
            }

            if let Some(it) = &mut self.current_list {
                if self.next_index >= it.len() {
                    self.current_list = None;
                    continue;
                }

                row.slots[self.dst] = it[self.next_index].clone();
                self.next_index += 1;
                return Ok(true);
            }
        }
    }
}

mod parser {
    use super::Val;
    use crate::backend::gram::{Graph, Node};
    use crate::backend::{Token, Tokens};
    use crate::pest::Parser;
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

                    let mut rel_type = None;

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
                                        Rule::rel_type => {
                                            let rt_id = rel_part.into_inner().next().unwrap();
                                            rel_type = Some(node_ids.tokenize(
                                                rt_id.into_inner().next().unwrap().as_str(),
                                            ));
                                        }
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
                        rel_type.unwrap_or(tokens.tokenize("_")),
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

                    let gid_string = identifier.unwrap();
                    let gid = tokens.tokenize(&gid_string);
                    g.add_node(
                        node_ids.tokenize(&gid_string),
                        Node {
                            gid,
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
pub struct Node {
    // Identifier assigned this node in the gram file
    gid: Token,
    labels: HashSet<Token>,
    properties: HashMap<Token, Val>,
    rels: Vec<RelHalf>,
}

#[derive(Debug)]
pub struct RelHalf {
    rel_type: Token,
    dir: Dir,
    other_node: usize,
    properties: Rc<HashMap<Token, Val>>,
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

    // Add a rel, return the index of the rel from the start nodes perspective
    fn add_rel(&mut self, from: usize, to: usize, rel_type: Token) -> usize {
        let props = Rc::new(Default::default());
        let fromrels = &mut self.nodes[from].rels;
        fromrels.push(RelHalf {
            rel_type,
            dir: Dir::Out,
            other_node: to,
            properties: Rc::clone(&props),
        });
        let index = fromrels.len() - 1;
        self.nodes[to].rels.push(RelHalf {
            rel_type,
            dir: Dir::In,
            other_node: from,
            properties: props,
        });
        return index;
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
    Uuid::new_v1(ts, &node_id).expect("failed to generate UUID")
}

fn append_node(
    ctx: &mut Context,
    tokens_in: Rc<RefCell<Tokens>>,
    labels: HashSet<Token>,
    node_properties: HashMap<Token, Val>,
) -> Result<GramVal, Error> {
    let mut tokens = tokens_in.borrow_mut();
    let properties_gram_ready: HashMap<&str, String> = node_properties
        .iter()
        .map(|kvp| (tokens.lookup(*kvp.0).unwrap(), format!("{}", (*kvp.1))))
        .collect();
    let gram_identifier = generate_uuid().to_hyphenated().to_string();
    let gram_string = if !labels.is_empty() {
        let labels_gram_ready: Vec<&str> =
            labels.iter().map(|l| tokens.lookup(*l).unwrap()).collect();
        format!(
            "(`{}`:{} {})\n",
            gram_identifier,
            labels_gram_ready.join(":"),
            json::stringify(properties_gram_ready)
        )
    } else {
        format!(
            "(`{}` {})\n",
            gram_identifier,
            json::stringify(properties_gram_ready)
        )
    };

    let out_node = Node {
        gid: tokens.tokenize(&gram_identifier),
        labels,
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

    match ctx.file.borrow_mut().write_all(gram_string.as_bytes()) {
        Ok(_) => Ok(GramVal::Node { id: node_id }),
        Err(e) => Err(Error::new(e)),
    }
}

fn append_rel(
    ctx: &mut Context,
    start_node: usize,
    end_node: usize,
    rel_type: Token,
    props: HashMap<Token, Val>,
) -> Result<GramVal, Error> {
    let tokens = ctx.tokens.borrow();
    let mut g = ctx.g.borrow_mut();

    let properties_gram_ready: HashMap<&str, String> = props
        .iter()
        .map(|kvp| (tokens.lookup(*kvp.0).unwrap(), format!("{}", (*kvp.1))))
        .collect();

    let startgid = tokens.lookup(g.nodes[start_node].gid).unwrap();
    let endgid = tokens.lookup(g.nodes[end_node].gid).unwrap();
    let reltype_str = tokens.lookup(rel_type).unwrap();

    let gram_string = format!(
        "(`{}`)-[:`{}` {}]->(`{}`)\n",
        startgid,
        reltype_str,
        json::stringify(properties_gram_ready),
        endgid,
    );

    println!("--- About to write ---");
    println!("{}", gram_string);
    println!("------");

    let rel_index = g.add_rel(start_node, end_node, rel_type);

    ctx.file
        .borrow_mut()
        .seek(SeekFrom::End(0))
        .expect("seek error");

    match ctx.file.borrow_mut().write_all(gram_string.as_bytes()) {
        Ok(_) => Ok(GramVal::Rel {
            node_id: start_node,
            rel_index: rel_index,
        }),
        Err(e) => Err(Error::new(e)),
    }
}

mod functions {
    use super::{Context, Expr, GramRow, GramVal, Val};
    use crate::backend::{FuncSignature, FuncType, Tokens};
    use crate::{Result, Type};
    use std::cmp::Ordering;
    use std::fmt::Debug;

    pub(super) fn aggregating(tokens: &mut Tokens) -> Vec<Box<dyn AggregatingFuncSpec>> {
        let mut out: Vec<Box<dyn AggregatingFuncSpec>> = Default::default();
        out.push(Box::new(MinSpec::new(tokens)));
        out.push(Box::new(MaxSpec::new(tokens)));
        return out;
    }

    pub(super) trait AggregatingFuncSpec: Debug {
        fn signature(&self) -> &FuncSignature;
        fn init(&self, args: Vec<Expr>) -> Box<dyn AggregatingFunc>;
    }

    // A running aggregation in an executing query
    pub(super) trait AggregatingFunc: Debug {
        fn apply(&mut self, ctx: &mut Context, row: &mut GramRow) -> Result<()>;
        fn complete(&mut self) -> Result<&GramVal>;
    }

    #[derive(Debug)]
    struct MinSpec {
        sig: FuncSignature,
    }

    impl MinSpec {
        pub fn new(tokens: &mut Tokens) -> MinSpec {
            let tok_min = tokens.tokenize("min");
            MinSpec {
                sig: FuncSignature {
                    func_type: FuncType::Aggregating,
                    name: tok_min,
                    returns: Type::Any,
                    args: vec![(tokens.tokenize("v"), Type::Any)],
                },
            }
        }
    }

    impl AggregatingFuncSpec for MinSpec {
        fn signature(&self) -> &FuncSignature {
            return &self.sig;
        }

        fn init(&self, mut args: Vec<Expr>) -> Box<dyn AggregatingFunc> {
            Box::new(Min {
                arg: args.pop().expect("min takes 1 arg"),
                min: None,
            })
        }
    }

    #[derive(Debug)]
    struct Min {
        arg: Expr,
        min: Option<GramVal>,
    }

    impl AggregatingFunc for Min {
        fn apply(&mut self, ctx: &mut Context, row: &mut GramRow) -> Result<()> {
            let v = self.arg.eval(ctx, row)?;
            if let Some(current_min) = &self.min {
                if v == GramVal::Lit(Val::Null) {
                    return Ok(());
                }
                if let Some(Ordering::Less) = v.partial_cmp(&current_min) {
                    self.min = Some(v);
                }
            } else {
                self.min = Some(v);
            }
            Ok(())
        }

        fn complete(&mut self) -> Result<&GramVal> {
            if let Some(v) = &self.min {
                return Ok(v);
            } else {
                Err(anyhow!(
                    "There were no input rows to the aggregation, cannot calculate min(..)"
                ))
            }
        }
    }

    #[derive(Debug)]
    struct MaxSpec {
        sig: FuncSignature,
    }

    impl MaxSpec {
        pub fn new(tokens: &mut Tokens) -> MaxSpec {
            let tok_max = tokens.tokenize("max");
            MaxSpec {
                sig: FuncSignature {
                    func_type: FuncType::Aggregating,
                    name: tok_max,
                    returns: Type::Any,
                    args: vec![(tokens.tokenize("v"), Type::Any)],
                },
            }
        }
    }

    impl AggregatingFuncSpec for MaxSpec {
        fn signature(&self) -> &FuncSignature {
            return &self.sig;
        }

        fn init(&self, mut args: Vec<Expr>) -> Box<dyn AggregatingFunc> {
            println!("Init max({:?})", args);
            Box::new(Max {
                arg: args.pop().expect("max takes 1 argument"),
                max: None,
            })
        }
    }

    #[derive(Debug)]
    struct Max {
        arg: Expr,
        max: Option<GramVal>,
    }

    impl AggregatingFunc for Max {
        fn apply(&mut self, ctx: &mut Context, row: &mut GramRow) -> Result<()> {
            let v = self.arg.eval(ctx, row)?;
            if let Some(current_max) = &self.max {
                if v == GramVal::Lit(Val::Null) {
                    return Ok(());
                }
                if let Some(Ordering::Greater) = v.partial_cmp(&current_max) {
                    self.max = Some(v);
                }
            } else {
                self.max = Some(v);
            }
            Ok(())
        }

        fn complete(&mut self) -> Result<&GramVal> {
            if let Some(v) = &self.max {
                return Ok(v);
            } else {
                Err(anyhow!(
                    "There were no input rows to the aggregation, cannot calculate min(..)"
                ))
            }
        }
    }
}

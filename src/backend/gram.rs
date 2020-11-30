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
use std::hash::{Hash, Hasher};
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
            LogicalPlan::SetProperties { src, actions } => {
                let mut out_actions = Vec::with_capacity(actions.len());
                for action in actions {
                    match action {
                        frontend::SetAction::SingleAssign { entity, key, value } => out_actions
                            .push(SetAction::SingleAssign {
                                entity,
                                key,
                                value: self.convert_expr(value),
                            }),
                        frontend::SetAction::Append { entity, value } => {
                            out_actions.push(SetAction::Append {
                                entity,
                                value: self.convert_expr(value),
                            })
                        }
                        frontend::SetAction::Overwrite { entity, value } => {
                            out_actions.push(SetAction::Overwrite {
                                entity,
                                value: self.convert_expr(value),
                            })
                        }
                    }
                }
                Ok(Box::new(SetProperties {
                    src: self.convert(*src)?,
                    actions: out_actions,
                }))
            }
            LogicalPlan::Expand {
                src,
                src_slot,
                rel_slot,
                dst_slot,
                rel_type,
                dir,
            } => Ok(Box::new(Expand {
                src: self.convert(*src)?,
                src_slot,
                rel_slot,
                dst_slot,
                rel_type,
                dir,
                next_rel_index: 0,
                state: ExpandState::NextNode,
            })),
            LogicalPlan::ExpandRel {
                src,
                src_rel_slot,
                start_node_slot: start_node,
                end_node_slot: end_node,
            } => Ok(Box::new(ExpandRel {
                src: self.convert(*src)?,
                src_rel_slot,
                start_node,
                end_node,
            })),
            LogicalPlan::ExpandInto {
                src,
                left_node_slot,
                right_node_slot,
                dst_slot,
                rel_type,
                dir,
            } => Ok(Box::new(ExpandInto {
                src: self.convert(*src)?,
                left_node_slot,
                right_node_slot,
                dst_slot,
                rel_type,
                dir,
            })),
            LogicalPlan::Selection { src, predicate } => {
                // self.convert(*src)
                Ok(Box::new(Selection {
                    src: self.convert(*src)?,
                    predicate: self.convert_expr(predicate),
                }))
            }
            LogicalPlan::Aggregate {
                src,
                grouping,
                aggregations,
            } => {
                let mut group_expr = Vec::new();
                for (expr, slot) in grouping {
                    group_expr.push(GroupEntry {
                        expr: self.convert_expr(expr),
                        slot,
                    })
                }
                let mut agg_exprs = Vec::new();
                for (expr, slot) in aggregations {
                    agg_exprs.push(AggregateEntry {
                        func: self.convert_aggregating_expr(expr),
                        slot,
                    })
                }
                Ok(Box::new(HashAggregation {
                    src: self.convert(*src)?,
                    grouping: group_expr,
                    aggregations: agg_exprs,
                    group_aggregations: Default::default(),
                    group_order: Vec::new(),
                    consumed: false,
                    aggregated: false,
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
            LogicalPlan::ProduceResult { src, fields } => Ok(Box::new(ProduceResults {
                src: self.convert(*src)?,
                fields,
                print_header: true,
            })),
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
            LogicalPlan::Sort { src, sort_by } => {
                let mut conv_sort_by = Vec::with_capacity(sort_by.len());
                for s in sort_by {
                    conv_sort_by.push(self.convert_expr(s));
                }
                Ok(Box::new(Sort {
                    src: self.convert(*src)?,
                    state: SortState::Init,
                    rows: vec![],
                    sort_by: conv_sort_by,
                }))
            }
            LogicalPlan::Limit { src, skip, limit } => {
                let mut conv_skip = None;
                let mut conv_limit = None;
                if let Some(skip_expr) = skip {
                    conv_skip = Some(self.convert_expr(skip_expr));
                }
                if let Some(limit_expr) = limit {
                    conv_limit = Some(self.convert_expr(limit_expr));
                }
                Ok(Box::new(Limit {
                    src: self.convert(*src)?,
                    skip: conv_skip,
                    limit: conv_limit,
                    initialized: false,
                    limit_remaining: None,
                }))
            }
            LogicalPlan::Optional { src, slots } => Ok(Box::new(Optional {
                src: self.convert(*src)?,
                initialized: false,
                slots,
            })),
            LogicalPlan::CartesianProduct {
                outer,
                inner,
                predicate,
            } => Ok(Box::new(NestLoop {
                outer: self.convert(*outer)?,
                inner: self.convert(*inner)?,
                predicate: self.convert_expr(predicate),
                initialized: false,
            })),
            LogicalPlan::Apply { lhs, rhs } => Ok(Box::new(Apply {
                lhs: self.convert(*lhs)?,
                rhs: self.convert(*rhs)?,
                initialized: false,
            })),
            LogicalPlan::AntiConditionalApply {
                lhs,
                rhs,
                conditions,
            } => Ok(Box::new(AntiConditionalApply {
                lhs: self.convert(*lhs)?,
                rhs: self.convert(*rhs)?,
                conditions,
            })),
            LogicalPlan::ConditionalApply {
                lhs,
                rhs,
                conditions,
            } => Ok(Box::new(ConditionalApply {
                lhs: self.convert(*lhs)?,
                rhs: self.convert(*rhs)?,
                conditions,
            })),
            other => Err(anyhow!("gram backend does not support {:?} yet", other)),
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
                    f.init(arguments)
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

            frontend::Expr::BinaryOp { left, right, op } => match op {
                frontend::Op::Eq => Expr::Equal(
                    Box::new(self.convert_expr(*left)),
                    Box::new(self.convert_expr(*right)),
                ),
                frontend::Op::NotEq => Expr::Call(
                    functions::Func::Not,
                    vec![Expr::Equal(
                        Box::new(self.convert_expr(*left)),
                        Box::new(self.convert_expr(*right)),
                    )],
                ),
                frontend::Op::Gt => Expr::Gt(
                    Box::new(self.convert_expr(*left)),
                    Box::new(self.convert_expr(*right)),
                ),
                frontend::Op::Mul => Expr::Mul(
                    Box::new(self.convert_expr(*left)),
                    Box::new(self.convert_expr(*right)),
                ),
                frontend::Op::Div => Expr::Div(
                    Box::new(self.convert_expr(*left)),
                    Box::new(self.convert_expr(*right)),
                ),
                frontend::Op::Add => Expr::Add(
                    Box::new(self.convert_expr(*left)),
                    Box::new(self.convert_expr(*right)),
                ),
                frontend::Op::Sub => Expr::Sub(
                    Box::new(self.convert_expr(*left)),
                    Box::new(self.convert_expr(*right)),
                ),
            },

            frontend::Expr::ListComprehension {
                src,
                stackslot,
                map_expr,
            } => Expr::ListComprehension {
                src: Box::new(self.convert_expr(*src)),
                stackslot,
                map_expr: Box::new(self.convert_expr(*map_expr)),
            },

            frontend::Expr::Prop(e, keys) => Expr::Prop(Box::new(self.convert_expr(*e)), keys),
            frontend::Expr::DynProp(e, key) => Expr::DynProp(
                Box::new(self.convert_expr(*e)),
                Box::new(self.convert_expr(*key)),
            ),

            frontend::Expr::RowRef(s) => Expr::RowRef(s),
            frontend::Expr::StackRef(s) => Expr::StackRef(s),
            frontend::Expr::List(es) => {
                let mut items = Vec::with_capacity(es.len());
                for e in es {
                    items.push(self.convert_expr(e));
                }
                Expr::List(items)
            }

            frontend::Expr::Map(es) => {
                let mut items = Vec::with_capacity(es.len());
                for e in es {
                    items.push((e.key, self.convert_expr(e.val)));
                }
                Expr::Map(items)
            }

            frontend::Expr::FuncCall { name, args } => {
                // TODO lol
                let convargs = args.iter().map(|i| self.convert_expr(i.clone())).collect();
                let mut tokens = self.tokens.borrow_mut();
                if name == tokens.tokenize("not") {
                    Expr::Call(functions::Func::Not, convargs)
                } else if name == tokens.tokenize("abs") {
                    Expr::Call(functions::Func::Abs, convargs)
                } else if name == tokens.tokenize("keys") {
                    Expr::Call(functions::Func::Keys, convargs)
                } else {
                    panic!("Unknown function: {:?}", tokens.lookup(name).unwrap(),)
                }
            }
            frontend::Expr::Bool(v) => Expr::Lit(Val::Bool(v)),

            frontend::Expr::And(terms) => {
                Expr::And(terms.iter().map(|e| self.convert_expr(e.clone())).collect())
            }

            frontend::Expr::HasLabel(slot, label) => Expr::HasLabel { slot, label },

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
                stack: vec![GramVal::Lit(Val::Null); 16],
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
            LogicalPlan::ProduceResult { fields, .. } => fields.clone(),
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
            stack: vec![GramVal::Lit(Val::Null); 16], // TODO needs to match plan stack size
        };
        cursor.slots = slots;
        cursor.plan = Some(plan);

        if cursor.row.slots.len() < 32 {
            // TODO derive this from the logical plan
            cursor.row.slots.resize(32, GramVal::Lit(Val::Null));
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

#[derive(Debug, Clone)]
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
    fn fields(&self) -> Vec<String> {
        let mut out = Vec::with_capacity(self.slots.len());
        let toks = self.ctx.tokens.borrow();
        for (tok, _) in &self.slots {
            out.push(toks.lookup(*tok).unwrap().to_string());
        }
        out
    }

    fn next(&mut self) -> Result<Option<&Row>> {
        if let Some(p) = &mut self.plan {
            // TODO hackety hack: If there are no slots to project, just spin through the tree
            if self.slots.is_empty() {
                while p.next(&mut self.ctx, &mut self.row)? {
                    // ..
                }
                return Ok(None);
            }
            if p.next(&mut self.ctx, &mut self.row)? {
                for slot in 0..self.slots.len() {
                    self.projection.slots[slot] =
                        self.row.slots[self.slots[slot].1].project(&mut self.ctx);
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
    // some expressions create local scopes while they evaluate (eg. list comprehensions),
    // those locals go on this stack.
    stack: Vec<GramVal>,
}

#[derive(Debug, Clone)]
enum Expr {
    Lit(Val),
    // Lookup a property by id
    Prop(Box<Expr>, Vec<Token>),
    // Dynamically lookup a property by a runtime expression
    DynProp(Box<Expr>, Box<Expr>),

    RowRef(Slot),
    StackRef(Slot),
    List(Vec<Expr>),
    Map(Vec<(Token, Expr)>),

    ListComprehension {
        src: Box<Expr>,
        // The temporary value of each entry in src gets stored in this local stack slot,
        // and then accessed by the map_expr
        stackslot: usize,
        map_expr: Box<Expr>,
    },

    Call(functions::Func, Vec<Expr>),
    And(Vec<Expr>),

    Gt(Box<Expr>, Box<Expr>),
    Equal(Box<Expr>, Box<Expr>),

    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),

    HasLabel {
        slot: usize,
        label: Token,
    },
}

impl Expr {
    fn eval_prop(ctx: &mut Context, row: &GramRow, expr: &Expr, prop: &[Token]) -> Result<GramVal> {
        let mut v = expr.eval(ctx, row)?;
        for key in prop {
            v = match v {
                GramVal::Node { id } => {
                    GramVal::Lit(ctx.g.borrow().get_node_prop(id, *key).unwrap_or(Val::Null))
                }
                GramVal::Rel { node_id, rel_index } => GramVal::Lit(
                    ctx.g
                        .borrow()
                        .get_rel_prop(node_id, rel_index, *key)
                        .unwrap_or(Val::Null),
                ),
                GramVal::Map(es) => es
                    .iter()
                    .find(|(ek, _)| ek == key)
                    .map(|e| e.1.clone())
                    .unwrap_or(GramVal::Lit(Val::Null)),
                GramVal::Lit(Val::Null) => {
                    bail!("Can't read property {:?} because {:?} is NULL", prop, expr)
                }
                v => bail!("Gram backend does not yet support {:?}", v),
            };
        }
        Ok(v)
    }

    fn eval(&self, ctx: &mut Context, row: &GramRow) -> Result<GramVal> {
        match self {
            Expr::Prop(expr, keys) => Expr::eval_prop(ctx, row, expr, keys),
            Expr::DynProp(expr, key) => {
                let keyval = key.eval(ctx, row)?;
                if let GramVal::Lit(Val::String(keystr)) = keyval {
                    let tok = ctx.tokens.borrow_mut().tokenize(keystr.as_str());
                    Expr::eval_prop(ctx, row, expr, &[tok])
                } else {
                    bail!(
                        "Don't know how to look up map entries by non-string keys: {:?}",
                        keyval
                    )
                }
            }
            Expr::RowRef(slot) => Ok(row.slots[*slot].clone()), // TODO not this
            Expr::StackRef(slot) => Ok(ctx.stack[*slot].clone()),
            Expr::Lit(v) => Ok(GramVal::Lit(v.clone())), // TODO not this,
            Expr::List(vs) => {
                let mut out = Vec::new();
                for v in vs {
                    out.push(v.eval(ctx, row)?);
                }
                Ok(GramVal::List(out))
            }
            Expr::Map(es) => {
                let mut out = Vec::with_capacity(es.len());
                for e in es {
                    out.push((e.0, e.1.eval(ctx, row)?));
                }
                Ok(GramVal::Map(out))
            }
            Expr::Gt(a, b) => {
                let a_val = a.eval(ctx, row)?;
                let b_val = b.eval(ctx, row)?;
                match a_val.partial_cmp(&b_val) {
                    Some(Ordering::Greater) => Ok(GramVal::Lit(Val::Bool(true))),
                    _ => Ok(GramVal::Lit(Val::Bool(false))),
                }
            }
            Expr::Equal(a, b) => {
                let a_val = a.eval(ctx, row)?;
                let b_val = b.eval(ctx, row)?;
                let eq = a_val.eq(&b_val);
                Ok(GramVal::Lit(Val::Bool(eq)))
            }
            Expr::Mul(a, b) => {
                let a_val = a.eval(ctx, row)?;
                let b_val = b.eval(ctx, row)?;
                match (&a_val, &b_val) {
                    (GramVal::Lit(Val::Int(a_int)), GramVal::Lit(Val::Int(b_int))) => {
                        Ok(GramVal::Lit(Val::Int(a_int * b_int)))
                    }
                    (GramVal::Lit(Val::Float(a_int)), GramVal::Lit(Val::Int(b_int))) => {
                        Ok(GramVal::Lit(Val::Float(a_int * *b_int as f64)))
                    }
                    _ => bail!(
                        "gram backend does not support multiplication of {:?} and {:?}",
                        a_val,
                        b_val
                    ),
                }
            }
            Expr::Div(a, b) => {
                let a_val = a.eval(ctx, row)?;
                let b_val = b.eval(ctx, row)?;
                match (&a_val, &b_val) {
                    (GramVal::Lit(Val::Int(a_int)), GramVal::Lit(Val::Int(b_int))) => {
                        Ok(GramVal::Lit(Val::Float(*a_int as f64 / *b_int as f64)))
                    }
                    _ => bail!(
                        "gram backend does not support division of {:?} and {:?}",
                        a_val,
                        b_val
                    ),
                }
            }
            Expr::Add(a, b) => {
                let a_val = a.eval(ctx, row)?;
                let b_val = b.eval(ctx, row)?;
                match (&a_val, &b_val) {
                    (GramVal::Lit(Val::Int(a_int)), GramVal::Lit(Val::Int(b_int))) => {
                        Ok(GramVal::Lit(Val::Int(a_int + b_int)))
                    }
                    (GramVal::Lit(Val::String(a_str)), GramVal::Lit(Val::String(b_str))) => {
                        Ok(GramVal::Lit(Val::String(a_str.to_owned() + b_str)))
                    }
                    _ => bail!(
                        "gram backend does not support addition of {:?} and {:?}",
                        a_val,
                        b_val
                    ),
                }
            }
            Expr::Sub(a, b) => {
                let a_val = a.eval(ctx, row)?;
                let b_val = b.eval(ctx, row)?;
                match (&a_val, &b_val) {
                    (GramVal::Lit(Val::Int(a_int)), GramVal::Lit(Val::Int(b_int))) => {
                        Ok(GramVal::Lit(Val::Int(a_int - b_int)))
                    }
                    (GramVal::Lit(Val::Int(a_int)), GramVal::Lit(Val::Float(b_float))) => {
                        Ok(GramVal::Lit(Val::Float(*a_int as f64 - *b_float)))
                    }
                    (GramVal::Lit(Val::Float(a_float)), GramVal::Lit(Val::Int(b_int))) => {
                        Ok(GramVal::Lit(Val::Float(a_float - *b_int as f64)))
                    }
                    _ => bail!(
                        "gram backend does not support subtraction of {:?} and {:?}",
                        a_val,
                        b_val
                    ),
                }
            }
            Expr::And(terms) => {
                for t in terms {
                    match t.eval(ctx, row)? {
                        GramVal::Lit(Val::Bool(b)) => if !b {
                            return Ok(GramVal::Lit(Val::Bool(false)))
                        },
                        _ => panic!("The gram backend does not know how to do binary logic on non-boolean expressions")
                    }
                }
                Ok(GramVal::Lit(Val::Bool(true)))
            }
            Expr::Call(f, args) => {
                let mut argv = Vec::with_capacity(args.len());
                for a in args {
                    argv.push(a.eval(ctx, row)?);
                }
                f.apply(ctx, &argv)
            }
            Expr::HasLabel { slot, label } => {
                let s: &GramVal = &row.slots[*slot];
                let node_id = s.as_node_id();
                let g = ctx.g.borrow();
                let node = g.nodes.get(node_id).unwrap();
                Ok(GramVal::Lit(Val::Bool(node.labels.contains(label))))
            }
            Expr::ListComprehension {
                src,
                stackslot,
                map_expr,
            } => {
                let src_data = src.eval(ctx, row)?;
                let mut result = Vec::new();
                match src_data {
                    GramVal::Lit(Val::List(vals)) => {
                        for src_val in vals {
                            ctx.stack[*stackslot] = GramVal::Lit(src_val);
                            result.push(map_expr.eval(ctx, row)?)
                        }
                    }
                    GramVal::List(vals) => {
                        for src_val in vals {
                            ctx.stack[*stackslot] = src_val;
                            result.push(map_expr.eval(ctx, row)?)
                        }
                    }

                    _ => panic!("The gram backend does not know how to do list comprehension with this as source: {:?}", src_data)
                }
                Ok(GramVal::List(result))
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
    Map(Vec<(Token, GramVal)>),
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
                Val::List(out)
            }
            GramVal::Map(es) => {
                let mut out = Vec::with_capacity(es.len());
                for entry in es {
                    let key = ctx.tokens.borrow().lookup(entry.0).unwrap().to_string();
                    let val = entry.1.project(ctx);
                    out.push((key, val))
                }
                Val::Map(out)
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
                Val::Node(crate::Node {
                    id: *id,
                    labels,
                    props,
                })
            }
            GramVal::Rel { node_id, rel_index } => {
                let n = &ctx.g.borrow().nodes[*node_id];
                let rel = &n.rels[*rel_index];

                let rel_type = ctx
                    .tokens
                    .borrow()
                    .lookup(rel.rel_type)
                    .unwrap()
                    .to_string();
                let mut props = crate::Map::new();
                for (k, v) in rel.properties.borrow().iter() {
                    props.push((
                        ctx.tokens.borrow().lookup(*k).unwrap().to_string(),
                        v.clone(),
                    ));
                }

                let start;
                let end;
                match rel.dir {
                    Dir::Out => {
                        start = *node_id;
                        end = rel.other_node;
                    }
                    Dir::In => {
                        end = *node_id;
                        start = rel.other_node;
                    }
                }
                Val::Rel(crate::Rel {
                    start,
                    end,
                    rel_type,
                    props,
                })
            }
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

    pub fn as_bool(&self) -> Result<bool> {
        match self {
            GramVal::Lit(Val::Bool(v)) => Ok(*v),
            _ => bail!(
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
                GramVal::List(other_vs) => self_v.partial_cmp(&other_vs),
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
            GramVal::Map(es) => f.write_fmt(format_args!("{:?}", es)),
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
    // "Restart" this operator tree, used by eg. Apply to run a given tree branch repeatedly
    fn reset(&mut self);
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

    pub dir: Option<Dir>,

    // In the current adjacency list, what is the next index we should return?
    pub next_rel_index: usize,

    pub state: ExpandState,
}

impl Operator for Expand {
    fn reset(&mut self) {
        self.src.reset();
        self.state = ExpandState::NextNode;
    }

    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool> {
        loop {
            match &self.state {
                ExpandState::NextNode => {
                    // Pull in the next node
                    if !self.src.next(ctx, out)? {
                        return Ok(false);
                    }
                    if let GramVal::Lit(Val::Null) = out.slots[self.src_slot] {
                        continue;
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

                    if self.rel_type.is_some() && rel.rel_type != self.rel_type.unwrap() {
                        continue;
                    }

                    if self.dir.is_some() && rel.other_node != node && rel.dir != self.dir.unwrap()
                    {
                        continue;
                    }

                    out.slots[self.rel_slot] = GramVal::Rel {
                        node_id: node,
                        rel_index: self.next_rel_index - 1,
                    };
                    out.slots[self.dst_slot] = GramVal::Node { id: rel.other_node };
                    return Ok(true);
                }
            }
        }
    }
}

#[derive(Debug)]
struct ExpandRel {
    pub src: Box<dyn Operator>,

    pub src_rel_slot: usize,

    pub start_node: usize,

    pub end_node: usize,
}

impl Operator for ExpandRel {
    fn reset(&mut self) {
        self.src.reset();
    }

    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool> {
        if !self.src.next(ctx, out)? {
            return Ok(false);
        }

        // TODO: This is wrong, the direction of the pattern needs to be considered,
        //       see the planner notes about planning ExpandRel; seeing how far the TCK will let
        //       me go wrong here
        let rel = &out.slots[self.src_rel_slot];
        match rel {
            GramVal::Rel { node_id, rel_index } => {
                let node_data = &ctx.g.borrow().nodes[*node_id];
                let rel_data = &node_data.rels[*rel_index];
                out.slots[self.end_node] = GramVal::Node { id: *node_id };
                out.slots[self.start_node] = GramVal::Node {
                    id: rel_data.other_node,
                }
            }
            _ => unreachable!(),
        }
        Ok(true)
    }
}

#[derive(Debug)]
struct ExpandInto {
    pub src: Box<dyn Operator>,

    pub left_node_slot: usize,
    pub right_node_slot: usize,
    pub dst_slot: usize,
    pub rel_type: Option<Token>,
    pub dir: Option<Dir>,
}

impl Operator for ExpandInto {
    fn reset(&mut self) {
        self.src.reset();
    }

    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool> {
        loop {
            if !self.src.next(ctx, out)? {
                return Ok(false);
            }

            // TODO this is wrong, it only handles cases of one matching rel, does not
            //      take type or direction into account.

            let left_raw = &out.slots[self.left_node_slot];
            let right_raw = &out.slots[self.right_node_slot];
            println!(
                "ExpandInto {:?} -[x]- {:?} @ {:?}",
                left_raw, right_raw, out.slots
            );
            match (left_raw, right_raw) {
                (GramVal::Node { id: left }, GramVal::Node { id: right }) => {
                    let left_node = &ctx.g.borrow().nodes[*left];
                    for (rel_index, candidate) in left_node.rels.iter().enumerate() {
                        if candidate.other_node == *right {
                            out.slots[self.dst_slot] = GramVal::Rel {
                                node_id: *left,
                                rel_index,
                            };
                            return Ok(true);
                        }
                    }

                    // No relationship between these two nodes
                }
                _ => panic!("TODO"),
            };
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
    Scanning { next_node: usize },
}

impl Operator for NodeScan {
    fn reset(&mut self) {
        self.src.reset();
        self.state = NodeScanState::Idle;
    }

    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool> {
        loop {
            match &self.state {
                NodeScanState::Idle => {
                    if !self.src.next(ctx, out)? {
                        return Ok(false);
                    }
                    self.state = NodeScanState::Scanning { next_node: 0 }
                }
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
                        self.state = NodeScanState::Scanning {
                            next_node: node_id + 1,
                        };
                        return Ok(true);
                    }
                    self.state = NodeScanState::Idle;
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
struct Argument {
    // Toggle that tracks if our one row has been emitted
    consumed: bool,
}

impl Operator for Argument {
    fn reset(&mut self) {
        self.consumed = false;
    }

    fn next(&mut self, _ctx: &mut Context, _out: &mut GramRow) -> Result<bool> {
        if self.consumed {
            return Ok(false);
        }
        self.consumed = true;
        Ok(true)
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
    fn reset(&mut self) {
        self.src.reset();
    }

    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool, Error> {
        if !self.src.next(ctx, out)? {
            return Ok(false);
        }
        for node in &self.nodes {
            let node_properties = node
                .props
                .iter()
                .map(|p| {
                    if let Ok(GramVal::Lit(val)) = p.1.eval(ctx, out) {
                        (*p.0, (val))
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
                        (*p.0, (val))
                    } else {
                        panic!("Property creation expression yielded non-literal?")
                    }
                })
                .collect();

            let start_node = match &out.slots[rel.start_node_slot] {
                GramVal::Node { id } => *id,
                v => unreachable!(
                    "Start node for rel create must be a node value, got {:?} from Slot({})",
                    v, rel.start_node_slot
                ),
            };
            let end_node = match out.slots[rel.end_node_slot] {
                GramVal::Node { id } => id,
                _ => unreachable!("End node for rel create must be a node value"),
            };

            out.slots[rel.slot] =
                append_rel(ctx, start_node, end_node, rel.rel_type, rel_properties)?;
        }
        Ok(true)
    }
}

#[derive(Debug)]
enum SetAction {
    SingleAssign {
        entity: Slot,
        key: Token,
        value: Expr,
    },
    Append {
        entity: Slot,
        value: Expr,
    },
    Overwrite {
        entity: Slot,
        value: Expr,
    },
}

#[derive(Debug)]
struct SetProperties {
    pub src: Box<dyn Operator>,
    pub actions: Vec<SetAction>,
}

impl SetProperties {
    // Look. We're gonna rewrite this whole massive file. Just want to get to a walking skeleton.
    fn write_prop_to_thing(
        &self,
        ctx: &mut Context,
        thing: &GramVal,
        key: usize,
        val: Val,
    ) -> Result<()> {
        match thing {
            GramVal::Rel { node_id, rel_index } => {
                let node = &ctx.g.borrow_mut().nodes[*node_id];
                let rel_half = &node.rels[*rel_index];
                if val == Val::Null {
                    rel_half.properties.borrow_mut().remove(&key);
                } else {
                    rel_half.properties.borrow_mut().insert(key, val);
                }
            }
            v => bail!("Don't know how to append properties to {:?}", v),
        }
        Ok(())
    }

    fn write_thing_to_thing(&self, ctx: &mut Context, thing: &GramVal, src: GramVal) -> Result<()> {
        match src {
            GramVal::Map(entries) => {
                for (k,v) in entries {
                    if let GramVal::Lit(litval) = v {
                        self.write_prop_to_thing(ctx, thing, k, litval)?;
                    } else {
                        bail!("Expected a literal value here, probably programming error? Got: {:?}", v)
                    }
                }
            }
            GramVal::Node { id } => {
                let clonedprops = {
                    let node = &ctx.g.borrow().nodes[id];
                    node.properties.clone()
                };
                for (k, v) in clonedprops.iter() {
                    self.write_prop_to_thing(ctx, thing, *k, v.clone())?;
                }
            }
            _ => {
                bail!("When appending properties to a node or rel, the value you're appending must be a map, got {:?}", src)
            }
        }
        Ok(())
    }

    fn clear_props_on_thing(&self, ctx: &mut Context, thing: &GramVal) -> Result<()> {
        match thing {
            GramVal::Rel { node_id, rel_index } => {
                let node = &mut ctx.g.borrow_mut().nodes[*node_id];
                let rel = &mut node.rels[*rel_index];
                let mut props = rel.properties.borrow_mut();
                let _num_props = props.len();
                props.clear();
            }
            v => bail!("Don't know how to append properties to {:?}", v),
        }
        Ok(())
    }
}

impl Operator for SetProperties {
    fn reset(&mut self) {
        self.src.reset();
    }

    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool, Error> {
        if !self.src.next(ctx, out)? {
            return Ok(false);
        }

        for action in &self.actions {
            match action {
                SetAction::SingleAssign { entity, key, value } => {
                    let entity_val = &out.slots[*entity];
                    if let GramVal::Lit(litval) = value.eval(ctx, out)? {
                        self.write_prop_to_thing(ctx, entity_val, *key, litval)?;
                    } else {
                        bail!("Expected a literal value here, from {:?}", value);
                    }
                }
                SetAction::Append { entity, value } => {
                    let entity_val = &out.slots[*entity];
                    let new_props = value.eval(ctx, out)?;
                    self.write_thing_to_thing(ctx, entity_val, new_props)?;
                }
                SetAction::Overwrite { entity, value } => {
                    let entity_val = &out.slots[*entity];
                    let new_props = value.eval(ctx, out)?;
                    self.clear_props_on_thing(ctx, entity_val)?;
                    self.write_thing_to_thing(ctx, entity_val, new_props)?;
                }
            }
        }

        Ok(true)
    }
}

#[derive(Debug)]
struct ProduceResults {
    pub src: Box<dyn Operator>,
    pub fields: Vec<(Token, usize)>,
    print_header: bool,
}

impl Operator for ProduceResults {
    fn reset(&mut self) {
        self.src.reset();
    }

    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool> {
        if self.print_header {
            println!("----");
            let mut first = true;
            for (token, _) in &self.fields {
                let toks = ctx.tokens.borrow();
                let field_name = toks.lookup(*token).unwrap();
                if first {
                    print!("{}", field_name);
                    first = false
                } else {
                    print!(", {}", field_name)
                }
            }
            println!();
            println!("----");
            self.print_header = false;
        }
        self.src.next(ctx, out)
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
    fn reset(&mut self) {
        self.src.reset();
    }

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
struct Limit {
    src: Box<dyn Operator>,
    skip: Option<Expr>,
    limit: Option<Expr>,

    initialized: bool,
    limit_remaining: Option<i64>,
}

impl Operator for Limit {
    fn reset(&mut self) {
        self.src.reset();
        self.initialized = false;
    }

    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool> {
        if !self.initialized {
            self.initialized = true;
            if let Some(skip_expr) = &self.skip {
                let skip_val = skip_expr.eval(ctx, out)?;
                let mut skip = if let GramVal::Lit(Val::Int(i)) = skip_val {
                    i
                } else {
                    bail!("SKIP expression must be an integer, got {:?}", skip_val)
                };
                while skip > 0 && self.src.next(ctx, out)? {
                    skip -= 1
                }
            }
            if let Some(limit_expr) = &self.limit {
                let limit_val = limit_expr.eval(ctx, out)?;
                self.limit_remaining = if let GramVal::Lit(Val::Int(i)) = limit_val {
                    Some(i)
                } else {
                    bail!("LIMIT expression must be an integer, got {:?}", limit_val)
                };
            }
        }

        if let Some(limit_remaining) = self.limit_remaining {
            if limit_remaining == 0 {
                return Ok(false);
            }
            self.limit_remaining = Some(limit_remaining - 1);
        }

        self.src.next(ctx, out)
    }
}

#[derive(Debug)]
struct Optional {
    src: Box<dyn Operator>,
    initialized: bool,
    slots: Vec<usize>,
}

impl Operator for Optional {
    fn reset(&mut self) {
        self.src.reset();
        self.initialized = false;
    }

    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool> {
        println!("Optional {:?} @ {:?}", self.slots, out);
        if !self.initialized {
            self.initialized = true;
            if self.src.next(ctx, out)? {
                return Ok(true);
            }
            for s in &self.slots {
                out.slots[*s] = GramVal::Lit(Val::Null);
            }
            println!("  Optional {:?} @ {:?}", self.slots, out);
            Ok(true)
        } else {
            self.src.next(ctx, out)
        }
    }
}

#[derive(Debug)]
struct NestLoop {
    outer: Box<dyn Operator>,
    inner: Box<dyn Operator>,
    predicate: Expr,
    initialized: bool,
}

impl Operator for NestLoop {
    fn reset(&mut self) {
        self.outer.reset();
        self.inner.reset();
        self.initialized = false;
    }

    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool> {
        if !self.initialized {
            if !self.outer.next(ctx, out)? {
                // Well. That was easy
                return Ok(false);
            }
            self.initialized = true;
        }

        loop {
            if !self.inner.next(ctx, out)? {
                // We need the ability to "reset" the inner operator here, which we don't
                // yet have.. and the TCK does not as-of-yet test any cases where the outer
                // is more than one row! So just ensure there's no more rows in the input and
                // then bail.
                if self.outer.next(ctx, out)? {
                    panic!("gram backend can't do cartesian product when outer has N > 1 yet")
                }
                return Ok(false);
            }

            if self.predicate.eval(ctx, out)?.as_bool()? {
                return Ok(true);
            }
        }
    }
}

#[derive(Debug)]
struct Sort {
    src: Box<dyn Operator>,
    state: SortState,
    rows: Vec<GramRow>,
    sort_by: Vec<Expr>,
}

#[derive(Debug)]
enum SortState {
    Init,
    Yielding { next: usize },
    Done,
}

impl Operator for Sort {
    fn reset(&mut self) {
        self.src.reset();
        self.state = SortState::Init;
    }

    // TODO lol
    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool> {
        if let SortState::Init = self.state {
            let mut rows = Vec::new();
            while self.src.next(ctx, out)? {
                rows.push(out.clone());
            }

            if rows.is_empty() {
                self.state = SortState::Done;
                return Ok(false);
            }

            rows.sort_by(|a, b| {
                for e in &self.sort_by {
                    let a_val = e.eval(ctx, a).unwrap();
                    let b_val = e.eval(ctx, b).unwrap();
                    let cmp = a_val.partial_cmp(&b_val);
                    match cmp {
                        Some(Ordering::Greater) => return Ordering::Greater,
                        Some(Ordering::Less) => return Ordering::Less,
                        // TODO: Val should probably implement Ord, because while we don't
                        //       implement a full Eq, there *is* a total ordering. As it happens,
                        //       things that aren't technically comparable (NULL > NULL et al)
                        //       "are equal" when it comes to sorting and grouping.. so this works
                        _ => (),
                    }
                }
                Ordering::Equal
            });
            self.rows = rows;
            self.state = SortState::Yielding { next: 0 };
        }

        if let SortState::Yielding { next } = self.state {
            let row = &self.rows[next];
            let size = out.slots.len();
            out.slots.clone_from_slice(&row.slots[..size]);
            if self.rows.len() > next + 1 {
                self.state = SortState::Yielding { next: next + 1 }
            } else {
                self.state = SortState::Done;
            }
            Ok(true)
        } else {
            Ok(false)
        }
    }
}

#[derive(Debug)]
struct Selection {
    pub src: Box<dyn Operator>,
    pub predicate: Expr,
}

impl Operator for Selection {
    fn reset(&mut self) {
        self.src.reset();
    }

    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool> {
        while self.src.next(ctx, out)? {
            let ok = self.predicate.eval(ctx, out)?;
            if let GramVal::Lit(Val::Bool(true)) = ok {
                return Ok(true);
            }
        }
        Ok(false)
    }
}

// So, this gets complicated. Cypher defines two types with a lot of baggage: NULL and IEEE-754
// floats. One of the side-effects of this is that the cypher type system only has partial order
// and partial equality defined. This creates problems; what should be the result of this
// query?
//
//   WITH toFloat("NaN") AS n UNWIND [{k:n,v:1},{k:n,v:1}] AS e RETURN e.k, COUNT(*);
//
// Well. Cypher hacks around this problem by defining a *second* type of equality called
// "equivalence". Predicates are evaluated with the equality rules, while aggregate keys are
// evaluated with the equivalence rules.
//
// This struct uses the equivalence rules to implement rusts equal and hashcode traits, so
// you can wrap your stuff with this and have rust follow the cypher equivalence rules.
#[derive(Debug, Clone)]
struct GroupKey {
    vals: Vec<GramVal>,
}

impl Eq for GroupKey {}

impl PartialEq for GroupKey {
    fn eq(&self, other: &Self) -> bool {
        for v in &self.vals {
            for ov in &other.vals {
                if v.ne(ov) {
                    return false;
                }
            }
        }
        true
    }
}

impl Hash for GroupKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for v in &self.vals {
            match v {
                GramVal::Lit(lv) => match lv {
                    Val::Null => 0.hash(state),
                    Val::String(sv) => sv.hash(state),
                    _ => panic!("gram backend can't yet use {:?} as aggregate keys", v),
                },
                GramVal::Node { id } => id.hash(state),
                _ => panic!("gram backend can't yet use {:?} as aggregate keys", v),
            };
        }
    }
}

#[derive(Debug)]
struct GroupEntry {
    expr: Expr,
    slot: Slot,
}

#[derive(Debug)]
struct AggregateEntry {
    func: Box<dyn functions::AggregatingFunc>,
    slot: Slot,
}

// This whole thing is throw-away, just want to spike through a working implementation to get
// a feel for things.
#[derive(Debug)]
struct HashAggregation {
    src: Box<dyn Operator>,

    grouping: Vec<GroupEntry>,
    aggregations: Vec<AggregateEntry>,

    group_aggregations: HashMap<GroupKey, Vec<Box<dyn functions::Aggregation>>>,
    group_order: Vec<GroupKey>,

    consumed: bool,
    aggregated: bool,
}

impl Operator for HashAggregation {
    fn reset(&mut self) {
        self.src.reset();
        self.consumed = false;
        self.aggregated = false;
        self.group_aggregations.clear();
        self.group_order.clear();
    }

    #[allow(clippy::needless_range_loop)]
    fn next(&mut self, ctx: &mut Context, row: &mut GramRow) -> Result<bool> {
        loop {
            if self.consumed {
                return Ok(false);
            }
            if self.aggregated {
                if self.group_aggregations.is_empty() {
                    self.consumed = true;
                    return Ok(false);
                }
                let key = self.group_order.pop().unwrap();
                let mut aggregation = self.group_aggregations.remove(&key).unwrap();

                for i in 0..self.grouping.len() {
                    let keyslot = self.grouping[i].slot;
                    let k = key.vals[i].clone();
                    row.slots[keyslot] = k;
                }

                for i in 0..self.aggregations.len() {
                    let agge = &mut aggregation[i];
                    let slot = self.aggregations[i].slot;
                    row.slots[slot] = agge.complete()?.clone();
                }

                return Ok(true);
            }
            let src = &mut *self.src;
            while src.next(ctx, row)? {
                // Calculate the group key
                let mut key = GroupKey {
                    vals: Vec::with_capacity(self.grouping.len()),
                };
                for group in &self.grouping {
                    key.vals.push(group.expr.eval(ctx, row)?)
                }
                // Does an entry like that exist?
                let maybe_state = self.group_aggregations.get_mut(&key);
                if let Some(group_state) = maybe_state {
                    for agge in group_state {
                        agge.apply(ctx, row)?;
                    }
                } else {
                    let mut group_state = Vec::with_capacity(self.aggregations.len());
                    for agge in &mut self.aggregations {
                        group_state.push(agge.func.init(ctx))
                    }
                    for agge in &mut group_state {
                        agge.apply(ctx, row)?;
                    }
                    self.group_order.push(key.clone());
                    self.group_aggregations.insert(key, group_state);
                }
            }

            self.aggregated = true;
        }
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
    fn reset(&mut self) {
        self.src.reset();
        self.current_list = None;
        self.next_index = 0;
    }
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

#[derive(Debug)]
struct Apply {
    pub lhs: Box<dyn Operator>,
    pub rhs: Box<dyn Operator>,
    pub initialized: bool,
}

impl Operator for Apply {
    fn reset(&mut self) {
        self.lhs.reset();
        self.rhs.reset();
        self.initialized = false;
    }
    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool> {
        if !self.initialized {
            self.initialized = true;
            if !self.lhs.next(ctx, out)? {
                return Ok(false);
            }
            self.rhs.reset()
        }

        loop {
            if self.rhs.next(ctx, out)? {
                return Ok(true);
            }

            // Exhausted rhs, fetch next lhs

            if !self.lhs.next(ctx, out)? {
                return Ok(false);
            }
            self.rhs.reset()
        }
    }
}

#[derive(Debug)]
struct AntiConditionalApply {
    pub lhs: Box<dyn Operator>,
    pub rhs: Box<dyn Operator>,

    pub conditions: Vec<usize>,
}

impl Operator for AntiConditionalApply {
    fn reset(&mut self) {
        self.lhs.reset();
        self.rhs.reset();
    }
    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool> {
        loop {
            if !self.lhs.next(ctx, out)? {
                return Ok(false);
            }

            let mut anticondition_passed = true;
            for condition_slot in &self.conditions {
                match out.slots[*condition_slot] {
                    GramVal::Lit(Val::Null) => (),
                    _ => {
                        anticondition_passed = false;
                        break;
                    }
                }
            }

            if anticondition_passed {
                self.rhs.reset();
                if self.rhs.next(ctx, out)? {
                    return Ok(true);
                }
            }
        }
    }
}

#[derive(Debug)]
struct ConditionalApply {
    pub lhs: Box<dyn Operator>,
    pub rhs: Box<dyn Operator>,

    pub conditions: Vec<usize>,
}

impl Operator for ConditionalApply {
    fn reset(&mut self) {
        self.lhs.reset();
        self.rhs.reset();
    }
    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool> {
        loop {
            if !self.lhs.next(ctx, out)? {
                return Ok(false);
            }

            let mut condition_passed = true;
            for condition_slot in &self.conditions {
                if let GramVal::Lit(Val::Null) = out.slots[*condition_slot] {
                    condition_passed = false;
                    break;
                }
            }
            if condition_passed {
                self.rhs.reset();
                if self.rhs.next(ctx, out)? {
                    return Ok(true);
                }
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
    use pest::iterators::Pair;
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

    struct ParserContext<'a> {
        anon_id_gen: u32,
        node_ids: Tokens,
        tokens: &'a mut Tokens,
    }

    fn parse_node(item: Pair<Rule>, ctx: &mut ParserContext) -> Result<Node> {
        let mut identifier: Option<String> = None;
        let mut props: HashMap<Token, Val> = HashMap::new();
        let mut labels: HashSet<Token> = HashSet::new();

        for part in item.into_inner() {
            match part.as_rule() {
                Rule::id => identifier = Some(part.as_str().to_string()),
                Rule::label => {
                    for label in part.into_inner() {
                        labels.insert(ctx.tokens.tokenize(label.as_str()));
                    }
                }
                Rule::map => parse_props(ctx, &mut props, part),
                _ => panic!("what? {:?} / {}", part.as_rule(), part.as_str()),
            }
        }

        let gid_string = identifier.unwrap_or_else(|| {
            // Entry with no identifier, generate one
            loop {
                let candidate = format!("anon#{}", ctx.anon_id_gen);
                if !ctx.node_ids.table.contains_key(&candidate) {
                    return candidate;
                }
                ctx.anon_id_gen += 1;
            }
        });
        let gid = ctx.tokens.tokenize(&gid_string);
        let id = ctx.node_ids.tokenize(&gid_string);
        Ok(Node {
            id,
            gid,
            labels,
            properties: props,
            rels: vec![],
        })
    }

    fn parse_props(ctx: &mut ParserContext, props: &mut HashMap<usize, Val>, part: Pair<Rule>) {
        for pair in part.into_inner() {
            let mut key: Option<String> = None;
            let mut val = None;
            match pair.as_rule() {
                Rule::map_pair => {
                    for pair_part in pair.into_inner() {
                        match pair_part.as_rule() {
                            Rule::id => key = Some(pair_part.as_str().to_string()),
                            Rule::expr => {
                                let stringval = pair_part.into_inner().next().unwrap();
                                let stringval_content = stringval.into_inner().next().unwrap();
                                val = Some(stringval_content.as_str().to_string())
                            }
                            _ => panic!("what? {:?} / {}", pair_part.as_rule(), pair_part.as_str()),
                        }
                    }
                }
                _ => panic!("what? {:?} / {}", pair.as_rule(), pair.as_str()),
            }
            let key_str = key.unwrap();
            props.insert(ctx.tokens.tokenize(&key_str), Val::String(val.unwrap()));
        }
    }

    pub fn load(tokens: &mut Tokens, file: &mut File) -> Result<Graph> {
        let mut g = Graph { nodes: vec![] };

        let query_str = read_to_string(file).unwrap();
        let mut parse_result = GramParser::parse(Rule::gram, &query_str)?;

        let gram = parse_result.next().unwrap(); // get and unwrap the `file` rule; never fails

        let node_ids = Tokens {
            table: Default::default(),
        };

        let mut pc = ParserContext {
            anon_id_gen: 0,
            node_ids,
            tokens,
        };

        for item in gram.into_inner() {
            match item.as_rule() {
                Rule::path => {
                    let mut start_identifier: Option<Token> = None;
                    let mut end_identifier: Option<Token> = None;

                    let mut rel_type = None;
                    let mut rel_props: HashMap<Token, Val> = HashMap::new();

                    for part in item.into_inner() {
                        match part.as_rule() {
                            Rule::node => {
                                let n = parse_node(part, &mut pc)?;
                                if start_identifier == None {
                                    start_identifier = Some(n.id);
                                } else {
                                    end_identifier = Some(n.id);
                                }
                                // need like a merge_node operation; but for now, insert the
                                // first occurrence of a node, so subsequent ones won't clear out
                                // properties
                                if g.nodes.len() <= n.id {
                                    g.add_node(n.id, n);
                                }
                            }
                            Rule::rel => {
                                for rel_part in part.into_inner() {
                                    match rel_part.as_rule() {
                                        Rule::map => {
                                            parse_props(&mut pc, &mut rel_props, rel_part);
                                        }
                                        Rule::rel_type => {
                                            let rt_id = rel_part.into_inner().next().unwrap();
                                            rel_type = Some(pc.node_ids.tokenize(
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
                        rel_type.unwrap_or_else(|| pc.tokens.tokenize("_")),
                        rel_props,
                    );
                }
                Rule::node => {
                    let n = parse_node(item, &mut pc)?;
                    g.add_node(n.id, n)
                }
                _ => (),
            }
        }

        Ok(g)
    }
}

#[derive(Debug)]
pub struct Node {
    // Identifier for this node, matches it's index into the node vector in g
    id: usize,
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
    properties: Rc<RefCell<HashMap<Token, Val>>>,
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
            .borrow()
            .get(&prop)
            .cloned()
    }

    fn add_node(&mut self, id: usize, n: Node) {
        while self.nodes.len() <= id {
            let filler_id = self.nodes.len();
            self.nodes.push(Node {
                id: filler_id,
                gid: 0,
                labels: Default::default(),
                properties: Default::default(),
                rels: vec![],
            })
        }
        self.nodes[id] = n;
    }

    // Add a rel, return the index of the rel from the start nodes perspective
    fn add_rel(
        &mut self,
        from: usize,
        to: usize,
        rel_type: Token,
        props: HashMap<Token, Val>,
    ) -> usize {
        let wrapped_props = Rc::new(RefCell::new(props));
        let fromrels = &mut self.nodes[from].rels;
        fromrels.push(RelHalf {
            rel_type,
            dir: Dir::Out,
            other_node: to,
            properties: Rc::clone(&wrapped_props),
        });
        let index = fromrels.len() - 1;
        self.nodes[to].rels.push(RelHalf {
            rel_type,
            dir: Dir::In,
            other_node: from,
            properties: wrapped_props,
        });
        index
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
    let p = serialize_props(ctx, &node_properties);
    let gram_identifier = generate_uuid().to_hyphenated().to_string();
    let mut tokens = tokens_in.borrow_mut();
    let gram_string = if !labels.is_empty() {
        let labels_gram_ready: Vec<&str> =
            labels.iter().map(|l| tokens.lookup(*l).unwrap()).collect();
        format!(
            "(`{}`:{} {})\n",
            gram_identifier,
            labels_gram_ready.join(":"),
            p
        )
    } else {
        format!("(`{}` {})\n", gram_identifier, p)
    };

    let id = ctx.g.borrow().nodes.len();
    let out_node = Node {
        id,
        gid: tokens.tokenize(&gram_identifier),
        labels,
        properties: node_properties,
        rels: vec![],
    };

    ctx.g.borrow_mut().add_node(id, out_node);

    println!("--- About to write ---");
    println!("{}", gram_string);
    println!("------");
    // TODO: actually write to the file:

    ctx.file
        .borrow_mut()
        .seek(SeekFrom::End(0))
        .expect("seek error");

    match ctx.file.borrow_mut().write_all(gram_string.as_bytes()) {
        Ok(_) => Ok(GramVal::Node { id }),
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
    let p = serialize_props(ctx, &props);
    let mut g = ctx.g.borrow_mut();
    let tokens = ctx.tokens.borrow();

    let startgid = tokens.lookup(g.nodes[start_node].gid).unwrap();
    let endgid = tokens.lookup(g.nodes[end_node].gid).unwrap();
    let reltype_str = tokens.lookup(rel_type).unwrap();

    let gram_string = format!(
        "(`{}`)-[:`{}` {}]->(`{}`)\n",
        startgid, reltype_str, p, endgid,
    );

    println!("--- About to write ---");
    println!("{}", gram_string);
    println!("------");

    let rel_index = g.add_rel(start_node, end_node, rel_type, props);

    ctx.file
        .borrow_mut()
        .seek(SeekFrom::End(0))
        .expect("seek error");

    match ctx.file.borrow_mut().write_all(gram_string.as_bytes()) {
        Ok(_) => Ok(GramVal::Rel {
            node_id: start_node,
            rel_index,
        }),
        Err(e) => Err(Error::new(e)),
    }
}

fn serialize_props(ctx: &mut Context, props: &HashMap<Token, Val>) -> String {
    let mut out = String::new();
    let mut first = true;
    out.push_str("{");
    for (k, v) in props {
        if !first {
            out.push_str(", ");
        } else {
            first = false;
        }
        {
            let toks = ctx.tokens.borrow_mut();
            let key = toks.lookup(*k).unwrap();
            out.push_str(key);
        }
        out.push_str(": ");
        out.push_str(&serialize_val(ctx, &v))
    }
    out.push_str("}");
    out
}

fn serialize_val(_ctx: &mut Context, v: &Val) -> String {
    match v {
        Val::String(s) => format!("\'{}\'", s),
        Val::Int(v) => format!("{}", v),
        Val::Bool(v) => format!("{}", v),
        _ => panic!("Don't know how to serialize {:?}", v),
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
        out.push(Box::new(CountSpec::new(tokens)));
        out
    }

    #[derive(Debug, Clone)]
    pub(super) enum Func {
        Not,
        Abs,
        Keys,
    }

    impl Func {
        pub fn apply(&self, ctx: &mut Context, args: &[GramVal]) -> Result<GramVal> {
            match self {
                Func::Not => match args
                    .get(0)
                    .ok_or_else(|| anyhow!("NOT takes one argument"))?
                {
                    GramVal::Lit(v) => match v {
                        Val::Bool(b) => Ok(GramVal::Lit(Val::Bool(!*b))),
                        v => bail!("don't know how to do NOT({:?})", v),
                    },
                    v => bail!("don't know how to do NOT({:?})", v),
                },
                Func::Abs => match args
                    .get(0)
                    .ok_or_else(|| anyhow!("ABS takes one argument"))?
                {
                    GramVal::Lit(Val::Int(v)) => Ok(GramVal::Lit(Val::Int(v.abs()))),
                    GramVal::Lit(Val::Float(v)) => Ok(GramVal::Lit(Val::Float(v.abs()))),
                    v => bail!("don't know how to take ABS({:?})", v),
                },
                Func::Keys => match args
                    .get(0)
                    .ok_or_else(|| anyhow!("ABS takes one argument"))?
                {
                    GramVal::Lit(Val::Map(m)) => {
                        // TODO this kind of allocation is interesting, where should it go?
                        let o: Vec<GramVal> = m
                            .iter()
                            .map(|(k, _)| GramVal::Lit(Val::String(k.to_owned())))
                            .collect();
                        Ok(GramVal::List(o))
                    }
                    GramVal::Rel { node_id, rel_index } => {
                        let node = &ctx.g.borrow().nodes[*node_id];
                        let rel = &node.rels[*rel_index];
                        let props = rel.properties.borrow();
                        let o: Vec<GramVal> = props
                            .keys()
                            // TODO obvs will blow up on reasonable queries
                            .map(|k| {
                                GramVal::Lit(Val::String(
                                    ctx.tokens.borrow().lookup(*k).unwrap().to_owned(),
                                ))
                            })
                            .collect();
                        Ok(GramVal::List(o))
                    }
                    GramVal::Node { id } => {
                        let node = &ctx.g.borrow().nodes[*id];
                        let props = &node.properties;
                        let o: Vec<GramVal> = props
                            .keys()
                            .map(|k| {
                                GramVal::Lit(Val::String(
                                    ctx.tokens.borrow().lookup(*k).unwrap().to_owned(),
                                ))
                            })
                            .collect();
                        Ok(GramVal::List(o))
                    }
                    v => bail!("don't know how to do KEYS({:?})", v),
                },
            }
        }
    }

    // This trait combines with AggregatingFunc and Aggregation to specify uhh, aggregation.
    // The split is basically: AggregatingFuncSpec is used before query execution starts,
    // we call init() with the expressions from the query plan to get an AggregatingFunc
    // specifically for the query we're executing now. Then aggregatingFunc#init is called
    // once for each aggregation group, yielding, finally, Aggregation, which is the accumulating
    // state for each group.
    //
    // There are a large number of problems with this design, but you gotta start somewhere :)
    //
    // Some thoughts: It's annoying that this is all heap allocated; aggregations is one of
    // two critical places where memory management really, really matters (sorting being the other),
    // and so it'd be nice if the environment these guys execute in had more control of where their
    // state goes and how big it gets..
    pub(super) trait AggregatingFuncSpec: Debug {
        fn signature(&self) -> &FuncSignature;
        fn init(&self, args: Vec<Expr>) -> Box<dyn AggregatingFunc>;
    }

    pub(super) trait AggregatingFunc: Debug {
        fn init(&mut self, ctx: &mut Context) -> Box<dyn Aggregation>;
    }

    pub(super) trait Aggregation: Debug {
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
            &self.sig
        }

        fn init(&self, mut args: Vec<Expr>) -> Box<dyn AggregatingFunc> {
            Box::new(Min {
                arg: args.pop().expect("min takes 1 arg"),
            })
        }
    }

    #[derive(Debug)]
    struct Min {
        arg: Expr,
    }

    impl AggregatingFunc for Min {
        fn init(&mut self, _ctx: &mut Context) -> Box<dyn Aggregation> {
            Box::new(MinAggregation {
                arg: self.arg.clone(),
                min: None,
            })
        }
    }

    #[derive(Debug)]
    struct MinAggregation {
        arg: Expr,
        min: Option<GramVal>,
    }

    impl Aggregation for MinAggregation {
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
                Ok(v)
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
            &self.sig
        }

        fn init(&self, mut args: Vec<Expr>) -> Box<dyn AggregatingFunc> {
            Box::new(Max {
                arg: args.pop().expect("max takes 1 argument"),
            })
        }
    }

    #[derive(Debug)]
    struct Max {
        arg: Expr,
    }

    impl AggregatingFunc for Max {
        fn init(&mut self, _ctx: &mut Context) -> Box<dyn Aggregation> {
            Box::new(MaxAggregation {
                arg: self.arg.clone(),
                max: None,
            })
        }
    }

    #[derive(Debug)]
    struct MaxAggregation {
        arg: Expr,
        max: Option<GramVal>,
    }

    impl Aggregation for MaxAggregation {
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
                Ok(v)
            } else {
                Err(anyhow!(
                    "There were no input rows to the aggregation, cannot calculate min(..)"
                ))
            }
        }
    }

    #[derive(Debug)]
    struct CountSpec {
        sig: FuncSignature,
    }

    impl CountSpec {
        pub fn new(tokens: &mut Tokens) -> CountSpec {
            let fn_name = tokens.tokenize("count");
            CountSpec {
                sig: FuncSignature {
                    func_type: FuncType::Aggregating,
                    name: fn_name,
                    returns: Type::Any,
                    args: vec![],
                },
            }
        }
    }

    impl AggregatingFuncSpec for CountSpec {
        fn signature(&self) -> &FuncSignature {
            &self.sig
        }

        fn init(&self, _args: Vec<Expr>) -> Box<dyn AggregatingFunc> {
            Box::new(Count {})
        }
    }

    #[derive(Debug)]
    struct Count {}

    impl AggregatingFunc for Count {
        fn init(&mut self, _ctx: &mut Context) -> Box<dyn Aggregation> {
            Box::new(CountAggregation {
                counter: 0,
                out: GramVal::Lit(Val::Int(0)),
            })
        }
    }

    #[derive(Debug)]
    struct CountAggregation {
        counter: i64,
        out: GramVal,
    }

    impl Aggregation for CountAggregation {
        fn apply(&mut self, _ctx: &mut Context, _row: &mut GramRow) -> Result<()> {
            self.counter += 1;
            Ok(())
        }

        fn complete(&mut self) -> Result<&GramVal> {
            self.out = GramVal::Lit(Val::Int(self.counter));
            Ok(&self.out)
        }
    }
}

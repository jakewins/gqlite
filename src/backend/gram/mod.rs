// The Gram backend is a backend implementation that acts on a Gram file.
// Note that this is primarily a playground currently, there are no tests and
// things are duct-taped together; we're interested in exploration and learning
// not a final product.

// It is currently single threaded, and provides no data durability guarantees.

use crate::backend::gram::functions::{AggregatingFuncSpec, MapAggregatingFunc};
use crate::backend::{Backend, BackendCursor, BackendDesc, Token, Tokens};
use crate::frontend::{Dir, LogicalPlan, Depth};
use crate::{frontend, Error, Row, Slot, Val};
use anyhow::Result;
use rand::Rng;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::fmt::{self, Debug, Display, Formatter};
use std::fs::File;
use std::hash::{Hash, Hasher};
use std::io::{Write};
use std::rc::Rc;
use std::time::SystemTime;
use uuid::v1::{Context as UuidContext, Timestamp};
use uuid::Uuid;
use crate::backend::gram::store::{Graph, Version, Node};

mod marshal;
mod store;

#[derive(Debug)]
pub struct GramBackend {
    tokens: Rc<RefCell<Tokens>>,
    g: Rc<RefCell<store::Graph>>,
    file: Rc<RefCell<File>>,
    aggregators: HashMap<Token, Box<dyn AggregatingFuncSpec>>,
    next_xid: u32,
}

impl GramBackend {
    pub fn open(mut file: File) -> Result<GramBackend> {
        let mut tokens = Tokens {
            table: Default::default(),
        };
        let g = marshal::load(&mut tokens, &mut file)?;

        let mut aggregators = HashMap::new();
        for agg in functions::aggregating(&mut tokens) {
            aggregators.insert(agg.signature().name, agg);
        }

        Ok(GramBackend {
            tokens: Rc::new(RefCell::new(tokens)),
            g: Rc::new(RefCell::new(g)),
            file: Rc::new(RefCell::new(file)),
            aggregators,
            next_xid: 1,
        })
    }

    pub fn flush(&mut self) -> Result<()> {
        let mut g = self.g.borrow_mut();
        let mut f = self.file.borrow_mut();
        let toks = self.tokens.borrow();
        marshal::store(&toks, &mut g, &mut f)
    }

    fn convert(&self, plan: LogicalPlan) -> Result<Box<dyn Operator>> {
        match plan {
            LogicalPlan::Argument => Ok(Box::new(Argument { consumed: false })),
            LogicalPlan::NodeScan { src, phase, slot, labels } => Ok(Box::new(NodeScan {
                src: self.convert(*src)?,
                phase,
                slot,
                labels,
                state: NodeScanState::Idle,
            })),
            LogicalPlan::Create { src, phase, nodes, rels } => {
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
                    phase,
                    nodes: out_nodes,
                    rels: out_rels,
                    tokens: self.tokens.clone(),
                }))
            }
            LogicalPlan::Update { src, phase, actions } => {
                let mut out_actions = Vec::with_capacity(actions.len());
                for action in actions {
                    match action {
                        frontend::UpdateAction::PropAssign { entity, key, value } => out_actions
                            .push(UpdateAction::SingleAssign {
                                entity,
                                key,
                                value: self.convert_expr(value),
                            }),
                        frontend::UpdateAction::PropAppend { entity, value } => {
                            out_actions.push(UpdateAction::Append {
                                entity,
                                value: self.convert_expr(value),
                            })
                        }
                        frontend::UpdateAction::PropOverwrite { entity, value } => {
                            out_actions.push(UpdateAction::Overwrite {
                                entity,
                                value: self.convert_expr(value),
                            })
                        }
                        frontend::UpdateAction::LabelSet { entity, label } => {
                            out_actions.push(UpdateAction::AppendLabel { entity, label })
                        }
                        frontend::UpdateAction::DeleteEntity { entity: node } => {
                            out_actions.push(UpdateAction::DeleteEntity {
                                entity: self.convert_expr(node),
                            })
                        }
                        frontend::UpdateAction::DetachDelete { entity: node } => {
                            out_actions.push(UpdateAction::DetachDelete{
                                entity: self.convert_expr(node),
                            })
                        }
                    }
                }
                Ok(Box::new(UpdateEntity {
                    src: self.convert(*src)?,
                    actions: out_actions,
                    phase,
                }))
            }
            LogicalPlan::Expand {
                src,
                phase,
                src_slot,
                rel_slot,
                dst_slot,
                rel_type,
                dir,
                depth,
            } => {
                let (min_depth, max_depth) = match depth {
                    Depth::Exact(d) => (d,d),
                    Depth::Unlimited => (0, usize::MAX),
                };
                Ok(Box::new(Expand {
                    src: self.convert(*src)?,
                    phase,
                    src_slot,
                    rel_slot,
                    dst_slot,
                    rel_type,
                    dir,
                    min_depth,
                    max_depth,
                    stack: Vec::new(),
                    state: ExpandState::NextNode,
                }))
            },
            LogicalPlan::ExpandRel {
                src,
                phase: _,
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
                phase,
                left_node_slot,
                right_node_slot,
                dst_slot,
                rel_type,
                dir,
            } => Ok(Box::new(ExpandInto {
                src: self.convert(*src)?,
                phase,
                left_node_slot,
                right_node_slot,
                dst_slot,
                rel_type,
                dir,
            })),
            LogicalPlan::Selection { src,  phase, predicate } => {
                // self.convert(*src)
                Ok(Box::new(Selection {
                    src: self.convert(*src)?,
                    phase,
                    predicate: self.convert_expr(predicate),
                }))
            }
            LogicalPlan::Aggregate {
                src,
                phase,
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
                    phase,
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
                phase,
                list_expr,
                alias,
            } => Ok(Box::new(Unwind {
                src: self.convert(*src)?,
                phase,
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
            LogicalPlan::Project { src, phase, projections } => {
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
                    phase,
                    projections: converted_projections,
                }))
            }
            LogicalPlan::Sort { src, phase, sort_by } => {
                let mut conv_sort_by = Vec::with_capacity(sort_by.len());
                for s in sort_by {
                    conv_sort_by.push(self.convert_expr(s));
                }
                Ok(Box::new(Sort {
                    src: self.convert(*src)?,
                    phase,
                    state: SortState::Init,
                    rows: vec![],
                    sort_by: conv_sort_by,
                }))
            }
            LogicalPlan::Limit { src, phase, skip, limit } => {
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
                    phase,
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
                phase,
                predicate,
            } => Ok(Box::new(NestLoop {
                outer: self.convert(*outer)?,
                inner: self.convert(*inner)?,
                phase,
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
            LogicalPlan::Barrier {
                src, ..
            } => {
                Ok(Box::new(Barrier{
                    src: self.convert(*src)?,
                    buf: None,
                    ptr: 0
                }))
            }
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
            frontend::Expr::Map(es) => {
                let mut aggregating = Vec::new();
                for e in es {
                    // TODO this will obviously break if there is anything non-aggregating in place..
                    aggregating.push((e.key, self.convert_aggregating_expr(e.val)));
                }
                Box::new(MapAggregatingFunc { aggregating })
            }
            _ => panic!(
                "The gram backend does not support this expression type in aggregations yet: {:?}",
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

            frontend::Expr::Param(ptok) => Expr::Param(ptok),

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

            frontend::Expr::Path(es) => {
                Expr::Path(es)
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
                } else if name == tokens.tokenize("range") {
                    Expr::Call(functions::Func::Range, convargs)
                } else {
                    panic!("Unknown function: {:?}", tokens.lookup(name).unwrap(),)
                }
            }
            frontend::Expr::Bool(v) => Expr::Lit(Val::Bool(v)),

            frontend::Expr::And(terms) => {
                Expr::And(terms.iter().map(|e| self.convert_expr(e.clone())).collect())
            }
            frontend::Expr::Not(e) => Expr::Not(Box::new(self.convert_expr(*e))),
            frontend::Expr::HasLabel(slot, label) => Expr::HasLabel { slot, label },
            frontend::Expr::IsNull(term) => Expr::IsNull(Box::new(self.convert_expr(*term))),
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
        let xid = self.next_xid;
        self.next_xid += 1;
        GramCursor {
            ctx: Context {
                tokens: Rc::clone(&self.tokens),
                g: Rc::clone(&self.g),
                file: Rc::clone(&self.file),
                stack: vec![GramVal::Lit(Val::Null); 16],
                parameters: Default::default(),
                xid: Version{
                    xid,
                    phase: 0
                },
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

    fn eval(
        &mut self,
        plan: LogicalPlan,
        cursor: &mut GramCursor,
        params: Option<&Val>,
    ) -> Result<(), Error> {
        let slots = match &plan {
            LogicalPlan::ProduceResult { fields, .. } => fields.clone(),
            _ => Vec::new(),
        };
        if cursor.projection.slots.len() < slots.len() {
            cursor.projection.slots.resize(slots.len(), Val::Null);
        }

        let plan = self.convert(plan)?;

        let mapped_params = match params {
            None => HashMap::new(),
            Some(Val::Map(entries)) => {
                let mut out = HashMap::new();
                for (k, v) in entries {
                    let ktok = self.tokens.borrow_mut().tokenize(k);
                    out.insert(ktok, v.to_owned());
                }
                out
            }
            _ => bail!("params must be a Val::Map, got {:?}", params),
        };

        let xid = self.next_xid;
        self.next_xid += 1;

        cursor.ctx = Context {
            tokens: Rc::clone(&self.tokens),
            g: Rc::clone(&self.g),
            file: Rc::clone(&self.file),
            stack: vec![GramVal::Lit(Val::Null); 16], // TODO needs to match plan stack size
            parameters: mapped_params,
            xid: Version{
                xid,
                phase: 0
            },
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
        let v = Version::new(self.ctx.xid.xid, u8::MAX);
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
                        self.row.slots[self.slots[slot].1].project(&mut self.ctx, v);
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
    xid: Version,
    // some expressions create local scopes while they evaluate (eg. list comprehensions),
    // those locals go on this stack.
    stack: Vec<GramVal>,
    // Parameters this query was ran with
    parameters: HashMap<Token, Val>,
}

#[derive(Debug, Clone)]
enum Expr {
    Lit(Val),
    // Lookup a property by id
    Prop(Box<Expr>, Vec<Token>),
    // Dynamically lookup a property by a runtime expression
    DynProp(Box<Expr>, Box<Expr>),

    Param(Token),

    RowRef(Slot),
    StackRef(Slot),
    List(Vec<Expr>),
    Map(Vec<(Token, Expr)>),

    // Always odd, alternating node/rel/node
    Path(Vec<Slot>),

    ListComprehension {
        src: Box<Expr>,
        // The temporary value of each entry in src gets stored in this local stack slot,
        // and then accessed by the map_expr
        stackslot: usize,
        map_expr: Box<Expr>,
    },

    Call(functions::Func, Vec<Expr>),

    And(Vec<Expr>),
    Not(Box<Expr>),

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
    IsNull(Box<Expr>),
}

impl Expr {
    fn eval_prop(ctx: &mut Context, row: &GramRow, expr: &Expr, prop: &[Token], v: Version) -> Result<GramVal> {
        let mut val = expr.eval(ctx, row, v)?;
        for key in prop {
            val = match val {
                GramVal::Node { id } => {
                    GramVal::Lit(ctx.g.borrow().get_node_prop(id, *key, v).unwrap_or(Val::Null))
                }
                GramVal::Rel { node_id, rel_index } => GramVal::Lit(
                    ctx.g
                        .borrow()
                        .get_rel_prop(node_id, rel_index, *key, v)
                        .unwrap_or(Val::Null),
                ),
                GramVal::Map(es) => es
                    .iter()
                    .find(|(ek, _)| ek == key)
                    .map(|e| e.1.clone())
                    .unwrap_or(GramVal::Lit(Val::Null)),
                GramVal::Lit(Val::Map(es)) => {
                    let toks = ctx.tokens.borrow();
                    let key_str = toks.lookup(*key).unwrap();
                    es.iter()
                        .find(|(ek, _)| ek == key_str)
                        .map(|e| GramVal::Lit(e.1.clone()))
                        .unwrap_or(GramVal::Lit(Val::Null))
                }
                GramVal::Lit(Val::Null) => GramVal::Lit(Val::Null),
                val => bail!("[eval_prop] Gram backend does not yet support {:?}", v),
            };
        }
        Ok(val)
    }

    fn eval(&self, ctx: &mut Context, row: &GramRow, v: Version) -> Result<GramVal> {
        match self {
            Expr::Param(ptok) => match ctx.parameters.get(ptok) {
                None => {
                    let toks = ctx.tokens.borrow();
                    let want = toks.lookup(*ptok).unwrap_or("N/A");
                    let have: Vec<String> = ctx
                        .parameters
                        .keys()
                        .map(|k| toks.lookup(*k).unwrap_or("N/A").to_owned())
                        .collect();
                    bail!(
                        "Query parameter '{}' was not specified, known parameters are: {:?}",
                        want,
                        have
                    )
                }
                Some(v) => Ok(GramVal::Lit(v.to_owned())),
            },
            Expr::Prop(expr, keys) => Expr::eval_prop(ctx, row, expr, keys, v),
            Expr::DynProp(expr, key) => {
                let keyval = key.eval(ctx, row, v)?;
                match keyval {
                    GramVal::Lit(Val::String(keystr)) => {
                        let tok = ctx.tokens.borrow_mut().tokenize(keystr.as_str());
                        Expr::eval_prop(ctx, row, expr, &[tok], v)
                    }
                    GramVal::Lit(Val::Int(index)) => {
                        Ok(expr.eval(ctx, row, v)?.get_index(index as usize)?.clone())
                    }
                    x => bail!("Don't know how to index / look up key: {:?}", x)
                }
            }
            Expr::RowRef(slot) => Ok(row.slots[*slot].clone()), // TODO not this
            Expr::StackRef(slot) => Ok(ctx.stack[*slot].clone()),
            Expr::Lit(v) => Ok(GramVal::Lit(v.clone())), // TODO not this,
            Expr::List(vs) => {
                let mut out = Vec::new();
                for ve in vs {
                    out.push(ve.eval(ctx, row, v)?);
                }
                Ok(GramVal::List(out))
            }
            Expr::Map(es) => {
                let mut out = Vec::with_capacity(es.len());
                for e in es {
                    out.push((e.0, e.1.eval(ctx, row, v)?));
                }
                Ok(GramVal::Map(out))
            }
            Expr::Path(es) => {
                let num_segments = (es.len() - 1) / 2;
                let mut out = Vec::with_capacity(num_segments);

                if let GramVal::Lit(Val::Null) = &row.slots[es[0]] {
                    return Ok(GramVal::Lit(Val::Null));
                }

                let start = unwrap_node_id(&row.slots[es[0]]).unwrap();
                let mut i = 1;
                while i < es.len() {
                    let r = unwrap_rel_index(&row.slots[es[i]]).unwrap();
                    let o = unwrap_node_id(&row.slots[es[i+1]]).unwrap();
                    out.push((r, o));
                    i += 2;
                }

                Ok(GramVal::Path {
                    start,
                    rest: out
                })
            }
            Expr::Gt(a, b) => {
                let a_val = a.eval(ctx, row, v)?;
                let b_val = b.eval(ctx, row, v)?;
                match a_val.partial_cmp(&b_val) {
                    Some(Ordering::Greater) => Ok(GramVal::Lit(Val::Bool(true))),
                    _ => Ok(GramVal::Lit(Val::Bool(false))),
                }
            }
            Expr::Equal(a, b) => {
                let a_val = a.eval(ctx, row, v)?;
                let b_val = b.eval(ctx, row, v)?;
                let eq = a_val.eq(&b_val);
                Ok(GramVal::Lit(Val::Bool(eq)))
            }
            Expr::Mul(a, b) => {
                let a_val = a.eval(ctx, row, v)?;
                let b_val = b.eval(ctx, row, v)?;
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
                let a_val = a.eval(ctx, row, v)?;
                let b_val = b.eval(ctx, row, v)?;
                match (&a_val, &b_val) {
                    (GramVal::Lit(Val::Int(a_int)), GramVal::Lit(Val::Int(b_int))) => {
                        Ok(GramVal::Lit(Val::Float(*a_int as f64 / *b_int as f64)))
                    }
                    (GramVal::Lit(Val::Int(a_int)), GramVal::Lit(Val::Float(b_float))) => {
                        Ok(GramVal::Lit(Val::Float(*a_int as f64 / *b_float)))
                    }
                    (GramVal::Lit(Val::Float(a_float)), GramVal::Lit(Val::Int(b_int))) => {
                        Ok(GramVal::Lit(Val::Float(*a_float / *b_int as f64)))
                    }
                    (GramVal::Lit(Val::Float(a_float)), GramVal::Lit(Val::Float(b_float))) => {
                        Ok(GramVal::Lit(Val::Float(*a_float / *b_float)))
                    }
                    _ => bail!(
                        "gram backend does not support division of {:?} and {:?}",
                        a_val,
                        b_val
                    ),
                }
            }
            Expr::Add(a, b) => {
                let a_val = a.eval(ctx, row, v)?;
                let b_val = b.eval(ctx, row, v)?;
                match (&a_val, &b_val) {
                    (GramVal::Lit(Val::Int(a_int)), GramVal::Lit(Val::Int(b_int))) => {
                        Ok(GramVal::Lit(Val::Int(a_int + b_int)))
                    }
                    (GramVal::Lit(Val::String(a_str)), GramVal::Lit(Val::String(b_str))) => {
                        Ok(GramVal::Lit(Val::String(a_str.to_owned() + b_str)))
                    }
                    (GramVal::List(a_items), GramVal::List(b_items)) => {
                        let mut out = Vec::with_capacity(a_items.len() + b_items.len());
                        for v in a_items {
                            out.push(v.to_owned())
                        }
                        for v in b_items {
                            out.push(v.to_owned())
                        }
                        Ok(GramVal::List(out))
                    }
                    (GramVal::Lit(Val::List(a_items)), GramVal::Lit(Val::List(b_items))) => {
                        let mut out = Vec::with_capacity(a_items.len() + b_items.len());
                        for v in a_items {
                            out.push(GramVal::Lit(v.to_owned()))
                        }
                        for v in b_items {
                            out.push(GramVal::Lit(v.to_owned()))
                        }
                        Ok(GramVal::List(out))
                    }
                    (GramVal::Lit(Val::List(a_items)), GramVal::List(b_items)) => {
                        let mut out = Vec::with_capacity(a_items.len() + b_items.len());
                        for v in a_items {
                            out.push(GramVal::Lit(v.to_owned()))
                        }
                        for v in b_items {
                            out.push(v.to_owned())
                        }
                        Ok(GramVal::List(out))
                    }
                    (GramVal::List(a_items), GramVal::Lit(Val::List(b_items))) => {
                        let mut out = Vec::with_capacity(a_items.len() + b_items.len());
                        for v in a_items {
                            out.push(v.to_owned())
                        }
                        for v in b_items {
                            out.push(GramVal::Lit(v.to_owned()))
                        }
                        Ok(GramVal::List(out))
                    }
                    _ => bail!(
                        "gram backend does not support addition of {:?} and {:?}",
                        a_val,
                        b_val
                    ),
                }
            }
            Expr::Sub(a, b) => {
                let a_val = a.eval(ctx, row, v)?;
                let b_val = b.eval(ctx, row, v)?;
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
                    match t.eval(ctx, row, v)? {
                        GramVal::Lit(Val::Bool(b)) => if !b {
                            return Ok(GramVal::Lit(Val::Bool(false)))
                        },
                        _ => panic!("The gram backend does not know how to do binary logic on non-boolean expressions")
                    }
                }
                Ok(GramVal::Lit(Val::Bool(true)))
            }
            Expr::Not(e) => match e.eval(ctx, row, v)? {
                GramVal::Lit(Val::Bool(v)) => Ok(GramVal::Lit(Val::Bool(!v))),
                _ => panic!("the gram backend cannot do NOT of {:?}", e),
            },
            Expr::Call(f, args) => {
                let mut argv = Vec::with_capacity(args.len());
                for a in args {
                    argv.push(a.eval(ctx, row, v)?);
                }
                f.apply(ctx, &argv)
            }
            Expr::HasLabel { slot, label } => {
                let s: &GramVal = &row.slots[*slot];
                let node_id = s.as_node_id();
                let g = ctx.g.borrow();
                let node = g.get_node(node_id, ctx.xid).unwrap();
                Ok(GramVal::Lit(Val::Bool(node.labels.contains(label))))
            }
            Expr::ListComprehension {
                src,
                stackslot,
                map_expr,
            } => {
                let src_data = src.eval(ctx, row, v)?;
                let mut result = Vec::new();
                match src_data {
                    GramVal::Lit(Val::List(vals)) => {
                        for src_val in vals {
                            ctx.stack[*stackslot] = GramVal::Lit(src_val);
                            result.push(map_expr.eval(ctx, row, v)?)
                        }
                    }
                    GramVal::List(vals) => {
                        for src_val in vals {
                            ctx.stack[*stackslot] = src_val;
                            result.push(map_expr.eval(ctx, row, v)?)
                        }
                    }

                    _ => panic!("The gram backend does not know how to do list comprehension with this as source: {:?}", src_data)
                }
                Ok(GramVal::List(result))
            }
            Expr::IsNull(e) => {
                if let GramVal::Lit(Val::Null) = e.eval(ctx, row, v)? {
                    Ok(GramVal::Lit(Val::Bool(true)))
                } else {
                    Ok(GramVal::Lit(Val::Bool(false)))
                }
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
    // Don't know about this.. lots of considerations. But TL;DR: Right now this is something like
    // `start` is the first node id, and may be all there is. There is then 0 or more (rel_index, other_node) pairs.
    Path{ start: usize, rest: Vec<(usize, usize)> }
}

impl GramVal {
    pub fn project(&self, ctx: &mut Context, v: Version) -> Val {
        fn project_node(ctx: &mut Context, v: Version, id: usize) -> crate::Node {
            let g = ctx.g.borrow();
            let n = g.get_node(id, v).unwrap();
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
            crate::Node {
                id,
                labels,
                props,
            }
        }

        fn project_rel(ctx: &mut Context, v: Version, node_id: usize, rel_index: usize) -> crate::Rel {
            let g = ctx.g.borrow();
            let n = g.get_node(node_id, v).unwrap();
            let rel = &n.rels[rel_index];

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
                    start = node_id;
                    end = rel.other_node;
                }
                Dir::In => {
                    end = node_id;
                    start = rel.other_node;
                }
            }
            crate::Rel {
                start,
                end,
                rel_type,
                props,
            }
        }
        match self {
            GramVal::Lit(v) => v.clone(),
            GramVal::List(vs) => {
                let mut out = Vec::new();
                out.resize(vs.len(), Val::Null);
                for i in 0..vs.len() {
                    out[i] = vs[i].project(ctx, v);
                }
                Val::List(out)
            }
            GramVal::Map(es) => {
                let mut out = Vec::with_capacity(es.len());
                for entry in es {
                    let key = ctx.tokens.borrow().lookup(entry.0).unwrap().to_string();
                    let val = entry.1.project(ctx, v);
                    out.push((key, val))
                }
                Val::Map(out)
            }
            GramVal::Node { id } => {
                Val::Node(project_node(ctx, v, *id))
            }
            GramVal::Rel { node_id, rel_index } => {
                Val::Rel(project_rel(ctx, v, *node_id, *rel_index))
            }
            GramVal::Path { start, rest } => {
                let mut segments = Vec::new();
                let mut prior_node = *start;
                for i in 0..rest.len() {
                    let seg = &rest[i];
                    let rel = project_rel(ctx, v, prior_node, seg.0);
                    let node = project_node(ctx, v, seg.1);
                    segments.push((rel, node));
                    prior_node = seg.1;
                }
                Val::Path(crate::Path{
                    start: project_node(ctx, v, *start),
                    segments,
                })
            }
        }
    }

    fn get_index(&self, index: usize) -> Result<&GramVal> {
        match self {
            GramVal::List(items) => {
                Ok(&items[index])
            }
            x => bail!("Don't know how to index into a {:?}", x)
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
            GramVal::Lit(Val::Null) => None,
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
            GramVal::Path { .. } => f.write_str(&format!("Path(<serialization not implemented in gram backend yet>)"))
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

    pub phase: u8,

    pub src_slot: usize,

    pub dst_slot: usize,

    pub rel_slot: Option<usize>,

    pub rel_type: Option<Token>,

    pub dir: Option<Dir>,

    pub min_depth: usize,

    pub max_depth: usize,

    // Each entry is a (node_id, rel_index); we push onto the stack as we expand; this is
    // a core dynamically sized data structure; it can equal the longest path in the graph
    // meaning this is something that needs to go onto a swappable datastructure if we want
    // to be using a fixed memory set.
    pub stack: Vec<(usize, usize)>,

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
                    self.stack.push((out.slots[self.src_slot].as_node_id(), 0));
                    self.state = ExpandState::InNode;
                }
                ExpandState::InNode => {
                    let v = store::Version::new(ctx.xid.xid, self.phase);
                    let frame = self.stack.last().unwrap();
                    let node = frame.0;
                    let current_rel_index = frame.1;
                    let g = ctx.g.borrow();
                    let rels = &g.get_node(node, v).unwrap().rels;

                    println!("Fetched rels @{:?}: {:?}", v, rels);

                    if current_rel_index >= rels.len() {
                        // No more rels on this node, pop stack
                        self.stack.pop();

                        // Done expanding from this source node, get the next source row
                        if self.stack.len() == 0 {
                            self.state = ExpandState::NextNode;
                        }

                        continue;
                    }

                    let rel = &rels[current_rel_index];
                    let last_stack = self.stack.len() - 1;
                    self.stack[last_stack] = (node, current_rel_index + 1);

                    // TODO This whole thing should be a mask
                    if rel.deleted {
                        continue;
                    }

                    if self.rel_type.is_some() && rel.rel_type != self.rel_type.unwrap() {
                        continue;
                    }

                    if self.dir.is_some() && rel.dir != self.dir.unwrap()
                    {
                        continue;
                    }

                    // Found a matching rel!

                    // Calc this before we potentially push to the stack below
                    let past_min_depth = self.min_depth <= self.stack.len();

                    // Before following a rel we need a uniqueness check, so we don't end up
                    // chasing a circle infinitely. Cypher uses relationship isomorphism for this;
                    // however, at this time that's a bit of a PITA to wedge in, because we don't have
                    // unique identities for relationships.. so, lets just use node isomorphism,
                    // and see how long it takes until the TCK picks up on that..
                    // TODO all the above stuff..
                    let mut already_traversed = false;
                    for (known_node, _) in &self.stack {
                        if *known_node == rel.other_node {
                            already_traversed = true;
                            break;
                        }
                    }

                    // If we haven't reached max_rel, follow this rel
                    if self.max_depth > self.stack.len() && ! already_traversed{
                        // Avoid infinite depth..
                        if self.stack.len() >= 1024 {
                            panic!("Gram backend does not yet support paths longer than 1024 :(")
                        }

                        self.stack.push((rel.other_node, 0))
                    }

                    if past_min_depth && !already_traversed {
                        if let Some(rslot) = self.rel_slot {
                            out.slots[rslot] = GramVal::Rel {
                                node_id: node,
                                rel_index: current_rel_index,
                            };
                        }
                        out.slots[self.dst_slot] = GramVal::Node { id: rel.other_node };
                        return Ok(true);
                    }
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
                let g = ctx.g.borrow();
                let node_data = g.get_node(*node_id, ctx.xid).unwrap();
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
    pub phase: u8,
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
        let v = Version::new(ctx.xid.xid, self.phase);
        loop {
            if !self.src.next(ctx, out)? {
                return Ok(false);
            }

            // TODO this is wrong, it only handles cases of one matching rel, does not
            //      take direction into account.

            let left_raw = &out.slots[self.left_node_slot];
            let right_raw = &out.slots[self.right_node_slot];
            match (left_raw, right_raw) {
                (GramVal::Node { id: left }, GramVal::Node { id: right }) => {
                    let g = ctx.g.borrow();
                    let left_node = g.get_node(*left, v).unwrap();
                    for (rel_index, candidate) in left_node.rels.iter().enumerate() {
                        if let Some(rt) = self.rel_type {
                            if candidate.rel_type != rt {
                                continue;
                            }
                        }
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

// For each src row, perform a full node scan with the specified filters
#[derive(Debug)]
struct NodeScan {
    pub src: Box<dyn Operator>,

    pub phase: u8,

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
                    let v = store::Version::new(ctx.xid.xid, self.phase);
                    while g.max_node_id() > node_id {
                        if let Some(vis_node) = g.get_node(node_id, v) {
                            if vis_node.deleted {
                                node_id += 1;
                                continue;
                            }

                            if let Some(tok) = self.labels {
                                if !vis_node.labels.contains(&tok) {
                                    node_id += 1;
                                    continue;
                                }
                            }

                            out.slots[self.slot] = GramVal::Node { id: node_id };
                            self.state = NodeScanState::Scanning {
                                next_node: node_id + 1,
                            };
                            return Ok(true);
                        } else {
                            // This node is not visible to us (eg. it was created by an event that logically happened
                            // after we are running, from the users pov)
                            node_id += 1;
                            continue
                        }
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
    phase: u8,
}

impl Operator for Create {
    fn reset(&mut self) {
        self.src.reset();
    }

    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool, Error> {
        let v = Version::new(ctx.xid.xid, self.phase);
        if !self.src.next(ctx, out)? {
            if self.rels.len() > 0 {
            println!("Create: No next");
            }
            return Ok(false);
        }
        for node in &self.nodes {
            let node_properties = node
                .props
                .iter()
                .map(|p| {
                    match p.1.eval(ctx, out, v) {
                        Ok(GramVal::Lit(val)) => (*p.0, (val)),
                        Ok(gval) => (*p.0, gval.project(ctx, v)),
                        r => panic!("property creation expression failed {:?}", r)
                    }
                })
                // In create, property expressions that evalutate to null are discarded
                .filter(|i| match i.1 { Val::Null => false, _ => true })
                .collect();
            out.slots[node.slot] = append_node(
                ctx,
                Rc::clone(&self.tokens),
                node.labels.clone(),
                node_properties,
                v,
            )?;
        }
        for rel in &self.rels {
            let rel_properties = rel
                .props
                .iter()
                .map(|p| {
                    match p.1.eval(ctx, out, v) {
                        Ok(GramVal::Lit(val)) => (*p.0, (val)),
                        Ok(gval) => (*p.0, gval.project(ctx, v)),
                        r => panic!("property creation expression failed {:?}", r)
                    }
                })
                // In create, property expressions that evalutate to null are discarded
                .filter(|i| match i.1 { Val::Null => false, _ => true })
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
enum UpdateAction {
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
    AppendLabel {
        entity: Slot,
        label: Token,
    },
    DeleteEntity {
        entity: Expr,
    },
    DetachDelete {
        entity: Expr,
    }
}

#[derive(Debug)]
struct UpdateEntity {
    pub src: Box<dyn Operator>,
    pub actions: Vec<UpdateAction>,

    pub phase: u8,
}

impl UpdateEntity {
    // Look. We're gonna rewrite this whole massive file. Just want to get to a walking skeleton.
    fn write_prop_to_thing(
        &self,
        ctx: &mut Context,
        v: Version,
        thing: &GramVal,
        key: usize,
        val: Val,
    ) -> Result<()> {
        match thing {
            GramVal::Rel { node_id, rel_index } => {
                let mut g = ctx.g.borrow_mut();
                let mut props = g.update_rel_props(*node_id, *rel_index, v).unwrap();
                if val == Val::Null {
                    props.remove(&key);
                } else {
                    props.insert(key, val);
                }
            }
            GramVal::Node { id } => {
                let mut g = ctx.g.borrow_mut();
                let props = g.update_node_props(*id, v).unwrap();
                if val == Val::Null {
                    props.remove(&key);
                } else {
                    props.insert(key, val);
                }
            }
            v => bail!("Don't know how to set properties to {:?}", v),
        }
        Ok(())
    }

    fn write_thing_to_thing(&self, ctx: &mut Context, v: Version, thing: &GramVal, src: GramVal) -> Result<()> {
        match src {
            GramVal::Map(entries) => {
                for (k, val) in entries {
                    if let GramVal::Lit(litval) = val {
                        self.write_prop_to_thing(ctx, v, thing, k, litval)?;
                    } else {
                        bail!(
                            "Expected a literal value here, probably programming error? Got: {:?}",
                            v
                        )
                    }
                }
            }
            GramVal::Node { id } => {
                let clonedprops = {
                    let g = ctx.g.borrow();
                    let node = g.get_node(id, ctx.xid).unwrap();
                    node.properties.clone()
                };
                for (k, val) in clonedprops.iter() {
                    self.write_prop_to_thing(ctx, v, thing, *k, val.clone())?;
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
                let mut g = ctx.g.borrow_mut();
                let mut props = g.update_rel_props(*node_id, *rel_index, ctx.xid).unwrap();
                let _num_props = props.len();
                props.clear();
            }
            GramVal::Node { id } => {
                let mut g = ctx.g.borrow_mut();
                let props = g.update_node_props(*id, ctx.xid).unwrap();
                props.clear();
            }
            v => bail!("Don't know how to clear properties on {:?}", v),
        }
        Ok(())
    }
}

impl Operator for UpdateEntity {
    fn reset(&mut self) {
        self.src.reset();
    }

    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool, Error> {
        if !self.src.next(ctx, out)? {
            return Ok(false);
        }

        let v = Version::new(ctx.xid.xid, self.phase);

        for action in &self.actions {
            match action {
                UpdateAction::SingleAssign { entity, key, value } => {
                    let entity_val = &out.slots[*entity];
                    let gramval = value.eval(ctx, out, v)?;
                    if let GramVal::Lit(litval) = gramval {
                        self.write_prop_to_thing(ctx, v, entity_val, *key, litval)?;
                    } else {
                        let litval = gramval.project(ctx, v);
                        self.write_prop_to_thing(ctx, v, entity_val, *key, litval)?;
                    }
                }
                UpdateAction::Append { entity, value } => {
                    let entity_val = &out.slots[*entity];
                    let new_props = value.eval(ctx, out, v)?;
                    self.write_thing_to_thing(ctx, v, entity_val, new_props)?;
                }
                UpdateAction::Overwrite { entity, value } => {
                    let entity_val = &out.slots[*entity];
                    let new_props = value.eval(ctx, out, v)?;
                    self.clear_props_on_thing(ctx, entity_val)?;
                    self.write_thing_to_thing(ctx, v, entity_val, new_props)?;
                }
                UpdateAction::AppendLabel { entity, label } => {
                    let entity_val = &out.slots[*entity];
                    match entity_val {
                        GramVal::Node { id } => {
                            ctx.g.borrow_mut().append_label(*id, *label, v);
                        }
                        _ => bail!("Can't add label to {:?}", entity_val)
                    }
                }
                UpdateAction::DeleteEntity { entity: node } => {
                    match node.eval(ctx, out, v)? {
                        GramVal::Node{ id } => {
                            ctx.g.borrow_mut().delete_node(id, v)
                        }
                        GramVal::Rel { node_id, rel_index } => {
                            ctx.g.borrow_mut().delete_rel(node_id, rel_index, v);
                        }
                        GramVal::Lit(Val::Null) => (),
                        GramVal::Path { start, rest } => {
                            let mut g = ctx.g.borrow_mut();
                            let mut current_node = start;
                            for (rel_index, next_node) in rest {
                                g.delete_rel(current_node, rel_index, v);
                                g.delete_node(current_node, v);
                                current_node = next_node;
                            }
                        }
                        x => bail!("Expression to DELETE must be a node or rel, got {:?}", x)
                    }
                }
                UpdateAction::DetachDelete { entity: node } => {
                    match node.eval(ctx, out, v)? {
                        GramVal::Node{ id } => {
                            let mut g = ctx.g.borrow_mut();
                            g.detach_delete_node(id, v)
                        }
                        GramVal::Rel { node_id, rel_index } => {
                            ctx.g.borrow_mut().delete_rel(node_id, rel_index, v);
                        }
                        GramVal::Path { start, rest } => {
                            let mut g = ctx.g.borrow_mut();
                            g.detach_delete_node(start, v);
                            for (_, next_node) in rest {
                                g.detach_delete_node(next_node, v);
                            }
                        }
                        GramVal::Lit(Val::Null) => (),
                        x => bail!("Expression to DETACH DELETE must be a node or rel, got {:?}", x)
                    }
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
    pub phase: u8,
    pub projections: Vec<Projection>,
}

impl Operator for Project {
    fn reset(&mut self) {
        self.src.reset();
    }

    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool> {
        let v = Version::new(ctx.xid.xid, self.phase);
        if self.src.next(ctx, out)? {
            for proj in &self.projections {
                out.slots[proj.slot] = proj.expr.eval(ctx, out, v)?;
            }
            return Ok(true);
        }
        Ok(false)
    }
}

#[derive(Debug)]
struct Limit {
    src: Box<dyn Operator>,
    phase: u8,
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
        let v = Version::new(ctx.xid.xid, self.phase);
        if !self.initialized {
            self.initialized = true;
            if let Some(skip_expr) = &self.skip {
                let skip_val = skip_expr.eval(ctx, out, v)?;
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
                let limit_val = limit_expr.eval(ctx, out, v)?;
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
        if !self.initialized {
            self.initialized = true;
            if self.src.next(ctx, out)? {
                return Ok(true);
            }
            for s in &self.slots {
                out.slots[*s] = GramVal::Lit(Val::Null);
            }
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
    phase: u8,
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

        let v = Version::new(ctx.xid.xid, self.phase);

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

            if self.predicate.eval(ctx, out, v)?.as_bool()? {
                return Ok(true);
            }
        }
    }
}

#[derive(Debug)]
struct Sort {
    src: Box<dyn Operator>,
    phase: u8,
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
        let v = Version::new(ctx.xid.xid, self.phase);
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
                    let a_val = e.eval(ctx, a, v).unwrap();
                    let b_val = e.eval(ctx, b, v).unwrap();
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
    pub phase: u8,
    pub predicate: Expr,
}

impl Operator for Selection {
    fn reset(&mut self) {
        self.src.reset();
    }

    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool> {
        let v = Version::new(ctx.xid.xid, self.phase);
        while self.src.next(ctx, out)? {
            println!("Eval pred: {:?} for {:?}", self.predicate, v);
            let ok = self.predicate.eval(ctx, out, v)?;
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
                    Val::Bool(v) => v.hash(state),
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
    phase: u8,

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
        let v = Version::new(ctx.xid.xid, self.phase);
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
                    key.vals.push(group.expr.eval(ctx, row, v)?)
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
                        group_state.push(agge.func.init(ctx, v))
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
    phase: u8,
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
        let v = Version::new(ctx.xid.xid, self.phase);
        loop {
            if self.current_list.is_none() {
                let src = &mut *self.src;
                if !src.next(ctx, row)? {
                    return Ok(false);
                }

                match self.list_expr.eval(ctx, row, v)? {
                    GramVal::List(items) => self.current_list = Some(items),
                    GramVal::Lit(Val::List(items)) => {
                        self.current_list =
                            Some(items.iter().map(|v| GramVal::Lit(v.to_owned())).collect())
                    }
                    GramVal::Lit(Val::Null) => self.current_list = Some(Vec::new()),
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
            let next = self.lhs.next(ctx, out)?;
            if !next {
                return Ok(false);
            }
            self.rhs.reset()
        }

        loop {
            if self.rhs.next(ctx, out)? {
                return Ok(true);
            }

            // Exhausted rhs, fetch next lhs

            let next = self.lhs.next(ctx, out)?;
            if !next {
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

            if !anticondition_passed {
                // Just return what we got from lhs
                return Ok(true)
            }

            // TODO this is super wrong; we should *keep* yielding from rhs until exhausted

            self.rhs.reset();
            if self.rhs.next(ctx, out)? {
                return Ok(true);
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


#[derive(Debug)]
struct Barrier {
    pub src: Box<dyn Operator>,

    // on first invocation, src is spooled into this buffer to "shake out" its side effects
    // then we return these one at a time
    pub buf: Option<Vec<GramRow>>,
    pub ptr: usize,
}

impl Operator for Barrier {
    fn reset(&mut self) {
        self.src.reset();
        self.buf = None;
        self.ptr = 0;
    }

    fn next(&mut self, ctx: &mut Context, out: &mut GramRow) -> Result<bool> {
        if let None = self.buf {
            let mut buf = Vec::new();
            while self.src.next(ctx, out)? {
                buf.push(out.clone());
            }
            self.buf = Some(buf);
        }

        let buf = self.buf.as_ref().unwrap();

        if self.ptr < buf.len() {
            let row = &buf[self.ptr];
            for (i, val) in row.slots.iter().enumerate() {
                out.slots[i] = val.clone();
            }
            self.ptr += 1;
            return Ok(true);
        }

        Ok(false)
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
    version: store::Version,
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

    let id = ctx.g.borrow().max_node_id();
    let out_node = Node {
        id,
        gid: tokens.tokenize(&gram_identifier),
        labels,
        properties: node_properties,
        rels: vec![],
        deleted: false,
        version,
        prior: None,
    };

    ctx.g.borrow_mut().add_node(id, out_node);

    Ok(GramVal::Node { id })
}

fn append_rel(
    ctx: &mut Context,
    start_node: usize,
    end_node: usize,
    rel_type: Token,
    props: HashMap<Token, Val>,
) -> Result<GramVal, Error> {
    // let p = serialize_props(ctx, &props);
    // let tokens = ctx.tokens.borrow();

    // let startgid = tokens.lookup(g.get_node(start_node, ctx.xid).unwrap().gid).unwrap();
    // let endgid = tokens.lookup(g.get_node(end_node, ctx.xid).unwrap().gid).unwrap();
    // let reltype_str = tokens.lookup(rel_type).unwrap();

    // let gram_string = format!(
    //     "(`{}`)-[:`{}` {}]->(`{}`)\n",
    //     startgid, reltype_str, p, endgid,
    // );

    // println!("--- About to write ---");
    // println!("{}", gram_string);
    // println!("------");

    let mut g = ctx.g.borrow_mut();
    let rel_index = g.add_rel(start_node, end_node, rel_type, props);

    // ctx.file
    //     .borrow_mut()
    //     .seek(SeekFrom::End(0))
    //     .expect("seek error");

    // match ctx.file.borrow_mut().write_all(gram_string.as_bytes()) {
    //     Ok(_) => Ok(GramVal::Rel {
    //         node_id: start_node,
    //         rel_index,
    //     }),
    //     Err(e) => Err(Error::new(e)),
    // }

    Ok(GramVal::Rel {
        node_id: start_node,
        rel_index,
    })
}

fn serialize_props(ctx: &mut Context, props: &HashMap<Token, Val>) -> String {
    let mut out = String::new();
    let mut first = true;
    out.push('{');
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
    out.push('}');
    out
}

fn serialize_val(_ctx: &mut Context, v: &Val) -> String {
    match v {
        Val::String(s) => format!("\'{}\'", s),
        Val::Int(v) => format!("{}", v),
        Val::Bool(v) => format!("{}", v),
        Val::List(v) => {
            let out: Vec<String> = v.iter().map(|it| serialize_val(_ctx, it)).collect();
            format!("[{}]", out.join(", "))
        },
        Val::Null => "null".to_owned(),
        _ => panic!("Don't know how to serialize {:?}", v),
    }
}

mod functions {
    use super::{Context, Expr, GramRow, GramVal, Val};
    use crate::backend::{FuncSignature, FuncType, Tokens, Token};
    use crate::{Result, Type};
    use std::cmp::Ordering;
    use std::fmt::Debug;
    use crate::backend::gram::store::Version;

    pub(super) fn aggregating(tokens: &mut Tokens) -> Vec<Box<dyn AggregatingFuncSpec>> {
        let mut out: Vec<Box<dyn AggregatingFuncSpec>> = Default::default();
        out.push(Box::new(MinSpec::new(tokens)));
        out.push(Box::new(MaxSpec::new(tokens)));
        out.push(Box::new(CountSpec::new(tokens)));
        out.push(Box::new(CollectSpec::new(tokens)));
        out
    }

    #[derive(Debug, Clone)]
    pub(super) enum Func {
        Not,
        Abs,
        Keys,
        Range,
    }

    impl Func {
        pub fn apply(&self, ctx: &mut Context, args: &[GramVal]) -> Result<GramVal> {
            match self {
                Func::Range => {
                    let min = args
                        .get(0)
                        .ok_or_else(|| anyhow!("range takes two arguments, got none"))?;
                    let max = args
                        .get(1)
                        .ok_or_else(|| anyhow!("range takes two arguments, got one"))?;
                    match (min, max) {
                        (GramVal::Lit(Val::Int(min_int)), GramVal::Lit(Val::Int(max_int))) => {
                            let mut out = Vec::with_capacity((max_int - min_int) as usize);
                            for i in *min_int..*max_int + 1 {
                                out.push(GramVal::Lit(Val::Int(i)))
                            }
                            Ok(GramVal::List(out))
                        }
                        _ => bail!("range takes two ints, got {:?}, {:?}", min, max),
                    }
                }
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
                    GramVal::Map(entries) => {
                        let o: Vec<GramVal> = entries
                            .iter()
                            .map(|(k, _)| {
                                GramVal::Lit(Val::String(
                                    ctx.tokens.borrow().lookup(*k).unwrap().to_owned(),
                                ))
                            })
                            .collect();
                        Ok(GramVal::List(o))
                    }
                    GramVal::Rel { node_id, rel_index } => {
                        let g = ctx.g.borrow();
                        let node = g.get_node(*node_id, ctx.xid).unwrap();
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
                        let g = ctx.g.borrow();
                        let node = g.get_node(*id, ctx.xid).unwrap();
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
        fn init(&self, ctx: &mut Context, v: Version) -> Box<dyn Aggregation>;
    }

    pub(super) trait Aggregation: Debug {
        fn apply(&mut self, ctx: &mut Context, row: &mut GramRow) -> Result<()>;
        fn complete(&mut self) -> Result<&GramVal>;
    }

    // This describes a map expression that, within it, contains an aggregation.
    // This is just the plumbing and delegation to those nested aggregations.
    #[derive(Debug)]
    pub(super) struct MapAggregatingFunc {
        pub(super) aggregating: Vec<(Token, Box<dyn AggregatingFunc>)>,
    }

    impl AggregatingFunc for MapAggregatingFunc {
        fn init(&self, ctx: &mut Context, v: Version) -> Box<dyn Aggregation> {
            // Initialize nested aggregators
            let aggregations = self.aggregating.iter().map(|(k, agg_expr)| {
                (*k, agg_expr.init(ctx, v))
            }).collect();
            Box::new(MapAggregation { aggregations, output: None, version: v })
        }
    }

    #[derive(Debug)]
    pub(super) struct MapAggregation {
        aggregations: Vec<(Token, Box<dyn Aggregation>)>,
        output: Option<GramVal>,
        version: Version,
    }

    impl Aggregation for MapAggregation {
        fn apply(&mut self, ctx: &mut Context, row: &mut GramRow) -> Result<()> {
            for (_, aggregation) in self.aggregations.iter_mut() {
                aggregation.apply(ctx, row)?;
            }
            Ok(())
        }

        fn complete(&mut self) -> Result<&GramVal> {
            // TODO this is garbage, and points to an interesting thing here where
            //      we can't wrap the borrow we're getting from the nested aggregagations
            //      also note the horror where we're storing this whole thing on the
            //      struct just to be able to return a borrow
            let mut out = Vec::with_capacity(self.aggregations.len());
            for (k, aggregation) in self.aggregations.iter_mut() {
                let v = aggregation.complete()?;
                out.push((*k, v.clone()));
            }
            println!("{:?}", out);
            self.output = Some(GramVal::Map(out));

            Ok(self.output.as_ref().unwrap())
        }
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
        fn init(&self, _ctx: &mut Context, v: Version) -> Box<dyn Aggregation> {
            Box::new(MinAggregation {
                arg: self.arg.clone(),
                min: None,
                version: v,
            })
        }
    }

    #[derive(Debug)]
    struct MinAggregation {
        arg: Expr,
        min: Option<GramVal>,
        version: Version,
    }

    impl Aggregation for MinAggregation {
        fn apply(&mut self, ctx: &mut Context, row: &mut GramRow) -> Result<()> {
            let v = self.arg.eval(ctx, row, self.version)?;
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
        fn init(&self, _ctx: &mut Context, v: Version) -> Box<dyn Aggregation> {
            Box::new(MaxAggregation {
                arg: self.arg.clone(),
                max: None,
                version: v,
            })
        }
    }

    #[derive(Debug)]
    struct MaxAggregation {
        arg: Expr,
        max: Option<GramVal>,
        version: Version,
    }

    impl Aggregation for MaxAggregation {
        fn apply(&mut self, ctx: &mut Context, row: &mut GramRow) -> Result<()> {
            let v = self.arg.eval(ctx, row, self.version)?;
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
        fn init(&self, _ctx: &mut Context, v: Version) -> Box<dyn Aggregation> {
            Box::new(CountAggregation {
                counter: 0,
                out: GramVal::Lit(Val::Int(0)),
                version: v,
            })
        }
    }

    #[derive(Debug)]
    struct CountAggregation {
        counter: i64,
        out: GramVal,
        version: Version,
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

    #[derive(Debug)]
    struct CollectSpec {
        sig: FuncSignature,
    }

    impl CollectSpec {
        pub fn new(tokens: &mut Tokens) -> CollectSpec {
            let tok_tollect = tokens.tokenize("collect");
            CollectSpec {
                sig: FuncSignature {
                    func_type: FuncType::Aggregating,
                    name: tok_tollect,
                    returns: Type::List(Box::new(Type::Any)),
                    args: vec![(tokens.tokenize("v"), Type::Any)],
                },
            }
        }
    }

    impl AggregatingFuncSpec for CollectSpec {
        fn signature(&self) -> &FuncSignature {
            &self.sig
        }

        fn init(&self, mut args: Vec<Expr>) -> Box<dyn AggregatingFunc> {
            Box::new(Collect {
                arg: args.pop().expect("collect takes 1 arg"),
            })
        }
    }

    #[derive(Debug)]
    struct Collect {
        arg: Expr,
    }

    impl AggregatingFunc for Collect {
        fn init(&self, _ctx: &mut Context, v: Version) -> Box<dyn Aggregation> {
            Box::new(CollectAggregation {
                arg: self.arg.clone(),
                collection: GramVal::List(Vec::new()),
                version: v,
            })
        }
    }

    #[derive(Debug)]
    struct CollectAggregation {
        arg: Expr,
        collection: GramVal,
        version: Version,
    }

    impl Aggregation for CollectAggregation {
        fn apply(&mut self, ctx: &mut Context, row: &mut GramRow) -> Result<()> {
            let v = self.arg.eval(ctx, row, self.version)?;
            match &mut self.collection {
                GramVal::List(entries) => entries.push(v),
                _ => bail!(
                    "collect function state corrupted, expected list val got {:?}",
                    self.collection
                ),
            }
            Ok(())
        }

        fn complete(&mut self) -> Result<&GramVal> {
            Ok(&self.collection)
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use tempfile::tempfile;

    #[test]
    fn test_misc() {
        // This whole module is intentionally untested; it is meant to be thrown out once the
        // feature tests pass; it's just here to walk through what needs doing.
        // This particular test is here to make debugging easier, fill it with what you will.

        let mut g = GramBackend::open(tempfile().unwrap()).unwrap();
        let f = frontend::Frontend {
            tokens: g.tokens(),
            backend_desc: g.describe().unwrap(),
        };
        let mut cursor = g.new_cursor();

        g.eval(
            f.plan("CREATE ({name: 'A'})").unwrap(),
            &mut cursor,
            None,
        ).unwrap();
        while cursor.next().unwrap().is_some() {
            // ..
        }

        g.eval(
            f.plan(
                "MATCH (n)
      MATCH (m)
      WITH n AS a, m AS b
      CREATE (a)-[:T]->(b)
      WITH a AS x, b AS y
      CREATE (x)-[:T]->(y)
      RETURN x, y",
            )
            .unwrap(),
            &mut cursor,
            None,
        )
        .unwrap();
        while cursor.next().unwrap().is_some() {
            println!("{:?}", cursor.projection)
        }

        g.eval(f.plan("MATCH (n) RETURN n").unwrap(), &mut cursor, None)
            .unwrap();
        while cursor.next().unwrap().is_some() {
            println!("{:?}", cursor.projection)
        }
    }
}

fn unwrap_node_id(v: &GramVal) -> Result<usize> {
    match v {
        GramVal::Node { id, .. } => Ok(*id),
        GramVal::Lit(Val::Node(n)) => Ok(n.id),
        _ => bail!("expected a node, got {:?}", v)
    }
}

fn unwrap_rel_index(v: &GramVal) -> Result<usize> {
    match v {
        GramVal::Rel { rel_index, .. } => Ok(*rel_index),
        _ => bail!("expected a GramVal::Rel, got {:?}", v)
    }
}

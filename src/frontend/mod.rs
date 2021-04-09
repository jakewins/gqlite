//
// The gqlite frontend contains the gql parser and logical planner.
// It produces a LogicalPlan, describing what needs to occur to fulfill the input query.
//

use pest::Parser;

use crate::backend::{BackendDesc, Token, Tokens};
use crate::Slot;
use anyhow::Result;
use pest::iterators::Pair;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::rc::Rc;

mod expr;
mod patterns;

mod call_stmt;
mod create_stmt;
mod delete_stmt;
mod match_stmt;
mod merge_stmt;
mod set_stmt;
mod with_stmt;

use core::mem;
use expr::plan_expr;
pub use expr::{Expr, MapEntryExpr, Op};

#[derive(Parser)]
#[grammar = "cypher.pest"]
pub struct CypherParser;

#[derive(Debug)]
pub struct Frontend {
    pub tokens: Rc<RefCell<Tokens>>,
    pub backend_desc: BackendDesc,
}

impl Frontend {
    pub fn plan(&self, query_str: &str) -> Result<LogicalPlan> {
        self.plan_in_context(
            query_str,
            &mut PlanningContext::new(Rc::clone(&self.tokens), &self.backend_desc),
        )
    }

    pub fn plan_in_context<'i, 'pc>(
        &self,
        query_str: &str,
        pc: &'i mut PlanningContext<'pc>,
    ) -> Result<LogicalPlan> {
        let query = CypherParser::parse(Rule::query, &query_str)?
            .next()
            .unwrap(); // get and unwrap the `query` rule; never fails

        let mut plan = LogicalPlan::Argument;

        for stmt in query.into_inner() {
            match stmt.as_rule() {
                Rule::match_stmt => {
                    plan = match_stmt::plan_match(pc, plan, stmt)?;
                }
                Rule::unwind_stmt => {
                    plan = plan_unwind(pc, plan, stmt)?;
                }
                Rule::create_stmt => {
                    plan = create_stmt::plan_create(pc, plan, stmt)?;
                }
                Rule::delete_stmt => {
                    plan = delete_stmt::plan_delete(pc, plan, stmt)?;
                }
                Rule::set_stmt => plan = set_stmt::plan_set(pc, plan, stmt)?,
                Rule::merge_stmt => {
                    plan = merge_stmt::plan_merge(pc, plan, stmt)?;
                }
                Rule::return_stmt => {
                    plan = with_stmt::plan_return(pc, plan, stmt)?;
                }
                Rule::call_stmt => {
                    plan = call_stmt::plan_call(pc, plan, stmt)?;
                }
                Rule::with_stmt => {
                    plan = with_stmt::plan_with(pc, plan, stmt)?;
                }
                Rule::EOI => (),
                _ => unreachable!("Unknown statement: {:?}", stmt),
            }
        }

        println!(
            "plan: {}",
            &plan.fmt_pretty(&"", &pc.scoping.tokens.borrow())
        );

        Ok(plan)
    }
}

// The ultimate output of the frontend is a logical plan. The logical plan is a tree of operators.
// The tree describes a stream processing pipeline starting at the leaves and ending at the root.
//
// This enumeration is the complete list of supported operators that the planner can emit.
//
// The pipeline has a single logical "row" - a vector of value slots - that's shared
// by all operators; the various things the operators do refer to slots in the row,
// like registers in a CPU.
//
// # Scope
// This deals with intra-query and intra-transaction visibility of modifications; each WITH
// statement introduces a new scope by incrementing the counter, plan nodes that look at or
// create graph data must take into account the scope; specifically they don't "see" actions
// taken by higher-numbered scopes.
//
// Example:
//
//   MATCH () CREATE ()  // Scope 0; can see things that existed before the query started
//   WITH *              // New scope introduced
//   MATCH () CREATE ()  // Scope 1: Can see scope 0 plus everything scope 0 sees
//
// Notably, reads in scope N can't see writes in scope N; this avoids infinite loops from
// seeing your own writes, and creates predictability about which writes you'll see when.
//
#[derive(Debug, PartialEq, Clone)]
pub enum LogicalPlan {
    // Terminates each branch in the plan tree; yields one row, which may have been
    // pre-populated with content. Can be reset to yield one more row, and so on, used
    // by plans like Apply that re-run one branch of the tree multiple times
    Argument,

    // List all visible nodes that match `labels`, and put them one-at-a-time in slot
    NodeScan {
        src: Box<Self>,
        scope: u8,
        slot: usize,
        labels: Option<Token>,
    },

    // Starting at a node, expand once according to the specifications in this plan, storing
    // each rel and node pair found in rel_slot and dst_slot
    Expand {
        src: Box<Self>,
        scope: u8,
        src_slot: usize,
        rel_slot: usize,
        dst_slot: usize,
        rel_type: Option<Token>,
        dir: Option<Dir>,
    },

    // Given a known relationship, produce the nodes it connects
    ExpandRel {
        src: Box<Self>,
        scope: u8,
        src_rel_slot: usize,

        start_node_slot: usize,
        end_node_slot: usize,
    },

    // Given two known nodes, yield one row per relationship they have in common
    // eg. MATCH (a), (b) WITH a, b MATCH (a)-[r]-(b)
    ExpandInto {
        src: Box<Self>,
        scope: u8,
        left_node_slot: usize,
        right_node_slot: usize,
        dst_slot: usize,
        rel_type: Option<Token>,
        dir: Option<Dir>,
    },

    // Produce source rows, unless source row is empty, in which case we produce one row with
    // the specified slots set to NULL
    Optional {
        src: Box<Self>,
        // Slots that we set to null if src is empty
        slots: Vec<Slot>,
    },
    Selection {
        src: Box<Self>,
        predicate: Expr,
    },
    Create {
        src: Box<Self>,
        scope: u8,
        nodes: Vec<NodeSpec>,
        rels: Vec<RelSpec>,
    },
    Update {
        src: Box<Self>,
        scope: u8,
        actions: Vec<UpdateAction>,
    },

    // For each row in lhs, reset the argument in rhs and yield from rhs until exhausted
    Apply {
        lhs: Box<Self>,
        rhs: Box<Self>,
    },

    // TODO I don't like these operators, they drop a ton of relevant bits of information.
    //      It seems it'd be both better and simpler with a less generic option, like
    //      a dedicated `Merge` operator, because otherwise the planner needs to start making
    //      assumptions about locking on the backend; a less generic operator would both be
    //      easier to reason about and carry more semantic information about user intent.
    //
    //      Lets come back to that once we know if they are used for anything outside of MERGE

    // For each entry in lhs, execute rhs iff all specified slots are non-null; otherwise
    // just yield the output of lhs
    ConditionalApply {
        lhs: Box<Self>,
        rhs: Box<Self>,
        // Iff all these slots are non-null after executing lhs, execute rhs
        conditions: Vec<Slot>,
    },
    // For each entry in lhs, execute rhs iff all specified slots ARE null; otherwise
    // just yield the output of lhs
    AntiConditionalApply {
        lhs: Box<Self>,
        rhs: Box<Self>,
        // Iff all these slots are null after executing lhs, execute rhs
        conditions: Vec<Slot>,
    },

    Aggregate {
        src: Box<Self>,
        // These projections together make up a grouping key, so if you have a query like
        //
        //   MATCH (n:Person) RETURN n.occupation, n.age, count(n)
        //
        // You get one count() per unique n.age per unique n.occupation.
        //
        // It is legal for this to be empty; indicating there is a single global group.

        // Grouping key
        grouping: Vec<(Expr, Slot)>,
        // "Please evaluate the aggregating expr and output the final accumulation in Slot"
        // Note that this may be empty, eg in the case of RETURN DISTINCT a.name.
        aggregations: Vec<(Expr, Slot)>,
    },

    // Side-effects, ie. modifications to the graph, done by src must be visible to operators
    // downstream. Note that this is *all* src, not just per-row. Conceptually this is meant to
    // be kind of like a memory barrier or memory fence like you'd use in CPU land.
    Barrier {
        src: Box<Self>,
        // These are the side-effects this barrier is ordering; if downstream operations can
        // ensure they are not affected by these, then the barrier can be ignored
        spec: HashSet<SideEffect>,
    },

    Unwind {
        src: Box<Self>,
        list_expr: Expr,
        alias: Slot,
    },

    Call {
        src: Box<Self>,
        name: Token,
        args: Vec<Expr>,
    },

    // For each outer row, go through the inner and yield each row where the predicate matches.
    // This can be used as a general JOIN mechanism - though in most cases we'll want a more
    // specialized hash join. Still, this lets us do all kinds of joins as a broad fallback
    CartesianProduct {
        outer: Box<Self>,
        inner: Box<Self>,
        predicate: Expr,
    },

    // Take the input and apply the specified projections
    Project {
        src: Box<Self>,
        projections: Vec<Projection>,
    },
    Sort {
        src: Box<Self>,
        sort_by: Vec<Expr>,
    },
    Limit {
        src: Box<Self>,
        skip: Option<Expr>,
        limit: Option<Expr>,
    },
    // For queries that end with RETURN, this describes the output fields
    ProduceResult {
        src: Box<Self>,
        fields: Vec<(Token, Slot)>,
    },
}

impl LogicalPlan {
    fn fmt_pretty(&self, ind: &str, t: &Tokens) -> String {
        match self {
            LogicalPlan::ProduceResult { src, fields } => {
                let next_indent = &format!("{}  ", ind);
                let mut proj = String::new();
                for (i, (tok, _)) in fields.iter().enumerate() {
                    if i > 0 {
                        proj.push_str(", ");
                    }
                    let field_name = t.lookup(*tok).unwrap();
                    proj.push_str(field_name)
                }
                format!(
                    "ProduceResult(\n{}src={},\n{}fields=[{}])",
                    ind,
                    src.fmt_pretty(&format!("{}  ", next_indent), t),
                    ind,
                    proj
                )
            }
            LogicalPlan::Project { src, projections } => {
                let next_indent = &format!("{}  ", ind);
                let mut proj = String::new();
                for (i, p) in projections.iter().enumerate() {
                    if i > 0 {
                        proj.push_str(", ");
                    }
                    proj.push_str(&p.fmt_pretty(next_indent, t))
                }
                format!(
                    "Project(\n{}src={},\n{}projections=[{}])",
                    ind, src.fmt_pretty(&format!("{}  ", next_indent), t),
                    ind, proj,
                )
            }
            LogicalPlan::NodeScan { src, scope, slot, labels } => {
                let next_indent = &format!("{}  ", ind);
                let mut lblstr = String::new();
                for (i, p) in labels.iter().enumerate() {
                    if i > 0 {
                        lblstr.push_str(", ");
                    }
                    lblstr.push_str(t.lookup(*p).unwrap_or("?"))
                }
                format!(
                    "NodeScan(\n{}src={}\n{}scope={}\n{}slot=Slot({})\n{}labels=[{}])",
                    ind,
                    src.fmt_pretty(next_indent, t),
                    ind, scope,
                    ind,
                    slot,
                    ind,
                    &lblstr
                )
            }
            LogicalPlan::Expand {
                src,
                scope,
                src_slot,
                rel_slot,
                dst_slot,
                rel_type,
                dir,
            } => {
                let next_indent = &format!("{}  ", ind);
                format!("Expand(\n{}src={}\n{}src={}\n{}src_slot=Slot({})\n{}rel_slot=Slot({})\n{}dst_slot=Slot({}),\n{}rel_type={},\n{}dir={})",
                        ind, src.fmt_pretty(next_indent, t),
                        ind, scope,
                        ind, src_slot,
                        ind, rel_slot,
                        ind, dst_slot,
                        ind, match rel_type {
                            Some(tok) => t.lookup(*tok).unwrap_or("?"),
                            None => "<any>",
                        },
                        ind, &format!("{:?}", dir))
            }
            LogicalPlan::ExpandInto {
                src,
                scope,
                left_node_slot,
                right_node_slot,
                dst_slot,
                rel_type,
                dir,
            } => {
                let next_indent = &format!("{}  ", ind);
                format!("ExpandInto(\n{}src={}\n{}src={}\n{}left_node_slot=Slot({})\n{}right_node_slot=Slot({})\n{}dst_slot=Slot({})\n{}rel_type={:?}\n{}dir={:?})",
                        ind, src.fmt_pretty(next_indent, t),
                        ind, scope,
                        ind, left_node_slot,
                        ind, right_node_slot,
                        ind, dst_slot,
                        ind, rel_type,
                        ind, dir)
            }
            LogicalPlan::ExpandRel {
                src,
                scope,
                src_rel_slot,
                start_node_slot: start_node,
                end_node_slot: end_node,
            } => {
                let next_indent = &format!("{}  ", ind);
                format!("ExpandRel(\n{}src={}\n{}scope={}\n{}src_rel_slot=Slot({})\n{}start_node=Slot({})\n{}end_node=Slot({}))",
                        ind, src.fmt_pretty(next_indent, t),
                        ind, scope,
                        ind, src_rel_slot,
                        ind, start_node,
                        ind, end_node)
            }
            LogicalPlan::Argument => "Argument()".to_string(),
            LogicalPlan::Create { src, scope, nodes, rels } => {
                let next_indent = &format!("{}  ", ind);
                format!(
                    "Create(\n{}src={},\n{}scope={},\n{}nodes={},\n{}rels={})",
                    ind,
                    src.fmt_pretty(&format!("{}  ", next_indent), t),
                    ind, scope,
                    ind,
                    format!("{:?}", nodes),
                    ind,
                    format!("{:?}", rels)
                )
            }
            LogicalPlan::Selection { src, predicate } => {
                let next_indent = &format!("{}  ", ind);
                format!(
                    "Selection(\n{}src={}\n{}predicate={:?})",
                    ind,
                    src.fmt_pretty(next_indent, t),
                    ind,
                    predicate,
                )
            }
            LogicalPlan::Limit { src, skip, limit } => {
                let next_indent = &format!("{}  ", ind);
                format!(
                    "Limit(\n{}src={}\n{}skip={:?},\n{}limit={:?})",
                    ind,
                    src.fmt_pretty(next_indent, t),
                    ind,
                    skip,
                    ind,
                    limit,
                )
            }
            LogicalPlan::Sort { src, sort_by } => {
                let next_indent = &format!("{}  ", ind);
                format!(
                    "Sort(\n{}src={}\n{}by={:?})",
                    ind,
                    src.fmt_pretty(next_indent, t),
                    ind,
                    sort_by,
                )
            }
            LogicalPlan::Aggregate {
                src,
                grouping,
                aggregations,
            } => {
                let next_indent = &format!("{}  ", ind);
                format!(
                    "Aggregate(\n{}src={}\n{}grouping=[{:?}]\n{}aggregations=[{:?}])",
                    ind,
                    src.fmt_pretty(next_indent, t),
                    ind,
                    grouping,
                    ind,
                    aggregations,
                )
            }
            LogicalPlan::Apply { lhs, rhs } => {
                let next_indent = &format!("{}  ", ind);
                format!(
                    "Apply(\n{}lhs={}\n{}rhs={})",
                    ind,
                    lhs.fmt_pretty(next_indent, t),
                    ind,
                    rhs.fmt_pretty(next_indent, t),
                )
            }
            LogicalPlan::ConditionalApply {
                lhs,
                rhs,
                conditions,
            } => {
                let next_indent = &format!("{}  ", ind);
                format!(
                    "ConditionalApply(\n{}lhs={}\n{}rhs={}\n{}conditions=[{:?}])",
                    ind,
                    lhs.fmt_pretty(next_indent, t),
                    ind,
                    rhs.fmt_pretty(next_indent, t),
                    ind,
                    conditions,
                )
            }
            LogicalPlan::AntiConditionalApply {
                lhs,
                rhs,
                conditions,
            } => {
                let next_indent = &format!("{}  ", ind);
                format!(
                    "AntiConditionalApply(\n{}lhs={}\n{}rhs={}\n{}conditions=[{:?}])",
                    ind,
                    lhs.fmt_pretty(next_indent, t),
                    ind,
                    rhs.fmt_pretty(next_indent, t),
                    ind,
                    conditions,
                )
            }
            LogicalPlan::Optional { src, slots } => {
                let next_indent = &format!("{}  ", ind);
                format!(
                    "Optional(\n{}src={}\n{}slots=[{:?}])",
                    ind,
                    src.fmt_pretty(next_indent, t),
                    ind,
                    slots,
                )
            }
            LogicalPlan::Update { src, scope, actions } => {
                let next_indent = &format!("{}  ", ind);
                format!(
                    "SetProperties(\n{}src={}\n{}scope={}\n{}actions=[{:?}])",
                    ind,
                    src.fmt_pretty(next_indent, t),
                    ind, scope,
                    ind,
                    actions,
                )
            }
            LogicalPlan::CartesianProduct {
                outer,
                inner,
                predicate,
            } => {
                let next_indent = &format!("{}  ", ind);
                format!(
                    "CartesianProduct(\n{}outer={}\n{}inner={}\n{}predicate={:?})",
                    ind,
                    outer.fmt_pretty(next_indent, t),
                    ind,
                    inner.fmt_pretty(next_indent, t),
                    ind,
                    predicate,
                )
            }
            LogicalPlan::Barrier {
                src, spec
            } => {
                let next_indent = &format!("{}  ", ind);
                format!(
                    "Barrier(\n{}src={}\n{}predicate={:?})",
                    ind,
                    src.fmt_pretty(next_indent, t),
                    ind,
                    spec,
                )
            }
            _ => format!("NoPretty({:?})", self),
        }
    }
}

// Update actions the Update plan can perform
#[derive(Debug, PartialEq, Clone)]
pub enum UpdateAction {
    // DELETE n
    DeleteEntity {
        entity: Expr,
    },
    // DETACH DELETE n
    DetachDelete {
        node: Expr,
    },
    // SET a.blah = 1
    PropAssign {
        entity: Slot,
        key: Token,
        value: Expr,
    },
    // SET a += b or SET a += { 'a': "Map" }
    PropAppend {
        entity: Slot,
        value: Expr,
    },
    // SET a = b or SET a = { 'a': "Map" }
    PropOverwrite {
        entity: Slot,
        value: Expr,
    },
    // SET a:User
    LabelSet {
        entity: Slot,
        label: Token,
    },
}

// Specification of a node to create
#[derive(Debug, PartialEq, Clone)]
pub struct NodeSpec {
    pub slot: usize,
    pub labels: Vec<Token>,
    pub props: Vec<MapEntryExpr>,
}

// Specification of a rel to create
#[derive(Debug, PartialEq, Clone)]
pub struct RelSpec {
    pub slot: usize,
    pub rel_type: Token,
    pub start_node_slot: usize,
    pub end_node_slot: usize,
    pub props: Vec<MapEntryExpr>,
}

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum Dir {
    Out,
    In,
}
impl Dir {
    pub(crate) fn reverse(self) -> Self {
        match self {
            Dir::Out => Dir::In,
            Dir::In => Dir::Out,
        }
    }
}

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum RelType {
    Defined(Token),
    Anon(Token),
}
impl RelType {
    pub fn token(&self) -> Token {
        match self {
            RelType::Defined(token) => *token,
            RelType::Anon(token) => *token,
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Predicate {
    And(Vec<Predicate>),
    Or(Vec<Predicate>),
    HasLabel(Token),
}

#[derive(Debug, PartialEq, Clone)]
pub struct Projection {
    pub expr: Expr,
    pub alias: Token,
    pub dst: Slot,
}

impl Projection {
    fn fmt_pretty(&self, ind: &str, t: &Tokens) -> String {
        format!(
            "Project({} => Slot({}) as `{}`",
            &self.expr.fmt_pretty(&format!("{}  ", ind), t),
            self.dst,
            t.lookup(self.alias).unwrap_or("?")
        )
    }
}

#[derive(Debug, Clone, Default)]
pub struct Scope {
    // This is the number that ends up in the .scope value for plan nodes in this scope
    // Note that we're really mixing two things here: "scope" as in "which identifiers can I
    // see" and scope as in "what version of the graph am I looking at"; we should probably
    // disambiguate better.
    number: u8,
    // Mapping of names used in the query string to slots in the row being processed
    slots: HashMap<Token, usize>,
    // Identifiers that the user has explictly declared. Eg in MATCH "(a)-->(b)" there are
    // three identifiers: a, b and an anonymous rel identifier. "a" and "b" are "named" here.
    named_identifiers: HashSet<Token>,
    // Named static expressions, used (currently) only to store named paths
    aliases: HashMap<Token, Expr>,
}

impl Scope {}

// Controls which scope Scoping delegates to, used when planning projections, where we toggle
// between the two scopes the projection bridges
#[derive(Debug, Clone)]
pub enum ScopingMode {
    Current,
    Prior,

    // Special scoping rules used "inside" WITH and RETURN statements, in the ORDER BY and
    // WHERE clauses associated with them; these get a bit tangly because we're dealing with
    // the transition from one scope to the next (eg. WITH introduce a new scope and navigates
    // the translation across)
    //
    // - You can't declare new stuff
    // - If you look something up, we first try to find it in the prior scope
    // - If we can't find it in the prior scope, we look it up in the current scope
    ProjectionMode,
}

// Owns variable scoping as the query is planned
#[derive(Debug, Clone)]
pub struct Scoping {
    // Scopes that are no longer in use, kept to allow tests to look stuff up after the fact
    history: Vec<Scope>,

    _prior: Scope,
    _current: Scope,

    mode: ScopingMode,

    // Not sure if this should be in Scope or here.. but either way, this is active pointers
    // to stack slots.
    stackrefs: HashMap<Token, usize>,

    // Next row slot to assign
    next_rowslot: usize,

    // Next stack slot to assign; this grows and shrinks as expressions use locals
    next_stackslot: usize,

    // Max next_stackslot used throughput the plan
    stack_highwater: usize,

    // Tokens are shared across scopes, but we ship them with each scope for programmer convenience
    tokens: Rc<RefCell<Tokens>>,

    anon_rel_seq: u32,
    anon_node_seq: u32,
}

impl Scoping {
    fn new(tokens: Rc<RefCell<Tokens>>) -> Scoping {
        Scoping {
            history: Default::default(),
            _prior: Scope {
                number: 0,
                slots: Default::default(),
                named_identifiers: Default::default(),
                aliases: Default::default()
            },
            _current: Scope {
                number: 1,
                slots: Default::default(),
                named_identifiers: Default::default(),
                aliases: Default::default()
            },
            mode: ScopingMode::Current,
            stackrefs: Default::default(),
            next_rowslot: 0,
            next_stackslot: 0,
            stack_highwater: 0,
            tokens,
            anon_rel_seq: 0,
            anon_node_seq: 0,
        }
    }

    pub fn begin_new_scope(&mut self) {
        let new_scope_no = self._current.number + 1;
        let new_prior = mem::replace(
            &mut self._current,
            Scope {
                number: new_scope_no,
                slots: Default::default(),
                named_identifiers: Default::default(),
                aliases: Default::default()
            },
        );
        let old_prior = mem::replace(&mut self._prior, new_prior);
        if !old_prior.slots.is_empty() || old_prior.named_identifiers.is_empty() {
            self.history.push(old_prior);
        }
    }

    // Get a list of copies of all scopes up to this point
    pub fn all_scopes(&self) -> Vec<Scope> {
        let mut out = Vec::new();
        for s in &self.history {
            out.push(s.clone())
        }
        out.push(self._prior.clone());
        out.push(self._current.clone());
        out
    }

    pub fn current_scope_no(&self) -> u8 {
        match self.mode {
            ScopingMode::Current => self._current.number,
            ScopingMode::Prior => self._prior.number,
            ScopingMode::ProjectionMode => {
                panic!("..")
            }
        }
    }

    pub fn new_anon_rel(&mut self) -> Token {
        let seq = self.anon_rel_seq;
        self.anon_rel_seq += 1;
        self.tokenize(&format!("$anonrel{}", seq))
    }

    pub fn new_anon_node(&mut self) -> Token {
        let seq = self.anon_node_seq;
        self.anon_node_seq += 1;
        self.tokenize(&format!("$anonnode{}", seq))
    }

    // Allocate a stack slot in this scope, referred to by the given token
    fn alloc_stack(&mut self, token: Token) -> usize {
        let slot = self.next_stackslot;
        self.next_stackslot += 1;
        self.stackrefs.insert(token, slot);
        slot
    }

    // Deallocate the topmost stack slot, asserting it's referred to by the given token
    fn dealloc_stack(&mut self, assert_token: Token) {
        let expected_slot = self.stackrefs.get(&assert_token).unwrap();
        if *expected_slot != self.next_stackslot - 1 {
            panic!("planner crashing due to programming error: next_stackslot does not match expected_slot, expected {}, got {}", expected_slot, self.next_stackslot - 1)
        }
        self.next_stackslot -= 1;
        self.stackrefs.remove(&assert_token);
    }

    // If the given id is a currently active stack reference, return the stack slot it's referencing
    fn lookup_stackref(&self, id: Token) -> Option<usize> {
        self.stackrefs.get(&id).copied()
    }

    fn tokenize(&mut self, contents: &str) -> Token {
        self.tokens.borrow_mut().tokenize(contents)
    }

    // So.. this is kind of a hack to defer a potential generalization. Up until this point in the
    // implementation, every identifier refers to a value in a slot. This concept is being introduced
    // to support an invariant: named paths.
    //
    // In this query:
    //
    //   MATCH p=(a)-->(b)--(c)
    //
    // All the values that make up the path p are already values in slots. `p` is just a name for
    // those slots together in a certain order, as far as the implementation is concerned.
    // Said another way: All identifiers we have dealt with so far are names for slots, but named
    // paths are not, named paths are names for a sequence of slots.
    //
    // The way I see it, there are three options:
    // 1) We store paths in slots, as a vector of RowRefs.
    // 2) We make all identifiers actually resolve to expressions, 99% of them being RowRefs
    // 3) We keep paths as a special snowflake
    //
    // I'm doing (3) because I think it'll be easy to throw away when we learn more. I'm avoiding
    // (1) because, at least when writing this, there's no easy way to stick static values into
    // runtime rows other than parameters, and that gets very confusing to use for this.
    fn alias(&mut self, id: Token, expr: Expr) {
        self.declare_tok(id);
        match self.mode {
            ScopingMode::Current => self._current.aliases.insert(id, expr),
            ScopingMode::Prior => self._prior.aliases.insert(id, expr),
            ScopingMode::ProjectionMode => {
                panic!("cannot alias variables in ORDER BY clause")
            }
        };
    }

    fn lookup_alias(&self, id: Token) -> Option<&Expr> {
        match self.mode {
            ScopingMode::Current => self._current.aliases.get(&id ),
            ScopingMode::Prior => self._prior.aliases.get(&id ),
            ScopingMode::ProjectionMode => {
                self._current.aliases.get(&id).or_else(||self._prior.aliases.get(&id))
            }
        }
    }

    // Declare a named identifier in the current scope if it isn't already;
    // the identifier becomes visible to operations like RETURN * and WITH *, et cetera.
    // Returns true if the token was not already declared
    fn declare_tok(&mut self, tok: Token) -> bool {
        match self.mode {
            ScopingMode::Current => self._current.named_identifiers.insert(tok),
            ScopingMode::Prior => self._prior.named_identifiers.insert(tok),
            ScopingMode::ProjectionMode => {
                panic!("cannot declare new variables in ORDER BY clause")
            }
        }
    }

    // Shorthand for tokenize + declare_tok
    fn declare(&mut self, contents: &str) -> Token {
        let tok = self.tokenize(contents);
        self.declare_tok(tok);
        tok
    }

    // Is the given token a value that we know about already?
    // This is used to determine if entities in CREATE refer to existing bound identifiers
    // or if they are introducing new entities to be created.
    pub fn is_declared(&self, tok: Token) -> bool {
        match self.mode {
            ScopingMode::Current => self._current.named_identifiers.contains(&tok),
            ScopingMode::Prior => self._prior.named_identifiers.contains(&tok),
            ScopingMode::ProjectionMode => {
                self._prior.named_identifiers.contains(&tok)
                    || self._current.named_identifiers.contains(&tok)
            }
        }
    }

    pub fn lookup_or_allocrow(&mut self, tok: Token) -> usize {
        match self.mode {
            ScopingMode::Current => match self._current.slots.get(&tok) {
                Some(slot) => *slot,
                None => {
                    let slot = self.next_rowslot;
                    self.next_rowslot += 1;
                    self._current.slots.insert(tok, slot);
                    slot
                }
            },
            ScopingMode::Prior => match self._prior.slots.get(&tok) {
                Some(slot) => *slot,
                None => {
                    let slot = self.next_rowslot;
                    self.next_rowslot += 1;
                    self._prior.slots.insert(tok, slot);
                    slot
                }
            },
            ScopingMode::ProjectionMode => {
                if let Some(slot) = self._prior.slots.get(&tok) {
                    *slot
                } else if let Some(slot) = self._current.slots.get(&tok) {
                    *slot
                } else {
                    panic!("Cannot allocate new row slots while in OrderBy scoping mode")
                }
            }
        }
    }
}

#[derive(Debug)]
pub struct PlanningContext<'i> {
    scoping: Scoping,

    // At the current state in the planning process, these are side-effects that occur
    // upstream in the plan we've built, that have no ordering guarantees
    unordered_sideffects: HashSet<SideEffect>,

    // Description of the backend this query is being planned for; intention is that this will
    // eventually contain things like listings of indexes etc. Once it does, it'll also need to
    // include a digest or a version that gets embedded with the planned query, because the query
    // plan may become invalid if indexes or constraints are added and removed.
    backend_desc: &'i BackendDesc,
}

impl<'i> PlanningContext<'i> {
    fn new(tokens: Rc<RefCell<Tokens>>, bd: &'i BackendDesc) -> Self {
        PlanningContext {
            scoping: Scoping::new(tokens),
            unordered_sideffects: Default::default(),
            backend_desc: bd,
        }
    }
}

// Tracks side-effects the query will generate as we plan it; this is used to determine
// when and where we need to insert logical barriers to ensure side-effects are seen by
// downstream parts of the plan.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum SideEffect {
    // Node created, deleted, labels added, labels removed or properties modified
    AnyNode,
    // Rel created, deleted or properties modified
    AnyRel,
}

fn plan_unwind(
    pc: &mut PlanningContext,
    src: LogicalPlan,
    unwind_stmt: Pair<Rule>,
) -> Result<LogicalPlan> {
    let mut parts = unwind_stmt.into_inner();

    let list_item = parts.next().expect("UNWIND must contain a list expression");
    let list_expr = plan_expr(&mut pc.scoping, list_item)?;
    let alias_token = pc.scoping.declare(
        parts
            .next()
            .expect("UNWIND must contain an AS alias")
            .as_str(),
    );
    let alias = pc.scoping.lookup_or_allocrow(alias_token);

    Ok(LogicalPlan::Unwind {
        src: Box::new(src),
        list_expr,
        alias,
    })
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::backend::{BackendDesc, FuncSignature, FuncType, Token, Tokens};
    use crate::Type;
    use anyhow::Result;
    use std::cell::RefCell;

    use std::rc::Rc;

    // Outcome of testing planning; the plan plus other related items to do checks on
    #[derive(Debug)]
    pub struct PlanArtifacts {
        pub plan: LogicalPlan,
        pub scopes: Vec<Scope>,
        pub tokens: Rc<RefCell<Tokens>>,
    }

    impl PlanArtifacts {
        pub fn slot(&self, k: Token) -> usize {
            for scope in &self.scopes {
                match scope.slots.get(&k) {
                    Some(s) => return *s,
                    _ => (),
                }
            }
            let toks = self.tokens.borrow();
            let tok = toks.lookup(k);
            panic!("No slot for token: {:?}", tok)
        }

        pub fn tokenize(&mut self, content: &str) -> Token {
            self.tokens.borrow_mut().tokenize(content)
        }
    }

    pub fn plan(q: &str) -> Result<PlanArtifacts> {
        let tokens = Rc::new(RefCell::new(Tokens::new()));
        let tok_expr = tokens.borrow_mut().tokenize("expr");
        let fn_count = tokens.borrow_mut().tokenize("count");
        let backend_desc = BackendDesc::new(vec![FuncSignature {
            func_type: FuncType::Aggregating,
            name: fn_count,
            returns: Type::Integer,
            args: vec![(tok_expr, Type::Any)],
        }]);

        let frontend = Frontend {
            tokens: Rc::clone(&tokens),
            backend_desc: BackendDesc::new(vec![]),
        };
        let mut pc = PlanningContext::new(Rc::clone(&tokens), &backend_desc);
        let plan = frontend.plan_in_context(q, &mut pc);

        let mut scopes = pc.scoping.all_scopes();
        // Gotta learn linked lists in rust..
        scopes.reverse();
        match plan {
            Ok(plan) => Ok(PlanArtifacts {
                plan,
                scopes,
                tokens: Rc::clone(&tokens),
            }),
            Err(e) => {
                println!("{}", e);
                Err(e)
            }
        }
    }

    mod unwind {
        use crate::frontend::tests::plan;
        use crate::frontend::{Expr, LogicalPlan};
        use crate::Error;

        #[test]
        fn plan_unwind() -> Result<(), Error> {
            let mut p = plan("UNWIND [[1], [2, 1.0]] AS x")?;

            let id_x = p.tokenize("x");
            assert_eq!(
                p.plan,
                LogicalPlan::Unwind {
                    src: Box::new(LogicalPlan::Argument),
                    list_expr: Expr::List(vec![
                        Expr::List(vec![Expr::Int(1)]),
                        Expr::List(vec![Expr::Int(2), Expr::Float(1.0)]),
                    ]),
                    alias: p.slot(id_x),
                }
            );
            Ok(())
        }
    }
}

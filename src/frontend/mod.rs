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
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::rc::Rc;

mod expr;

mod match_stmt;
mod create_stmt;
mod with_stmt;

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
                Rule::return_stmt => {
                    plan = with_stmt::plan_return(pc, plan, stmt)?;
                }
                Rule::with_stmt => {
                    plan = with_stmt::plan_with(pc, plan, stmt)?;
                }
                Rule::EOI => (),
                _ => unreachable!("Unknown statement: {:?}", stmt),
            }
        }

        println!("plan: {}", &plan.fmt_pretty(&"", &pc.tokens.borrow()));

        Ok(plan)
    }
}

// The ultimate output of the frontend is a logical plan. The logical plan is a tree of operators.
// The tree describes a stream processing pipeline starting at the leafs and ending at the root.
//
// This enumeration is the complete list of supported operators that the planner can emit.
//
// The slots are indexes into the row being produced
#[derive(Debug, PartialEq)]
pub enum LogicalPlan {
    Argument,
    NodeScan {
        src: Box<Self>,
        slot: usize,
        labels: Option<Token>,
    },
    Expand {
        src: Box<Self>,
        src_slot: usize,
        rel_slot: usize,
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
        nodes: Vec<NodeSpec>,
        rels: Vec<RelSpec>,
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
    Unwind {
        src: Box<Self>,
        list_expr: Expr,
        alias: Slot,
    },

    // Return and Project can probably be combined?
    Return {
        src: Box<Self>,
        projections: Vec<Projection>,
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
}

impl LogicalPlan {
    fn fmt_pretty(&self, ind: &str, t: &Tokens) -> String {
        match self {
            LogicalPlan::Return { src, projections } => {
                let next_indent = &format!("{}  ", ind);
                let mut proj = String::new();
                for (i, p) in projections.iter().enumerate() {
                    if i > 0 {
                        proj.push_str(", ");
                    }
                    proj.push_str(&p.fmt_pretty(next_indent, t))
                }
                format!(
                    "Return(\n{}src={},\n{}projections=[{}])",
                    next_indent,
                    src.fmt_pretty(&format!("{}  ", next_indent), t),
                    next_indent,
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
                    next_indent,
                    src.fmt_pretty(&format!("{}  ", next_indent), t),
                    next_indent,
                    proj,
                )
            }
            LogicalPlan::NodeScan { src, slot, labels } => {
                let next_indent = &format!("{}  ", ind);
                let mut lblstr = String::new();
                for (i, p) in labels.iter().enumerate() {
                    if i > 0 {
                        lblstr.push_str(", ");
                    }
                    lblstr.push_str(t.lookup(*p).unwrap_or("?"))
                }
                format!(
                    "NodeScan(\n{}src={}\n{}slot=Slot({})\n{}labels=[{}])",
                    ind,
                    src.fmt_pretty(next_indent, t),
                    ind,
                    slot,
                    ind,
                    &lblstr
                )
            }
            LogicalPlan::Expand {
                src,
                src_slot,
                rel_slot,
                dst_slot,
                rel_type,
                dir,
            } => {
                let next_indent = &format!("{}  ", ind);
                format!("Expand(\n{}src={}\n{}src_slot=Slot({})\n{}rel_slot=Slot({})\n{}dst_slot=Slot({}),\n{}rel_type={},\n{}dir={})",
                        ind, src.fmt_pretty(next_indent, t),
                        ind, src_slot,
                        ind, rel_slot,
                        ind, dst_slot,
                        ind, match rel_type {
                            Some(tok) => t.lookup(*tok).unwrap_or("?"),
                            None => "<any>",
                        },
                        ind, &format!("{:?}", dir))
            }
            LogicalPlan::Argument => format!("Argument()"),
            LogicalPlan::Create { src, nodes, rels } => {
                let next_indent = &format!("{}  ", ind);
                format!(
                    "Create(\n{}src={},\n{}nodes={},\n{}rels={})",
                    next_indent,
                    src.fmt_pretty(&format!("{}  ", next_indent), t),
                    next_indent,
                    format!("{:?}", nodes),
                    next_indent,
                    format!("{:?}", rels)
                )
            }
            LogicalPlan::Selection { src, predicate } => {
                let next_indent = &format!("{}  ", ind);
                format!(
                    "Selection(\n{}src={}\n{}predicate={:?})",
                    next_indent,
                    src.fmt_pretty(next_indent, t),
                    next_indent,
                    predicate,
                )
            }
            LogicalPlan::Limit { src, skip, limit } => {
                let next_indent = &format!("{}  ", ind);
                format!(
                    "Limit(\n{}src={}\n{}skip={:?},\n{}limit={:?})",
                    next_indent,
                    src.fmt_pretty(next_indent, t),
                    next_indent,
                    skip,
                    next_indent,
                    limit,
                )
            }
            LogicalPlan::Sort { src, sort_by } => {
                let next_indent = &format!("{}  ", ind);
                format!(
                    "Sort(\n{}src={}\n{}by={:?})",
                    next_indent,
                    src.fmt_pretty(next_indent, t),
                    next_indent,
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
            _ => format!("NoPretty({:?})", self),
        }
    }
}

// Specification of a node to create
#[derive(Debug, PartialEq)]
pub struct NodeSpec {
    pub slot: usize,
    pub labels: Vec<Token>,
    pub props: Vec<MapEntryExpr>,
}

// Specification of a rel to create
#[derive(Debug, PartialEq)]
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
    fn reverse(self) -> Self {
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

#[derive(Debug, PartialEq)]
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

#[derive(Debug)]
pub struct PlanningContext<'i> {
    // Mapping of names used in the query string to slots in the row being processed
    slots: HashMap<Token, usize>,
    // Identifiers that the user has explictly declared. Eg in MATCH "(a)-->(b)" there are
    // three identifiers: a, b and an anonymous rel identifier. "a" and "b" are "named" here.
    named_identifiers: HashSet<Token>,

    // TODO is there some nicer way to do this than Rc+RefCell?
    tokens: Rc<RefCell<Tokens>>,

    // Description of the backend this query is being planned for; intention is that this will
    // eventually contain things like listings of indexes etc. Once it does, it'll also need to
    // include a digest or a version that gets embedded with the planned query, because the query
    // plan may become invalid if indexes or constraints are added and removed.
    backend_desc: &'i BackendDesc,

    anon_rel_seq: u32,
    anon_node_seq: u32,
}

impl<'i> PlanningContext<'i> {
    fn new(tokens: Rc<RefCell<Tokens>>, bd: &'i BackendDesc) -> Self {
        PlanningContext {
            slots: Default::default(),
            named_identifiers: Default::default(),
            tokens,
            backend_desc: bd,
            anon_rel_seq: 0,
            anon_node_seq: 0,
        }
    }

    // Note: See declare() if you are declaring a named identifier that should be subject to
    // operations that refer to "all named identifiers", like RETURN *
    fn tokenize(&mut self, contents: &str) -> Token {
        self.tokens.borrow_mut().tokenize(contents)
    }

    // Declare a named identifier in the current scope if it isn't already;
    // the identifier becomes visible to operations like RETURN * and WITH *, et cetera.
    fn declare_tok(&mut self, tok: Token) {
        self.named_identifiers.insert(tok);
    }

    // Shorthand for tokenize + declare_tok
    fn declare(&mut self, contents: &str) -> Token {
        let tok = self.tokenize(contents);
        self.declare_tok(tok);
        return tok;
    }

    // Is the given token a value that we know about already?
    // This is used to determine if entities in CREATE refer to existing bound identifiers
    // or if they are introducing new entities to be created.
    pub fn is_declared(&self, tok: Token) -> bool {
        self.named_identifiers.contains(&tok)
    }

    pub fn get_or_alloc_slot(&mut self, tok: Token) -> usize {
        match self.slots.get(&tok) {
            Some(slot) => *slot,
            None => {
                let slot = self.slots.len();
                self.slots.insert(tok, slot);
                slot
            }
        }
    }

    pub fn new_anon_rel(&mut self) -> Token {
        let seq = self.anon_rel_seq;
        self.anon_rel_seq += 1;
        self.tokenize(&format!("AnonRel#{}", seq))
    }

    pub fn new_anon_node(&mut self) -> Token {
        let seq = self.anon_node_seq;
        self.anon_node_seq += 1;
        self.tokenize(&format!("AnonNode#{}", seq))
    }
}

fn plan_unwind(
    pc: &mut PlanningContext,
    src: LogicalPlan,
    unwind_stmt: Pair<Rule>,
) -> Result<LogicalPlan> {
    let mut parts = unwind_stmt.into_inner();

    let list_item = parts.next().expect("UNWIND must contain a list expression");
    let list_expr = plan_expr(pc, list_item)?;
    let alias_token = pc.declare(
        parts
            .next()
            .expect("UNWIND must contain an AS alias")
            .as_str(),
    );
    let alias = pc.get_or_alloc_slot(alias_token);

    return Ok(LogicalPlan::Unwind {
        src: Box::new(src),
        list_expr,
        alias,
    });
}

#[derive(Debug, PartialEq)]
pub struct PatternNode {
    identifier: Token,
    labels: Vec<Token>,
    props: Vec<MapEntryExpr>,
    // In the pattern, was this node assigned an identifier?
    // eg. in "MATCH (a)-->()", the second node is anonymous; it will have
    // been assigned an anonymous identifier
    anonymous: bool,
    solved: bool,
}

impl PatternNode {
    fn merge(&mut self, _other: &PatternNode) {}
}

#[derive(Debug, PartialEq)]
pub struct PatternRel {
    identifier: Token,
    rel_type: Option<Token>,
    left_node: Token,
    right_node: Option<Token>,
    // From the perspective of the left node, is this pattern inbound or outbound?
    dir: Option<Dir>,
    props: Vec<MapEntryExpr>,
    // In the pattern, was this node assigned an identifier?
    // eg. in "MATCH (a)-[r]->(b)-->(c)", the second rel is anonymous; it will have
    // been assigned an auto-generated identifier
    anonymous: bool,
    solved: bool,
}

#[derive(Debug, Default)]
pub struct PatternGraph {
    v: HashMap<Token, PatternNode>,
    v_order: Vec<Token>,
    e: Vec<PatternRel>,

    // If this pattern is an OPTIONAL MATCH patterh
    optional: bool,

    // The following expression must be true for the pattern to match; this can be a
    // deeply nested combination of Expr::And / Expr::Or. The pattern parser does not guarantee
    // it is a boolean expression.
    //
    // TODO: Currently this contains the entire WHERE clause, forcing evaluation of the WHERE
    //       predicates once all the expands and scans have been done. This can cause catastrophic
    //       cases, compared to if predicates where evaluated earlier in the plan.
    //
    // Imagine a cartesian join like:
    //
    //   MATCH (a:User {id: "a"}), (b:User {id: "b"})
    //
    // vs the same thing expressed as
    //
    //   MATCH (a:User), (b:User)
    //   WHERE a.id = "a" AND b.id = "b"
    //
    // The first will filter `a` down to 1 row before doing the cartesian product over `b`,
    // while the latter will first do the cartesian product of *all nodes in the database* and
    // then filter. The difference is something like 6 orders of magnitude of comparisons made.
    //
    // Long story short: We want a way to "lift" predicates out of this filter when we plan MATCH,
    // so that we filter stuff down as early as possible.
    predicate: Option<Expr>,
}

impl PatternGraph {
    fn merge_node(&mut self, n: PatternNode) {
        let entry = self.v.entry(n.identifier);
        match entry {
            Entry::Occupied(mut on) => {
                on.get_mut().merge(&n);
            }
            Entry::Vacant(entry) => {
                self.v_order.push(*entry.key());
                entry.insert(n);
            }
        };
    }

    fn merge_rel(&mut self, r: PatternRel) {
        self.e.push(r)
    }
}

fn parse_pattern_graph(pc: &mut PlanningContext, patterns: Pair<Rule>) -> Result<PatternGraph> {
    let mut pg: PatternGraph = PatternGraph::default();

    for part in patterns.into_inner() {
        match part.as_rule() {
            Rule::optional_clause => pg.optional = true,
            Rule::pattern => {
                let mut prior_node_id = None;
                let mut prior_rel: Option<PatternRel> = None;
                // For each node and rel segment of eg: (n:Message)-[:KNOWS]->()
                for segment in part.into_inner() {
                    match segment.as_rule() {
                        Rule::node => {
                            let prior_node = parse_pattern_node(pc, segment)?;
                            prior_node_id = Some(prior_node.identifier);
                            pg.merge_node(prior_node);
                            if let Some(mut rel) = prior_rel {
                                rel.right_node = prior_node_id;
                                pg.merge_rel(rel);
                                prior_rel = None
                            }
                        }
                        Rule::rel => {
                            prior_rel = Some(parse_pattern_rel(
                                pc,
                                prior_node_id.expect("pattern rel must be preceded by node"),
                                segment,
                            )?);
                            prior_node_id = None
                        }
                        _ => unreachable!(),
                    }
                }
            }
            Rule::where_clause => {
                pg.predicate = Some(plan_expr(
                    pc,
                    part.into_inner()
                        .next()
                        .expect("where clause must contain a predicate"),
                )?)
            }
            _ => unreachable!(),
        }
    }

    Ok(pg)
}

// Figures out what step we need to find the specified node
fn parse_pattern_node(pc: &mut PlanningContext, pattern_node: Pair<Rule>) -> Result<PatternNode> {
    let mut identifier = None;
    let mut labels = Vec::new();
    let mut props = Vec::new();
    for part in pattern_node.into_inner() {
        match part.as_rule() {
            Rule::id => identifier = Some(pc.tokenize(part.as_str())),
            Rule::label => {
                for label in part.into_inner() {
                    labels.push(pc.tokenize(label.as_str()));
                }
            }
            Rule::map => {
                props = expr::parse_map_expression(pc, part)?;
            }
            _ => panic!("don't know how to handle: {}", part),
        }
    }

    let anonymous = identifier.is_none();
    let id = identifier.unwrap_or_else(|| pc.new_anon_node());
    labels.sort_unstable();
    labels.dedup();
    Ok(PatternNode {
        identifier: id,
        labels,
        props,
        anonymous,
        solved: false,
    })
}

fn parse_pattern_rel(
    pc: &mut PlanningContext,
    left_node: Token,
    pattern_rel: Pair<Rule>,
) -> Result<PatternRel> {
    let mut identifier = None;
    let mut rel_type = None;
    let mut dir = None;
    let mut props = Vec::new();
    for part in pattern_rel.into_inner() {
        match part.as_rule() {
            Rule::id => identifier = Some(pc.tokenize(part.as_str())),
            Rule::rel_type => rel_type = Some(pc.tokenize(part.as_str())),
            Rule::left_arrow => dir = Some(Dir::In),
            Rule::right_arrow => {
                if dir.is_some() {
                    bail!("relationship can't be directed in both directions. If you want to find relationships in either direction, leave the arrows out")
                }
                dir = Some(Dir::Out)
            }
            Rule::map => {
                props = expr::parse_map_expression(pc, part)?;
            }
            _ => unreachable!(),
        }
    }
    let anonymous = identifier.is_none();
    let id = identifier.unwrap_or_else(|| pc.new_anon_rel());
    Ok(PatternRel {
        left_node,
        right_node: None,
        identifier: id,
        rel_type,
        dir,
        props,
        anonymous,
        solved: false,
    })
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::backend::{BackendDesc, FuncSignature, FuncType, Token, Tokens};
    use crate::Type;
    use anyhow::Result;
    use std::cell::RefCell;
    use std::collections::HashMap;
    use std::rc::Rc;

    // Outcome of testing planning; the plan plus other related items to do checks on
    #[derive(Debug)]
    pub struct PlanArtifacts {
        pub plan: LogicalPlan,
        pub slots: HashMap<Token, usize>,
        pub tokens: Rc<RefCell<Tokens>>,
    }

    impl PlanArtifacts {
        pub fn slot(&self, k: Token) -> usize {
            self.slots[&k]
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

        match plan {
            Ok(plan) => Ok(PlanArtifacts {
                plan,
                slots: pc.slots,
                tokens: Rc::clone(&tokens),
            }),
            Err(e) => {
                println!("{}", e);
                Err(e)
            }
        }
    }

    #[cfg(test)]
    mod aggregate {
        use crate::frontend::tests::plan;
        use crate::frontend::{Expr, LogicalPlan, Projection};
        use crate::Error;

        #[test]
        fn plan_simple_count() -> Result<(), Error> {
            let mut p = plan("MATCH (n:Person) RETURN count(n)")?;

            let lbl_person = p.tokenize("Person");
            let id_n = p.tokenize("n");
            let fn_count = p.tokenize("count");
            let col_count_n = p.tokenize("count(n)");
            assert_eq!(
                p.plan,
                LogicalPlan::Return {
                    src: Box::new(LogicalPlan::Aggregate {
                        src: Box::new(LogicalPlan::NodeScan {
                            src: Box::new(LogicalPlan::Argument),
                            slot: 0,
                            labels: Some(lbl_person)
                        }),
                        grouping: vec![],
                        aggregations: vec![(
                            Expr::FuncCall {
                                name: fn_count,
                                args: vec![Expr::Slot(p.slot(id_n))]
                            },
                            p.slot(col_count_n)
                        )]
                    }),
                    projections: vec![Projection {
                        expr: Expr::Slot(p.slot(col_count_n)),
                        alias: col_count_n,
                        dst: p.slot(col_count_n),
                    }]
                }
            );
            Ok(())
        }

        #[test]
        fn plan_simple_count_no_label() -> Result<(), Error> {
            let mut p = plan("MATCH (n) RETURN count(n)")?;

            let id_n = p.tokenize("n");
            let fn_count = p.tokenize("count");
            let col_count_n = p.tokenize("count(n)");
            assert_eq!(
                p.plan,
                LogicalPlan::Return {
                    src: Box::new(LogicalPlan::Aggregate {
                        src: Box::new(LogicalPlan::NodeScan {
                            src: Box::new(LogicalPlan::Argument),
                            slot: 0,
                            labels: None
                        }),
                        grouping: vec![],
                        aggregations: vec![(
                            Expr::FuncCall {
                                name: fn_count,
                                args: vec![Expr::Slot(p.slot(id_n))]
                            },
                            p.slot(col_count_n)
                        )]
                    }),
                    projections: vec![Projection {
                        expr: Expr::Slot(p.slot(col_count_n)),
                        alias: col_count_n,
                        dst: p.slot(col_count_n),
                    }]
                }
            );
            Ok(())
        }

        #[test]
        fn plan_grouped_count() -> Result<(), Error> {
            let mut p = plan("MATCH (n:Person) RETURN n.age, n.occupation, count(n)")?;

            let lbl_person = p.tokenize("Person");
            let id_n = p.tokenize("n");
            let key_age = p.tokenize("age");
            let key_occupation = p.tokenize("occupation");
            let fn_count = p.tokenize("count");
            let col_count_n = p.tokenize("count(n)");
            let col_n_age = p.tokenize("n.age");
            let col_n_occupation = p.tokenize("n.occupation");
            assert_eq!(
                p.plan,
                LogicalPlan::Return {
                    src: Box::new(LogicalPlan::Aggregate {
                        src: Box::new(LogicalPlan::NodeScan {
                            src: Box::new(LogicalPlan::Argument),
                            slot: 0,
                            labels: Some(lbl_person)
                        }),
                        grouping: vec![
                            (
                                Expr::Prop(Box::new(Expr::Slot(p.slot(id_n))), vec![key_age]),
                                p.slot(col_n_age)
                            ),
                            (
                                Expr::Prop(
                                    Box::new(Expr::Slot(p.slot(id_n))),
                                    vec![key_occupation]
                                ),
                                p.slot(col_n_occupation)
                            ),
                        ],
                        aggregations: vec![(
                            Expr::FuncCall {
                                name: fn_count,
                                args: vec![Expr::Slot(p.slot(id_n))]
                            },
                            p.slot(col_count_n)
                        )]
                    }),
                    projections: vec![
                        Projection {
                            expr: Expr::Slot(p.slot(col_n_age)),
                            alias: col_n_age,
                            dst: p.slot(col_n_age),
                        },
                        Projection {
                            expr: Expr::Slot(p.slot(col_n_occupation)),
                            alias: col_n_occupation,
                            dst: p.slot(col_n_occupation),
                        },
                        Projection {
                            expr: Expr::Slot(p.slot(col_count_n)),
                            alias: col_count_n,
                            dst: p.slot(col_count_n),
                        },
                    ]
                }
            );
            Ok(())
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

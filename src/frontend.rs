//
// The gqlite frontend contains the gql parser and logical planner.
// It produces a LogicalPlan, describing what needs to occur to fulfill the input query.
//

use pest::Parser;

use crate::backend::{Token, Tokens};
use crate::{Dir, Slot, Val};
use anyhow::Result;
use pest::iterators::Pair;
use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::fmt::Debug;
use std::rc::Rc;

#[derive(Parser)]
#[grammar = "cypher.pest"]
pub struct CypherParser;

#[derive(Debug)]
pub struct Frontend {
    pub tokens: Rc<RefCell<Tokens>>,
}

impl Frontend {
    // TODO obviously the query string shouldn't be static
    pub fn plan(&self, query_str: &str) -> Result<LogicalPlan> {
        self.plan_in_context(
            query_str,
            &mut PlanningContext {
                slots: Default::default(),
                anon_rel_seq: 0,
                anon_node_seq: 0,
                tokens: Rc::clone(&self.tokens),
            },
        )
    }

    pub fn plan_in_context(
        &self,
        query_str: &str,
        pc: &mut PlanningContext,
    ) -> Result<LogicalPlan> {
        let query = CypherParser::parse(Rule::query, &query_str)?
            .next()
            .unwrap(); // get and unwrap the `query` rule; never fails

        let mut plan = LogicalPlan::Argument;

        for stmt in query.into_inner() {
            match stmt.as_rule() {
                Rule::match_stmt => {
                    plan = plan_match(pc, plan, stmt)?;
                }
                Rule::create_stmt => {
                    plan = plan_create(pc, plan, stmt)?;
                }
                Rule::return_stmt => {
                    plan = plan_return(pc, plan, stmt);
                }
                Rule::EOI => (),
                _ => unreachable!(),
            }
        }

        println!("plan: {:?}", plan);

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
        rel_type: Token,
    },
    Create {
        src: Box<Self>,
        nodes: Vec<NodeSpec>,
        rels: Vec<RelSpec>,
    },
    Return {
        src: Box<Self>,
        projections: Vec<Projection>,
    },
}

#[derive(Debug, PartialEq)]
pub struct Projection {
    pub expr: Expr,
    pub alias: String, // TODO this should be Token
}

pub struct PlanningContext {
    // Mapping of names used in the query string to slots in the row being processed
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

    // Is the given token a value that we know about already?
    // This is used to determine if entities in CREATE refer to existing bound identifiers
    // or if they are introducing new entities to be created.
    pub fn is_bound(&self, tok: Token) -> bool {
        self.slots.contains_key(&tok)
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

fn plan_create(
    pc: &mut PlanningContext,
    src: LogicalPlan,
    create_stmt: Pair<Rule>,
) -> Result<LogicalPlan> {
    let pg = parse_pattern_graph(pc, create_stmt)?;

    let mut nodes = Vec::new();
    let mut rels = Vec::new();
    for (_, node) in pg.e {
        if pc.is_bound(node.identifier) {
            // We already know about this node, it isn't meant to be created. ie
            // MATCH (n) CREATE (n)-[:NEWREL]->(newnode)
            continue;
        }
        nodes.push(NodeSpec {
            slot: pc.get_or_alloc_slot(node.identifier),
            labels: node.labels,
            props: node.props,
        });
    }

    for rel in pg.v {
        match rel.dir {
            Some(Dir::Out) => {
                rels.push(RelSpec {
                    slot: pc.get_or_alloc_slot(rel.identifier),
                    rel_type: rel.rel_type,
                    start_node_slot: pc.get_or_alloc_slot(rel.left_node),
                    end_node_slot: pc.get_or_alloc_slot(rel.right_node.unwrap()),
                    props: rel.props,
                });
            }
            Some(Dir::In) => {
                rels.push(RelSpec {
                    slot: pc.get_or_alloc_slot(rel.identifier),
                    rel_type: rel.rel_type,
                    start_node_slot: pc.get_or_alloc_slot(rel.right_node.unwrap()),
                    end_node_slot: pc.get_or_alloc_slot(rel.left_node),
                    props: vec![],
                });
            }
            None => bail!("relationships in CREATE clauses must have a direction"),
        }
    }

    Ok(LogicalPlan::Create {
        src: Box::new(src),
        nodes,
        rels,
    })
}

// Specification of a node to create
#[derive(Debug, PartialEq)]
pub struct NodeSpec {
    slot: usize,
    labels: Vec<Token>,
    props: Vec<MapEntryExpr>,
}

// Specification of a rel to create
#[derive(Debug, PartialEq)]
pub struct RelSpec {
    slot: usize,
    rel_type: Token,
    start_node_slot: usize,
    end_node_slot: usize,
    props: Vec<MapEntryExpr>,
}

fn plan_return(pc: &mut PlanningContext, src: LogicalPlan, return_stmt: Pair<Rule>) -> LogicalPlan {
    let mut parts = return_stmt.into_inner();
    let projections = parts
        .next()
        .map(|p| plan_return_projections(pc, p))
        .expect("RETURN must start with projections");
    LogicalPlan::Return {
        src: Box::new(src),
        projections,
    }
}

fn plan_return_projections(pc: &mut PlanningContext, projections: Pair<Rule>) -> Vec<Projection> {
    let mut out = Vec::new();
    for projection in projections.into_inner() {
        if let Rule::projection = projection.as_rule() {
            let default_alias = String::from(projection.as_str());
            let mut parts = projection.into_inner();
            let expr = parts.next().map(|p| plan_expr(pc, p)).unwrap();
            let alias = parts
                .next()
                .and_then(|p| match p.as_rule() {
                    Rule::id => Some(String::from(p.as_str())),
                    _ => None,
                })
                .unwrap_or(default_alias);
            out.push(Projection { expr, alias });
        }
    }
    out
}

fn plan_expr(pc: &mut PlanningContext, expression: Pair<Rule>) -> Expr {
    for inner in expression.into_inner() {
        match inner.as_rule() {
            Rule::string => {
                let content = inner
                    .into_inner()
                    .next()
                    .expect("Strings should always have an inner value")
                    .as_str();
                return Expr::Lit(Val::String(String::from(content)));
            }
            Rule::id => {
                let tok = pc.tokenize(inner.as_str());
                return Expr::Slot(pc.get_or_alloc_slot(tok));
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
                return Expr::Prop(Box::new(base), props);
            }
            _ => panic!(String::from(inner.as_str())),
        }
    }
    panic!("Invalid expression from parser.")
}

#[derive(Debug, PartialEq)]
pub struct PatternNode {
    identifier: Token,
    labels: Vec<Token>,
    props: Vec<MapEntryExpr>,
    solved: bool,
}

impl PatternNode {
    fn merge(&mut self, _other: &PatternNode) {}
}

#[derive(Debug, PartialEq)]
pub struct PatternRel {
    identifier: Token,
    rel_type: Token,
    left_node: Token,
    right_node: Option<Token>,
    // From the perspective of the left node, is this pattern inbound or outbound?
    dir: Option<Dir>,
    props: Vec<MapEntryExpr>,
    solved: bool,
}

#[derive(Debug, Default)]
pub struct PatternGraph {
    e: HashMap<Token, PatternNode>,
    e_order: Vec<Token>,
    v: Vec<PatternRel>,
}

impl PatternGraph {
    fn merge_node(&mut self, n: PatternNode) {
        let entry = self.e.entry(n.identifier);
        match entry {
            Entry::Occupied(mut on) => {
                on.get_mut().merge(&n);
            }
            Entry::Vacant(entry) => {
                self.e_order.push(*entry.key());
                entry.insert(n);
            }
        };
    }

    fn merge_rel(&mut self, r: PatternRel) {
        self.v.push(r)
    }
}

fn plan_match(
    pc: &mut PlanningContext,
    src: LogicalPlan,
    match_stmt: Pair<Rule>,
) -> Result<LogicalPlan> {
    let mut plan = src;
    let mut pg = parse_pattern_graph(pc, match_stmt)?;

    // Ok, now we have parsed the pattern into a full graph, time to start solving it
    println!("built pg: {:?}", pg);
    // Start by picking one high-selectivity node
    for id in &pg.e_order {
        let candidate = pg.e.get_mut(id).unwrap();
        // Advanced algorithm: Pick first node with a label filter on it and call it an afternoon
        if !candidate.labels.is_empty() {
            plan = LogicalPlan::NodeScan {
                src: Box::new(plan),
                slot: pc.get_or_alloc_slot(*id),
                labels: candidate.labels.first().cloned(),
            };
            candidate.solved = true;
            break;
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
                continue;
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
                    dst_slot: pc.get_or_alloc_slot(right_id),
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
                    dst_slot: pc.get_or_alloc_slot(left_id),
                    rel_type: rel.rel_type,
                };
            }
        }

        if !found_unsolved {
            break;
        }

        if !solved_any {
            panic!("Failed to solve pattern: {:?}", pg)
        }
    }

    Ok(plan)
}

fn parse_pattern_graph(pc: &mut PlanningContext, patterns: Pair<Rule>) -> Result<PatternGraph> {
    let mut pg: PatternGraph = PatternGraph::default();

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
            _ => unreachable!(),
        }
    }

    Ok(pg)
}

// Figures out what step we need to find the specified node
fn parse_pattern_node(pc: &mut PlanningContext, pattern_node: Pair<Rule>) -> PatternNode {
    let mut identifier = None;
    let mut label = None;
    let mut props = Vec::new();
    for part in pattern_node.into_inner() {
        match part.as_rule() {
            Rule::id => identifier = Some(pc.tokenize(part.as_str())),
            Rule::label => label = Some(pc.tokenize(part.as_str())),
            Rule::map => {
                props = parse_map_expression(pc, part);
            }
            _ => panic!("don't know how to handle: {}", part),
        }
    }

    let id = identifier.unwrap_or_else(|| pc.new_anon_node());

    let labels = if let Some(lbl) = label {
        vec![lbl]
    } else {
        vec![]
    };

    PatternNode {
        identifier: id,
        labels,
        props,
        solved: false,
    }
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
                props = parse_map_expression(pc, part);
            }
            _ => unreachable!(),
        }
    }
    // TODO don't use this empty identifier here
    let id = identifier.unwrap_or_else(|| pc.new_anon_rel());
    let rt = rel_type.unwrap_or_else(|| pc.new_anon_rel());
    Ok(PatternRel {
        left_node,
        right_node: None,
        identifier: id,
        rel_type: rt,
        dir,
        props,
        solved: false,
    })
}

fn parse_map_expression(pc: &mut PlanningContext, map_expr: Pair<Rule>) -> Vec<MapEntryExpr> {
    let mut out = Vec::new();
    for pair in map_expr.into_inner() {
        match pair.as_rule() {
            Rule::map_pair => {
                let mut pair_iter = pair.into_inner();
                let id_token = pair_iter
                    .next()
                    .expect("Map pair must contain an identifier");
                let identifier = pc.tokenize(id_token.as_str());

                let expr_token = pair_iter
                    .next()
                    .expect("Map pair must contain an expression");
                let expr = plan_expr(pc, expr_token);
                out.push(MapEntryExpr {
                    key: identifier,
                    val: expr,
                })
            }
            _ => unreachable!(),
        }
    }
    out
}

#[derive(Debug, PartialEq)]
pub enum Expr {
    Lit(Val),
    // Lookup a property by id
    Prop(Box<Self>, Vec<Token>),
    Slot(Slot),
    // Map expressions differ from eg. Lit(Val::Map) in that they can have expressions as
    // values, like `{ name: trim_spaces(n.name) }`, and evaluate to Val maps.
    Map(Vec<MapEntryExpr>),
}

#[derive(Debug, PartialEq)]
pub struct MapEntryExpr {
    key: Token,
    val: Expr,
}

#[cfg(test)]
mod tests {
    use crate::backend::Tokens;
    use crate::frontend::{
        Expr, Frontend, LogicalPlan, MapEntryExpr, NodeSpec, PatternNode, PatternRel,
        PlanningContext, RelSpec,
    };
    use crate::Dir::Out;
    use crate::{Dir, Val};
    use anyhow::Result;
    use std::cell::RefCell;
    use std::rc::Rc;

    fn plan(q: &'static str) -> Result<(LogicalPlan, PlanningContext)> {
        let tokens = Rc::new(RefCell::new(Tokens::new()));

        let frontend = Frontend {
            tokens: Rc::clone(&tokens),
        };
        let mut pc = PlanningContext {
            slots: Default::default(),
            anon_rel_seq: 0,
            anon_node_seq: 0,
            tokens: Rc::clone(&tokens),
        };

        match frontend.plan_in_context(q, &mut pc) {
            Ok(plan) => Ok((plan, pc)),
            Err(e) => {
                println!("{}", e);
                Err(e)
            }
        }
    }

    #[test]
    fn plan_create() -> Result<()> {
        let (plan, mut pc) = plan("CREATE (n:Person)")?;

        let lbl_person = pc.tokenize("Person");
        let id_n = pc.tokenize("n");
        assert_eq!(
            plan,
            LogicalPlan::Create {
                src: Box::new(LogicalPlan::Argument),
                nodes: vec![NodeSpec {
                    slot: pc.get_or_alloc_slot(id_n),
                    labels: vec![lbl_person],
                    props: vec![]
                }],
                rels: vec![]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_create_with_props() -> Result<()> {
        let (plan, mut pc) = plan("CREATE (n:Person {name: \"Bob\"})")?;

        let lbl_person = pc.tokenize("Person");
        let id_n = pc.tokenize("n");
        let key_name = pc.tokenize("name");
        assert_eq!(
            plan,
            LogicalPlan::Create {
                src: Box::new(LogicalPlan::Argument),
                nodes: vec![NodeSpec {
                    slot: pc.get_or_alloc_slot(id_n),
                    labels: vec![lbl_person],
                    props: vec![MapEntryExpr {
                        key: key_name,
                        val: Expr::Lit(Val::String("Bob".to_string())),
                    }]
                }],
                rels: vec![]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_create_rel() -> Result<()> {
        let (plan, mut pc) = plan("CREATE (n:Person)-[r:KNOWS]->(n)")?;

        let rt_knows = pc.tokenize("KNOWS");
        let lbl_person = pc.tokenize("Person");
        let id_n = pc.tokenize("n");
        let id_r = pc.tokenize("r");
        assert_eq!(
            plan,
            LogicalPlan::Create {
                src: Box::new(LogicalPlan::Argument),
                nodes: vec![NodeSpec {
                    slot: pc.get_or_alloc_slot(id_n),
                    labels: vec![lbl_person],
                    props: vec![]
                }],
                rels: vec![RelSpec {
                    slot: pc.get_or_alloc_slot(id_r),
                    rel_type: rt_knows,
                    start_node_slot: pc.get_or_alloc_slot(id_n),
                    end_node_slot: pc.get_or_alloc_slot(id_n),
                    props: vec![]
                },]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_create_rel_with_props() -> Result<()> {
        let (plan, mut pc) = plan("CREATE (n:Person)-[r:KNOWS {since:\"2012\"}]->(n)")?;

        let rt_knows = pc.tokenize("KNOWS");
        let lbl_person = pc.tokenize("Person");
        let id_n = pc.tokenize("n");
        let id_r = pc.tokenize("r");
        assert_eq!(
            plan,
            LogicalPlan::Create {
                src: Box::new(LogicalPlan::Argument),
                nodes: vec![NodeSpec {
                    slot: pc.get_or_alloc_slot(id_n),
                    labels: vec![lbl_person],
                    props: vec![]
                }],
                rels: vec![RelSpec {
                    slot: pc.get_or_alloc_slot(id_r),
                    rel_type: rt_knows,
                    start_node_slot: pc.get_or_alloc_slot(id_n),
                    end_node_slot: pc.get_or_alloc_slot(id_n),
                    props: vec![MapEntryExpr {
                        key: pc.tokenize("since"),
                        val: Expr::Lit(Val::String("2012".to_string()))
                    },]
                },]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_create_outbound_rel_on_preexisting_node() -> Result<()> {
        let (plan, mut pc) = plan("MATCH (n:Person) CREATE (n)-[r:KNOWS]->(o:Person)")?;

        let rt_knows = pc.tokenize("KNOWS");
        let lbl_person = pc.tokenize("Person");
        let id_n = pc.tokenize("n");
        let id_o = pc.tokenize("o");
        let id_r = pc.tokenize("r");
        assert_eq!(
            plan,
            LogicalPlan::Create {
                src: Box::new(LogicalPlan::NodeScan {
                    src: Box::new(LogicalPlan::Argument),
                    slot: pc.get_or_alloc_slot(id_n),
                    labels: Some(lbl_person),
                }),
                nodes: vec![
                    // Note there is just one node here, the planner should understand "n" already exists
                    NodeSpec {
                        slot: pc.get_or_alloc_slot(id_o),
                        labels: vec![lbl_person],
                        props: vec![]
                    }
                ],
                rels: vec![RelSpec {
                    slot: id_r,
                    rel_type: rt_knows,
                    start_node_slot: pc.get_or_alloc_slot(id_n),
                    end_node_slot: pc.get_or_alloc_slot(id_o),
                    props: vec![]
                },]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_create_inbound_rel_on_preexisting_node() -> Result<()> {
        let (plan, mut pc) = plan("MATCH (n:Person) CREATE (n)<-[r:KNOWS]-(o:Person)")?;

        let rt_knows = pc.tokenize("KNOWS");
        let lbl_person = pc.tokenize("Person");
        let id_n = pc.tokenize("n");
        let id_o = pc.tokenize("o");
        let id_r = pc.tokenize("r");
        assert_eq!(
            plan,
            LogicalPlan::Create {
                src: Box::new(LogicalPlan::NodeScan {
                    src: Box::new(LogicalPlan::Argument),
                    slot: pc.get_or_alloc_slot(id_n),
                    labels: Some(lbl_person),
                }),
                nodes: vec![
                    // Note there is just one node here, the planner should understand "n" already exists
                    NodeSpec {
                        slot: pc.get_or_alloc_slot(id_o),
                        labels: vec![lbl_person],
                        props: vec![]
                    }
                ],
                rels: vec![RelSpec {
                    slot: id_r,
                    rel_type: rt_knows,
                    start_node_slot: pc.get_or_alloc_slot(id_o),
                    end_node_slot: pc.get_or_alloc_slot(id_n),
                    props: vec![]
                },]
            }
        );
        Ok(())
    }
}

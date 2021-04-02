
use crate::backend::{Token};
use anyhow::Result;
use pest::iterators::Pair;
use std::collections::hash_map::Entry;
use std::collections::{HashMap};
use std::fmt::Debug;

use super::{Dir, PlanningContext, Rule};
use super::expr::{plan_expr, parse_map_expression, Expr, MapEntryExpr};


#[derive(Debug, PartialEq, Clone)]
pub struct PatternNode {
    pub identifier: Token,
    pub labels: Vec<Token>,
    pub props: Vec<MapEntryExpr>,
    // In the pattern, was this node assigned an identifier?
    // eg. in "MATCH (a)-->()", the second node is anonymous; it will have
    // been assigned an anonymous identifier
    pub anonymous: bool,
    // This is mutated as the pattern is solved. Initially bound nodes - nodes we already
    // know about from before the MATCH, like in `MATCH (a) WITH a MATCH (a)-->(b)` - are
    // marked solved. As the pattern solver works it incrementally marks more and more stuff
    // solved.
    pub solved: bool,
}

impl PatternNode {
    pub fn merge(&mut self, _other: &PatternNode) {}
}

#[derive(Debug, PartialEq, Clone)]
pub struct PatternRel {
    pub identifier: Token,
    pub rel_type: Option<Token>,
    pub left_node: Token,
    pub right_node: Option<Token>,
    // From the perspective of the left node, is this pattern inbound or outbound?
    pub dir: Option<Dir>,
    pub props: Vec<MapEntryExpr>,
    // See PatternNode#anonymous
    pub anonymous: bool,
    // See PatternNode#solved
    pub solved: bool,
}

#[derive(Debug, PartialEq, Clone)]
pub struct NamedPattern {
    pub identifier: Token,
    // Alternating node/rel references
    pub parts: Vec<Token>,
}

#[derive(Debug, Default, Clone)]
pub struct PatternGraph {
    pub v: HashMap<Token, PatternNode>,
    pub v_order: Vec<Token>,
    pub e: Vec<PatternRel>,

    // Patterns the user has assigned a name to via the `MATCH p=()-->()` format.
    pub named_patterns: Vec<NamedPattern>,

    // Nodes and rels introduced in this pattern; eg for
    //
    //   MATCH (n) WITH n MATCH (n)-[r]->(p)
    //
    // In MATCH (n)-[r]->(p), `r` and `p` are new identifiers and would show up in this list.
    pub unbound_identifiers: Vec<Token>,

    // If this pattern is an OPTIONAL MATCH
    pub optional: bool,

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
    pub predicate: Option<Expr>,
}

impl PatternGraph {
    pub fn merge_node(&mut self, n: PatternNode) {
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

    pub fn merge_rel(&mut self, r: PatternRel) {
        self.e.push(r)
    }
}

pub fn parse_pattern_graph(pc: &mut PlanningContext, patterns: Pair<Rule>) -> Result<PatternGraph> {
    let mut pg: PatternGraph = PatternGraph::default();
    let mut named_pattern = None;

    for part in patterns.into_inner() {
        match part.as_rule() {
            Rule::optional_clause => pg.optional = true,
            Rule::pattern_name => {
                let id = part.into_inner().next().unwrap();
                if let Rule::id = id.as_rule() {
                    named_pattern = Some(NamedPattern {
                        identifier: pc.scoping.tokenize(id.as_str()),
                        parts: vec![]
                    });
                } else {
                    bail!("parse error, expected an identifier as path name, got {:?}", id)
                }
            }
            Rule::pattern => {
                let mut prior_node_id = None;
                let mut prior_rel: Option<PatternRel> = None;
                // For each node and rel segment of eg: (n:Message)-[:KNOWS]->()
                for segment in part.into_inner() {
                    match segment.as_rule() {
                        Rule::node => {
                            let current_node = parse_pattern_node(pc, segment)?;
                            if let Some(np) = &mut named_pattern {
                                np.parts.push(current_node.identifier);
                            }
                            if !current_node.anonymous && !current_node.solved {
                                let is_new = pc.scoping.declare_tok(current_node.identifier);
                                if is_new {
                                    pg.unbound_identifiers.push(current_node.identifier)
                                }
                            } else if current_node.anonymous {
                                pg.unbound_identifiers.push(current_node.identifier)
                            }
                            prior_node_id = Some(current_node.identifier);
                            pg.merge_node(current_node);
                            if let Some(mut rel) = prior_rel {
                                rel.right_node = prior_node_id;
                                pg.merge_rel(rel);
                                prior_rel = None
                            }
                        }
                        Rule::rel => {
                            let current_rel = parse_pattern_rel(
                                pc,
                                prior_node_id.expect("pattern rel must be preceded by node"),
                                segment,
                            )?;
                            if let Some(np) = &mut named_pattern {
                                np.parts.push(current_rel.identifier);
                            }
                            if !current_rel.anonymous && !current_rel.solved {
                                let is_new = pc.scoping.declare_tok(current_rel.identifier);
                                if is_new {
                                    pg.unbound_identifiers.push(current_rel.identifier)
                                }
                            } else if current_rel.anonymous {
                                pg.unbound_identifiers.push(current_rel.identifier)
                            }
                            prior_rel = Some(current_rel);
                            prior_node_id = None
                        }
                        _ => unreachable!(),
                    }
                }
                if let Some(np) = named_pattern {
                    pg.named_patterns.push(np);
                    named_pattern = None;
                }
            }
            Rule::where_clause => {
                pg.predicate = Some(plan_expr(
                    &mut pc.scoping,
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
            Rule::id => identifier = Some(pc.scoping.tokenize(part.as_str())),
            Rule::label => {
                for label in part.into_inner() {
                    labels.push(pc.scoping.tokenize(label.as_str()));
                }
            }
            Rule::map => {
                props = parse_map_expression(&mut pc.scoping, part)?;
            }
            _ => panic!("don't know how to handle: {}", part),
        }
    }

    let anonymous = identifier.is_none();
    let id = identifier.unwrap_or_else(|| pc.scoping.new_anon_node());
    labels.sort_unstable();
    labels.dedup();
    let is_bound = pc.scoping.is_declared(id);
    Ok(PatternNode {
        identifier: id,
        labels,
        props,
        anonymous,
        solved: is_bound,
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
            Rule::id => identifier = Some(pc.scoping.tokenize(part.as_str())),
            Rule::rel_type => rel_type = Some(pc.scoping.tokenize(part.as_str())),
            Rule::left_arrow => dir = Some(Dir::In),
            Rule::right_arrow => {
                if dir.is_some() {
                    bail!("relationship can't be directed in both directions. If you want to find relationships in either direction, leave the arrows out")
                }
                dir = Some(Dir::Out)
            }
            Rule::map => {
                props = parse_map_expression(&mut pc.scoping, part)?;
            }
            _ => unreachable!(),
        }
    }
    let anonymous = identifier.is_none();
    let id = identifier.unwrap_or_else(|| pc.scoping.new_anon_rel());
    let is_bound = pc.scoping.is_declared(id);
    Ok(PatternRel {
        left_node,
        right_node: None,
        identifier: id,
        rel_type,
        dir,
        props,
        anonymous,
        solved: is_bound,
    })
}

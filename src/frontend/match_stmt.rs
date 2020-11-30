use super::{parse_pattern_graph, Dir, Expr, LogicalPlan, Pair, PlanningContext, Result, Rule};
use crate::backend::Token;
use crate::frontend::{Op, PatternNode, PatternGraph};

pub fn plan_match(
    pc: &mut PlanningContext,
    src: LogicalPlan,
    match_stmt: Pair<Rule>,
) -> Result<LogicalPlan> {
    let pg = parse_pattern_graph(pc, match_stmt)?;

    println!("PG: {:?}", pg);

    if pg.optional {
        // We currently only handle a singular case here, OPTIONAL MATCH with a single unbound node:
        if pg.e.len() > 0 {
            bail!("gqlite does not yet support OPTIONAL MATCH with relationships, sorry")
        }

        if pg.predicate.is_some() {
            bail!("gqlite does not yet support OPTIONAL MATCH with WHERE clause, sorry")
        }

        let (_, node) = pg.v.iter().next().unwrap();

        let node_slot = pc.scoping.lookup_or_allocrow(node.identifier);
        return Ok(LogicalPlan::Optional {
            src: Box::new(LogicalPlan::NodeScan {
                src: Box::new(src),
                slot: node_slot,
                labels: node.labels.first().cloned(),
            }),
            slots: vec![node_slot],
        });
    }

    return plan_match_patterngraph(pc, src, pg)
}

pub fn plan_match_patterngraph(pc: &mut PlanningContext, src: LogicalPlan, mut pg: PatternGraph) -> Result<LogicalPlan> {
    fn filter_expand(expand: LogicalPlan, slot: Token, labels: &[Token]) -> LogicalPlan {
        let labels = labels
            .iter()
            .map(|&label| Expr::HasLabel(slot, label))
            .collect::<Vec<_>>();
        if labels.is_empty() {
            expand
        } else if labels.len() == 1 {
            LogicalPlan::Selection {
                src: Box::new(expand),
                predicate: labels.into_iter().next().unwrap(),
            }
        } else {
            LogicalPlan::Selection {
                src: Box::new(expand),
                predicate: Expr::And(labels),
            }
        }
    }

    let mut plan = src;

    // 0: Loop through the rels in the pattern and find bound rels
    let mut pattern_has_solved_nodes = false;
    for rel in &mut pg.e {
        if rel.solved {
            pattern_has_solved_nodes = true;
            let left_node = pg.v.get(&rel.left_node).unwrap();
            let right_node = pg.v.get(&rel.right_node.unwrap()).unwrap();

            // TODO this is wrong, lets see how far it can go before the TCK catches on to that..
            //      eg. at the very least this needs to emit two rows if the path has no direction.
            //      like in MATCH ()-[r]->() WITH r MATCH (a)-[r]-(b), there are two rows for each
            //      rel, one with the start node as `a`, one with the start node as `b`.
            plan = LogicalPlan::ExpandRel {
                src: Box::new(plan),
                src_rel_slot: pc.scoping.lookup_or_allocrow(rel.identifier),
                start_node_slot: pc.scoping.lookup_or_allocrow(left_node.identifier),
                end_node_slot: pc.scoping.lookup_or_allocrow(right_node.identifier)
            };

            rel.solved = true;
            pg.v.get_mut(&rel.left_node).unwrap().solved = true;
            pg.v.get_mut(&rel.right_node.unwrap()).unwrap().solved = true;
        }
    }

    // 1: Loop through all nodes in the pattern and..
    //    - Find any pre-existing bound nodes we could start from
    //    - Pick a candidate start point to use if ^^ doesn't work
    //    - Declare all identifiers introduced
    let mut candidate_id = None;
    for id in &pg.v_order {
        if let None = candidate_id {
            candidate_id = Some(id);
        }
        let candidate = pg.v.get_mut(id).unwrap();

        if candidate.solved {
            pattern_has_solved_nodes = true;
            break;
        }

        // Prefer a candidate with labels since that has higher selectivity
        if !candidate.labels.is_empty() {
            if candidate.labels.len() > 1 {
                panic!("Multiple label match not yet implemented")
            }
            candidate_id = Some(id)
        }
    }

    // 2: If there's no bound nodes, use the candidate as start point
    if !pattern_has_solved_nodes {
        if let Some(candidate_id) = candidate_id {
            let candidate = pg.v.get_mut(candidate_id).unwrap();
            candidate.solved = true;
            plan = plan_match_node(pc, candidate, plan)?;
        }
    }

    // 3: Solve the pattern
    //
    // We iterate until the whole pattern is solved. The way this works is that "solving"
    // a part of the pattern expands the plan such that when the top-level part of the plan is
    // executed, all the solved identifiers will be present in the output row. That then unlocks
    // the ability to solve other parts of the pattern, and so on.
    loop {
        let mut found_unsolved = false;
        let mut solved_any = false;
        // Look for relationships we can expand
        for mut rel in &mut pg.e {
            if rel.solved {
                continue;
            }
            found_unsolved = true;

            let right_id = rel.right_node.unwrap();
            let left_id = rel.left_node;
            let left_solved = pg.v.get(&left_id).unwrap().solved;
            let right_solved = pg.v.get_mut(&right_id).unwrap().solved;

            if left_solved && !right_solved {
                // Left is solved and right isn't, so we can expand to the right
                let mut right_node = pg.v.get_mut(&right_id).unwrap();
                right_node.solved = true;
                rel.solved = true;
                solved_any = true;

                let dst = pc.scoping.lookup_or_allocrow(right_id);
                let expand = LogicalPlan::Expand {
                    src: Box::new(plan),
                    src_slot: pc.scoping.lookup_or_allocrow(left_id),
                    rel_slot: pc.scoping.lookup_or_allocrow(rel.identifier),
                    dst_slot: dst,
                    rel_type: rel.rel_type,
                    dir: rel.dir,
                };
                plan = filter_expand(expand, dst, &right_node.labels);
            } else if !left_solved && right_solved {
                // Right is solved and left isn't, so we can expand to the left
                let mut left_node = pg.v.get_mut(&left_id).unwrap();
                left_node.solved = true;
                rel.solved = true;
                solved_any = true;

                let dst = pc.scoping.lookup_or_allocrow(left_id);
                let expand = LogicalPlan::Expand {
                    src: Box::new(plan),
                    src_slot: pc.scoping.lookup_or_allocrow(right_id),
                    rel_slot: pc.scoping.lookup_or_allocrow(rel.identifier),
                    dst_slot: dst,
                    rel_type: rel.rel_type,
                    dir: rel.dir.map(Dir::reverse),
                };
                plan = filter_expand(expand, dst, &left_node.labels);
            } else if left_solved && right_solved {
                // Both sides are solved, need to find rel that bridges them.
                rel.solved = true;
                solved_any = true;
                let dst_slot = pc.scoping.lookup_or_allocrow(rel.identifier);
                plan = LogicalPlan::ExpandInto {
                    src: Box::new(plan),
                    left_node_slot: pc.scoping.lookup_or_allocrow(left_id),
                    right_node_slot: pc.scoping.lookup_or_allocrow(right_id),
                    dst_slot,
                    rel_type: rel.rel_type,
                    dir: rel.dir
                }
            }
        }

        // If we didn't solve any rels, most likely we're just done.
        // However, there is a chance we've got a disjoint pattern,
        // eg. something like MATCH (a), (b) or MATCH (a), (b)-->(). So, go through the nodes
        // and, if there are unsolved ones, this means there's a cartesian product we need to solve
        if !solved_any {
            for (_, v) in &mut pg.v {
                if v.solved {
                    continue;
                }

                // Found an unsolved node; for now just go with the first one we find
                found_unsolved = true;
                v.solved = true;

                let inner = Box::new(plan_match_node(pc, v, LogicalPlan::Argument)?);
                plan = LogicalPlan::CartesianProduct {
                    outer: Box::new(plan),
                    inner,
                    predicate: Expr::Bool(true),
                };

                // Just solve one and see if that's enough to expand the others
                solved_any = true;
                break;
            }
        }

        if !found_unsolved {
            break;
        }

        // Eg. we currently don't handle circular patterns (requiring JOINs) or patterns
        // with multiple disjoint subgraphs.
        if !solved_any {
            panic!("Failed to solve pattern: {:?}", pg)
        }
    }

    // Finally, add the pattern-wide predicate to filter the result of the pattern match
    // see the note on PatternGraph about issues with this "late filter" approach
    if let Some(pred) = &pg.predicate {
        return Ok(LogicalPlan::Selection {
            src: Box::new(plan),
            predicate: pred.clone(),
        });
    }

    Ok(plan)
}

fn plan_match_node(
    pc: &mut PlanningContext,
    v: &mut PatternNode,
    src: LogicalPlan,
) -> Result<LogicalPlan> {
    if v.labels.len() > 1 {
        bail!("Multiple label match not yet implemented")
    }
    // Getting all possible nodes..
    let node_slot = pc.scoping.lookup_or_allocrow(v.identifier);
    let mut plan = LogicalPlan::NodeScan {
        src: Box::new(src),
        slot: node_slot,
        labels: v.labels.first().cloned(),
    };

    if !v.props.is_empty() {
        // Need to filter on props
        let mut and_terms = Vec::new();
        for e in &v.props {
            and_terms.push(Expr::BinaryOp {
                left: Box::new(Expr::Prop(Box::new(Expr::RowRef(node_slot)), vec![e.key])),
                right: Box::new(e.val.clone()),
                op: Op::Eq,
            })
        }

        let predicate = if and_terms.len() == 1 {
            and_terms[0].clone()
        } else {
            Expr::And(and_terms)
        };
        plan = LogicalPlan::Selection {
            src: Box::new(plan),
            predicate,
        }
    }

    Ok(plan)
}

#[cfg(test)]
mod tests {
    use crate::frontend::tests::plan;
    use crate::frontend::{Dir, Expr, LogicalPlan, Op, Projection};
    use crate::Error;

    #[test]
    fn plan_match_with_anonymous_rel_type() -> Result<(), Error> {
        let mut p = plan("MATCH (n:Person)-->(o)")?;
        let lbl_person = p.tokenize("Person");
        let id_anon = p.tokenize("$anonrel0");
        let id_n = p.tokenize("n");
        let id_o = p.tokenize("o");

        assert_eq!(
            p.plan,
            LogicalPlan::Expand {
                src: Box::new(LogicalPlan::NodeScan {
                    src: Box::new(LogicalPlan::Argument),
                    slot: p.slot(id_n),
                    labels: Some(lbl_person),
                }),
                src_slot: p.slot(id_n),
                rel_slot: p.slot(id_anon),
                dst_slot: p.slot(id_o),
                rel_type: None,
                dir: Some(Dir::Out),
            }
        );
        Ok(())
    }

    #[test]
    fn plan_match_with_selection() -> Result<(), Error> {
        let mut p = plan("MATCH (n:Person)-[r:KNOWS]->(o:Person)")?;
        let lbl_person = p.tokenize("Person");
        let tpe_knows = p.tokenize("KNOWS");
        let id_n = p.tokenize("n");
        let id_r = p.tokenize("r");
        let id_o = p.tokenize("o");

        assert_eq!(
            p.plan,
            LogicalPlan::Selection {
                src: Box::new(LogicalPlan::Expand {
                    src: Box::new(LogicalPlan::NodeScan {
                        src: Box::new(LogicalPlan::Argument),
                        slot: p.slot(id_o),
                        labels: Some(lbl_person),
                    }),
                    src_slot: p.slot(id_o),
                    rel_slot: p.slot(id_r),
                    dst_slot: p.slot(id_n),
                    rel_type: Some(tpe_knows),
                    dir: Some(Dir::In),
                }),
                predicate: Expr::HasLabel(p.slot(id_n), lbl_person)
            }
        );
        Ok(())
    }

    #[test]
    fn plan_match_with_unhoistable_where() -> Result<(), Error> {
        let mut p = plan("MATCH (n) WHERE true = opaque()")?;
        let id_n = p.tokenize("n");
        let id_opaque = p.tokenize("opaque");

        assert_eq!(
            p.plan,
            LogicalPlan::Selection {
                src: Box::new(LogicalPlan::NodeScan {
                    src: Box::new(LogicalPlan::Argument),
                    slot: p.slot(id_n),
                    labels: None,
                }),
                predicate: Expr::BinaryOp {
                    left: Box::new(Expr::Bool(true)),
                    right: Box::new(Expr::FuncCall {
                        name: id_opaque,
                        args: vec![]
                    }),
                    op: Op::Eq
                }
            }
        );
        Ok(())
    }

    #[test]
    fn plan_match_with_bound_rel() -> Result<(), Error> {
        let mut p = plan("MATCH (x)-[r]->(y) WITH r MATCH (a)-[r]->(b)")?;
        let id_x = p.tokenize("x");
        let id_y = p.tokenize("y");
        let id_a = p.tokenize("a");
        let id_b = p.tokenize("b");
        let id_r = p.tokenize("r");

        assert_eq!(
            p.plan,
            LogicalPlan::ExpandRel {
                src: Box::new(LogicalPlan::Project {
                    src: Box::new(LogicalPlan::Expand {
                        src: Box::new(LogicalPlan::NodeScan {
                            src: Box::new(LogicalPlan::Argument),
                            slot: p.slot(id_x),
                            labels: None
                        }),
                        src_slot: 0,
                        rel_slot: p.slot(id_r),
                        dst_slot: p.slot(id_y),
                        rel_type: None,
                        dir: Some(Dir::Out)
                    }),
                    projections: vec![
                        Projection{
                            expr: Expr::RowRef(p.slot(id_r)),
                            alias: id_r,
                            dst: p.slot(id_r)
                        }
                    ] }),
                src_rel_slot: p.slot(id_r),
                start_node_slot: p.slot(id_a),
                end_node_slot: p.slot(id_b)
            }
        );
        Ok(())
    }

    #[test]
    fn plan_match_with_inline_predicate() -> Result<(), Error> {
        let mut p = plan("MATCH (n {name: 'David'})-->(m)")?;
        let id_n = p.tokenize("n");
        let id_m = p.tokenize("m");
        let key_name = p.tokenize("name");

        assert_eq!(
            p.plan,
            LogicalPlan::Expand {
                src: Box::new(LogicalPlan::Selection {
                    src: Box::new(LogicalPlan::NodeScan {
                        src: Box::new(LogicalPlan::Argument),
                        slot: p.slot(id_n),
                        labels: None,
                    }),
                    predicate: Expr::BinaryOp {
                        left: Box::new(Expr::Prop(
                            Box::new(Expr::RowRef(p.slot(id_n))),
                            vec![key_name]
                        )),
                        right: Box::new(Expr::String("David".to_string())),
                        op: Op::Eq
                    }
                }),
                src_slot: p.slot(id_n),
                rel_slot: 2,
                dst_slot: p.slot(id_m),
                rel_type: None,
                dir: Some(Dir::Out)
            }
        );
        Ok(())
    }

    #[test]
    fn plan_optional_match() -> Result<(), Error> {
        let mut p = plan("OPTIONAL MATCH (n) RETURN n")?;
        let id_n = p.tokenize("n");

        assert_eq!(
            p.plan,
            LogicalPlan::ProduceResult {
                src: Box::new(LogicalPlan::Project {
                    src: Box::new(LogicalPlan::Optional {
                        src: Box::new(LogicalPlan::NodeScan {
                            src: Box::new(LogicalPlan::Argument),
                            slot: p.slot(id_n),
                            labels: None,
                        }),
                        slots: vec![p.slot(id_n)]
                    }),
                    projections: vec![Projection {
                        expr: Expr::RowRef(p.slot(id_n)),
                        alias: id_n,
                        dst: p.slot(id_n)
                    }]
                }),
                fields: vec![(id_n, p.slot(id_n))]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_cartesian_product() -> Result<(), Error> {
        let mut p = plan("MATCH (a), (b) RETURN a, b")?;
        let id_a = p.tokenize("a");
        let id_b = p.tokenize("b");

        assert_eq!(
            p.plan,
            LogicalPlan::ProduceResult {
                src: Box::new(LogicalPlan::Project {
                    src: Box::new(LogicalPlan::CartesianProduct {
                        outer: Box::new(LogicalPlan::NodeScan {
                            src: Box::new(LogicalPlan::Argument),
                            slot: p.slot(id_a),
                            labels: None,
                        }),
                        inner: Box::new(LogicalPlan::NodeScan {
                            src: Box::new(LogicalPlan::Argument),
                            slot: p.slot(id_b),
                            labels: None,
                        }),
                        // always-true predicate makes this a cartesian product, every row combo will
                        // match the join condition
                        predicate: Expr::Bool(true),
                    }),
                    projections: vec![
                        Projection {
                            expr: Expr::RowRef(p.slot(id_a)),
                            alias: id_a,
                            dst: p.slot(id_a)
                        },
                        Projection {
                            expr: Expr::RowRef(p.slot(id_b)),
                            alias: id_b,
                            dst: p.slot(id_b)
                        }
                    ]
                }),
                fields: vec![(id_a, p.slot(id_a)), (id_b, p.slot(id_b))]
            }
        );
        Ok(())
    }
}

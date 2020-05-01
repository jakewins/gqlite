use super::{parse_pattern_graph, Dir, Expr, LogicalPlan, Pair, PlanningContext, Result, Rule};
use crate::backend::Token;

pub fn plan_match(
    pc: &mut PlanningContext,
    src: LogicalPlan,
    match_stmt: Pair<Rule>,
) -> Result<LogicalPlan> {
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
    let mut pg = parse_pattern_graph(pc, match_stmt)?;

    if pg.optional {
        // We currently only handle a singular case here, OPTIONAL MATCH with a single unbound node:
        if pg.e.len() > 0 {
            bail!("gqlite does not yet support OPTIONAL MATCH entirely, sorry")
        }

        if pg.predicate.is_some() {
            bail!("gqlite does not yet support OPTIONAL MATCH entirely, sorry")
        }

        let (_, node) = pg.v.iter().next().unwrap();

        let node_slot = pc.get_or_alloc_slot(node.identifier);
        return Ok(LogicalPlan::Optional {
            src: Box::new(LogicalPlan::NodeScan {
                src: Box::new(plan),
                slot: node_slot,
                labels: node.labels.first().cloned(),
            }),
            slots: vec![node_slot],
        });
    }

    // Ok, now we have parsed the pattern into a full graph, time to start solving it
    println!("built pg: {:?}", pg);

    // 1: Loop through all nodes in the pattern and..
    //    - Find any pre-existing bound nodes we could start from
    //    - Pick a candidate start point to use if ^^ doesn't work
    //    - Declare all identifiers introduced
    let mut candidate_id = None;
    let mut pattern_has_bound_nodes = false;
    for id in &pg.v_order {
        if let None = candidate_id {
            candidate_id = Some(id);
        }
        let candidate = pg.v.get_mut(id).unwrap();

        if pc.is_declared(candidate.identifier) {
            // MATCH (n) WITH n MATCH (n)-->(b); "n" is already a bound value, so we start there
            pattern_has_bound_nodes = true;
            candidate.solved = true;
        }

        // If the node is not anonymous, make sure its identifier is declared
        if !candidate.anonymous {
            pc.declare_tok(candidate.identifier)
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
    if !pattern_has_bound_nodes {
        if let Some(candidate_id) = candidate_id {
            let candidate = pg.v.get_mut(candidate_id).unwrap();
            if candidate.labels.len() > 1 {
                panic!("Multiple label match not yet implemented")
            }
            plan = LogicalPlan::NodeScan {
                src: Box::new(plan),
                slot: pc.get_or_alloc_slot(*candidate_id),
                labels: candidate.labels.first().cloned(),
            };
            candidate.solved = true;
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

                // Annoying to have to do this here, maybe move this
                // back up into parse_pattern_graph..
                if !rel.anonymous {
                    pc.declare_tok(rel.identifier);
                }

                let dst = pc.get_or_alloc_slot(right_id);
                let expand = LogicalPlan::Expand {
                    src: Box::new(plan),
                    src_slot: pc.get_or_alloc_slot(left_id),
                    rel_slot: pc.get_or_alloc_slot(rel.identifier),
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

                // Annoying to have to do this here, maybe move this
                // back up into parse_pattern_graph..
                if !rel.anonymous {
                    pc.declare_tok(rel.identifier);
                }

                let dst = pc.get_or_alloc_slot(left_id);
                let expand = LogicalPlan::Expand {
                    src: Box::new(plan),
                    src_slot: pc.get_or_alloc_slot(right_id),
                    rel_slot: pc.get_or_alloc_slot(rel.identifier),
                    dst_slot: dst,
                    rel_type: rel.rel_type,
                    dir: rel.dir.map(Dir::reverse),
                };
                plan = filter_expand(expand, dst, &left_node.labels);
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

                let inner = Box::new(LogicalPlan::NodeScan {
                    src: Box::new(LogicalPlan::Argument),
                    slot: pc.get_or_alloc_slot(v.identifier),
                    labels: v.labels.first().cloned(),
                });
                plan = LogicalPlan::NestLoop {
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
    if let Some(pred) = pg.predicate {
        return Ok(LogicalPlan::Selection {
            src: Box::new(plan),
            predicate: pred,
        });
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
        let id_anon = p.tokenize("AnonRel#0");
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
    fn plan_optional_match() -> Result<(), Error> {
        let mut p = plan("OPTIONAL MATCH (n) RETURN n")?;
        let id_n = p.tokenize("n");

        assert_eq!(
            p.plan,
            LogicalPlan::Return {
                src: Box::new(LogicalPlan::Optional {
                    src: Box::new(LogicalPlan::NodeScan {
                        src: Box::new(LogicalPlan::Argument),
                        slot: p.slot(id_n),
                        labels: None,
                    }),
                    slots: vec![p.slot(id_n)]
                }),
                projections: vec![Projection {
                    expr: Expr::Slot(p.slot(id_n)),
                    alias: id_n,
                    dst: p.slot(id_n)
                }]
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
            LogicalPlan::Return {
                src: Box::new(LogicalPlan::NestLoop {
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
                        expr: Expr::Slot(p.slot(id_a)),
                        alias: id_a,
                        dst: p.slot(id_a)
                    },
                    Projection {
                        expr: Expr::Slot(p.slot(id_b)),
                        alias: id_b,
                        dst: p.slot(id_b)
                    }
                ]
            }
        );
        Ok(())
    }
}

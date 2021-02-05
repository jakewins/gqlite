use super::{
    parse_pattern_graph, Dir, LogicalPlan, NodeSpec, Pair, PlanningContext, RelSpec, Result, Rule,
};
use crate::frontend::{PatternGraph, SideEffect};

pub fn plan_create(
    mut pc: &mut PlanningContext,
    src: LogicalPlan,
    create_stmt: Pair<Rule>,
) -> Result<LogicalPlan> {
    let pg = parse_pattern_graph(pc, create_stmt)?;

    plan_create_patterngraph(&mut pc, src, pg)
}

pub fn plan_create_patterngraph(
    pc: &mut PlanningContext,
    src: LogicalPlan,
    mut pg: PatternGraph,
) -> Result<LogicalPlan> {
    let mut nodes = Vec::new();
    let mut rels = Vec::new();
    for id in pg.v_order {
        if pg.v.get(&id).map(|n| n.solved).unwrap_or(false) {
            // We already know about this node, it isn't meant to be created. ie
            // MATCH (n) CREATE (n)-[:NEWREL]->(newnode)
            continue;
        }

        let node = pg.v.remove(&id).ok_or_else(||anyhow!("failed to parse pattern in query, please report this and include the query you are running"))?;

        pc.unordered_sideffects.insert(SideEffect::AnyNode);
        nodes.push(NodeSpec {
            slot: pc.scoping.lookup_or_allocrow(id),
            labels: node.labels,
            props: node.props,
        });
    }

    if ! pg.e.is_empty() {
        pc.unordered_sideffects.insert(SideEffect::AnyRel);
    }

    for rel in pg.e {
        if !rel.anonymous {
            pc.scoping.declare_tok(rel.identifier);
        }
        match rel.dir {
            Some(Dir::Out) => {
                rels.push(RelSpec {
                    slot: pc.scoping.lookup_or_allocrow(rel.identifier),
                    rel_type: rel.rel_type.ok_or_else(|| {
                        anyhow!("Relationship patterns in CREATE must have a type specified")
                    })?,
                    start_node_slot: pc.scoping.lookup_or_allocrow(rel.left_node),
                    end_node_slot: pc.scoping.lookup_or_allocrow(rel.right_node.unwrap()),
                    props: rel.props,
                });
            }
            Some(Dir::In) => {
                rels.push(RelSpec {
                    slot: pc.scoping.lookup_or_allocrow(rel.identifier),
                    rel_type: rel.rel_type.ok_or_else(|| {
                        anyhow!("Relationship patterns in CREATE must have a type specified")
                    })?,
                    start_node_slot: pc.scoping.lookup_or_allocrow(rel.right_node.unwrap()),
                    end_node_slot: pc.scoping.lookup_or_allocrow(rel.left_node),
                    props: vec![],
                });
            }
            None => bail!("relationships in CREATE clauses must have a direction"),
        }
    }

    Ok(LogicalPlan::Create {
        src: Box::new(src),
        scope: pc.scoping.current_scope_no(),
        nodes,
        rels,
    })
}

#[cfg(test)]
mod tests {
    use crate::frontend::tests::plan;
    use crate::frontend::{Expr, LogicalPlan, MapEntryExpr, NodeSpec, RelSpec};
    use crate::Error;

    #[test]
    fn plan_create() -> Result<(), Error> {
        let mut p = plan("CREATE (n:Person)")?;

        let lbl_person = p.tokenize("Person");
        let id_n = p.tokenize("n");
        assert_eq!(
            p.plan,
            LogicalPlan::Create {
                src: Box::new(LogicalPlan::Argument),
                scope: 1,
                nodes: vec![NodeSpec {
                    slot: p.slot(id_n),
                    labels: vec![lbl_person],
                    props: vec![]
                }],
                rels: vec![]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_create_no_label() -> Result<(), Error> {
        let mut p = plan("CREATE (n)")?;

        let id_n = p.tokenize("n");
        assert_eq!(
            p.plan,
            LogicalPlan::Create {
                src: Box::new(LogicalPlan::Argument),
                scope: 1,
                nodes: vec![NodeSpec {
                    slot: p.slot(id_n),
                    labels: vec![],
                    props: vec![]
                }],
                rels: vec![]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_create_multiple_labels() -> Result<(), Error> {
        let mut p = plan("CREATE (n:Person:Actor)")?;

        let id_n = p.tokenize("n");
        let lbl_person = p.tokenize("Person");
        let lbl_actor = p.tokenize("Actor");

        assert_eq!(
            p.plan,
            LogicalPlan::Create {
                src: Box::new(LogicalPlan::Argument),
                scope: 1,
                nodes: vec![NodeSpec {
                    slot: p.slot(id_n),
                    labels: vec![lbl_person, lbl_actor],
                    props: vec![]
                }],
                rels: vec![]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_create_with_props() -> Result<(), Error> {
        let mut p = plan("CREATE (n:Person {name: \"Bob\"})")?;

        let lbl_person = p.tokenize("Person");
        let id_n = p.tokenize("n");
        let key_name = p.tokenize("name");
        assert_eq!(
            p.plan,
            LogicalPlan::Create {
                src: Box::new(LogicalPlan::Argument),
                scope: 1,
                nodes: vec![NodeSpec {
                    slot: p.slot(id_n),
                    labels: vec![lbl_person],
                    props: vec![MapEntryExpr {
                        key: key_name,
                        val: Expr::String("Bob".to_string()),
                    }]
                }],
                rels: vec![]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_create_rel() -> Result<(), Error> {
        let mut p = plan("CREATE (n:Person)-[r:KNOWS]->(n)")?;

        let rt_knows = p.tokenize("KNOWS");
        let lbl_person = p.tokenize("Person");
        let id_n = p.tokenize("n");
        let id_r = p.tokenize("r");
        assert_eq!(
            p.plan,
            LogicalPlan::Create {
                src: Box::new(LogicalPlan::Argument),
                scope: 1,
                nodes: vec![NodeSpec {
                    slot: p.slot(id_n),
                    labels: vec![lbl_person],
                    props: vec![]
                }],
                rels: vec![RelSpec {
                    slot: p.slot(id_r),
                    rel_type: rt_knows,
                    start_node_slot: p.slot(id_n),
                    end_node_slot: p.slot(id_n),
                    props: vec![]
                },]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_create_disjoint_patterns() -> Result<(), Error> {
        let mut p = plan("CREATE (a:A), (), (a)-[:KNOWS]->()")?;

        let rt_knows = p.tokenize("KNOWS");
        let lbl_a = p.tokenize("A");
        let id_a = p.tokenize("a");
        assert_eq!(
            p.plan,
            LogicalPlan::Create {
                src: Box::new(LogicalPlan::Argument),
                scope: 1,
                nodes: vec![
                    NodeSpec {
                        slot: p.slot(id_a),
                        labels: vec![lbl_a],
                        props: vec![]
                    },
                    NodeSpec {
                        slot: 1,
                        labels: vec![],
                        props: vec![]
                    },
                    NodeSpec {
                        slot: 2,
                        labels: vec![],
                        props: vec![]
                    }
                ],
                rels: vec![RelSpec {
                    slot: 3,
                    rel_type: rt_knows,
                    start_node_slot: p.slot(id_a),
                    end_node_slot: 2,
                    props: vec![]
                },]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_create_rel_with_props() -> Result<(), Error> {
        let mut p = plan("CREATE (n:Person)-[r:KNOWS {since:\"2012\"}]->(n)")?;

        let rt_knows = p.tokenize("KNOWS");
        let lbl_person = p.tokenize("Person");
        let id_n = p.tokenize("n");
        let id_r = p.tokenize("r");
        let k_since = p.tokenize("since");
        assert_eq!(
            p.plan,
            LogicalPlan::Create {
                src: Box::new(LogicalPlan::Argument),
                scope: 1,
                nodes: vec![NodeSpec {
                    slot: p.slot(id_n),
                    labels: vec![lbl_person],
                    props: vec![]
                }],
                rels: vec![RelSpec {
                    slot: p.slot(id_r),
                    rel_type: rt_knows,
                    start_node_slot: p.slot(id_n),
                    end_node_slot: p.slot(id_n),
                    props: vec![MapEntryExpr {
                        key: k_since,
                        val: Expr::String("2012".to_string())
                    },]
                },]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_create_outbound_rel_on_preexisting_node() -> Result<(), Error> {
        let mut p = plan("MATCH (n:Person) CREATE (n)-[r:KNOWS]->(o:Person)")?;

        let rt_knows = p.tokenize("KNOWS");
        let lbl_person = p.tokenize("Person");
        let id_n = p.tokenize("n");
        let id_o = p.tokenize("o");
        let id_r = p.tokenize("r");
        assert_eq!(
            p.plan,
            LogicalPlan::Create {
                src: Box::new(LogicalPlan::NodeScan {
                    src: Box::new(LogicalPlan::Argument),
                    scope: 1,
                    slot: p.slot(id_n),
                    labels: Some(lbl_person),
                }),
                scope: 1,
                nodes: vec![
                    // Note there is just one node here, the planner should understand "n" already exists
                    NodeSpec {
                        slot: p.slot(id_o),
                        labels: vec![lbl_person],
                        props: vec![]
                    }
                ],
                rels: vec![RelSpec {
                    slot: p.slot(id_r),
                    rel_type: rt_knows,
                    start_node_slot: p.slot(id_n),
                    end_node_slot: p.slot(id_o),
                    props: vec![]
                },]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_create_referring_to_prop_in_same_create_stmt() -> Result<(), Error> {
        // It's not entirely clear *why* this is a useful feature, or what the semantics
        // of the ordering here is, so if you come back here and are confused.. you're not
        // missing something. However, this is part of a setup statement in the TCK, so we need
        // it to work this specific way to pass the TCK
        // Note that if you invert it (so the (b) node comes first) then the num property is set
        // to null in Neo4j Cypher (as of 3.5 at least).
        let mut p = plan("CREATE (a {id: 0}), (b {num: a.id})")?;

        let id_a = p.tokenize("a");
        let id_b = p.tokenize("b");
        let key_num = p.tokenize("num");
        let key_id = p.tokenize("id");
        assert_eq!(
            p.plan,
            LogicalPlan::Create {
                src: Box::new(LogicalPlan::Argument),
                scope: 1,
                nodes: vec![
                    NodeSpec {
                        slot: p.slot(id_a),
                        labels: vec![],
                        props: vec![MapEntryExpr {
                            key: key_id,
                            val: Expr::Int(0)
                        }]
                    },
                    NodeSpec {
                        slot: p.slot(id_b),
                        labels: vec![],
                        props: vec![MapEntryExpr {
                            key: key_num,
                            val: Expr::Prop(Box::new(Expr::RowRef(p.slot(id_a))), vec![key_id])
                        }]
                    }
                ],
                rels: vec![]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_create_inbound_rel_on_preexisting_node() -> Result<(), Error> {
        let mut p = plan("MATCH (n:Person) CREATE (n)<-[r:KNOWS]-(o:Person)")?;

        let rt_knows = p.tokenize("KNOWS");
        let lbl_person = p.tokenize("Person");
        let id_n = p.tokenize("n");
        let id_o = p.tokenize("o");
        let id_r = p.tokenize("r");
        assert_eq!(
            p.plan,
            LogicalPlan::Create {
                src: Box::new(LogicalPlan::NodeScan {
                    src: Box::new(LogicalPlan::Argument),
                    scope: 1,
                    slot: p.slot(id_n),
                    labels: Some(lbl_person),
                }),
                scope: 1,
                nodes: vec![
                    // Note there is just one node here, the planner should understand "n" already exists
                    NodeSpec {
                        slot: p.slot(id_o),
                        labels: vec![lbl_person],
                        props: vec![]
                    }
                ],
                rels: vec![RelSpec {
                    slot: p.slot(id_r),
                    rel_type: rt_knows,
                    start_node_slot: p.slot(id_o),
                    end_node_slot: p.slot(id_n),
                    props: vec![]
                },]
            }
        );
        Ok(())
    }
}

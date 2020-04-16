use super::{
    parse_pattern_graph, Dir, LogicalPlan, NodeSpec, Pair, PlanningContext, RelSpec, Result, Rule,
};

pub fn plan_create(
    pc: &mut PlanningContext,
    src: LogicalPlan,
    create_stmt: Pair<Rule>,
) -> Result<LogicalPlan> {
    let mut pg = parse_pattern_graph(pc, create_stmt)?;

    let mut nodes = Vec::new();
    let mut rels = Vec::new();
    for id in pg.e_order {
        if pc.is_bound(id) {
            // We already know about this node, it isn't meant to be created. ie
            // MATCH (n) CREATE (n)-[:NEWREL]->(newnode)
            continue;
        }
        let node = pg.e.remove(&id).ok_or(anyhow!("failed to parse pattern in query, please report this and include the query you are running"))?;
        nodes.push(NodeSpec {
            slot: pc.get_or_alloc_slot(id),
            labels: node.labels,
            props: node.props,
        });
    }

    for rel in pg.v {
        match rel.dir {
            Some(Dir::Out) => {
                rels.push(RelSpec {
                    slot: pc.get_or_alloc_slot(rel.identifier),
                    rel_type: rel.rel_type.ok_or(anyhow!(
                        "Relationship patterns in CREATE must have a type specified"
                    ))?,
                    start_node_slot: pc.get_or_alloc_slot(rel.left_node),
                    end_node_slot: pc.get_or_alloc_slot(rel.right_node.unwrap()),
                    props: rel.props,
                });
            }
            Some(Dir::In) => {
                rels.push(RelSpec {
                    slot: pc.get_or_alloc_slot(rel.identifier),
                    rel_type: rel.rel_type.ok_or(anyhow!(
                        "Relationship patterns in CREATE must have a type specified"
                    ))?,
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
                    slot: p.slot(id_n),
                    labels: Some(lbl_person),
                }),
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
                    slot: p.slot(id_n),
                    labels: Some(lbl_person),
                }),
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

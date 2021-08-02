use super::{plan_expr, Expr, LogicalPlan, Pair, PlanningContext, Projection, Result, Rule};
use crate::frontend::{Scoping, ScopingMode};
use core::mem;
use pest::iterators::Pairs;

pub fn plan_with(
    pc: &mut PlanningContext,
    src: LogicalPlan,
    stmt: Pair<Rule>,
) -> Result<LogicalPlan> {
    let parts = stmt.into_inner();
    let projections = parse_projections(pc, parts)?;
    let mut plan = plan_parsed_with(pc, src, projections)?;

    // WITH statements introduce logical "happens before" / "happens after" execution constraints;
    // side-effects from stuff above the WITH are visible after it.
    // Enforcing this logical order is potentially extremely expensive, and so we really don't
    // want to do it unless we have to.

    // The ordering enforcement is only needed if there are side-effects without ordering
    // guarantees "upstream" in the plan.
    // The intent here is that the side-effects calculation can get smarter over time, so that
    // we only include the Barrier if there are activities later on that may see the side-effects
    if pc.unordered_sideffects.len() > 0 {
        let sideffects = mem::replace(&mut pc.unordered_sideffects, Default::default());
        plan = LogicalPlan::Barrier {
            src: Box::new(plan),
            spec: sideffects,
        }
    }

    Ok(plan)
}

// This is shared between the RETURN and WITH plan functions
fn plan_parsed_with(
    pc: &mut PlanningContext,
    src: LogicalPlan,
    projections: Projections,
) -> Result<LogicalPlan> {
    // Simple case, no need to do a bunch of introspection
    let mut plan = if !projections.is_aggregating && !projections.is_distinct {
        LogicalPlan::Project {
            src: Box::new(src),
            projections: projections.projections,
        }
    } else {
        plan_aggregation(pc, src, projections.projections)?
    };

    if let Some(e) = projections.selection {
        plan = LogicalPlan::Selection {
            src: Box::new(plan),
            predicate: e,
        };
    }

    // TODO: The plan nodes should somehow track metadata about what they promise wrt order
    //       and distinctness. If we know the source is sorted, we can skip this (like if we
    //       are using an index). Likewise if you know there won't be repeats you can do
    //       grouped aggregation rather than hash aggregation. And, if you know the result is
    //       partially sorted (like by a prefix), you can do partial sort.. etc.
    if let Some(e) = projections.sort {
        plan = LogicalPlan::Sort {
            src: Box::new(plan),
            sort_by: e,
        }
    }

    if projections.limit.is_some() || projections.skip.is_some() {
        plan = LogicalPlan::Limit {
            src: Box::new(plan),
            skip: projections.skip,
            limit: projections.limit,
        }
    }

    Ok(plan)
}

pub fn plan_aggregation(
    pc: &mut PlanningContext,
    src: LogicalPlan,
    projections: Vec<Projection>,
) -> Result<LogicalPlan> {
    // This is a good thing to have read when thinking about aggregations:
    // https://github.com/postgres/postgres/blob/master/src/backend/executor/nodeAgg.c

    let mut post_aggregation_projections = Vec::new();
    let mut grouping = Vec::new();
    let mut aggregations = Vec::new();
    for p in projections {
        if p.expr.is_aggregating(&pc.backend_desc.aggregates) {
            aggregations.push((p.expr, p.dst))
        } else {
            grouping.push((p.expr, p.dst))
        }
        // After the aggregation we still have a projection, for now at least, that
        // exists only to define the order and aliasing of the slots
        post_aggregation_projections.push(Projection {
            expr: Expr::RowRef(p.dst),
            alias: p.alias,
            dst: p.dst,
        })
    }

    Ok(LogicalPlan::Project {
        src: Box::new(LogicalPlan::Aggregate {
            src: Box::new(src),
            grouping,
            aggregations,
        }),
        projections: post_aggregation_projections,
    })
}

pub fn plan_return(
    pc: &mut PlanningContext,
    src: LogicalPlan,
    stmt: Pair<Rule>,
) -> Result<LogicalPlan> {
    let parts = stmt.into_inner();
    let projections: Projections = parse_projections(pc, parts)?;

    let mut fields = Vec::with_capacity(projections.projections.len());
    for p in &projections.projections {
        fields.push((p.alias, p.dst));
    }

    let result = plan_parsed_with(pc, src, projections)?;
    Ok(LogicalPlan::ProduceResult {
        src: Box::new(result),
        fields,
    })
}

struct Projections {
    projections: Vec<Projection>,
    is_distinct: bool,
    // Does the projection include explicit aggregating expressions, more than just "DISTINCT"?
    is_aggregating: bool,
    selection: Option<Expr>,
    sort: Option<Vec<Expr>>,
    skip: Option<Expr>,
    limit: Option<Expr>,
}

fn parse_projections(pc: &mut PlanningContext, parts: Pairs<Rule>) -> Result<Projections> {
    let mut projections = Vec::new();
    let mut is_distinct = false;
    let mut is_aggregating = false;
    let mut skip = None;
    let mut limit = None;
    let mut selection = None;
    let mut sort = None;

    pc.scoping.begin_new_scope();

    for part in parts {
        match part.as_rule() {
            Rule::distinct_clause => {
                is_distinct = true;
            }
            // WITH a as b, count(c); aka normal explicit projection
            Rule::projections => {
                for projection in part.into_inner() {
                    let p = parse_projection(projection, &mut pc.scoping)?;
                    is_aggregating =
                        is_aggregating || p.expr.is_aggregating(&pc.backend_desc.aggregates);
                    projections.push(p);
                }
            }
            // WITH *
            Rule::project_all => {
                for id in &pc.scoping._prior.named_identifiers {
                    let slot = *pc.scoping._prior.slots.get(id).unwrap();
                    pc.scoping._current.slots.insert(*id, slot);
                    projections.push(Projection {
                        expr: Expr::RowRef(slot),
                        alias: *id,
                        dst: slot,
                    });
                }
                let tokens = pc.scoping.tokens.borrow();
                projections.sort_by(|a, b| {
                    let a_str = tokens.lookup(a.alias);
                    let b_str = tokens.lookup(b.alias);
                    a_str.cmp(&b_str)
                });
            }
            Rule::where_clause => {
                let where_expr = part
                    .into_inner()
                    .next()
                    .ok_or_else(|| anyhow!("WHERE contained unexpected part"))?;
                let prior_mode = mem::replace(&mut pc.scoping.mode, ScopingMode::ProjectionMode);
                let maybe_where_expr = plan_expr(&mut pc.scoping, where_expr);
                pc.scoping.mode = prior_mode;
                selection = Some(maybe_where_expr?);
            }
            Rule::skip_clause => {
                let skip_expr = part
                    .into_inner()
                    .next()
                    .ok_or_else(|| anyhow!("SKIP contained unexpected part"))?;
                skip = Some(plan_expr(&mut pc.scoping, skip_expr)?);
            }
            Rule::limit_clause => {
                let limit_expr = part
                    .into_inner()
                    .next()
                    .ok_or_else(|| anyhow!("LIMIT contained unexpected part"))?;
                limit = Some(plan_expr(&mut pc.scoping, limit_expr)?);
            }
            Rule::order_clause => {
                let mut out = Vec::new();
                for sort_group in part.into_inner() {
                    let sort_expr = sort_group
                        .into_inner()
                        .next()
                        .ok_or_else(|| anyhow!("SORT contained unexpected part"))?;
                    let planned_sort_expr =
                        plan_order_key_expression(&mut pc.scoping, &projections, sort_expr)?;
                    out.push(planned_sort_expr)
                }
                sort = Some(out);
            }
            _ => bail!("unexpected part of WITH or RETURN: {:?}", part),
        }
    }

    Ok(Projections {
        projections,
        is_distinct,
        is_aggregating,
        selection,
        sort,
        skip,
        limit,
    })
}

// See OrderByMode on Scoping
fn plan_order_key_expression(
    scoping: &mut Scoping,
    projections: &[Projection],
    expression: Pair<Rule>,
) -> Result<Expr> {
    // Enter special ORDER BY scoping mode, see OrderByMode
    let original_scoping_mode = mem::replace(&mut scoping.mode, ScopingMode::ProjectionMode);
    let maybe_sortkey = plan_expr(scoping, expression);
    scoping.mode = original_scoping_mode;
    let sortkey = maybe_sortkey?;

    for proj in projections {
        // Sort expression is explicitly the exact same as expression used in aggregation
        if sortkey == proj.expr {
            return Ok(Expr::RowRef(proj.dst));
        }

        match &sortkey {
            Expr::Prop(entity, _) => {
                // Sort expression is a property of a map or entity we're using in the projection
                if **entity == proj.expr {
                    return Ok(sortkey);
                }
            }
            // Sort key is a slot produced by the projection
            Expr::RowRef(slot) => {
                if *slot == proj.dst {
                    return Ok(sortkey);
                }
            }

            _ => (),
        }
    }

    bail!("Can't sort by {:?}, because the planner can't tell if it is used in DISTINCT or aggregation, so is not sure if it is visible to the sorting step", sortkey)
}

fn parse_projection(projection: Pair<Rule>, scoping: &mut Scoping) -> Result<Projection> {
    let default_alias = projection.as_str();
    let mut parts = projection.into_inner();

    scoping.mode = ScopingMode::Prior;
    let expr = parts.next().map(|p| plan_expr(scoping, p)).unwrap()?;
    scoping.mode = ScopingMode::Current;

    let alias = parts
        .next()
        .and_then(|p| match p.as_rule() {
            Rule::id => Some(scoping.declare(p.as_str())),
            _ => None,
        })
        .unwrap_or_else(|| scoping.declare(default_alias.trim_end()));

    // If we're just renaming stuff, don't bother assigning new slots, just rename the existing one
    if let Expr::RowRef(slot) = expr {
        scoping._current.slots.insert(alias, slot);
    };

    Ok(Projection {
        expr,
        alias,
        dst: scoping.lookup_or_allocrow(alias),
    })
}

#[cfg(test)]
mod tests {
    use crate::frontend::tests::plan;
    use crate::frontend::{Dir, Expr, LogicalPlan, Op, Projection, NodeSpec, SideEffect, Depth};
    use crate::Error;

    #[test]
    fn plan_noop_with() -> Result<(), Error> {
        let mut p = plan("MATCH (n) WITH n")?;

        let id_n = p.tokenize("n");
        assert_eq!(
            p.plan,
            LogicalPlan::Project {
                src: Box::new(LogicalPlan::NodeScan {
                    src: Box::new(LogicalPlan::Argument),
                    phase: 0,
                    slot: 0,
                    labels: None,
                }),
                projections: vec![Projection {
                    expr: Expr::RowRef(p.slot(id_n)),
                    alias: id_n,
                    dst: p.slot(id_n),
                }],
            }
        );
        Ok(())
    }

    #[test]
    fn plan_with_aliased() -> Result<(), Error> {
        let mut p = plan("MATCH (n) WITH n as p")?;

        let id_n = p.tokenize("n");
        let id_p = p.tokenize("p");
        assert_eq!(
            p.plan,
            LogicalPlan::Project {
                src: Box::new(LogicalPlan::NodeScan {
                    src: Box::new(LogicalPlan::Argument),
                    phase: 0,
                    slot: 0,
                    labels: None,
                }),
                projections: vec![Projection {
                    expr: Expr::RowRef(p.slot(id_n)),
                    alias: id_p,
                    dst: p.slot(id_p),
                }],
            }
        );
        Ok(())
    }

    #[test]
    fn plan_with_visible_sideffects_has_barrier() -> Result<(), Error> {
        let mut p = plan("CREATE (n) WITH 1 as p")?;

        let id_p = p.tokenize("p");
        assert_eq!(
            p.plan,
            LogicalPlan::Barrier {
                src: Box::new(LogicalPlan::Project {
                    src: Box::new(LogicalPlan::Create {
                        src: Box::new(LogicalPlan::Argument),
                        phase: 0,
                        nodes: vec![NodeSpec{
                            slot: 0,
                            labels: vec![],
                            props: vec![]
                        }],
                        rels: vec![]
                    }),
                    projections: vec![Projection {
                        expr: Expr::Int(1),
                        alias: id_p,
                        dst: p.slot(id_p),
                    }],
                }),
                spec: [SideEffect::AnyNode].iter().cloned().collect(),
            }
        );
        Ok(())
    }


    #[test]
    fn plan_with_two_withs_only_has_one_barrier() -> Result<(), Error> {
        let mut p = plan("CREATE (n) WITH 1 as p MATCH (m) WITH 2 as o")?;

        let id_m = p.tokenize("m");
        let id_p = p.tokenize("p");
        let id_o = p.tokenize("o");
        assert_eq!(
            p.plan,
            LogicalPlan::Project {
                src: Box::new(LogicalPlan::NodeScan {
                    src: Box::new(LogicalPlan::Barrier {
                        src: Box::new(LogicalPlan::Project {
                            src: Box::new(LogicalPlan::Create {
                                src: Box::new(LogicalPlan::Argument),
                                phase: 0,
                                nodes: vec![NodeSpec{
                                    slot: 0,
                                    labels: vec![],
                                    props: vec![]
                                }],
                                rels: vec![]
                            }),
                            projections: vec![Projection {
                                expr: Expr::Int(1),
                                alias: id_p,
                                dst: p.slot(id_p),
                            }],
                        }),
                        spec: [SideEffect::AnyNode].iter().cloned().collect(),
                    }),
                    phase: 0,
                    slot: p.slot(id_m),
                    labels: None
                }),
                projections: vec![Projection {
                    expr: Expr::Int(2),
                    alias: id_o,
                    dst: p.slot(id_o),
                }],
            }
        );
        Ok(())
    }

    #[test]
    fn plan_with_order_skip() -> Result<(), Error> {
        let mut p = plan("WITH 1 as p ORDER BY p SKIP 1")?;

        let id_p = p.tokenize("p");
        assert_eq!(
            p.plan,
            LogicalPlan::Limit {
                src: Box::new(LogicalPlan::Sort {
                    src: Box::new(LogicalPlan::Project {
                        src: Box::new(LogicalPlan::Argument),
                        projections: vec![Projection {
                            expr: Expr::Int(1),
                            alias: id_p,
                            dst: p.slot(id_p),
                        }],
                    }),
                    sort_by: vec![Expr::RowRef(p.slot(id_p))]
                }),
                skip: Some(Expr::Int(1)),
                limit: None,
            }
        );
        Ok(())
    }

    // TODO technically the project is not needed here.. we're just renaming references..
    // TODO the barrier is also not needed
    #[test]
    fn plan_with_limit() -> Result<(), Error> {
        let mut p = plan("MATCH (n) WITH n as p LIMIT 1")?;

        let id_n = p.tokenize("n");
        let id_p = p.tokenize("p");
        assert_eq!(
            p.plan,
            LogicalPlan::Limit {
                src: Box::new(LogicalPlan::Project {
                    src: Box::new(LogicalPlan::NodeScan {
                        src: Box::new(LogicalPlan::Argument),
                        phase: 0,
                        slot: 0,
                        labels: None,
                    }),
                    projections: vec![Projection {
                        expr: Expr::RowRef(p.slot(id_n)),
                        alias: id_p,
                        dst: p.slot(id_p),
                    }],
                }),
                skip: None,
                limit: Some(Expr::Int(1)),
            }
        );
        Ok(())
    }

    #[test]
    fn plan_with_swap_identifiers() -> Result<(), Error> {
        // Eg. a as b, b as tmp should not cause the slot holding `b` to be overwritten by `a`
        let mut p = plan("MATCH (a:A)-[r:REL]->(b:B) WITH a AS b, b AS tmp, r AS r")?;

        let _id_a = p.tokenize("a");
        let id_b = p.tokenize("b");
        let id_tmp = p.tokenize("tmp");
        let id_r = p.tokenize("r");

        let projections = if let LogicalPlan::Project {
            src: _,
            projections,
        } = &p.plan
        {
            projections.clone().to_vec()
        } else {
            panic!("Expected plan to be a projection, got {:?}", p.plan)
        };

        assert_eq!(
            projections,
            vec![
                Projection {
                    expr: Expr::RowRef(p.slot(id_b)),
                    alias: id_b,
                    dst: p.slot(id_b),
                },
                Projection {
                    expr: Expr::RowRef(p.slot(id_tmp)),
                    alias: id_tmp,
                    dst: p.slot(id_tmp),
                },
                Projection {
                    expr: Expr::RowRef(p.slot(id_r)),
                    alias: id_r,
                    dst: p.slot(id_r),
                }
            ]
        );
        Ok(())
    }

    #[test]
    fn plan_with_swap_and_introduce_identifiers() -> Result<(), Error> {
        // see plan_with_swap_identifiers; trick here is that we're also introducing new stuff,
        // and the planner needs to tiptoe a bit to not accidentally re-use in-use slots
        let mut p = plan("MATCH (a:A)-[r:REL]->(b:B) WITH a AS b, 1 AS one, r AS r")?;

        let id_b = p.tokenize("b");
        let id_one = p.tokenize("one");
        let id_r = p.tokenize("r");

        let projections = if let LogicalPlan::Project {
            src: _,
            projections,
        } = &p.plan
        {
            projections.clone().to_vec()
        } else {
            panic!("Expected plan to be a projection, got {:?}", p.plan)
        };

        assert_eq!(
            projections,
            vec![
                Projection {
                    expr: Expr::RowRef(p.slot(id_b)),
                    alias: id_b,
                    dst: p.slot(id_b),
                },
                Projection {
                    expr: Expr::Int(1),
                    alias: id_one,
                    dst: p.slot(id_one),
                },
                Projection {
                    expr: Expr::RowRef(p.slot(id_r)),
                    alias: id_r,
                    dst: p.slot(id_r),
                }
            ]
        );
        Ok(())
    }

    #[test]
    fn plan_with_order() -> Result<(), Error> {
        let mut p = plan("MATCH (n) WITH n.name as name ORDER BY name")?;

        let id_n = p.tokenize("n");
        let key_name = p.tokenize("name");
        assert_eq!(
            p.plan,
            LogicalPlan::Sort {
                src: Box::new(LogicalPlan::Project {
                    src: Box::new(LogicalPlan::NodeScan {
                        src: Box::new(LogicalPlan::Argument),
                        phase: 0,
                        slot: 0,
                        labels: None,
                    }),
                    projections: vec![Projection {
                        expr: Expr::Prop(Box::new(Expr::RowRef(p.slot(id_n))), vec![key_name]),
                        alias: key_name,
                        dst: p.slot(key_name),
                    }],
                }),
                sort_by: vec![Expr::RowRef(p.slot(key_name))]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_with_order_by_expression_from_aggregation() -> Result<(), Error> {
        let mut p = plan("MATCH (n) WITH n, count(*) ORDER BY count(*)")?;

        let id_n = p.tokenize("n");
        let id_count_call = p.tokenize("count(*)");
        let fn_count = p.tokenize("count");
        assert_eq!(
            p.plan,
            LogicalPlan::Sort {
                src: Box::new(LogicalPlan::Project {
                    src: Box::new(LogicalPlan::Aggregate {
                        src: Box::new(LogicalPlan::NodeScan {
                            src: Box::new(LogicalPlan::Argument),
                            phase: 0,
                            slot: 0,
                            labels: None,
                        }),
                        grouping: vec![(Expr::RowRef(p.slot(id_n)), p.slot(id_n))],
                        aggregations: vec![(
                            Expr::FuncCall {
                                name: fn_count,
                                args: vec![]
                            },
                            p.slot(id_count_call)
                        )]
                    }),
                    projections: vec![
                        Projection {
                            expr: Expr::RowRef(p.slot(id_n)),
                            alias: id_n,
                            dst: p.slot(id_n),
                        },
                        Projection {
                            expr: Expr::RowRef(p.slot(id_count_call)),
                            alias: id_count_call,
                            dst: p.slot(id_count_call),
                        }
                    ],
                }),
                sort_by: vec![Expr::RowRef(p.slot(id_count_call))]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_with_order_repeating_aliased_aggregated_expression() -> Result<(), Error> {
        // Not sure at all that this is the right thing here, but basically:
        // If you've got a query that does some aggregation, and then orders by the aggregate
        // key, it is legal to use the expression you used in the aggregation in the order by
        // rather than the alias. Eg. you can do the query in this test. But you can't do
        // *other* expressions, like you couldn't do n.age here.
        let mut p = plan("MATCH (n) WITH DISTINCT n.name as name ORDER BY n.name")?;

        let id_n = p.tokenize("n");
        let key_name = p.tokenize("name");
        assert_eq!(
            p.plan,
            LogicalPlan::Sort {
                src: Box::new(LogicalPlan::Project {
                    src: Box::new(LogicalPlan::Aggregate {
                        src: Box::new(LogicalPlan::NodeScan {
                            src: Box::new(LogicalPlan::Argument),
                            phase: 0,
                            slot: 0,
                            labels: None,
                        }),
                        grouping: vec![(
                            Expr::Prop(Box::new(Expr::RowRef(p.slot(id_n))), vec![key_name]),
                            p.slot(key_name)
                        )],
                        aggregations: vec![]
                    }),
                    projections: vec![Projection {
                        expr: Expr::RowRef(p.slot(key_name)),
                        alias: key_name,
                        dst: p.slot(key_name),
                    }],
                }),
                sort_by: vec![Expr::RowRef(p.slot(key_name))]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_with_order_by_nested_property_of_aggregate() -> Result<(), Error> {
        // Eg. we aggregate by "n" and then order by n.name, a nested property of the aggregate
        let mut p = plan("MATCH (n) WITH DISTINCT n ORDER BY n.name")?;

        let id_n = p.tokenize("n");
        let key_name = p.tokenize("name");
        assert_eq!(
            p.plan,
            LogicalPlan::Sort {
                src: Box::new(LogicalPlan::Project {
                    src: Box::new(LogicalPlan::Aggregate {
                        src: Box::new(LogicalPlan::NodeScan {
                            src: Box::new(LogicalPlan::Argument),
                            phase: 0,
                            slot: 0,
                            labels: None,
                        }),
                        grouping: vec![(Expr::RowRef(p.slot(id_n)), p.slot(id_n))],
                        aggregations: vec![]
                    }),
                    projections: vec![Projection {
                        expr: Expr::RowRef(p.slot(id_n)),
                        alias: id_n,
                        dst: p.slot(id_n),
                    }],
                }),
                sort_by: vec![Expr::Prop(
                    Box::new(Expr::RowRef(p.slot(id_n))),
                    vec![key_name]
                )]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_with_where() -> Result<(), Error> {
        let mut p = plan("MATCH (n) WITH n WHERE n.name = 'bob'")?;

        // TODO while in this particular case this is an ok plan, if there were skip/limit
        //      involved then doing the selection afterwards won't fly; it needs to go
        //      between the projection and the skip/limit
        let id_n = p.tokenize("n");
        let key_name = p.tokenize("name");
        assert_eq!(
            p.plan,
            LogicalPlan::Selection {
                src: Box::new(LogicalPlan::Project {
                    src: Box::new(LogicalPlan::NodeScan {
                        src: Box::new(LogicalPlan::Argument),
                        phase: 0,
                        slot: 0,
                        labels: None,
                    }),
                    projections: vec![Projection {
                        expr: Expr::RowRef(p.slot(id_n)),
                        alias: id_n,
                        dst: p.slot(id_n),
                    }],
                }),
                predicate: Expr::BinaryOp {
                    left: Box::new(Expr::Prop(
                        Box::new(Expr::RowRef(p.slot(id_n))),
                        vec![key_name]
                    )),
                    right: Box::new(Expr::String("bob".to_string())),
                    op: Op::Eq
                }
            }
        );
        Ok(())
    }

    #[test]
    fn plan_with_where_referring_to_prior_scope() -> Result<(), Error> {
        let mut p = plan("MATCH (n) WITH n.name AS name WHERE n.name = 'bob'")?;
        let id_n = p.tokenize("n");
        let key_name = p.tokenize("name");
        assert_eq!(
            p.plan,
            LogicalPlan::Selection {
                src: Box::new(LogicalPlan::Project {
                    src: Box::new(LogicalPlan::NodeScan {
                        src: Box::new(LogicalPlan::Argument),
                        phase: 0,
                        slot: 0,
                        labels: None,
                    }),
                    projections: vec![Projection {
                        expr: Expr::Prop(Box::new(Expr::RowRef(p.slot(id_n))), vec![key_name]),
                        alias: key_name,
                        dst: p.slot(key_name),
                    }],
                }),
                predicate: Expr::BinaryOp {
                    left: Box::new(Expr::Prop(
                        Box::new(Expr::RowRef(p.slot(id_n))),
                        vec![key_name]
                    )),
                    right: Box::new(Expr::String("bob".to_string())),
                    op: Op::Eq
                }
            }
        );
        Ok(())
    }

    #[test]
    fn plan_with_basic_scoping() -> Result<(), Error> {
        // The RETURN * should only see 'a' because the WITH scopes away the `z`
        let mut p = plan("MATCH (a)-->(z) WITH a RETURN *")?;

        let id_a = p.tokenize("a");
        let id_z = p.tokenize("z");
        assert_eq!(
            p.plan,
            LogicalPlan::ProduceResult {
                src: Box::new(LogicalPlan::Project {
                    src: Box::new(LogicalPlan::Project {
                        src: Box::new(LogicalPlan::Expand {
                            src: Box::new(LogicalPlan::NodeScan {
                                src: Box::new(LogicalPlan::Argument),
                                phase: 0,
                                slot: p.slot(id_a),
                                labels: None,
                            }),
                            phase: 0,
                            src_slot: p.slot(id_a),
                            rel_slot: Some(2),
                            dst_slot: p.slot(id_z),
                            rel_type: None,
                            dir: Some(Dir::Out),
                            depth: Depth::Exact(1),
                        }),
                        projections: vec![Projection {
                            expr: Expr::RowRef(p.slot(id_a)),
                            alias: id_a,
                            dst: p.slot(id_a),
                        }],
                    }),
                    projections: vec![Projection {
                        expr: Expr::RowRef(p.slot(id_a)),
                        alias: id_a,
                        dst: p.slot(id_a),
                    }]
                }),
                fields: vec![(id_a, p.slot(id_a))]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_return_star() -> Result<(), Error> {
        let mut p = plan("MATCH (n) RETURN *")?;

        let id_n = p.tokenize("n");
        assert_eq!(
            p.plan,
            LogicalPlan::ProduceResult {
                src: Box::new(LogicalPlan::Project {
                    src: Box::new(LogicalPlan::NodeScan {
                        src: Box::new(LogicalPlan::Argument),
                        phase: 0,
                        slot: 0,
                        labels: None,
                    }),
                    projections: vec![Projection {
                        expr: Expr::RowRef(p.slot(id_n)),
                        alias: id_n,
                        dst: p.slot(id_n),
                    }]
                }),
                fields: vec![(id_n, p.slot(id_n))]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_return_count() -> Result<(), Error> {
        let mut p = plan("MATCH (n) RETURN COUNT(*)")?;
        let alias = p.tokenize("COUNT(*)");
        let fn_count = p.tokenize("count");
        assert_eq!(
            p.plan,
            LogicalPlan::ProduceResult {
                src: Box::new(LogicalPlan::Project {
                    src: Box::new(LogicalPlan::Aggregate {
                        src: Box::new(LogicalPlan::NodeScan {
                            src: Box::new(LogicalPlan::Argument),
                            phase: 0,
                            slot: 0,
                            labels: None,
                        }),
                        grouping: vec![],
                        aggregations: vec![(
                            Expr::FuncCall {
                                name: fn_count,
                                args: vec![]
                            },
                            p.slot(alias)
                        )]
                    }),
                    projections: vec![Projection {
                        expr: Expr::RowRef(p.slot(alias)),
                        alias,
                        dst: p.slot(alias),
                    }]
                }),
                fields: vec![(alias, p.slot(alias))]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_return_distinct() -> Result<(), Error> {
        let mut p = plan("MATCH (n) RETURN DISTINCT n.name")?;
        let alias = p.tokenize("n.name");
        let id_n = p.tokenize("n");
        let prop_name = p.tokenize("name");
        assert_eq!(
            p.plan,
            LogicalPlan::ProduceResult {
                src: Box::new(LogicalPlan::Project {
                    src: Box::new(LogicalPlan::Aggregate {
                        src: Box::new(LogicalPlan::NodeScan {
                            src: Box::new(LogicalPlan::Argument),
                            phase: 0,
                            slot: 0,
                            labels: None,
                        }),
                        grouping: vec![(
                            Expr::Prop(Box::new(Expr::RowRef(p.slot(id_n))), vec![prop_name]),
                            1
                        ),],
                        aggregations: vec![]
                    }),
                    projections: vec![Projection {
                        expr: Expr::RowRef(p.slot(alias)),
                        alias,
                        dst: p.slot(alias),
                    }]
                }),
                fields: vec![(alias, p.slot(alias))],
            }
        );
        Ok(())
    }

    #[test]
    fn plan_simple_count() -> Result<(), Error> {
        let mut p = plan("MATCH (n:Person) RETURN count(n)")?;

        let lbl_person = p.tokenize("Person");
        let id_n = p.tokenize("n");
        let fn_count = p.tokenize("count");
        let col_count_n = p.tokenize("count(n)");
        assert_eq!(
            p.plan,
            LogicalPlan::ProduceResult {
                src: Box::new(LogicalPlan::Project {
                    src: Box::new(LogicalPlan::Aggregate {
                        src: Box::new(LogicalPlan::NodeScan {
                            src: Box::new(LogicalPlan::Argument),
                            phase: 0,
                            slot: 0,
                            labels: Some(lbl_person)
                        }),
                        grouping: vec![],
                        aggregations: vec![(
                            Expr::FuncCall {
                                name: fn_count,
                                args: vec![Expr::RowRef(p.slot(id_n))]
                            },
                            p.slot(col_count_n)
                        )]
                    }),
                    projections: vec![Projection {
                        expr: Expr::RowRef(p.slot(col_count_n)),
                        alias: col_count_n,
                        dst: p.slot(col_count_n),
                    }]
                }),
                fields: vec![(col_count_n, p.slot(col_count_n))]
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
            LogicalPlan::ProduceResult {
                src: Box::new(LogicalPlan::Project {
                    src: Box::new(LogicalPlan::Aggregate {
                        src: Box::new(LogicalPlan::NodeScan {
                            src: Box::new(LogicalPlan::Argument),
                            phase: 0,
                            slot: 0,
                            labels: None
                        }),
                        grouping: vec![],
                        aggregations: vec![(
                            Expr::FuncCall {
                                name: fn_count,
                                args: vec![Expr::RowRef(p.slot(id_n))]
                            },
                            p.slot(col_count_n)
                        )]
                    }),
                    projections: vec![Projection {
                        expr: Expr::RowRef(p.slot(col_count_n)),
                        alias: col_count_n,
                        dst: p.slot(col_count_n),
                    }]
                }),
                fields: vec![(col_count_n, p.slot(col_count_n))]
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
            LogicalPlan::ProduceResult {
                src: Box::new(LogicalPlan::Project {
                    src: Box::new(LogicalPlan::Aggregate {
                        src: Box::new(LogicalPlan::NodeScan {
                            src: Box::new(LogicalPlan::Argument),
                            phase: 0,
                            slot: 0,
                            labels: Some(lbl_person)
                        }),
                        grouping: vec![
                            (
                                Expr::Prop(Box::new(Expr::RowRef(p.slot(id_n))), vec![key_age]),
                                p.slot(col_n_age)
                            ),
                            (
                                Expr::Prop(
                                    Box::new(Expr::RowRef(p.slot(id_n))),
                                    vec![key_occupation]
                                ),
                                p.slot(col_n_occupation)
                            ),
                        ],
                        aggregations: vec![(
                            Expr::FuncCall {
                                name: fn_count,
                                args: vec![Expr::RowRef(p.slot(id_n))]
                            },
                            p.slot(col_count_n)
                        )]
                    }),
                    projections: vec![
                        Projection {
                            expr: Expr::RowRef(p.slot(col_n_age)),
                            alias: col_n_age,
                            dst: p.slot(col_n_age),
                        },
                        Projection {
                            expr: Expr::RowRef(p.slot(col_n_occupation)),
                            alias: col_n_occupation,
                            dst: p.slot(col_n_occupation),
                        },
                        Projection {
                            expr: Expr::RowRef(p.slot(col_count_n)),
                            alias: col_count_n,
                            dst: p.slot(col_count_n),
                        },
                    ]
                }),
                fields: vec![
                    (col_n_age, p.slot(col_n_age)),
                    (col_n_occupation, p.slot(col_n_occupation)),
                    (col_count_n, p.slot(col_count_n))
                ]
            }
        );
        Ok(())
    }
}

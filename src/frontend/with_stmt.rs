use super::{plan_expr, Expr, LogicalPlan, Pair, PlanningContext, Projection, Result, Rule};
use pest::iterators::Pairs;

pub fn plan_with(
    pc: &mut PlanningContext,
    src: LogicalPlan,
    stmt: Pair<Rule>,
) -> Result<LogicalPlan> {
    let parts = stmt.into_inner();
    let projections: Projections = parse_projections(pc, parts)?;
    return plan_parsed_with(pc, src, projections);
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

    return Ok(plan);
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
            expr: Expr::Slot(p.dst),
            alias: p.alias,
            dst: p.dst,
        })
    }

    return Ok(LogicalPlan::Project {
        src: Box::new(LogicalPlan::Aggregate {
            src: Box::new(src),
            grouping,
            aggregations,
        }),
        projections: post_aggregation_projections,
    });
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
    return Ok(LogicalPlan::ProduceResult {
        src: Box::new(result),
        fields,
    });
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
    for part in parts {
        match part.as_rule() {
            Rule::distinct_clause => {
                is_distinct = true;
            }
            // WITH a as b, count(c); aka normal explicit projection
            Rule::projections => {
                // This projection clears out all named identifiers that existed previously;
                // what we need here is scopes, but for now we're doing the bare minimum to pass
                // the TCK..
                pc.named_identifiers.clear();

                for projection in part.into_inner() {
                    let p = parse_projection(pc, projection)?;
                    is_aggregating =
                        is_aggregating || p.expr.is_aggregating(&pc.backend_desc.aggregates);
                    projections.push(p);
                }
            }
            // WITH *
            Rule::project_all => {
                for id in &pc.named_identifiers {
                    projections.push(Projection {
                        expr: Expr::Slot(*pc.slots.get(id).unwrap()),
                        alias: *id,
                        // TODO note that this adds a bunch of unecessary copying in all RETURN clauses and
                        //      in cases where we use projections that just rename stuff (eg. WITH blah as
                        //      x); we should consider making expr in Projection Optional, so it can be
                        //      used for pure renaming, if benchmarking shows that's helpful.
                        dst: *pc.slots.get(id).unwrap(),
                    });
                }
                let tokens = pc.tokens.borrow();
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
                    .ok_or(anyhow!("WHERE contained unexpected part"))?;
                selection = Some(plan_expr(pc, where_expr)?);
            }
            Rule::skip_clause => {
                let skip_expr = part
                    .into_inner()
                    .next()
                    .ok_or(anyhow!("SKIP contained unexpected part"))?;
                skip = Some(plan_expr(pc, skip_expr)?);
            }
            Rule::limit_clause => {
                let limit_expr = part
                    .into_inner()
                    .next()
                    .ok_or(anyhow!("LIMIT contained unexpected part"))?;
                limit = Some(plan_expr(pc, limit_expr)?);
            }
            Rule::order_clause => {
                // Skip this for now; we don't support ORDER BY, but there are
                // TCK specs that use ORDER BY where just ignoring it still passes the test
                let mut out = Vec::new();
                for sort_group in part.into_inner() {
                    let sort_expr = sort_group
                        .into_inner()
                        .next()
                        .ok_or(anyhow!("SORT contained unexpected part"))?;
                    let planned_expr = plan_expr(pc, sort_expr)?;
                    if is_aggregating || is_distinct {
                        out.push(sort_expr_for_aggregation(&projections, planned_expr)?)
                    } else {
                        out.push(planned_expr);
                    }
                }
                sort = Some(out);
            }
            _ => bail!("unexpected part of WITH or RETURN: {:?}", part),
        }
    }
    Ok(Projections {
        projections: projections,
        is_distinct,
        is_aggregating,
        selection,
        sort,
        skip,
        limit,
    })
}

// Sort expressions are a bit painful; they can't refer to stuff that was made out-of-scope
// by the preceding WITH/RETURN projection, if the projection contains aggregation.
fn sort_expr_for_aggregation(projections: &Vec<Projection>, e: Expr) -> Result<Expr> {
    // This is only allowed if the projections explicitly use this property,
    // or the entity we're pulling the property off is an aggregate key
    // otherwise it won't be available (since it won't survive across the aggregation)
    for proj in projections {
        // Sort expression is explicitly the exact same as expression used in aggregation
        if e == proj.expr {
            return Ok(Expr::Slot(proj.dst));
        }

        match &e {
            Expr::Prop(entity, _) => {
                // Sort expression is a property of a map or entity we're using as aggregate key
                if **entity == proj.expr {
                    return Ok(e);
                }
            }
            _ => bail!("Don't know how to sort by {:?} yet", e),
        }
    }

    bail!("Can't sort by {:?}, because the planner can't tell if it is used in DISTINCT or aggregation, so is not sure if it is visible to the sorting step", e)
}

fn parse_projection(pc: &mut PlanningContext, projection: Pair<Rule>) -> Result<Projection> {
    let default_alias = projection.as_str();
    let mut parts = projection.into_inner();
    let expr = parts.next().map(|p| plan_expr(pc, p)).unwrap()?;
    let alias = parts
        .next()
        .and_then(|p| match p.as_rule() {
            Rule::id => Some(pc.declare(p.as_str())),
            _ => None,
        })
        .unwrap_or_else(|| pc.declare(default_alias.trim_end()));
    Ok(Projection {
        expr,
        alias,
        // TODO note that this adds a bunch of unecessary copying in all RETURN clauses and
        //      in cases where we use projections that just rename stuff (eg. WITH blah as
        //      x); we should consider making expr in Projection Optional, so it can be
        //      used for pure renaming, if benchmarking shows that's helpful.
        dst: pc.get_or_alloc_slot(alias),
    })
}

#[cfg(test)]
mod tests {
    use crate::frontend::tests::plan;
    use crate::frontend::{Dir, Expr, LogicalPlan, Op, Projection};
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
                    slot: 0,
                    labels: None,
                }),
                projections: vec![Projection {
                    expr: Expr::Slot(p.slot(id_n)),
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
                    slot: 0,
                    labels: None,
                }),
                projections: vec![Projection {
                    expr: Expr::Slot(p.slot(id_n)),
                    alias: id_p,
                    dst: p.slot(id_p),
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
                    sort_by: vec![Expr::Slot(p.slot(id_p))]
                }),
                skip: Some(Expr::Int(1)),
                limit: None,
            }
        );
        Ok(())
    }

    // TODO technically the project is not needed here.. we're just renaming references..
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
                        slot: 0,
                        labels: None,
                    }),
                    projections: vec![Projection {
                        expr: Expr::Slot(p.slot(id_n)),
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
                        slot: 0,
                        labels: None,
                    }),
                    projections: vec![Projection {
                        expr: Expr::Prop(Box::new(Expr::Slot(p.slot(id_n))), vec![key_name]),
                        alias: key_name,
                        dst: p.slot(key_name),
                    }],
                }),
                sort_by: vec![Expr::Slot(p.slot(key_name))]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_with_order_repeating_aliased_aggregated_expression() -> Result<(), Error> {
        // Not sure at all that this is the right thing here, but basically:
        // If you've got a query that does some aggregation, and the orders by the aggregate
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
                            slot: 0,
                            labels: None,
                        }),
                        grouping: vec![(
                            Expr::Prop(Box::new(Expr::Slot(p.slot(id_n))), vec![key_name]),
                            p.slot(key_name)
                        )],
                        aggregations: vec![]
                    }),
                    projections: vec![Projection {
                        expr: Expr::Slot(p.slot(key_name)),
                        alias: key_name,
                        dst: p.slot(key_name),
                    }],
                }),
                sort_by: vec![Expr::Slot(p.slot(key_name))]
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
                            slot: 0,
                            labels: None,
                        }),
                        grouping: vec![(Expr::Slot(p.slot(id_n)), p.slot(id_n))],
                        aggregations: vec![]
                    }),
                    projections: vec![Projection {
                        expr: Expr::Slot(p.slot(id_n)),
                        alias: id_n,
                        dst: p.slot(id_n),
                    }],
                }),
                sort_by: vec![Expr::Prop(
                    Box::new(Expr::Slot(p.slot(id_n))),
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
                        slot: 0,
                        labels: None,
                    }),
                    projections: vec![Projection {
                        expr: Expr::Slot(p.slot(id_n)),
                        alias: id_n,
                        dst: p.slot(id_n),
                    }],
                }),
                predicate: Expr::BinaryOp {
                    left: Box::new(Expr::Prop(
                        Box::new(Expr::Slot(p.slot(id_n))),
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
                                slot: p.slot(id_a),
                                labels: None,
                            }),
                            src_slot: p.slot(id_a),
                            rel_slot: 2,
                            dst_slot: p.slot(id_z),
                            rel_type: None,
                            dir: Some(Dir::Out),
                        }),
                        projections: vec![Projection {
                            expr: Expr::Slot(p.slot(id_a)),
                            alias: id_a,
                            dst: p.slot(id_a),
                        }],
                    }),
                    projections: vec![Projection {
                        expr: Expr::Slot(p.slot(id_a)),
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
                        slot: 0,
                        labels: None,
                    }),
                    projections: vec![Projection {
                        expr: Expr::Slot(p.slot(id_n)),
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
                        expr: Expr::Slot(p.slot(alias)),
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
                            slot: 0,
                            labels: None,
                        }),
                        grouping: vec![(
                            Expr::Prop(Box::new(Expr::Slot(p.slot(id_n))), vec![prop_name]),
                            1
                        ),],
                        aggregations: vec![]
                    }),
                    projections: vec![Projection {
                        expr: Expr::Slot(p.slot(alias)),
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

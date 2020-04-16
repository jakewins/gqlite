use super::{plan_expr, Expr, LogicalPlan, Pair, PlanningContext, Projection, Result, Rule};

pub fn plan_with(
    pc: &mut PlanningContext,
    src: LogicalPlan,
    stmt: Pair<Rule>,
) -> Result<LogicalPlan> {
    let mut parts = stmt.into_inner();

    let (is_aggregate, projections) = parts
        .next()
        .map(|p| plan_projections(pc, p))
        .expect("RETURN must start with projections")?;
    if !is_aggregate {
        return Ok(LogicalPlan::Project {
            src: Box::new(src),
            projections,
        });
    }

    // Split the projections into groupings and aggregating projections, so in a statement like
    //
    //   MATCH (n) RETURN n.age, count(n)
    //
    // You end up with `n.age` in the groupings vector and count(n) in the aggregations vector.
    // For RETURNs (and WITHs) with no aggregations, this ends up being effectively a wasted copy of
    // the projections vector into the groupings vector; so we double the allocation in the common case
    // which kind of sucks. We could probably do this split in plan_return_projections instead,
    // avoiding the copying.
    let mut grouping = Vec::new();
    let mut aggregations = Vec::new();
    // If we end up producing an aggregation, then we wrap it in a Return that describes the order
    // the user asked values to be returned in
    let mut aggregation_projections = Vec::new();
    for projection in projections {
        let agg_projection_slot = pc.get_or_alloc_slot(projection.alias);
        aggregation_projections.push(Projection {
            expr: Expr::Slot(agg_projection_slot),
            alias: projection.alias,
            dst: agg_projection_slot,
        });
        if projection.expr.is_aggregating(&pc.backend_desc.aggregates) {
            aggregations.push((projection.expr, pc.get_or_alloc_slot(projection.alias)));
        } else {
            grouping.push((projection.expr, pc.get_or_alloc_slot(projection.alias)));
        }
    }

    Ok(LogicalPlan::Project {
        src: Box::new(LogicalPlan::Aggregate {
            src: Box::new(src),
            grouping,
            aggregations,
        }),
        projections: aggregation_projections,
    })
}

pub fn plan_return(
    pc: &mut PlanningContext,
    src: LogicalPlan,
    return_stmt: Pair<Rule>,
) -> Result<LogicalPlan> {
    let result = plan_with(pc, src, return_stmt)?;
    if let LogicalPlan::Project { src, projections } = result {
        // TODO This is the same as plan_with; we should drop LogicalPlan::Return and instead have
        //      RETURN represented as ProduceResult{src: Project{..}}, so return is just an embellishment
        //      on WITH.
        // For now, just map Project to Return
        Ok(LogicalPlan::Return { src, projections })
    } else {
        unreachable!("plan_with emitted other plan than Project: {:?}", result)
    }
}

// The bool return here is nasty, refactor, maybe make into a struct?
fn plan_projections(
    pc: &mut PlanningContext,
    projections: Pair<Rule>,
) -> Result<(bool, Vec<Projection>)> {
    match projections.as_rule() {
        // WITH a as b, count(c); aka normal explicit projection
        Rule::projections => {
            // This projection clears out all named identifiers that existed previously;
            // what we need here is scopes, but for now we're doing the bare minimum to pass
            // the TCK..
            pc.named_identifiers.clear();

            let mut out = Vec::new();
            let mut contains_aggregations = false;
            for projection in projections.into_inner() {
                if let Rule::projection = projection.as_rule() {
                    let default_alias = projection.as_str();
                    let mut parts = projection.into_inner();
                    let expr = parts.next().map(|p| plan_expr(pc, p)).unwrap()?;
                    contains_aggregations =
                        contains_aggregations || expr.is_aggregating(&pc.backend_desc.aggregates);
                    let alias = parts
                        .next()
                        .and_then(|p| match p.as_rule() {
                            Rule::id => Some(pc.declare(p.as_str())),
                            _ => None,
                        })
                        .unwrap_or_else(|| pc.declare(default_alias.trim_end()));
                    out.push(Projection {
                        expr,
                        alias,
                        // TODO note that this adds a bunch of unecessary copying in all RETURN clauses and
                        //      in cases where we use projections that just rename stuff (eg. WITH blah as
                        //      x); we should consider making expr in Projection Optional, so it can be
                        //      used for pure renaming, if benchmarking shows that's helpful.
                        dst: pc.get_or_alloc_slot(alias),
                    });
                }
            }
            Ok((contains_aggregations, out))
        }
        // WITH *
        Rule::project_all => {
            let mut out = Vec::new();
            for id in &pc.named_identifiers {
                out.push(Projection {
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
            out.sort_by(|a, b| {
                let a_str = tokens.lookup(a.alias);
                let b_str = tokens.lookup(b.alias);
                a_str.cmp(&b_str)
            });
            Ok((false, out))
        }
        _ => unreachable!("RETURN projections must either be project_all or list of projection"),
    }
}

#[cfg(test)]
mod tests {
    use crate::frontend::tests::plan;
    use crate::frontend::{Dir, Expr, LogicalPlan, Projection};
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
                }]
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
                }]
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
            LogicalPlan::Return {
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
                        dir: Some(Dir::Out)
                    }),
                    projections: vec![Projection {
                        expr: Expr::Slot(p.slot(id_a)),
                        alias: id_a,
                        dst: p.slot(id_a),
                    }]
                }),
                projections: vec![Projection {
                    expr: Expr::Slot(p.slot(id_a)),
                    alias: id_a,
                    dst: p.slot(id_a),
                }]
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
            LogicalPlan::Return {
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
            }
        );
        Ok(())
    }
}

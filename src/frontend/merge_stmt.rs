use super::{
    parse_pattern_graph, Dir, LogicalPlan, NodeSpec, Pair, PlanningContext, RelSpec, Result, Rule,
};
use crate::frontend::{SetAction};
use pest::iterators::Pairs;
use crate::frontend::expr::plan_expr;
use crate::frontend::match_stmt::{plan_match, plan_match_patterngraph};
use crate::frontend::create_stmt::{plan_create, plan_create_patterngraph};
use crate::frontend::set_stmt::parse_set_clause;

pub fn plan_merge(
    mut pc: &mut PlanningContext,
    src: LogicalPlan,
    merge_stmt: Pair<Rule>,
) -> Result<LogicalPlan> {
    let mut pairs = merge_stmt.into_inner();
    let patterns = pairs.next().unwrap();

    let mut pg = parse_pattern_graph(pc, patterns)?;

    let mut on_create: Vec<SetAction> = Vec::new();
    let mut on_match: Vec<SetAction> = Vec::new();

    for on_x in pairs {
        match on_x.as_rule() {
            Rule::on_create_clause => {
                on_create.append(&mut parse_set_clause(&mut pc.scoping, on_x)?)
            },
            Rule::on_match_clause => {
                on_match.append(&mut parse_set_clause(&mut pc.scoping, on_x)?)
            },
            r => unreachable!("{:?}", r),
        }
    }

    // plan_match_patterngraph and plan_create_patterngraph both mutate the pattern you give them,
    // so they each need a dedicated one, for now at least; might want to modify them to keep
    // the mutating state hidden in their own implementations and take an immutable graph later on..
    // Eg. pathological MERGE statements may contain hundreds of thousands of pattern nodes, so
    // clone is expensive
    let mut matchpg = pg.clone();

    // Slots the pattern populates; either the match will fill these or the create will; we use
    // this list in the ConditionalApply/AntiConditionalApply plans below
    let mut pattern_slots = Vec::new();
    for id in &matchpg.unbound_identifiers {
        pattern_slots.push(pc.scoping.lookup_or_allocrow(*id));
    }

    let mut matchplan = LogicalPlan::Optional {
        src: Box::new(plan_match_patterngraph(&mut pc, LogicalPlan::Argument, matchpg)?),
        slots: pattern_slots.clone(),
    };
    let mut createplan = plan_create_patterngraph(&mut pc, LogicalPlan::Argument, pg)?;

    if !on_create.is_empty() {
        createplan = LogicalPlan::SetProperties {
            src: Box::new(createplan),
            actions: on_create
        }
    }

    if !on_match.is_empty() {
        matchplan = LogicalPlan::ConditionalApply {
            lhs: Box::new(matchplan ),
            rhs: Box::new(LogicalPlan::SetProperties {
                src: Box::new(LogicalPlan::Argument),
                actions: on_match,
            }),
            conditions: pattern_slots.clone(),
        };
    }

    let mut mergeplan = LogicalPlan::AntiConditionalApply {
        lhs: Box::new(matchplan),
        rhs: Box::new(createplan),
        conditions: pattern_slots
    };

    match src {
        LogicalPlan::Argument => (),
        _ => {
            // If the input is not Argument, that means we need to run the merge for each input
            // row, which we do via an Apply plan
            mergeplan = LogicalPlan::Apply {
                lhs: Box::new(src ),
                rhs: Box::new(mergeplan )
            }
        }
    }

    Ok(mergeplan)
}

#[cfg(test)]
mod tests {
    use crate::frontend::tests::plan;
    use crate::frontend::{Expr, LogicalPlan, MapEntryExpr, NodeSpec, Op, SetAction, Dir, RelSpec};
    use crate::Error;

    #[test]
    fn plan_merge() -> Result<(), Error> {
        let mut p = plan("MERGE (n:Person {name: $name})
ON CREATE SET n.created = timestamp()
ON MATCH SET n.updated = timestamp()")?;

        let lbl_person = p.tokenize("Person");
        let tok_name = p.tokenize("name");
        let param_name = p.tokenize("$name");
        let key_created = p.tokenize("created");
        let key_updated = p.tokenize("updated");
        let id_n = p.tokenize("n");
        let fn_timestamp = p.tokenize("timestamp");
        let slot_n = p.slot(id_n);
        assert_eq!(
            p.plan,
            LogicalPlan::AntiConditionalApply {
                lhs: Box::new(LogicalPlan::ConditionalApply {
                    lhs: Box::new(LogicalPlan::Optional {
                        src: Box::new(LogicalPlan::Selection {
                            src: Box::new(LogicalPlan::NodeScan {
                                src: Box::new(LogicalPlan::Argument),
                                slot: slot_n,
                                labels: Some(lbl_person)
                            }),
                            predicate: Expr::BinaryOp {
                                left: Box::new(Expr::Prop(Box::new(Expr::RowRef(slot_n)), vec![tok_name])),
                                right: Box::new(Expr::Param(param_name)),
                                op: Op::Eq
                            }
                        }),
                        slots: vec![slot_n]
                    }),
                    rhs: Box::new(LogicalPlan::SetProperties {
                        src: Box::new(LogicalPlan::Argument),
                        actions: vec![
                            SetAction::SingleAssign {
                                entity: slot_n,
                                key: key_updated,
                                value: Expr::FuncCall {
                                    name: fn_timestamp,
                                    args: vec![]
                                }
                            }
                        ]
                    }),
                    conditions: vec![slot_n]
                }),
                // TODO: This SetProperties should be folded into the Create
                rhs: Box::new(LogicalPlan::SetProperties {
                    src: Box::new(LogicalPlan::Create {
                        src: Box::new(LogicalPlan::Argument),
                        nodes: vec![NodeSpec{
                            slot: slot_n,
                            labels: vec![lbl_person],
                            props: vec![MapEntryExpr{ key: tok_name, val: Expr::Param(param_name) }]
                        }],
                        rels: vec![]
                    }),
                    actions: vec![
                        SetAction::SingleAssign {
                            entity: slot_n,
                            key: key_created,
                            value: Expr::FuncCall {
                                name: fn_timestamp,
                                args: vec![]
                            }
                        }]
                }),
                // eg. rhs is executed iff slot_n is null after executing lhs
                conditions: vec![slot_n]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_merge_rel() -> Result<(), Error> {
        let mut p = plan("MATCH (a), (b) MERGE (a)-[r:TYPE]->(b)")?;

        let id_a = p.tokenize("a");
        let id_b = p.tokenize("b");
        let id_r = p.tokenize("r");
        let tok_type = p.tokenize("TYPE");
        assert_eq!(
            p.plan,
            LogicalPlan::Apply {
                lhs: Box::new(LogicalPlan::CartesianProduct {
                    outer: Box::new(LogicalPlan::NodeScan {
                        src: Box::new(LogicalPlan::Argument),
                        slot: p.slot(id_a),
                        labels: None
                    }),
                    inner: Box::new(LogicalPlan::NodeScan {
                        src: Box::new(LogicalPlan::Argument),
                        slot: p.slot(id_b),
                        labels: None
                    }),
                    predicate: Expr::Bool(true),
                }),
                rhs: Box::new(LogicalPlan::AntiConditionalApply {
                    lhs: Box::new(LogicalPlan::Optional {
                        src: Box::new(LogicalPlan::ExpandInto {
                            src: Box::new(LogicalPlan::Argument ),
                            left_node_slot: p.slot(id_a),
                            right_node_slot: p.slot(id_b),
                            dst_slot: p.slot(id_r),
                            rel_type: Some(tok_type),
                            dir: Some(Dir::Out)
                        }),
                        slots: vec![p.slot(id_r)]
                    }),
                    rhs: Box::new(LogicalPlan::Create {
                        src: Box::new(LogicalPlan::Argument),
                        nodes: vec![],
                        rels: vec![RelSpec{
                            slot: p.slot(id_r),
                            rel_type: tok_type,
                            start_node_slot: p.slot(id_a),
                            end_node_slot: p.slot(id_b),
                            props: vec![]
                        }]
                    }),
                    conditions: vec![p.slot(id_r)]
                })
            }
        );
        Ok(())
    }

}
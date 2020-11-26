use super::{
    parse_pattern_graph, Dir, LogicalPlan, NodeSpec, Pair, PlanningContext, RelSpec, Result, Rule,
};
use crate::frontend::{PropertyUpdate, PropertyAction};
use pest::iterators::Pairs;
use crate::frontend::expr::plan_expr;
use crate::frontend::match_stmt::{plan_match, plan_match_patterngraph};
use crate::frontend::create_stmt::{plan_create, plan_create_patterngraph};

pub fn plan_merge(
    mut pc: &mut PlanningContext,
    src: LogicalPlan,
    create_stmt: Pair<Rule>,
) -> Result<LogicalPlan> {
    let mut pairs = create_stmt.into_inner();
    let patterns = pairs.next().unwrap();

    let mut pg = parse_pattern_graph(pc, patterns)?;

    let mut on_create: Vec<PropertyUpdate> = Vec::new();
    let mut on_match: Vec<PropertyUpdate> = Vec::new();

    for on_x in pairs {
        match on_x.as_rule() {
            Rule::on_create_clause => {
                on_create.append(&mut parse_on_x_clause(pc, on_x)?)
            },
            Rule::on_match_clause => {
                on_match.append(&mut parse_on_x_clause(pc, on_x)?)
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
        pattern_slots.push(pc.get_or_alloc_slot(*id));
    }

    let matchplan = plan_match_patterngraph(&mut pc, src, matchpg)?;
    let mut createplan = plan_create_patterngraph(&mut pc, LogicalPlan::Argument, pg)?;

    if !on_create.is_empty() {
        createplan = LogicalPlan::SetProperties {
            src: Box::new(createplan),
            updates: on_create
        }
    }

    Ok(LogicalPlan::AntiConditionalApply {
        lhs: Box::new(LogicalPlan::ConditionalApply {
            lhs: Box::new(LogicalPlan::Optional {
                src: Box::new(matchplan ),
                slots: pattern_slots.clone(),
            } ),
            rhs: Box::new(LogicalPlan::SetProperties {
                src: Box::new(LogicalPlan::Argument),
                updates: on_match,
            }),
            conditions: pattern_slots.clone(),
        }),
        rhs: Box::new(createplan),
        conditions: pattern_slots
    })
}

fn parse_on_x_clause(pc: &mut PlanningContext, on_x: Pair<Rule>) -> Result<Vec<PropertyUpdate>> {
    let mut out = Vec::new();
    for part in on_x.into_inner() {
        match part.as_rule() {
            Rule::assignment => {
                let mut parts = part.into_inner();
                let identifier = pc.tokenize(parts.next().unwrap().as_str());
                let entity = pc.get_or_alloc_slot(identifier);
                let key = pc.tokenize(parts.next().unwrap().as_str());
                let val = plan_expr(pc.scope_mut(), parts.next().unwrap())?;
                out.push(PropertyUpdate{
                    entity,
                    key,
                    action: PropertyAction::Set(val),
                })
            },
            _ => unreachable!()
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use crate::frontend::tests::plan;
    use crate::frontend::{Expr, LogicalPlan, MapEntryExpr, NodeSpec, Op, PropertyUpdate, PropertyAction};
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
                                left: Box::new(Expr::Prop(Box::new(Expr::Slot(slot_n)), vec![tok_name])),
                                right: Box::new(Expr::Param(param_name)),
                                op: Op::Eq
                            }
                        }),
                        slots: vec![slot_n]
                    }),
                    rhs: Box::new(LogicalPlan::SetProperties {
                        src: Box::new(LogicalPlan::Argument),
                        updates: vec![
                            PropertyUpdate{
                                entity: slot_n,
                                key: key_updated,
                                action: PropertyAction::Set(Expr::FuncCall {
                                    name: fn_timestamp,
                                    args: vec![]
                                })
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
                    updates: vec![
                        PropertyUpdate{
                            entity: slot_n,
                            key: key_created,
                            action: PropertyAction::Set(Expr::FuncCall {
                                name: fn_timestamp,
                                args: vec![]
                            })
                        }]
                }),
                // eg. rhs is executed iff slot_n is null after executing lhs
                conditions: vec![slot_n]
            }
        );
        Ok(())
    }

}

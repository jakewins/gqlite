use super::{LogicalPlan, Pair, PlanningContext, Result, Rule};

use crate::frontend::expr::plan_expr;
use crate::frontend::{Scoping, UpdateAction};

pub fn plan_set(
    pc: &mut PlanningContext,
    src: LogicalPlan,
    set_stmt: Pair<Rule>,
) -> Result<LogicalPlan> {
    let actions = parse_set_clause(&mut pc.scoping, set_stmt)?;
    Ok(LogicalPlan::Update {
        src: Box::new(src),
        scope: pc.scoping.current_scope_no(),
        actions,
    })
}

pub fn parse_set_clause(scoping: &mut Scoping, set_stmt: Pair<Rule>) -> Result<Vec<UpdateAction>> {
    let mut actions = Vec::new();
    for assignment in set_stmt.into_inner() {
        match assignment.as_rule() {
            Rule::single_assignment => {
                let mut parts = assignment.into_inner();
                let entity = scoping.tokenize(parts.next().unwrap().as_str());
                let key = scoping.tokenize(parts.next().unwrap().as_str());

                let expr = plan_expr(scoping, parts.next().unwrap())?;
                actions.push(UpdateAction::PropAssign {
                    entity: scoping.lookup_or_allocrow(entity),
                    key,
                    value: expr,
                });
            }
            Rule::append_assignment => {
                let mut parts = assignment.into_inner();
                let entity = scoping.tokenize(parts.next().unwrap().as_str());

                let expr = plan_expr(scoping, parts.next().unwrap())?;
                actions.push(UpdateAction::PropAppend {
                    entity: scoping.lookup_or_allocrow(entity),
                    value: expr,
                });
            }
            Rule::overwrite_assignment => {
                let mut parts = assignment.into_inner();
                let entity = scoping.tokenize(parts.next().unwrap().as_str());

                let expr = plan_expr(scoping, parts.next().unwrap())?;
                actions.push(UpdateAction::PropOverwrite {
                    entity: scoping.lookup_or_allocrow(entity),
                    value: expr,
                });
            }
            Rule::label_assignment => {
                let mut parts = assignment.into_inner();
                let entity = scoping.tokenize(parts.next().unwrap().as_str());
                let label = scoping.tokenize(parts.next().unwrap().as_str());
                actions.push(UpdateAction::LabelSet {
                    entity: scoping.lookup_or_allocrow(entity),
                    label
                })
            }
            _ => unreachable!("{:?}", assignment),
        }
    }

    Ok(actions)
}

#[cfg(test)]
mod tests {
    use crate::frontend::tests::plan;
    use crate::frontend::{Expr, LogicalPlan, MapEntryExpr, UpdateAction};
    use crate::Error;

    #[test]
    fn plan_set_single_property() -> Result<(), Error> {
        let mut p = plan("MATCH (a) SET a.name = 'bob'")?;

        let id_a = p.tokenize("a");
        let key_name = p.tokenize("name");

        assert_eq!(
            p.plan,
            LogicalPlan::Update {
                src: Box::new(LogicalPlan::NodeScan {
                    src: Box::new(LogicalPlan::Argument),
                    scope: 1,
                    slot: p.slot(id_a),
                    labels: None
                }),
                scope: 1,
                actions: vec![UpdateAction::PropAssign {
                    entity: p.slot(id_a),
                    key: key_name,
                    value: Expr::String("bob".to_string())
                }]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_set_overwrite_entity() -> Result<(), Error> {
        let mut p = plan("MATCH (a), (b) SET a = b")?;
        let id_a = p.tokenize("a");
        let id_b = p.tokenize("b");
        let _key_name = p.tokenize("name");

        assert_eq!(
            p.plan,
            LogicalPlan::Update {
                src: Box::new(LogicalPlan::CartesianProduct {
                    outer: Box::new(LogicalPlan::NodeScan {
                        src: Box::new(LogicalPlan::Argument),
                        scope: 1,
                        slot: p.slot(id_a),
                        labels: None
                    }),
                    inner: Box::new(LogicalPlan::NodeScan {
                        src: Box::new(LogicalPlan::Argument),
                        scope: 1,
                        slot: p.slot(id_b),
                        labels: None
                    }),
                    predicate: Expr::Bool(true),
                }),
                scope: 1,
                actions: vec![UpdateAction::PropOverwrite {
                    entity: p.slot(id_a),
                    value: Expr::RowRef(p.slot(id_b)),
                }]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_set_append_map() -> Result<(), Error> {
        let mut p = plan("MATCH (a) SET a += {name: 'baz'}")?;
        let id_a = p.tokenize("a");
        let key_name = p.tokenize("name");

        assert_eq!(
            p.plan,
            LogicalPlan::Update {
                src: Box::new(LogicalPlan::NodeScan {
                    src: Box::new(LogicalPlan::Argument),
                    scope: 1,
                    slot: p.slot(id_a),
                    labels: None
                }),
                scope: 1,
                actions: vec![UpdateAction::PropAppend {
                    entity: p.slot(id_a),
                    value: Expr::Map(vec![MapEntryExpr {
                        key: key_name,
                        val: Expr::String("baz".to_string())
                    },]),
                }]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_set_append_label() -> Result<(), Error> {
        let mut p = plan("MATCH (a) SET a:Hello")?;
        let id_a = p.tokenize("a");
        let lbl_hello = p.tokenize("Hello");

        assert_eq!(
            p.plan,
            LogicalPlan::Update {
                src: Box::new(LogicalPlan::NodeScan {
                    src: Box::new(LogicalPlan::Argument),
                    scope: 1,
                    slot: p.slot(id_a),
                    labels: None
                }),
                scope: 1,
                actions: vec![UpdateAction::LabelSet {
                    entity: p.slot(id_a),
                    label: lbl_hello,
                }],
            }
        );
        Ok(())
    }
}

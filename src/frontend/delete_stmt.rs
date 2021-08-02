use super::{
    LogicalPlan, Pair, PlanningContext, Result, Rule,
    UpdateAction
};
use crate::frontend::expr::plan_expr;

pub fn plan_delete(
    pc: &mut PlanningContext,
    src: LogicalPlan,
    delete_stmt: Pair<Rule>,
) -> Result<LogicalPlan> {

    let mut parts = delete_stmt.into_inner();
    let mut part = parts.next().unwrap();

    let is_detach = if let Rule::detach_clause = part.as_rule() {
        part = parts.next().unwrap();
        true
    } else {
        false
    };

    let mut actions = Vec::new();
    loop {
        let delete_expr = if let Rule::expr = part.as_rule() {
            let expr = plan_expr(&mut pc.scoping, part)?;
            if is_detach {
                UpdateAction::DetachDelete { entity: expr }
            } else {
                UpdateAction::DeleteEntity { entity: expr }
            }
        } else {
            bail!("unknown delete statement, expected expression")
        };
        actions.push(delete_expr);

        if let Some(p) = parts.next() {
            part = p;
        } else {
            break;
        }
    }

    Ok(LogicalPlan::Update {
        src: Box::new(src),
        phase: pc.get_or_create_write_phase(),
        actions,
    })
}


#[cfg(test)]
mod tests {
    use crate::frontend::tests::plan;
    use crate::frontend::{Expr, LogicalPlan, UpdateAction};
    use crate::Error;
    use super::*;

    #[test]
    fn plan_node_delete() -> Result<(), Error> {
        let mut p = plan("MATCH (n) DELETE n")?;

        let id_n = p.tokenize("n");
        assert_eq!(
            p.plan,
            LogicalPlan::Update {
                src: Box::new(LogicalPlan::NodeScan {
                    src: Box::new(LogicalPlan::Argument),
                    phase: 0,
                    slot: p.slot(id_n),
                    labels: None
                }),
                phase: 1,
                actions: vec![
                    UpdateAction::DeleteEntity { entity: Expr::RowRef(p.slot(id_n)) }
                ]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_multiple_deletes() -> Result<(), Error> {
        let mut p = plan("MATCH (n), (m) DELETE n, m")?;

        let id_n = p.tokenize("n");
        let id_m = p.tokenize("m");
        assert_eq!(
            p.plan,
            LogicalPlan::Update {
                src: Box::new(LogicalPlan::CartesianProduct{
                    outer: Box::new(LogicalPlan::NodeScan {
                        src: Box::new(LogicalPlan::Argument),
                        phase: 0,
                        slot: p.slot(id_n),
                        labels: None
                    }),
                    inner: Box::new(LogicalPlan::NodeScan {
                        src: Box::new(LogicalPlan::Argument),
                        phase: 0,
                        slot: p.slot(id_m),
                        labels: None
                    }),
                    predicate: Expr::Bool(true),
                }),
                phase: 1,
                actions: vec![
                    UpdateAction::DeleteEntity { entity: Expr::RowRef(p.slot(id_n)) },
                    UpdateAction::DeleteEntity { entity: Expr::RowRef(p.slot(id_m)) },
                ]
            }
        );
        Ok(())
    }

    #[test]
    fn plan_detach_delete() -> Result<(), Error> {
        let mut p = plan("MATCH (n) DETACH DELETE n")?;

        let id_n = p.tokenize("n");
        assert_eq!(
            p.plan,
            LogicalPlan::Update {
                src: Box::new(LogicalPlan::NodeScan {
                    src: Box::new(LogicalPlan::Argument),
                    phase: 0,
                    slot: p.slot(id_n),
                    labels: None
                }),
                phase: 1,
                actions: vec![
                    UpdateAction::DetachDelete { entity: Expr::RowRef(p.slot(id_n)) }
                ]
            }
        );
        Ok(())
    }
}

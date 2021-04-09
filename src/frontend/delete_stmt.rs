use super::{
    LogicalPlan, Pair, PlanningContext, Result, Rule,
    UpdateAction
};
use crate::frontend::expr::plan_expr;

pub fn plan_delete(
    mut pc: &mut PlanningContext,
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

    let delete_expr = if let Rule::expr = part.as_rule() {
        let expr = plan_expr(&mut pc.scoping, part)?;
        if is_detach {
            UpdateAction::DetachDelete { node: expr }
        } else {
            UpdateAction::DeleteEntity { entity: expr }
        }
    } else {
        bail!("unknown delete statement, expected expression")
    };

    Ok(LogicalPlan::Update {
        src: Box::new(src),
        scope: pc.scoping.current_scope_no(),
        actions: vec![delete_expr]
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
                    scope: 1,
                    slot: p.slot(id_n),
                    labels: None
                }),
                scope: 1,
                actions: vec![
                    UpdateAction::DeleteEntity { entity: Expr::RowRef(p.slot(id_n)) }
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
                    scope: 1,
                    slot: p.slot(id_n),
                    labels: None
                }),
                scope: 1,
                actions: vec![
                    UpdateAction::DetachDelete { node: Expr::RowRef(p.slot(id_n)) }
                ]
            }
        );
        Ok(())
    }
}

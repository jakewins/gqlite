use super::{Expr, LogicalPlan, Pair, PlanningContext, Result, Rule};
use crate::backend::Token;
use crate::frontend::expr::plan_expr;

pub fn plan_call(
    pc: &mut PlanningContext,
    src: LogicalPlan,
    call_stmt: Pair<Rule>,
) -> Result<LogicalPlan> {
    let mut name: Option<Token> = None;
    let mut args: Option<Vec<Expr>> = None;
    for part in call_stmt.into_inner() {
        match part.as_rule() {
            Rule::function_id => {
                name = Some(pc.scoping.tokenize(part.as_str()));
            }
            Rule::arglist => {
                args = Some(plan_args(pc, part)?);
            }
            _ => unreachable!(),
        }
    }

    if name.is_none() {
        return Err(anyhow!("Unable to parse procedure name in CALL statement"));
    }
    Ok(LogicalPlan::Call {
        src: Box::new(src),
        name: name.unwrap(),
        args: args.unwrap_or_default(),
    })
}

fn plan_args(pc: &mut PlanningContext, arglist: Pair<Rule>) -> Result<Vec<Expr>> {
    let mut out = Vec::new();
    for part in arglist.into_inner() {
        match part.as_rule() {
            Rule::expr => out.push(plan_expr(&mut pc.scoping, part)?),
            _ => unreachable!(),
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use crate::frontend::tests::plan;
    use crate::frontend::{Expr, LogicalPlan};
    use crate::Error;

    #[test]
    fn plan_call_with_parameter() -> Result<(), Error> {
        let mut p = plan("CALL dbms.cluster.routing.getRoutingTable($context)")?;
        let get_routing_table = p.tokenize("dbms.cluster.routing.getRoutingTable");
        let p_context = p.tokenize("context");

        assert_eq!(
            p.plan,
            LogicalPlan::Call {
                src: Box::new(LogicalPlan::Argument),
                name: get_routing_table,
                args: vec![Expr::Param(p_context)]
            }
        );
        Ok(())
    }
}

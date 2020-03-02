// This module contains our definition of expressions, including code to convert parse streams
// to expressions.

use crate::backend::Token;
use crate::frontend::{PlanningContext, Result, Rule};
use crate::{Slot, Val};
use pest::iterators::Pair;
use std::collections::HashSet;

#[derive(Debug, PartialEq, Clone)]
pub enum Op {
    Eq,
}

impl Op {
    pub fn from_str(s: &str) -> Result<Op> {
        match s {
            "=" => Ok(Op::Eq),
            _ => Err(anyhow!("Unknown operator: {}", s)),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    And(Vec<Self>),
    Or(Vec<Self>),

    // An operator that takes two expressions as its arguments, for instance
    // "a = b" or "a > b".
    BinaryOp {
        left: Box<Self>,
        right: Box<Self>,
        op: Op,
    },

    Bool(bool),

    // TODO: Drop this in favor of having the literal types directly at this level, so we can
    //       remove the dependency on Val, so that backends can be free to define Val representations
    //       as they prefer
    Lit(Val),

    // Lookup a property by id
    Prop(Box<Self>, Vec<Token>),
    Slot(Slot),
    // Map expressions differ from eg. Lit(Val::Map) in that they can have expressions as
    // values, like `{ name: trim_spaces(n.name) }`, and evaluate to Val maps.
    Map(Vec<MapEntryExpr>),
    // Same as map expressions in that they differ from List(Val::List) in having nested exprs
    List(Vec<Expr>),
    FuncCall {
        name: Token,
        args: Vec<Expr>,
    },

    // True if the Node in the specified Slot has the specified Label
    HasLabel(Slot, Token),
}

impl Expr {
    // Does this expression - when considered recursively - aggregate rows?
    pub fn is_aggregating(&self, aggregating_funcs: &HashSet<Token>) -> bool {
        match self {
            Expr::Lit(_) => false,
            Expr::Prop(c, _) => c.is_aggregating(aggregating_funcs),
            Expr::Slot(_) => false,
            Expr::Map(children) => children
                .iter()
                .any(|c| c.val.is_aggregating(aggregating_funcs)),
            Expr::List(children) => children.iter().any(|v| v.is_aggregating(aggregating_funcs)),
            Expr::FuncCall { name, args } => {
                aggregating_funcs.contains(name)
                    || args.iter().any(|c| c.is_aggregating(aggregating_funcs))
            }
            Expr::And(terms) => terms.iter().any(|c| c.is_aggregating(aggregating_funcs)),
            Expr::Or(terms) => terms.iter().any(|c| c.is_aggregating(aggregating_funcs)),
            Expr::Bool(_) => false,
            Expr::BinaryOp { left, right, op: _ } => {
                left.is_aggregating(aggregating_funcs) | right.is_aggregating(aggregating_funcs)
            }
            Expr::HasLabel(_, _) => false,
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct MapEntryExpr {
    pub key: Token,
    pub val: Expr,
}

pub(super) fn plan_expr(pc: &mut PlanningContext, expression: Pair<Rule>) -> Result<Expr> {
    let mut or_expressions = Vec::new();
    for inner in expression.into_inner() {
        match inner.as_rule() {
            Rule::and_expr => {
                let mut and_expressions: Vec<Expr> = Vec::new();
                for term in inner.into_inner() {
                    and_expressions.push(plan_term(pc, term)?)
                }
                if and_expressions.len() == 1 {
                    or_expressions.push(and_expressions.remove(0))
                } else {
                    or_expressions.push(Expr::And(and_expressions))
                }
            }
            _ => panic!("({:?}): {}", inner.as_rule(), inner.as_str()),
        }
    }
    if or_expressions.len() == 1 {
        return Ok(or_expressions.remove(0));
    } else {
        return Ok(Expr::Or(or_expressions));
    }
}

fn plan_term(pc: &mut PlanningContext, term: Pair<Rule>) -> Result<Expr> {
    match term.as_rule() {
        Rule::string => {
            let content = term
                .into_inner()
                .next()
                .expect("Strings should always have an inner value")
                .as_str();
            return Ok(Expr::Lit(Val::String(String::from(content))));
        }
        Rule::id => {
            let tok = pc.tokenize(term.as_str());
            return Ok(Expr::Slot(pc.get_or_alloc_slot(tok)));
        }
        Rule::prop_lookup => {
            let mut prop_lookup = term.into_inner();
            let prop_lookup_expr = prop_lookup.next().unwrap();
            let base = match prop_lookup_expr.as_rule() {
                Rule::id => {
                    let tok = pc.tokenize(prop_lookup_expr.as_str());
                    Expr::Slot(pc.get_or_alloc_slot(tok))
                }
                _ => unreachable!(),
            };
            let mut props = Vec::new();
            for p_inner in prop_lookup {
                if let Rule::id = p_inner.as_rule() {
                    props.push(pc.tokenize(p_inner.as_str()));
                }
            }
            return Ok(Expr::Prop(Box::new(base), props));
        }
        Rule::func_call => {
            let mut func_call = term.into_inner();
            let func_name_item = func_call
                .next()
                .expect("All func_calls must start with an identifier");
            let name = pc.tokenize(func_name_item.as_str());
            // Parse args
            let mut args = Vec::new();
            for arg in func_call {
                args.push(plan_expr(pc, arg)?);
            }
            return Ok(Expr::FuncCall { name, args });
        }
        Rule::list => {
            let mut items = Vec::new();
            let exprs = term.into_inner();
            for exp in exprs {
                items.push(plan_expr(pc, exp)?);
            }
            return Ok(Expr::List(items));
        }
        Rule::int => {
            let v = term.as_str().parse::<i64>()?;
            return Ok(Expr::Lit(Val::Int(v)));
        }
        Rule::float => {
            let v = term.as_str().parse::<f64>()?;
            return Ok(Expr::Lit(Val::Float(v)));
        }
        Rule::lit_true => return Ok(Expr::Bool(true)),
        Rule::lit_false => return Ok(Expr::Bool(false)),
        Rule::binary_op => {
            let mut parts = term.into_inner();
            let left = parts.next().expect("binary operators must have a left arg");
            let op = parts
                .next()
                .expect("binary operators must have an operator");
            let right = parts
                .next()
                .expect("binary operators must have a right arg");

            let left_expr = plan_term(pc, left)?;
            let right_expr = plan_term(pc, right)?;
            return Ok(Expr::BinaryOp {
                left: Box::new(left_expr),
                right: Box::new(right_expr),
                op: Op::from_str(op.as_str())?,
            });
        }
        Rule::expr => {
            // this happens when there are parenthetises forcing "full" expressions down here
            return plan_expr(pc, term);
        }
        _ => panic!("({:?}): {}", term.as_rule(), term.as_str()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::{BackendDesc, FuncSignature, FuncType, Token, Tokens};
    use crate::frontend::{Frontend, LogicalPlan};
    use crate::Type;
    use anyhow::Result;
    use std::cell::RefCell;
    use std::collections::HashMap;
    use std::rc::Rc;

    // Outcome of testing planning; the plan plus other related items to do checks on
    #[derive(Debug)]
    struct PlanArtifacts {
        expr: Expr,
        slots: HashMap<Token, usize>,
        tokens: Rc<RefCell<Tokens>>,
    }

    impl PlanArtifacts {
        fn slot(&self, k: Token) -> usize {
            self.slots[&k]
        }

        fn tokenize(&mut self, content: &str) -> Token {
            self.tokens.borrow_mut().tokenize(content)
        }
    }

    fn plan(q: &str) -> Result<PlanArtifacts> {
        let tokens = Rc::new(RefCell::new(Tokens::new()));
        let tok_expr = tokens.borrow_mut().tokenize("expr");
        let fn_count = tokens.borrow_mut().tokenize("count");
        let backend_desc = BackendDesc::new(vec![FuncSignature {
            func_type: FuncType::Aggregating,
            name: fn_count,
            returns: Type::Integer,
            args: vec![(tok_expr, Type::Any)],
        }]);

        let frontend = Frontend {
            tokens: Rc::clone(&tokens),
            backend_desc: BackendDesc::new(vec![]),
        };
        let mut pc = PlanningContext {
            slots: Default::default(),
            anon_rel_seq: 0,
            anon_node_seq: 0,
            tokens: Rc::clone(&tokens),
            backend_desc: &backend_desc,
        };
        let plan = frontend.plan_in_context(&format!("RETURN {}", q), &mut pc);

        if let Ok(LogicalPlan::Return {
            src: _,
            projections,
        }) = plan
        {
            return Ok(PlanArtifacts {
                expr: projections[0].expr.clone(),
                slots: pc.slots,
                tokens: Rc::clone(&tokens),
            });
        } else {
            return Err(anyhow!("Expected RETURN plan, got: {:?}", plan?));
        }
    }

    #[test]
    fn plan_boolean_logic() -> Result<()> {
        assert_eq!(plan("true")?.expr, Expr::Bool(true));
        assert_eq!(plan("false")?.expr, Expr::Bool(false));
        assert_eq!(
            plan("true and false")?.expr,
            Expr::And(vec![Expr::Bool(true), Expr::Bool(false)])
        );
        assert_eq!(
            plan("true and false and true")?.expr,
            Expr::And(vec![Expr::Bool(true), Expr::Bool(false), Expr::Bool(true)])
        );
        assert_eq!(
            plan("true or false")?.expr,
            Expr::Or(vec![Expr::Bool(true), Expr::Bool(false)])
        );
        assert_eq!(
            plan("true or false or true")?.expr,
            Expr::Or(vec![Expr::Bool(true), Expr::Bool(false), Expr::Bool(true)])
        );
        assert_eq!(
            plan("true and false or true")?.expr,
            Expr::Or(vec![
                Expr::And(vec![Expr::Bool(true), Expr::Bool(false)]),
                Expr::Bool(true)
            ])
        );
        assert_eq!(
            plan("true or false and true")?.expr,
            Expr::Or(vec![
                Expr::Bool(true),
                Expr::And(vec![Expr::Bool(false), Expr::Bool(true)])
            ])
        );
        Ok(())
    }

    #[test]
    fn plan_binary_operators() -> Result<()> {
        assert_eq!(
            plan("true = false")?.expr,
            Expr::BinaryOp {
                left: Box::new(Expr::Bool(true)),
                right: Box::new(Expr::Bool(false)),
                op: Op::Eq
            },
        );
        assert_eq!(
            plan("false = ( true = true )")?.expr,
            Expr::BinaryOp {
                left: Box::new(Expr::Bool(false)),
                right: Box::new(Expr::BinaryOp {
                    left: Box::new(Expr::Bool(true)),
                    right: Box::new(Expr::Bool(true)),
                    op: Op::Eq
                }),
                op: Op::Eq
            },
        );
        Ok(())
    }
}

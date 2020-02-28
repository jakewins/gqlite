
// This module contains our definition of expressions, including code to convert parse streams
// to expressions.


use crate::frontend::{PlanningContext, Result, Rule};
use pest::iterators::Pair;
use crate::backend::Token;
use crate::{Val, Slot};
use std::collections::HashSet;

#[derive(Debug, PartialEq)]
pub enum Expr {
    Lit(Val),
    // Lookup a property by id
    Prop(Box<Self>, Vec<Token>),
    Slot(Slot),
    // Map expressions differ from eg. Lit(Val::Map) in that they can have expressions as
    // values, like `{ name: trim_spaces(n.name) }`, and evaluate to Val maps.
    Map(Vec<MapEntryExpr>),
    // Same as map expressions in that they differ from List(Val::List) in having nested exprs
    List(Vec<Expr>),
    FuncCall { name: Token, args: Vec<Expr> },
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
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct MapEntryExpr {
    pub key: Token,
    pub val: Expr,
}

pub(super) fn plan_expr(pc: &mut PlanningContext, expression: Pair<Rule>) -> Result<Expr> {
    for inner in expression.into_inner() {
        match inner.as_rule() {
            Rule::string => {
                let content = inner
                    .into_inner()
                    .next()
                    .expect("Strings should always have an inner value")
                    .as_str();
                return Ok(Expr::Lit(Val::String(String::from(content))));
            }
            Rule::id => {
                let tok = pc.tokenize(inner.as_str());
                return Ok(Expr::Slot(pc.get_or_alloc_slot(tok)));
            }
            Rule::prop_lookup => {
                let mut prop_lookup = inner.into_inner();
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
                let mut func_call = inner.into_inner();
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
                let exprs = inner.into_inner();
                for exp in exprs {
                    items.push(plan_expr(pc, exp)?);
                }
                return Ok(Expr::List(items));
            }
            Rule::int => {
                let v = inner.as_str().parse::<i64>()?;
                return Ok(Expr::Lit(Val::Int(v)));
            }
            Rule::float => {
                let v = inner.as_str().parse::<f64>()?;
                return Ok(Expr::Lit(Val::Float(v)));
            }
            _ => panic!(String::from(inner.as_str())),
        }
    }
    panic!("Invalid expression from parser.")
}

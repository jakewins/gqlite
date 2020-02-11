
use super::{Context, Row, Val, Expr, Error, Token};
use crate::steps::ExpandState::{InNode, NextNode};

pub trait Step: std::fmt::Debug {
    // Produce the next row
    fn next(&mut self, ctx: &mut Context, out: &mut Row) -> Result<bool, Error>;
}

#[derive(Debug)]
pub enum ExpandState {
    NextNode,
    InNode,
}

#[derive(Debug)]
pub struct Expand<'i> {
    pub src: Box<dyn Step + 'i>,

    pub src_slot: usize,

    pub rel_slot: usize,

    pub dst_slot: usize,

    pub rel_type: Token,

    // In the current adjacency list, what is the next index we should return?
    pub next_rel_index: usize,

    pub state: ExpandState,
}

impl Expand<'_> {
    pub fn new<'i> (src: Box<dyn Step + 'i>, src_slot: usize, rel_slot: usize, dst_slot: usize, rel_type: Token) -> Expand<'i> {
        return Expand{
            src,
            src_slot,
            rel_slot,
            dst_slot,
            rel_type,
            next_rel_index: 0,
            state: ExpandState::NextNode
        }
    }
}

impl<'i> Step for Expand<'i> {
    fn next(&mut self, ctx: &mut Context, out: &mut Row) -> Result<bool, Error> {
        loop {
            match &self.state {
                ExpandState::NextNode => {
                    // Pull in the next node
                    if ! self.src.next(ctx, out)? {
                        return Ok(false)
                    }
                    self.state = InNode;
                },
                ExpandState::InNode => {
                    let node = out.slots[self.src_slot].as_node_id();
                    let rels = &ctx.g.nodes[node].rels;
                    if self.next_rel_index >= rels.len() {
                        // No more rels on this node
                        self.state = NextNode;
                        self.next_rel_index = 0;
                        continue
                    }

                    let rel = &rels[self.next_rel_index];
                    self.next_rel_index += 1;

                    if rel.rel_type == self.rel_type {
                        out.slots[self.rel_slot] = Val::Rel{ node, rel_index: self.next_rel_index-1 };
                        out.slots[self.dst_slot] = Val::Node( rel.other_node );
                        return Ok(true);
                    }
                },
            }
        }
    }
}


#[derive(Debug)]
pub struct Filter;

impl Step for Filter {
    fn next(&mut self, ctx: &mut Context, out: &mut Row) -> Result<bool, Error> {
        unimplemented!()
    }
}

// For each src row, perform a full no de scan with the specified filters
#[derive(Debug)]
pub struct NodeScan<'i> {
    pub src: Box<dyn Step + 'i>,

    // Next node id in g to return
    pub next_node: usize,

    // Where should this scan write its output?
    pub slot: usize,

    // If the empty string, return all nodes, otherwise only nodes with the specified label
    pub labels: Option<Token>,
}

impl<'i> Step for NodeScan<'i> {
    fn next(&mut self, ctx: &mut Context, out: &mut Row) -> Result<bool, Error> {
        loop {
            if ctx.g.nodes.len() > self.next_node {
                let node = ctx.g.nodes.get(self.next_node).unwrap();
                if let Some(tok) = self.labels {
                    if !node.labels.contains(&tok) {
                        self.next_node += 1;
                        continue;
                    }
                }

                out.slots[self.slot] = Val::Node(self.next_node);
                self.next_node += 1;
                return Ok(true)
            }
            return Ok(false)
        }
    }
}

#[derive(Debug)]
pub struct Leaf;

impl Step for Leaf {
    fn next(&mut self, ctx: &mut Context, out: &mut Row) -> Result<bool, Error> {
        unimplemented!()
    }
}

#[derive(Debug)]
pub struct Projection {
    pub expr: Expr,
    pub alias: String,
}

#[derive(Debug)]
pub struct Return<'i> {
    pub src: Box<dyn Step + 'i>,
    pub projections: Vec<Projection>,
}

impl<'i> Step for Return<'i> {
    fn next(&mut self, ctx: &mut Context, out: &mut Row) -> Result<bool, Error> {
        let mut first = true;
        for cell in &self.projections {
            if first {
                print!("{}", cell.alias);
                first = false
            } else {
                print!(", {}", cell.alias)
            }
        }
        println!();
        while self.src.next(ctx, out)? {
            first = true;
            for cell in &self.projections {
                let v = cell.expr.eval(ctx, out)?;
                if first {
                    print!("{}", v);
                    first = false
                } else {
                    print!(", {}", v)
                }
            }
            println!();
        }
        Ok(false)
    }
}
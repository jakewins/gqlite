
use super::{Context, Row, Val, Expr, Error, Token};

pub trait Step: std::fmt::Debug {
    // Produce the next row
    fn next(&mut self, ctx: &mut Context, out: &mut Row) -> Result<bool, Error>;
}

#[derive(Debug)]
pub struct Expand<'i> {
    pub src: Box<dyn Step + 'i>,

    pub src_slot: usize,

    pub dst_slot: usize,

    pub rel_type: Token,

    // In the current adjacency list, what is the next index we should return?
    pub next_rel_index: usize,
}

impl<'i> Step for Expand<'i> {
    fn next(&mut self, ctx: &mut Context, out: &mut Row) -> Result<bool, Error> {
        unimplemented!()
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
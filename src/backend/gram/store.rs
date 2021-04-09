use super::{Token, Val, Dir};
use std::collections::{HashSet, HashMap};
use std::rc::Rc;
use std::cell::RefCell;

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub struct Version {
    xid: u32,
    // Say you have a query that does something insane, like
    //
    // MATCH () CREATE (a)
    // WITH a MATCH () CREATE (b)
    // WITH b MATCH () CREATE (c)
    //
    // Then the first match should not see *any* nodes created by the subsequent
    // CREATE statements. The second match should see nodes created by CREATE (a),
    // and the last match should see nodes created by both CREATE (a) and CREATE (b)
    //
    // Say the initial db is a billion nodes, so we'll be at 1 billion old nodes, 1 billion
    // "invisible" nodes at the first NodeScan for the first MATCH.. TL;DR this is another
    // piece of infinitely large user-controlled state, I think? we need to know this for
    // every node, rel etc
    //
    // So, we do a sort of intra-query multi-versioning, tracking not just which XID a change
    // is occurring in, but what section of a given query it happened in.. the problem with this
    // is that it blows up the amount of space we need to keep around for versions, making them
    // significantly larger.. hrm.
    //
    // TL;DR cursor stability.
    //
    // How does PG do this, for INSERT INTO SELECT FROM statements? I guess that's just one
    // level, not an arbitrary number of stable cursors layering on top of one another.. cypher
    // lets you express arbitrarily deep pipelines.. but is there any difference between that
    // and multiple INSERT INTO SELECT FROM statements within one tx? How do they handle stability
    // in that case?
    scope: u8,
}

impl Version {
    pub fn zero() -> Self {
        Version{ xid: 0, scope: 0 }
    }

    pub fn new(xid: u32, scope: u8) -> Version {
        Version{ xid, scope }
    }
}

#[derive(Debug)]
pub struct Node {
    // Identifier for this node, matches it's index into the node vector in g
    pub id: usize,
    // Identifier assigned this node in the gram file
    gid: Token,
    pub labels: HashSet<Token>,
    pub properties: HashMap<Token, Val>,
    pub rels: Vec<RelHalf>,
    pub deleted: bool,
    pub version: Version,
}

impl Node {
    pub fn at_version(&self, v: Version) -> Option<&Self> {
        if self.version.xid != v.xid || self.version.scope < v.scope {
            // Because we are single-threaded, if the latest version isn't the executing
            // tx version, then this is the version that's visible
            return Some(&self);
        }

        // TODO: This is wrong right, this makes nodes with modifications dissappear
        None
    }
}

#[derive(Debug)]
pub struct RelHalf {
    rel_type: Token,
    dir: Dir,
    other_node: usize,
    properties: Rc<RefCell<HashMap<Token, Val>>>,
    deleted: bool,
}

// Describes enough detail to go find a rel half without knowing its index
#[derive(Debug)]
struct RelLookup {
    node_id: usize,
    dir: Dir,
    rel_type: Token,
    other_node: usize,
}

#[derive(Debug)]
pub struct Graph {
    nodes: Vec<Node>,
}

impl Graph {

    pub fn get_node(&self, node_id: usize, v: Version) -> Option<&Node> {
        Some(&self.nodes[node_id])
    }

    pub fn get_node_prop(&self, node_id: usize, prop: Token) -> Option<Val> {
        self.nodes[node_id].properties.get(&prop).cloned()
    }

    pub fn get_rel_prop(&self, node_id: usize, rel_index: usize, prop: Token) -> Option<Val> {
        self.nodes[node_id].rels[rel_index]
            .properties
            .borrow()
            .get(&prop)
            .cloned()
    }

    pub fn detach_delete_node(&mut self, id: usize) {
        // TODO it's tricksy to get two mutable pointers into a vec, because
        //      the compiler can't validate - at compile time - that the indexes
        //      we ask for differ.. so we just copy the stuff we need to delete

        // From a memory POV, we could do this in batches, actually, like 10K
        // rels at a time or something, so the memory use of this function is bound
        let mut other_rels = Vec::new();
        for rh in &mut self.nodes[id].rels {
            rh.deleted = true;
            other_rels.push(RelLookup{
                node_id: rh.other_node,
                dir: rh.dir.reverse(),
                rel_type: rh.rel_type,
                other_node: id
            })
        }
        for rl in other_rels {
            for rh in &mut self.nodes[rl.node_id].rels {
                if rh.other_node == rl.other_node && rh.dir == rl.dir && rh.rel_type == rl.rel_type {
                    rh.deleted = true;
                }
            }
        }
        self.nodes[id].deleted = true;
    }

    pub fn delete_node(&mut self, id: usize) {
        // TODO should explode if rels exist
        self.nodes[id].deleted = true;
    }

    pub fn add_node(&mut self, id: usize, n: Node) {
        while self.nodes.len() <= id {
            let filler_id = self.nodes.len();
            self.nodes.push(Node {
                id: filler_id,
                gid: 0,
                labels: Default::default(),
                properties: Default::default(),
                rels: vec![],
                deleted: false,
                version: Version::zero()
            })
        }
        self.nodes[id] = n;
    }

    pub fn delete_rel(&mut self, node_id: usize, rel_index: usize) {
        let n1 = &mut self.nodes[node_id];
        let rel1 = &mut n1.rels[rel_index];
        rel1.deleted = true;
        let rel2_dir = rel1.dir.reverse();
        let rel2_other_node = n1.id;
        let rel2_rel_type = rel1.rel_type;
        let n2id = rel1.other_node;

        let n2 = &mut self.nodes[n2id];
        for r in &mut n2.rels {
            if r.other_node == rel2_other_node && r.rel_type == rel2_rel_type && r.dir == rel2_dir {
                r.deleted = true;
                break
            }
        }
    }

    // Add a rel, return the index of the rel from the start nodes perspective
    pub fn add_rel(
        &mut self,
        from: usize,
        to: usize,
        rel_type: Token,
        props: HashMap<Token, Val>,
    ) -> usize {
        let wrapped_props = Rc::new(RefCell::new(props));
        let fromrels = &mut self.nodes[from].rels;
        fromrels.push(RelHalf {
            rel_type,
            dir: Dir::Out,
            other_node: to,
            properties: Rc::clone(&wrapped_props),
            deleted: false
        });
        let index = fromrels.len() - 1;
        self.nodes[to].rels.push(RelHalf {
            rel_type,
            dir: Dir::In,
            other_node: from,
            properties: wrapped_props,
            deleted: false
        });
        index
    }
}
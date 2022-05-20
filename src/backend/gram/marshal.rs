
use super::Val;
use crate::backend::gram::{Graph, Node, Version};
use crate::backend::{Token, Tokens};
use crate::pest::Parser;
use anyhow::Result;
use pest::iterators::Pair;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fs::File;
use std::io::Read;

#[derive(Parser)]
#[grammar = "backend/gram/gram.pest"]
pub struct GramParser;

/// Indicates how large a buffer to pre-allocate before reading the entire file.
fn initial_buffer_size(file: &File) -> usize {
    // Allocate one extra byte so the buffer doesn't need to grow before the
    // final `read` call at the end of the file.  Don't worry about `usize`
    // overflow because reading will fail regardless in that case.
    file.metadata().map(|m| m.len() as usize + 1).unwrap_or(0)
}

fn read_to_string(file: &mut File) -> Result<String> {
    //todo lock this (and other io on the file)
    let mut string = String::with_capacity(initial_buffer_size(&file));
    file.read_to_string(&mut string)?;
    Ok(string)
}

struct ParserContext<'a> {
    anon_id_gen: u32,
    node_ids: Tokens,
    tokens: &'a mut Tokens,
}

fn parse_node(item: Pair<Rule>, ctx: &mut ParserContext) -> Result<Node> {
    let mut identifier: Option<String> = None;
    let mut props: HashMap<Token, Val> = HashMap::new();
    let mut labels: HashSet<Token> = HashSet::new();

    for part in item.into_inner() {
        match part.as_rule() {
            Rule::id => identifier = Some(part.as_str().to_string()),
            Rule::label => {
                for label in part.into_inner() {
                    labels.insert(ctx.tokens.tokenize(label.as_str()));
                }
            }
            Rule::map => parse_props(ctx, &mut props, part),
            _ => panic!("what? {:?} / {}", part.as_rule(), part.as_str()),
        }
    }

    let gid_string = identifier.unwrap_or_else(|| {
        // Entry with no identifier, generate one
        loop {
            let candidate = format!("anon#{}", ctx.anon_id_gen);
            if !ctx.node_ids.table.contains_key(&candidate) {
                return candidate;
            }
            ctx.anon_id_gen += 1;
        }
    });
    let gid = ctx.tokens.tokenize(&gid_string);
    let id = ctx.node_ids.tokenize(&gid_string);
    Ok(Node {
        id,
        gid,
        labels,
        properties: props,
        rels: vec![],
        deleted: false,
        version: Version::zero(),
        prior: None,
    })
}

fn parse_props(ctx: &mut ParserContext, props: &mut HashMap<usize, Val>, part: Pair<Rule>) {
    for pair in part.into_inner() {
        let mut key: Option<String> = None;
        let mut val = None;
        match pair.as_rule() {
            Rule::map_pair => {
                for pair_part in pair.into_inner() {
                    match pair_part.as_rule() {
                        Rule::id => key = Some(pair_part.as_str().to_string()),
                        Rule::expr => {
                            let stringval = pair_part.into_inner().next().unwrap();
                            let stringval_content = stringval.into_inner().next().unwrap();
                            val = Some(stringval_content.as_str().to_string())
                        }
                        _ => panic!("what? {:?} / {}", pair_part.as_rule(), pair_part.as_str()),
                    }
                }
            }
            _ => panic!("what? {:?} / {}", pair.as_rule(), pair.as_str()),
        }
        let key_str = key.unwrap();
        props.insert(ctx.tokens.tokenize(&key_str), Val::String(val.unwrap()));
    }
}

pub fn load(tokens: &mut Tokens, file: &mut File) -> Result<Graph> {
    let mut g = Graph::new();

    let query_str = read_to_string(file).unwrap();
    let mut parse_result = GramParser::parse(Rule::gram, &query_str)?;

    let gram = parse_result.next().unwrap(); // get and unwrap the `file` rule; never fails

    let node_ids = Tokens {
        table: Default::default(),
    };

    let mut pc = ParserContext {
        anon_id_gen: 0,
        node_ids,
        tokens,
    };

    for item in gram.into_inner() {
        match item.as_rule() {
            Rule::path => {
                let mut start_identifier: Option<Token> = None;
                let mut end_identifier: Option<Token> = None;

                let mut rel_type = None;
                let mut rel_props: HashMap<Token, Val> = HashMap::new();

                for part in item.into_inner() {
                    match part.as_rule() {
                        Rule::node => {
                            let n = parse_node(part, &mut pc)?;
                            if start_identifier == None {
                                start_identifier = Some(n.id);
                            } else {
                                end_identifier = Some(n.id);
                            }
                            // need like a merge_node operation; but for now, insert the
                            // first occurrence of a node, so subsequent ones won't clear out
                            // properties
                            if g.max_node_id() <= n.id {
                                g.add_node(n.id, n);
                            }
                        }
                        Rule::rel => {
                            for rel_part in part.into_inner() {
                                match rel_part.as_rule() {
                                    Rule::map => {
                                        parse_props(&mut pc, &mut rel_props, rel_part);
                                    }
                                    Rule::rel_type => {
                                        let rt_id = rel_part.into_inner().next().unwrap();
                                        rel_type = Some(pc.tokens.tokenize(
                                            rt_id.into_inner().next().unwrap().as_str(),
                                        ));
                                    }
                                    _ => panic!(
                                        "what? {:?} / {}",
                                        rel_part.as_rule(),
                                        rel_part.as_str()
                                    ),
                                }
                            }
                        }
                        _ => panic!("what? {:?} / {}", part.as_rule(), part.as_str()),
                    }
                }

                g.add_rel(
                    start_identifier.unwrap(),
                    end_identifier.unwrap(),
                    rel_type.unwrap_or_else(|| pc.tokens.tokenize("_")),
                    rel_props,
                );
            }
            Rule::node => {
                let n = parse_node(item, &mut pc)?;
                g.add_node(n.id, n)
            }
            _ => (),
        }
    }

    Ok(g)
}



pub fn store(toks: &Tokens, g: &mut Graph, file: &mut File) -> Result<()> {

    let mut out = String::with_capacity(1024);

    for n in &g.nodes {
        out.push_str(&format!("({})", toks.lookup(n.gid).unwrap()))
    }

    // println!("{}", out);

    Ok(())


}

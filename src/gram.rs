
use super::{Graph, Error, Val, Tokens, Token, Node};
use std::collections::HashMap;
use crate::pest::Parser;

#[derive(Parser)]
#[grammar = "gram.pest"]
pub struct GramParser;


pub fn load(tokens: &mut Tokens, path: &str) -> Result<Graph, Error> {
    let mut g = Graph{ nodes: vec![] };


    let query_str = std::fs::read_to_string(path).unwrap();
    let maybe_parse = GramParser::parse(Rule::gram, &query_str);

    let gram = maybe_parse
        .expect("unsuccessful parse") // unwrap the parse result
        .next().unwrap(); // get and unwrap the `file` rule; never fails

//    let id_map = HashMap::new();
    let mut node_ids = Tokens{ table: Default::default() };

    for item in gram.into_inner() {
        match item.as_rule() {
            Rule::path => {
                let mut start_identifier : Option<Token> = None;
                let mut end_identifier : Option<Token> = None;
                let mut props : HashMap<Token, Val> = HashMap::new();

                for part in item.into_inner() {
                    match part.as_rule() {
                        Rule::node => {
                            let identifier = part.into_inner().next().unwrap().as_str();
                            if start_identifier == None {
                                start_identifier = Some(node_ids.tokenize(identifier));
                            } else {
                                end_identifier = Some(node_ids.tokenize(identifier));
                            }
                        }
                        Rule::rel => {
                            for rel_part in part.into_inner() {
                                match rel_part.as_rule() {
                                    Rule::map => {

                                    }
                                    _ => panic!("what? {:?} / {}", rel_part.as_rule(), rel_part.as_str())
                                }
                            }
                        }
                        _ => panic!("what? {:?} / {}", part.as_rule(), part.as_str())
                    }
                }

                g.add_rel(start_identifier.unwrap(), end_identifier.unwrap(), tokens.tokenize("KNOWS"));
            }
            Rule::node => {
                let mut identifier : Option<String> = None;
                let mut props : HashMap<Token, Val> = HashMap::new();

                for part in item.into_inner() {
                    match part.as_rule() {
                        Rule::id => identifier = Some(part.as_str().to_string()),
                        Rule::map => {
                            for pair in part.into_inner() {
                                let mut key: Option<String> = None;
                                let mut val = None;
                                match pair.as_rule() {
                                    Rule::map_pair => {
                                        for pair_part in pair.into_inner() {
                                            match pair_part.as_rule() {
                                                Rule::id => key = Some(pair_part.as_str().to_string()),
                                                Rule::expr => val = Some(pair_part.as_str().to_string()),
                                                _ => panic!("what? {:?} / {}", pair_part.as_rule(), pair_part.as_str())
                                            }
                                        }
                                    }
                                    _ => panic!("what? {:?} / {}", pair.as_rule(), pair.as_str())
                                }
                                let key_str = key.unwrap();
                                props.insert(tokens.tokenize(&key_str), Val::String(val.unwrap()) );
                            }
                        },
                        _ => panic!("what? {:?} / {}", part.as_rule(), part.as_str())
                    }
                }

                g.add_node(node_ids.tokenize(&identifier.unwrap()), Node{
                    labels: vec![tokens.tokenize("Person")].iter().cloned().collect(),
                    properties: props,
                    rels: vec![]
                });
            },
            _ => ()
        }
    }

    return Ok(g)
}
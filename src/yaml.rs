use super::{Graph, Error, Node, Tokens, Token, Val};
use serde_yaml::{Value};
use std::collections::{HashMap, HashSet};

pub fn load_yaml_graph(tokens: &mut Tokens, path: &str) -> Result<Graph, Error> {
    let mut g = Graph{ nodes: vec![] };
    let f = std::fs::File::open("g.yaml")?;
    let d: Value = serde_yaml::from_reader(f)?;


    match d {
        Value::Mapping(m) => {
            // First pull in all the nodes
            for (k, v) in m.iter() {
                let labels = v.get("labels").and_then(|l| match l {
                        Value::Sequence(lbls) => {
                            let labels: HashSet<Token> = lbls.iter().map(|l| tokens.tokenize(l.as_str().unwrap())).collect();
                            Some(labels)
                        },
                        _ => panic!("invalid yaml")
                    }).unwrap_or(HashSet::new());
                let props = v.get("properties").and_then(|ps| match ps {
                    Value::Mapping(ps_map) => {
                        let mut properties = HashMap::new();
                        for (prop_key, prop_val) in ps_map.iter() {
                            properties.insert(tokens.tokenize( prop_key.as_str().unwrap() ), Val::String(prop_val.as_str().unwrap().to_string()));
                        }
                        Some(properties)
                    },
                    _ => panic!("invalid yaml")
                }).unwrap_or(HashMap::new());
                g.add_node(k.as_i64().unwrap() as usize, Node{
                    labels: labels,
                    properties: props,
                    rels: vec![]
                })
            }

            // Then go over again and pull in all the rels
            for (k, v) in m.iter() {
                let node_id = k.as_i64().unwrap() as usize;
                if let Some(Value::Sequence(rels)) = v.get("rels") {
                    for raw in rels.iter() {
                        if let Value::Sequence(parts) = &raw {
                            let rel_type = tokens.tokenize(parts.get(0).unwrap().as_str().unwrap());
                            let other_node = parts.get(1).unwrap().as_i64().unwrap();
                            g.add_rel(node_id, other_node as usize, rel_type);

                        }
                    }
                }

            }
        },
        _ => panic!("invalid yaml")
    }

    println!("Graph: {:?}", g);

    return Ok(g)
}


use crate::{Cursor, Error};

trait Backend<Plan, PlanCtx> {
    fn new_planning_context() -> PlanCtx;
    fn step_expand(src: Plan) -> Plan;
    fn step_node_scan(src: Plan) -> Plan;

    fn run(plan: Plan, cursor: &mut Cursor) -> Result<(), Error>;
}

mod gram {
    use crate::{Error, Cursor, Token, Val, Dir};
    use std::collections::{HashMap, HashSet};
    use std::rc::Rc;
    use std::cell::RefCell;

    struct Expand {

    }

    struct NodeScan {

    }

    enum Plan {
        Expand(Expand),
        NodeScan(NodeScan),
    }
    struct PlanningContext;

    #[derive(Debug)]
    pub struct Tokens {
        table: HashMap<String, Token>,
    }

    impl Tokens {
        fn tokenize(&mut self, contents: &str) -> Token {
            match self.table.get(contents) {
                Some(tok) => { return *tok }
                None => {
                    let tok = self.table.len();
                    self.table.insert(contents.to_string(), tok);
                    return tok
                }
            }
        }

        fn get(&self, tok: Token) -> Option<&str> {
            for (content, candidate) in self.table.iter() {
                if *candidate == tok {
                    return Some(&content);
                }
            }
            return None
        }
    }

    struct GramBackend {
        tokens: Rc<RefCell<Tokens>>,
        g: Rc<Graph>,
    }

    impl GramBackend {
        pub fn open(path: &str) -> Result<GramBackend, Error> {

            let mut tokens = Tokens { table: Default::default() };
            let mut g = parser::load(&mut tokens, path)?;

            return Ok(GramBackend {
                tokens: Rc::new(RefCell::new(tokens)), g: Rc::new(g)
            })
        }
    }

    impl super::Backend<Plan, PlanningContext> for GramBackend {
        fn new_planning_context() -> PlanningContext {
            unimplemented!()
        }

        fn step_expand(src: Plan) -> Plan {
            unimplemented!()
        }

        fn step_node_scan(src: Plan) -> Plan {
            unimplemented!()
        }

        fn run(plan: Plan, cursor: &mut Cursor) -> Result<(), Error> {
            unimplemented!()
        }
    }

    mod parser {
        use std::collections::{HashMap, HashSet};
        use crate::pest::Parser;
        use crate::backend::gram::{Tokens, Node, Graph};
        use crate::{Error, Token, Val, Dir};
        use std::rc::Rc;

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
    }


    #[derive(Debug)]
    pub struct RelHalf {
        rel_type: Token,
        dir: Dir,
        other_node: usize,
        properties: Rc<HashMap<Token, Val>>,
    }

    #[derive(Debug)]
    pub struct Node {
        labels: HashSet<Token>,
        properties: HashMap<Token, Val>,
        rels: Vec<RelHalf>,
    }

    impl Node {
        pub fn new(labels: Vec<Token>, properties: HashMap<Token, Val>) -> Node {
            return Node {
                labels: labels.iter().cloned().collect(),
                properties,
                rels: vec![]
            }
        }
    }


    #[derive(Debug)]
    pub struct Graph  {
        nodes: Vec<Node>
    }

    impl Graph {
        fn get_node_prop(&self, node_id: usize, prop: Token) -> Option<Val> {
            if let Some(v) = self.nodes[node_id].properties.get(&prop) {
                Some(v.clone())
            } else {
                None
            }
        }

        fn get_rel_prop(&self, node_id: usize, rel_index: usize, prop: Token) -> Option<Val> {
            if let Some(v) = self.nodes[node_id].rels[rel_index].properties.get(&prop) {
                Some(v.clone())
            } else {
                None
            }
        }

        fn add_node(&mut self, id: usize, n: Node) {
            self.nodes.insert(id,n);
        }

        fn add_rel(&mut self, from: usize, to: usize, rel_type: Token) {
            let props = Rc::new(Default::default());
            self.nodes[from].rels.push(RelHalf{
                rel_type,
                dir: Dir::Out,
                other_node: to,
                properties: Rc::clone(&props)
            });
            self.nodes[to].rels.push(RelHalf{
                rel_type,
                dir: Dir::In,
                other_node: from,
                properties: props,
            })
        }
    }

}
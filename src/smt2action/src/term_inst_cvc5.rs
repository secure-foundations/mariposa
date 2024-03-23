use core::panic;
use pest::{iterators::Pair, Parser};
use pest_derive::Parser;
use std::{
    collections::{HashMap, HashSet},
    fs,
};

use smt2parser::{
    concrete::{self, Symbol, Term},
    visitors::AttributeValue,
};

#[derive(Parser)]
#[grammar = "cvc5_inst.pest"]
pub struct CVC5InstParser;

#[derive(Debug)]
enum InstSExpr {
    Ident(String),
    Let(Vec<(String, InstSExpr)>, Box<InstSExpr>),
    App(Vec<InstSExpr>),
}

impl std::fmt::Display for InstSExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            InstSExpr::Ident(s) => write!(f, "{}", s),
            InstSExpr::Let(bindings, term) => {
                write!(f, "(let (")?;
                for (var, inst) in bindings {
                    write!(f, "({} {})", var, inst)?;
                }
                write!(f, ") {})", term)
            }
            InstSExpr::App(insts) => {
                write!(f, "(")?;
                for inst in insts {
                    write!(f, "{} ", inst)?;
                }
                write!(f, ")")
            }
        }
    }
}

fn parse_bind(pair: Pair<Rule>) -> Vec<(String, InstSExpr)> {
    match pair.as_rule() {
        Rule::bind => {
            let mut inner_rules = pair.into_inner();
            vec![(
                inner_rules.next().unwrap().as_str().to_string(),
                parse_term(inner_rules.next().unwrap()),
            )]
        }
        Rule::binds => pair
            .into_inner()
            .map(|bind| parse_bind(bind))
            .flatten()
            .collect(),
        _ => {
            println!("{}", pair.as_str().to_string());
            panic!("unexpected rule: {:?}", pair.as_rule())
        }
    }
}

fn parse_term(pair: Pair<Rule>) -> InstSExpr {
    match pair.as_rule() {
        // Rule::inst => {
        //     let term = pair.into_inner().next().unwrap();
        //     parse_term(term)
        // }
        Rule::ident => {
            let term = pair.as_str().to_string();
            InstSExpr::Ident(term)
        }
        Rule::term => {
            let mut inner_rules = pair.into_inner();
            if inner_rules.len() == 1 {
                return parse_term(inner_rules.next().unwrap());
            }
            let insts = inner_rules.map(|inst| parse_term(inst)).collect();
            InstSExpr::App(insts)
        }
        Rule::let_term => {
            let mut inner_rules = pair.into_inner();
            InstSExpr::Let(
                parse_bind(inner_rules.next().unwrap()),
                Box::new(parse_term(inner_rules.next().unwrap())),
            )
        }
        _ => {
            println!("{}", pair.as_str().to_string());
            panic!("unexpected rule: {:?}", pair.as_rule())
        }
    }
}

fn parse_quant(pair: Pair<Rule>) -> (String, Vec<InstSExpr>) {
    match pair.as_rule() {
        Rule::quant => {
            let mut inner_rules = pair.into_inner();
            (
                inner_rules.next().unwrap().as_str().to_string(),
                inner_rules.map(|inst| parse_term(inst)).collect(),
            )
        }
        _ => {
            panic!("unexpected rule: {:?}", pair.as_rule())
        }
    }
}

fn parse_skolem(pair: Pair<Rule>) -> (String, String) {
    match pair.as_rule() {
        Rule::skolem => {
            let mut inner_rules = pair.into_inner();
            (
                inner_rules.next().unwrap().as_str().to_string(),
                inner_rules.next().unwrap().as_str().to_string(),
            )
        }
        _ => {
            panic!("unexpected rule: {:?}", pair.as_rule())
        }
    }
}

struct Record {
    // skolem name to qid
    skolem_vars: HashMap<String, String>,
    // qid to quantified instances
    quant_insts: HashMap<String, Vec<InstSExpr>>,
    // anonymous quantified instances
    anon_quant_insts: Vec<(InstSExpr, Vec<InstSExpr>)>,
}

impl Record {
    fn new() -> Record {
        Record {
            skolem_vars: HashMap::new(),
            quant_insts: HashMap::new(),
            anon_quant_insts: Vec::new(),
        }
    }

    fn insert_qi(&mut self, qid: String, insts: Vec<InstSExpr>) {
        if let Some(entry) = self.quant_insts.get_mut(&qid) {
            entry.extend(insts);
        } else {
            self.quant_insts.insert(qid, insts);
        }
    }

    fn insert_skolem(&mut self, skolem: String, qid: String) {
        self.skolem_vars.insert(skolem, qid);
    }
}

fn parse_log(inst_file_path: &String) -> Record {
    let unparsed_file = fs::read_to_string(inst_file_path).expect("cannot read file");

    let res = CVC5InstParser::parse(Rule::file, &unparsed_file)
        .expect("unsuccessful parse")
        .next()
        .unwrap();

    if res.as_rule() != Rule::file {
        panic!("unexpected rule: {:?}", res.as_rule());
    }

    let mut record = Record::new();

    res.into_inner().for_each(|pair| match pair.as_rule() {
        Rule::quant => {
            let (qid, insts) = parse_quant(pair);
            record.insert_qi(qid, insts);
        }
        Rule::skolem => {
            let (qid, skolem) = parse_skolem(pair);
            record.insert_skolem(skolem, qid);
        }
        Rule::anon_quant => {}
        Rule::EOI => {}
        _ => {
            println!("unexpected rule: {:?}", pair.as_rule());
        }
    });
    record
}

fn collect_quantifiers_rec(
    term: &concrete::Term,
    depth: u32,
    quantifiers: &mut HashMap<Symbol, (Term, u32)>,
) -> Option<Symbol> {
    match term {
        Term::Constant(_) => None,
        Term::QualIdentifier(_) => None,
        Term::Application { arguments, .. } => {
            arguments.iter().for_each(|arg| {
                let _ = collect_quantifiers_rec(arg, depth, quantifiers);
            });
            None
        }
        Term::Forall { vars, term } => {
            let qid = collect_quantifiers_rec(term, depth + 1, quantifiers).unwrap();
            quantifiers.insert(
                qid,
                (
                    Term::Forall {
                        vars: vars.clone(),
                        term: term.clone(),
                    },
                    depth,
                ),
            );
            None
        }
        Term::Exists { vars, term } => {
            let qid = collect_quantifiers_rec(term, depth + 1, quantifiers).unwrap();
            quantifiers.insert(
                qid,
                (
                    Term::Forall {
                        vars: vars.clone(),
                        term: term.clone(),
                    },
                    depth,
                ),
            );
            None
        }
        Term::Let { var_bindings, term } => {
            var_bindings.iter().for_each(|(_, term)| {
                let _ = collect_quantifiers_rec(term, depth, quantifiers);
            });
            collect_quantifiers_rec(term, depth, quantifiers);
            None
        }
        Term::Match { term: _, cases: _ } => {
            panic!("not supporting match yet");
        }
        Term::Attributes { term, attributes } => {
            let mut res = None;
            attributes.iter().for_each(|f| {
                let concrete::Keyword(k) = &f.0;
                if k == "qid" {
                    if let AttributeValue::Symbol(s) = &f.1 {
                        res = Some(s.clone());
                    } else {
                        panic!("unexpected qid attribute value");
                    }
                }
            });
            collect_quantifiers_rec(term, depth, quantifiers);
            res
        }
    }
}

pub fn inst_cvc5(commands: &mut Vec<concrete::Command>, inst_file_path: &String) {
    let record = parse_log(inst_file_path);

    let mut quantifiers = HashMap::new();
    for command in commands.iter() {
        match command {
            concrete::Command::Assert { term } => {
                collect_quantifiers_rec(term, 0, &mut quantifiers);
            }
            _ => {}
        }
    }

    for qid in record.quant_insts.keys() {
        let qid = Symbol(qid.clone());
        let qt = quantifiers.get(&qid);
        if qt.is_none() {
            println!("qid not found in the query: {}", qid);
            continue;
        }

        let (body, depth) = qt.unwrap();

        println!("qid: {}", qid);
        println!("body {}", body);
        println!("depth {}", depth);

        for inst in record.quant_insts.get(qid.0.as_str()).unwrap() {
            println!("\t{}", inst);
        }
        break;
    }

    // for (qid, insts) in record.quant_insts.iter() {
    //     println!("qid: {}", qid);
    //     for inst in insts {
    //         println!("\t{}", inst);
    //     }
    // }
}

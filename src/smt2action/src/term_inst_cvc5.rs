use core::panic;
use pest::{iterators::Pair, Parser};
use pest_derive::Parser;
use std::{
    collections::HashMap,
    fs::{self, read_to_string},
};

use smt2parser::{
    concrete::{self, Symbol, Term},
    visitors::AttributeValue,
};

#[derive(Parser)]
#[grammar = "cvc5_inst.pest"]
pub struct CVC5InstParser;

fn collect_quantifiers_rec(term: &concrete::Term, quantifiers: &mut HashMap<Symbol, Term>) {
    match term {
        Term::Constant(_) => {}
        Term::QualIdentifier(_) => {}
        Term::Application { arguments, .. } => {
            arguments
                .iter()
                .for_each(|arg| collect_quantifiers_rec(arg, quantifiers));
        }
        Term::Forall { vars: _, term } => {
            collect_quantifiers_rec(term, quantifiers);
        }
        Term::Exists { vars: _, term } => {
            collect_quantifiers_rec(term, quantifiers);
        }
        Term::Let { var_bindings, term } => {
            var_bindings.iter().for_each(|(_, term)| {
                collect_quantifiers_rec(term, quantifiers);
            });
            collect_quantifiers_rec(term, quantifiers);
        }
        Term::Match { term: _, cases: _ } => {
            panic!("not supporting match yet");
        }
        Term::Attributes { term, attributes } => {
            attributes.iter().for_each(|f| {
                let concrete::Keyword(k) = &f.0;
                if k == "qid" {
                    if let AttributeValue::Symbol(s) = &f.1 {
                        quantifiers.insert(s.clone(), *term.clone());
                    } else {
                        panic!("unexpected qid attribute value");
                    }
                }
            });
            collect_quantifiers_rec(term, quantifiers);
        }
    }
}

#[derive(Debug)]
enum InstSExpr {
    Ident(String),
    Let(Vec<(String, InstSExpr)>, Box<InstSExpr>),
    App(Vec<InstSExpr>),
}

fn parse_inst_log(inst_file_path: &String) {
    let unparsed_file = fs::read_to_string(inst_file_path).expect("cannot read file");

    let res = CVC5InstParser::parse(Rule::file, &unparsed_file)
        .expect("unsuccessful parse") // unwrap the parse result
        .next()
        .unwrap(); // get and unwrap the `file` rule; never

    if res.as_rule() != Rule::file {
        panic!("unexpected rule: {:?}", res.as_rule());
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
            Rule::inst => {
                let term = pair.into_inner().next().unwrap();
                return parse_term(term);
            }
            Rule::ident => {
                let term = pair.as_str().to_string();
                return InstSExpr::Ident(term);
            }
            Rule::term => {
                let mut inner_rules = pair.into_inner();
                if inner_rules.len() == 1 {
                    return parse_term(inner_rules.next().unwrap());
                }
                let insts = inner_rules.map(|inst| parse_term(inst)).collect();
                return InstSExpr::App(insts);
            }
            Rule::let_term => {
                let mut inner_rules = pair.into_inner();
                return InstSExpr::Let(
                    parse_bind(inner_rules.next().unwrap()),
                    Box::new(parse_term(inner_rules.next().unwrap())),
                );
            }
            _ => {
                println!("{}", pair.as_str().to_string());
                panic!("unexpected rule: {:?}", pair.as_rule())
            }
        }
    }

    fn parse_qis(pair: Pair<Rule>) -> (String, Vec<InstSExpr>) {
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

    let mut all_qis: HashMap<String, Vec<InstSExpr>> = HashMap::new();
    for pair in res.into_inner() {
        match pair.as_rule() {
            Rule::quant => {
                let (qid, qis) = parse_qis(pair);
                all_qis.insert(qid, qis);
            }
            Rule::EOI => {}
            _ => {
                println!("unexpected rule: {:?}", pair.as_rule());
            }
        }
    }
    for qid in all_qis.keys() {
        println!("qid: {}", qid);
        let qis = all_qis.get(qid).unwrap();
        for q in qis {
            println!("\t{:?}", q);
        }
    }
}

pub fn inst_cvc5(commands: &mut Vec<concrete::Command>, inst_file_path: &String)
//  -> HashMap<Symbol, Term>
{
    parse_inst_log(inst_file_path);
    let mut quantifiers = HashMap::new();
    for command in commands.iter() {
        match command {
            concrete::Command::Assert { term } => {
                collect_quantifiers_rec(term, &mut quantifiers);
            }
            _ => {}
        }
    }
    // for (s, t) in quantifiers.iter()
    // {
    //     println!("{}: {}", s.0, t);
    // }
}

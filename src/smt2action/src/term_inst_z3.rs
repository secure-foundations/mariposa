use core::panic;
use pest::{iterators::Pair, Parser};
use pest_derive::Parser;
use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fs, path,
};

use smt2parser::{
    concrete::{self, Command, Keyword, Sort, Symbol, Term},
    visitors::AttributeValue,
};
use smt_log_parser::{
    display_with::{DisplayCtxt, DisplayWithCtxt},
    items::{MatchKind, QuantKind, Quantifier, TermIdx},
    LogParser, Z3Parser,
};

use crate::query_io::{self, get_attr_cid, get_attr_qid};

fn get_symbols(commands: &Vec<concrete::Command>) -> HashMap<String, String> {
    let mut symbols = HashSet::new();
    commands.iter().for_each(|x| {
        match x {
            concrete::Command::DeclareConst { symbol, sort: _ } => {
                symbols.insert(symbol.clone());
            }
            concrete::Command::DeclareDatatypes { datatypes } => {
                datatypes.iter().for_each(|x| {
                    // symbols.insert(x.0.clone());
                    assert_eq!(x.2.parameters.len(), 0);
                    x.2.constructors.iter().for_each(|y| {
                        symbols.insert(y.symbol.clone());
                        y.selectors.iter().for_each(|z| {
                            symbols.insert(z.0.clone());
                        });
                    });
                });
            }
            concrete::Command::DeclareDatatype { .. } => {
                panic!("Datatype not considered");
            }
            concrete::Command::DeclareFun { symbol, .. } => {
                symbols.insert(symbol.clone());
            }
            concrete::Command::DefineFun { sig, .. } => {
                symbols.insert(sig.name.clone());
            }
            concrete::Command::DeclareSort { .. } => {
                // println!("Sort symbol not considered");
                // symbols.insert(symbol.0.clone());
            }
            _ => (),
        }
    });
    symbols
        .into_iter()
        .map(|x| {
            let x = x.to_string();
            if x.starts_with("|") && x.ends_with("|") {
                (x[1..x.len() - 1].to_string(), x)
            } else {
                (x.clone(), x)
            }
        }).collect()
}

struct Inserter {
    simple_function_ids: HashSet<String>,
}

impl Inserter {
    fn new() -> Self {
        Inserter {
            simple_function_ids: HashSet::new(),
        }
    }

    fn introduce_simple_forall(&mut self, command: &concrete::Command) -> Option<concrete::Command> {
        let concrete::Command::Assert { term } = command else {
            return None;
        };
        let concrete::Term::Attributes { term, attributes } = term else {
            panic!("Expected Attributes");
        };

        let concrete::Term::Forall { vars, term } = &**term else {
            return None;
        };

        let concrete::Term::Attributes { term, attributes } = &**term else {
            panic!("Expected Attributes");
        };

        let qid = get_attr_qid(attributes);
        self.simple_function_ids.insert(qid.clone());

        Some(concrete::Command::DefineFun {
            sig: concrete::FunctionDec {
                name: Symbol(format!("fun_{}", qid)),
                parameters: vars.clone(),
                result: Sort::Simple {
                    identifier: concrete::Identifier::Simple {
                        symbol: Symbol("Bool".to_string()),
                    },
                },
            },
            term: *term.clone(),
        })
    }

    // fn create_simple_instance(&self)
}

pub fn handle_z3_trace(path: &path::Path, commands: &mut Vec<concrete::Command>) {
    let (_metadata, parser) = Z3Parser::from_file(path).unwrap();
    let parser = parser.process_all().unwrap();
    let symbols = get_symbols(commands);

    let last = commands.pop().unwrap();

    let Command::CheckSat = last else {
        panic!("Expected CheckSat");
    };

    let mut inserter = Inserter::new();

    query_io::load_mariposa_ids(commands);
    let decls = commands
        .iter()
        .filter_map(|x| inserter.introduce_simple_forall(x))
        .collect::<Vec<_>>();

    commands.extend(decls);

    let ctxt = DisplayCtxt {
        parser: &parser,
        display_term_ids: false,
        display_quantifier_name: false,
        use_mathematical_symbols: false,
        s_expr_mode: true,
        symbols: Some(symbols),
    };

    for inst in &parser.insts.matches {
        match &inst.kind {
            MatchKind::Quantifier {
                quant, bound_terms, ..
            } => {
                if let Quantifier {
                    kind: QuantKind::NamedQuant(name_id),
                    ..
                } = parser.quantifiers[*quant]
                {
                    let name = &parser.strings[name_id];
                    println!("{}", name);

                    if inserter.simple_function_ids.contains(name) {
                        println!("(assert (|fun_{}| ", name);
                        for bound_term in bound_terms {
                            print!("\t{}\n", TermIdx(bound_term.0).with(&ctxt));
                        }
                        println!("))");
                        continue;
                    }
                    // println!();
                    // if !qid_to_usage_count.contains_key(name) {
                    //     qid_to_usage_count.insert(name, 0);
                    // }
                    // qid_to_usage_count.insert(name, qid_to_usage_count[name] + 1);
                }
            }
            _ => {}
        }
    }

    commands.push(Command::CheckSat);
}

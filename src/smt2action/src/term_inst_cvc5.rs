use core::panic;
use pest::{iterators::Pair, Parser};
use pest_derive::Parser;
use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fs,
    hash::Hash,
};

use smt2parser::{
    concrete::{self, Command, Symbol, Term},
    visitors::AttributeValue,
};

use crate::{term_match::make_simple_qual_identifier_term, term_substitute::Substituter};

#[derive(Parser)]
#[grammar = "cvc5_inst.pest"]
pub struct CVC5InstParser;

#[derive(Debug)]
enum InstSExpr {
    Ident(String),
    Let(Vec<(String, InstSExpr)>, Box<InstSExpr>),
    List(Vec<InstSExpr>),
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
            InstSExpr::List(insts) => {
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
            let inner_rules = pair.into_inner();
            let insts = inner_rules.map(|inst| parse_term(inst)).collect();
            InstSExpr::List(insts)
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
    skolem_vars: BTreeMap<String, String>,
    // qid to quantified instances
    quant_insts: BTreeMap<String, Vec<InstSExpr>>,
    // anonymous quantified instances
    anon_quant_insts: Vec<(InstSExpr, Vec<InstSExpr>)>,
}

impl Record {
    fn new() -> Record {
        Record {
            skolem_vars: BTreeMap::new(),
            quant_insts: BTreeMap::new(),
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
    quantifiers: &mut BTreeMap<Symbol, (Term, u32)>,
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

// fn substitute(term: concrete::Term, vars: BTreeMap<Symbol, concrete::Term>)
// {
//     match term {
//         concrete::Term::Constant(_) => {}
//         concrete::Term::QualIdentifier(_) => {}
//         concrete::Term::Application { function, arguments } => {
//             let new_args = arguments.iter().map(|arg| substitute(arg.clone(), vars.clone())).collect();
//             concrete::Term::Application {
//                 function: function.clone(),
//                 arguments: new_args,
//             }
//         }
//         concrete::Term::Forall { vars, term } => {
//             let new_vars = vars.iter().map(|var| {
//                 let new_term = substitute(term.clone(), vars.clone());
//                 concrete::Term::Forall {
//                     vars: vars.clone(),
//                     term: new_term,
//                 }
//             }).collect();
//             concrete::Term::Forall {
//                 vars: vars.clone(),
//                 term: term.clone(),
//             }
//         }
//         concrete::Term::Exists { vars, term } => {
//             let new_vars = vars.iter().map(|var| {
//                 let new_term = substitute(term.clone(), vars.clone());
//                 concrete::Term::Exists {
//                     vars: vars.clone(),
//                     term: new_term,
//                 }
//             }).collect();
//             concrete::Term::Exists {
//                 vars: vars.clone(),
//                 term: term.clone(),
//             }
//         }
//         concrete::Term::Let { var_bindings, term } => {
//             let new_bindings = var_bindings.iter().map(|(var, term)| {
//                 let new_term = substitute(term.clone(), vars.clone());
//                 (var.clone(), new_term)
//             }).collect();
//             let new_term = substitute(term.clone(), vars.clone());
//             concrete::Term::Let {
//                 var_bindings: new_bindings,
//                 term: new_term,
//             }
//         }
//         concrete::Term::Match { term, cases } => {
//             panic!("NYI");
//         }
//         concrete::Term::Attributes { term, attributes } => {
//             let new_term = substitute(term.clone(), vars.clone());
//         }
//         panic!("NYI");
//     }
// }

// pub fn get_datatypes(command: &concrete::Command) {
//     match command {
//         Command::DeclareDatatypes { datatypes } => {
//             datatypes.iter().for_each(|x| {
//                 println!("datatype: {}", x.0);
//                 // symbols.insert(x.0.clone());
//                 // assert_eq!(x.2.parameters.len(), 0);
//                 x.2.constructors.iter().for_each(|y| {
//                     println!("\tconstructor: {}", y.symbol.0);
//                     y.selectors.iter().for_each(|z| {
//                         println!("\t\tselector: {} {}", z.0, z.1);
//                     });
//                 });
//             });
//         }
//         _ => (),
//     }
// }

pub fn inst_cvc5(commands: &mut Vec<concrete::Command>, inst_file_path: &String) {
    let record = parse_log(inst_file_path);

    // commands.iter().for_each(|command| get_datatypes(command));

    let mut quantifiers = BTreeMap::new();
    for command in commands.iter() {
        match command {
            concrete::Command::Assert { term } => {
                collect_quantifiers_rec(term, 0, &mut quantifiers);
            }
            // concrete::Command::DeclareDatatypes { datatypes } => {
            //     panic!("not supporting datatypes yet");
            // }
            _ => {}
        }
    }

    // let mut mismatch = 0;
    // let mut missed_qids = HashMap::new();
    // let mut inst_var_id = 0;

    // for qid in record.quant_insts.keys() {
    //     let qid = Symbol(qid.clone());
    //     let qt = quantifiers.get(&qid);

    //     if qt.is_none() {
    //         println!("qid not found in the query: {}", qid);
    //         continue;
    //     }

    //     let (quantifier, depth) = qt.unwrap();

    //     if *depth != 0 {
    //         continue;
    //     }

    //     if let concrete::Term::Forall { vars, term } = quantifier {
    //         for inst in record.quant_insts.get(qid.0.as_str()).unwrap() {
    //             if let InstSExpr::List(args) = inst {
    //                 if vars.len() != args.len() {
    //                     continue;
    //                     // println!("qid: {}", qid);
    //                     // println!("quanti: {}", quantifier);
    //                     // for arg in args {
    //                     //     println!("\t\t{}", arg);
    //                     // }
    //                     // println!();
    //                 }
    //                 let mut subst: HashMap<concrete::Symbol, concrete::Term> = HashMap::new();
    //                 for (var, inst) in vars.iter().zip(args.iter()) {
    //                     let inst = std::format!("{}", inst);
    //                     let i_var = Symbol(std::format!("inst_var_{}", inst_var_id));
    //                     println!("(define-fun {} () {} {})", i_var, var.1, inst);
    //                     subst.insert(
    //                         var.0.clone(),
    //                         make_simple_qual_identifier_term(i_var)
    //                     );
    //                     inst_var_id += 1;
    //                 }
    //                 let mut sub = Substituter::new(subst);
    //                 if let concrete::Term::Attributes { term, .. } = &**term {
    //                     println!("term before inst: {}", term);
    //                     let mut term = *term.clone();
    //                     sub.substitute(&mut term);
    //                     println!("term after inst: {}", term);
    //                 } else {
    //                     panic!("unexpected term");
    //                 }
    //             } else {
    //                 panic!("unexpected inst");
    //             }
    //             // for var in vars {
    //             //     subst.insert(var.clone(), concrete::Term::Constant(concrete::Constant("0".to_owned())));
    //             // }
    //             // println!("\t{}", inst);
    //         }

    //         // let new_term = substitute(term.clone(), subst);
    //         // println!("new term: {}", new_term);
    //     } else {
    //         panic!("NYI");
    //     }
    // }
    // // println!("mismatch: {}/{}", mismatch, total);
    // // for (qid, args) in missed_qids {
    // //     println!("qid: {}", qid);
    // //     println!("args: {:?}", args);
    // // }
}

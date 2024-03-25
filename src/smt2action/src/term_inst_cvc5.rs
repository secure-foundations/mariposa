use core::panic;
use if_chain::if_chain;
use pest::{iterators::Pair, Parser};
use pest_derive::Parser;
use std::{collections::BTreeMap, fs};

use smt2parser::{
    concrete::{self, Symbol, Term},
    visitors::AttributeValue,
};

#[derive(Parser)]
#[grammar = "cvc5_inst.pest"]
pub struct CVC5InstParser;

#[derive(Debug)]
enum InstSExpr {
    Atom(String),
    List(Vec<InstSExpr>),
}

impl std::fmt::Display for InstSExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            InstSExpr::Atom(s) => write!(f, "{}", s),
            InstSExpr::List(l) => {
                write!(f, "(")?;
                for (i, e) in l.iter().enumerate() {
                    write!(f, "{}", e)?;
                    if i != l.len() - 1 {
                        write!(f, " ")?;
                    }
                }
                write!(f, ")")
            }
        }
    }
}

fn parse_term(pair: Pair<Rule>) -> InstSExpr {
    match pair.as_rule() {
        Rule::atom => InstSExpr::Atom(pair.as_str().to_string()),
        Rule::term => parse_term(pair.into_inner().next().unwrap()),
        Rule::list => {
            let inner_rules = pair.into_inner();
            InstSExpr::List(inner_rules.map(|inst| parse_term(inst)).collect())
        }
        _ => {
            println!("{}", pair.as_str().to_string());
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
    fn new(inst_file_path: &String) -> Record {
        let unparsed_file = fs::read_to_string(inst_file_path).expect("cannot read file");

        let mut record = Record {
            skolem_vars: BTreeMap::new(),
            quant_insts: BTreeMap::new(),
            anon_quant_insts: Vec::new(),
        };

        CVC5InstParser::parse(Rule::file, &unparsed_file)
            .expect("unsuccessful parse")
            .next()
            .unwrap()
            .into_inner()
            .for_each(|pair| record.parse_entry(pair));
        record
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

    fn parse_entry(&mut self, pair: Pair<Rule>) {
        match pair.as_rule() {
            Rule::quant => {
                let mut inner_rules = pair.into_inner();
                let qid = inner_rules.next().unwrap().as_str().to_string();
                let insts = inner_rules.map(|inst| parse_term(inst)).collect();
                self.insert_qi(qid, insts);
            }
            Rule::anon_quant => {}
            Rule::skolem => {
                let mut inner_rules = pair.into_inner();
                let skolem = inner_rules.next().unwrap().as_str().to_string();
                let qid = inner_rules.next().unwrap().as_str().to_string();
                self.insert_skolem(skolem, qid);
            }
            Rule::EOI => {}
            _ => {
                println!("unexpected rule: {:?}", pair.as_rule());
            }
        }
    }
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

fn create_instance(term: &Term, args: &InstSExpr) {
    if_chain! {
        if let concrete::Term::Forall { vars, term } = term;
        if let concrete::Term::Attributes { term, .. } = &**term;
        if let InstSExpr::List(args) = args;
        if vars.len() == args.len();
        then {
            println!("{}", term);
        } else {
            panic!("NYI");
        }
    }
}

pub fn inst_cvc5(commands: &mut Vec<concrete::Command>, inst_file_path: &String) {
    let record = Record::new(inst_file_path);
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

    for qid in record.quant_insts.keys() {
        let qexp = &quantifiers[&Symbol(qid.clone())];
        println!("qid: {}", qid);
        println!("qexp: {}", &qexp.0);
        for inst in record.quant_insts.get(qid).unwrap() {
            // println!("\t{}", inst);
            create_instance(&qexp.0, &inst);
        }
    }
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

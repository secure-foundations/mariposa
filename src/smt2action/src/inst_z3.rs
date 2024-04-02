use rand::seq::IteratorRandom;
use smt2parser::concrete::{self, Command, Sort, Symbol, Term};
use smt_log_parser::{
    display_with::{DisplayCtxt, DisplayWithCtxt},
    items::{MatchKind, QuantKind, Quantifier, TermIdx},
    LogParser, Z3Parser,
};
use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use crate::{
    query_io::{find_goal_command_index, get_attr_qid},
    term_match::{mk_simple_qual_id, mk_simple_qual_id_term},
};

fn mk_fun_forall(qid: &String) -> String {
    format!("fun_forall_{}", qid)
}

struct Converter {
    simple_function_ids: HashSet<String>,
}

impl Converter {
    fn new() -> Self {
        Converter {
            simple_function_ids: HashSet::new(),
        }
    }

    fn introduce_simple_forall(
        &mut self,
        command: &mut concrete::Command,
    ) -> Option<concrete::Command> {
        let concrete::Command::Assert { term } = command else {
            return None;
        };
        let concrete::Term::Attributes {
            term,
            attributes: _,
        } = term
        else {
            panic!("Expected Attributes");
        };
        let concrete::Term::Forall {
            ref vars,
            ref mut term,
        } = **term
        else {
            return None;
        };
        Some(self.replace_forall_body(term, vars))
    }

    fn replace_forall_body(&mut self, term: &mut Term, vars: &Vec<(Symbol, Sort)>) -> Command {
        let concrete::Term::Attributes {
            term: body,
            attributes,
        } = term
        else {
            panic!("Expected Attributes");
        };
        let qid = get_attr_qid(attributes);
        let fid = mk_fun_forall(qid);
        self.simple_function_ids.insert(fid.clone());

        let arguments = vars
            .iter()
            .map(|x| mk_simple_qual_id_term(x.0.clone()))
            .collect::<Vec<_>>();
        let mut call = Box::new(Term::Application {
            qual_identifier: mk_simple_qual_id(Symbol(fid.clone())),
            arguments,
        });

        std::mem::swap(body, &mut call);

        concrete::Command::DefineFun {
            sig: concrete::FunctionDec {
                name: Symbol(fid.clone()),
                parameters: vars.clone(),
                result: Sort::Simple {
                    identifier: concrete::Identifier::Simple {
                        symbol: Symbol("Bool".to_string()),
                    },
                },
            },
            term: *call,
        }
    }
}

pub fn preprocess_for_instantiation(commands: &mut Vec<concrete::Command>) {
    let mut inserter = Converter::new();

    let goal_index = find_goal_command_index(commands);
    let rest = commands.split_off(goal_index);
    let temp = commands.drain(..);

    let temp = temp
        .into_iter()
        .map(|mut x| {
            if let Some(d) = inserter.introduce_simple_forall(&mut x) {
                vec![d, x]
            } else {
                vec![x]
            }
        })
        .flatten()
        .collect::<Vec<_>>();

    commands.extend(temp);
    commands.extend(rest);
}

struct Inserter {
    total_qi_count: usize,
    skipped_qi_count: usize,
    failed_qi_count: usize,

    defined_symbols: HashMap<String, String>,
    forall_fun_symbols: HashSet<String>,
}

impl Inserter {
    fn new(commands: &Vec<concrete::Command>) -> Self {
        let mut ins = Inserter {
            total_qi_count: 0,
            skipped_qi_count: 0,
            failed_qi_count: 0,
            defined_symbols: HashMap::new(),
            forall_fun_symbols: HashSet::new(),
        };
        ins.init_symbols(commands);
        ins
    }

    fn init_symbols(&mut self, commands: &Vec<concrete::Command>) {
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
                    if symbol.0.starts_with("fun_forall_") {
                        self.forall_fun_symbols.insert(symbol.0.clone());
                    }
                }
                concrete::Command::DefineFun { sig, .. } => {
                    symbols.insert(sig.name.clone());
                }
                concrete::Command::DeclareSort { .. } => {
                    // println!("Sort symbol not considered");
                }
                _ => (),
            }
        });
        let symbols = symbols
            .into_iter()
            .map(|x| {
                let x = x.to_string();
                if x.starts_with("|") && x.ends_with("|") {
                    (x[1..x.len() - 1].to_string(), x)
                } else {
                    (x.clone(), x)
                }
            })
            .collect();
        self.defined_symbols = symbols;
    }
}

pub fn handle_z3_trace(path: &std::path::Path, commands: &mut Vec<concrete::Command>, max_inst: usize) {
    let (_metadata, parser) = Z3Parser::from_file(path).unwrap();
    let parser = parser.process_all().unwrap();
    let mut inserter = Inserter::new(commands);

    let goal_index = find_goal_command_index(commands);
    let rest = commands.split_off(goal_index);

    let ctxt = DisplayCtxt {
        parser: &parser,
        display_term_ids: false,
        display_quantifier_name: false,
        use_mathematical_symbols: false,
        s_expr_mode: true,
        symbols: inserter.defined_symbols.clone(),
        missing_symbols: HashSet::new(),
    };

    let mut inst_cmds: Vec<concrete::Command> = Vec::new();

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

                    if inserter.forall_fun_symbols.contains(name) {
                        let mut ok = true;
                        let mut instance = "\n".to_string();
                        for bound_term in bound_terms.iter().rev() {
                            let res = write!(instance, "\t{}\n", TermIdx(bound_term.0).with(&ctxt));
                            if res.is_err() {
                                ok = false;
                                break;
                            }
                        }

                        if ok {
                            // println!("name: {}", name);
                            // println!("Instance: {}", instance);
                            let instance = format!(
                                "(assert (|{}| {}))",
                                mk_fun_forall(&name.to_string()),
                                instance
                            );
                            inst_cmds.push(Command::MariposaArbitrary(instance));
                        } else {
                            inserter.failed_qi_count += 1;
                        }
                    } else {
                        inserter.skipped_qi_count += 1;
                    }
                    inserter.total_qi_count += 1;
                }
            }
            _ => {}
        }
    }

    let sample: Vec<_> = inst_cmds.into_iter()
        .choose_multiple(&mut rand::thread_rng(), max_inst);

    println!(
        "Total QI count: {}, Skipped QI count: {}, Failed QI count: {}",
        inserter.total_qi_count, inserter.skipped_qi_count, inserter.failed_qi_count
    );
    commands.extend(sample);
    commands.extend(rest);
}

// struct Replacer {
//     // function_ids: HashSet<String>,
//     forall_defs: Vec<concrete::Command>,
//     exists_defs: Vec<concrete::Command>,
//     fun_id: usize,
// }

// fn introduce_fun_forall(
//     rep: &mut Replacer,
//     cur_term: &mut Term,
//     call: Option<Term>,
// ) -> Option<Term> {
//     match cur_term {
//         Term::Constant(_) => {}
//         Term::QualIdentifier(_) => {}
//         Term::Application { arguments, .. } => {
//             arguments
//                 .iter_mut()
//                 .for_each(|arg| assert!(introduce_fun_forall(rep, arg, None).is_none()));
//         }
//         Term::Forall { vars, term } => {
//             let arguments = vars
//                 .iter()
//                 .map(|x| mk_simple_qual_id_term(x.0.clone()))
//                 .collect::<Vec<_>>();

//             rep.fun_id += 1;

//             let app = Term::Application {
//                 qual_identifier: mk_simple_qual_id(Symbol(fid.clone())),
//                 arguments,
//             };

//             let body = introduce_fun_forall(rep, term, Some(app)).unwrap();

//             let fun = concrete::Command::DefineFun {
//                 sig: concrete::FunctionDec {
//                     name: Symbol(fid),
//                     parameters: vars.clone(),
//                     result: Sort::Simple {
//                         identifier: concrete::Identifier::Simple {
//                             symbol: Symbol("Bool".to_string()),
//                         },
//                     },
//                 },
//                 term: body,
//             };

//             rep.forall_defs.push(fun);
//         }
//         Term::Exists { vars, term } => {
//             let arguments = vars
//                 .iter()
//                 .map(|x| mk_simple_qual_id_term(x.0.clone()))
//                 .collect::<Vec<_>>();

//             let fid = format!("fun_exists_{}", rep.fun_id);
//             rep.fun_id += 1;

//             let app = Term::Application {
//                 qual_identifier: mk_simple_qual_id(Symbol(fid.clone())),
//                 arguments,
//             };

//             let body = introduce_fun_forall(rep, term, Some(app)).unwrap();

//             let fun = concrete::Command::DefineFun {
//                 sig: concrete::FunctionDec {
//                     name: Symbol(fid),
//                     parameters: vars.clone(),
//                     result: Sort::Simple {
//                         identifier: concrete::Identifier::Simple {
//                             symbol: Symbol("Bool".to_string()),
//                         },
//                     },
//                 },
//                 term: body,
//             };

//             rep.exists_defs.push(fun);
//         }
//         Term::Let { var_bindings, term } => {
//             var_bindings.iter_mut().for_each(|(_, term)| {
//                 introduce_fun_forall(rep, term, None);
//             });
//             introduce_fun_forall(rep, term, None);
//         }
//         Term::Match { term: _, cases: _ } => {
//             panic!("not supporting match yet");
//         }
//         Term::Attributes { term, attributes } => {
//             if call.is_none() {
//                 println!("Attributes: {}", term);
//                 introduce_fun_forall(rep, term, None);
//             } else {
//                 let mut call = Box::new(call.unwrap());
//                 introduce_fun_forall(rep, term, None);
//                 std::mem::swap(term, &mut call);
//                 return Some(*call);
//             }
//         }
//     }
//     None
// }

// pub fn replace_quant(commands: &mut Vec<concrete::Command>) {
//     let mut rep = Replacer {
//         forall_defs: Vec::new(),
//         exists_defs: Vec::new(),
//         fun_id: 0,
//     };
//     commands
//         .iter_mut()
//         .for_each(|x| match x {
//             concrete::Command::Assert { term } => {
//                 let concrete::Term::Attributes {
//                     term,
//                     attributes: _,
//                 } = term
//                 else {
//                     panic!("Expected Attributes");
//                 };
//                 assert!(introduce_fun_forall(&mut rep, term, None).is_none());
//             }
//             _ => {}
//         });
//     commands.extend(rep.forall_defs.drain(..));
//     commands.extend(rep.exists_defs.drain(..));
// }

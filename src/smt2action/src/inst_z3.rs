use smt2parser::concrete::{self, Command, Sort, Symbol, Term};
use smt_log_parser::{
    display_with::{DisplayCtxt, DisplayWithCtxt},
    items::{MatchKind, QuantKind, Quantifier, TermIdx},
    LogParser, Z3Parser,
};
use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use crate::{
    query_io::{find_goal_command_index, get_attr_cid_usize, get_attr_qid},
    term_match::{mk_simple_qual_id, mk_simple_qual_id_term},
};

fn mk_fun_forall(qid: &String) -> String {
    format!("fun_forall_{}", qid)
}

fn unquote_symbol(s: &Symbol) -> String {
    let s = &s.0;
    if s.starts_with("|") && s.ends_with("|") {
        s[1..s.len() - 1].to_string()
    } else {
        s.clone()
    }
}

fn introduce_simple_forall(command: &mut concrete::Command) -> Option<concrete::Command> {
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
    Some(replace_forall_body(term, vars))
}

fn replace_forall_body(term: &mut Term, vars: &Vec<(Symbol, Sort)>) -> Command {
    let concrete::Term::Attributes {
        term: body,
        attributes,
    } = term
    else {
        panic!("Expected Attributes");
    };
    let qid = get_attr_qid(attributes);
    let fid = mk_fun_forall(qid);

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

pub fn preprocess_for_instantiation(commands: &mut Vec<concrete::Command>) {
    let goal_index = find_goal_command_index(commands);
    let rest = commands.split_off(goal_index);

    let temp = commands
        .drain(..)
        .into_iter()
        .map(|mut x| {
            if let Some(d) = introduce_simple_forall(&mut x) {
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
    max_cid: usize,
    defined_symbols: HashMap<String, String>,
    forall_fun_symbols: HashSet<String>,

    unhandled_qids: HashMap<String, usize>,
    malformed_qids: HashMap<String, usize>,
    wellformed_qids: HashMap<String, Vec<Command>>,
}

impl Inserter {
    fn new(commands: &Vec<concrete::Command>) -> Self {
        let mut ins = Inserter {
            max_cid: 0,
            defined_symbols: HashMap::new(),
            forall_fun_symbols: HashSet::new(),

            unhandled_qids: HashMap::new(),
            malformed_qids: HashMap::new(),
            wellformed_qids: HashMap::new(),
        };
        ins.init_symbols(commands);
        // since max is present, add 1
        ins.max_cid += 1;
        ins
    }

    fn init_symbols(&mut self, commands: &Vec<concrete::Command>) {
        let mut symbols = HashSet::new();
        commands.iter().for_each(|x| {
            match x {
                concrete::Command::Assert { term } => {
                    let concrete::Term::Attributes { attributes, .. } = term else {
                        panic!("Expected Attributes");
                    };
                    let cid = get_attr_cid_usize(attributes);
                    self.max_cid = self.max_cid.max(cid);
                }
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
                concrete::Command::DeclareFun { symbol, .. } => {
                    symbols.insert(symbol.clone());
                }
                concrete::Command::DefineFun { sig, .. } => {
                    let symbol = sig.name.clone();
                    symbols.insert(symbol.clone());
                    if symbol.0.starts_with("fun_forall_") {
                        self.forall_fun_symbols.insert(symbol.0);
                    }
                }
                concrete::Command::DeclareDatatype { .. } => {
                    panic!("Datatype not considered");
                }
                // concrete::Command::DeclareSort { .. } => { }
                _ => (),
            }
        });

        self.defined_symbols = symbols
            .into_iter()
            .map(|x| (unquote_symbol(&x), x.to_string()))
            .collect();
    }

    fn fun_name<'a>(
        &mut self,
        ctxt: &DisplayCtxt<'a>,
        qid: &String,
        bound_terms: &Vec<smt_log_parser::items::ENodeIdx>,
    ) {
        let fname = mk_fun_forall(qid);
        if self.forall_fun_symbols.contains(&fname) {
            let mut ok = true;
            let mut instance = "\n".to_string();
            for bound_term in bound_terms.iter().rev() {
                let res = write!(instance, "\t{}\n", TermIdx(bound_term.0).with(&ctxt));
                if res.is_err() || instance.len() > 2048 {
                    ok = false;
                    break;
                }
            }

            if ok {
                let instance = format!(
                    "(assert (!(|{}| {}) :named mariposa_cid_{}))",
                    fname, instance, self.max_cid,
                );
                self.max_cid += 1;
                self.wellformed_qids
                    .entry(qid.to_string())
                    .or_insert(Vec::new())
                    .push(Command::MariposaArbitrary(instance));
            } else {
                *self.malformed_qids.entry(qid.to_string()).or_insert(0) += 1;
            }
        } else {
            *self.unhandled_qids.entry(qid.to_string()).or_insert(0) += 1;
        }
    }

    fn debug(&self) {
        let unhandled = self.unhandled_qids.values().sum::<usize>();
        let malformed = self.malformed_qids.values().sum::<usize>();
        let wellformed = self
            .wellformed_qids
            .values()
            .map(|x| x.len())
            .sum::<usize>();

        println!("Unhandled Insts ({}):", unhandled);
        let mut qids: Vec<_> = self.unhandled_qids.iter().collect();
        qids.sort_by(|a, b| b.1.cmp(a.1));
        for (qid, count) in qids {
            println!("\t{}: {}", qid, count);
        }
        println!("\nMalformed Insts ({}):", malformed);
        let mut qids: Vec<_> = self.malformed_qids.iter().collect();
        qids.sort_by(|a, b| b.1.cmp(a.1));
        for (qid, count) in qids {
            println!("\t{}: {}", qid, count);
        }
        println!("\nWellformed Insts ({})", wellformed);
    }

    fn insts_error_free(mut self, commands: &mut Vec<concrete::Command>, max_inst: usize) {
        let max_inst = if max_inst == 0 { usize::MAX } else { max_inst };
        let mut selected_qids: HashSet<String> = HashSet::new();
        let mut selected_insts: Vec<concrete::Command> = Vec::new();

        let temp = std::mem::replace(&mut self.wellformed_qids, HashMap::new());
        let mut temp: Vec<(String, Vec<Command>)> = temp.into_iter().collect::<Vec<_>>();
        temp.sort_by(|a, b| a.1.len().cmp(&b.1.len()));

        for (qid, insts) in temp.iter_mut() {
            if self.malformed_qids.contains_key(&qid.to_string()) {
                continue;
            }
            if selected_insts.len() >= max_inst {
                break;
            }
            selected_insts.extend(insts.drain(..));
            selected_qids.insert(qid.clone());
        }

        // if we still need more instances
        if selected_insts.len() < max_inst {
            for (_, insts) in temp.iter_mut() {
                if selected_insts.len() >= max_inst {
                    break;
                }
                selected_insts.extend(insts.drain(..));
            }
        }

        commands.retain(|x| match x {
            concrete::Command::Assert { term } => {
                let concrete::Term::Attributes { term, .. } = term else {
                    panic!("Expected Attributes");
                };
                if let Term::Forall { term, .. } = &**term {
                    let Term::Attributes { attributes, .. } = &**term else {
                        panic!("Expected Attributes");
                    };
                    let qid = get_attr_qid(attributes);
                    !selected_qids.contains(qid)
                } else {
                    true
                }
            }
            _ => true,
        });

        self.debug();
        println!("Selected Insts ({})", selected_insts.len());
        commands.extend(selected_insts);
    }
}

pub fn handle_z3_trace_v2(
    path: &std::path::Path,
    commands: &mut Vec<concrete::Command>,
    max_inst: usize,
) {
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
                    let name = &parser.strings[name_id].to_string();
                    inserter.fun_name(&ctxt, name, bound_terms);
                }
            }
            _ => {}
        }
    }

    inserter.insts_error_free(commands, max_inst);
    commands.extend(rest);
}

// pub fn handle_z3_trace(
//     path: &std::path::Path,
//     commands: &mut Vec<concrete::Command>,
//     max_inst: usize,
// ) {
//     let (_metadata, parser) = Z3Parser::from_file(path).unwrap();
//     let parser = parser.process_all().unwrap();
//     let mut inserter = Inserter::new(commands);

//     let goal_index = find_goal_command_index(commands);
//     let rest = commands.split_off(goal_index);

//     let ctxt = DisplayCtxt {
//         parser: &parser,
//         display_term_ids: false,
//         display_quantifier_name: false,
//         use_mathematical_symbols: false,
//         s_expr_mode: true,
//         symbols: inserter.defined_symbols.clone(),
//         missing_symbols: HashSet::new(),
//     };

//     let mut inst_cmds: Vec<concrete::Command> = Vec::new();

//     for inst in &parser.insts.matches {
//         match &inst.kind {
//             MatchKind::Quantifier {
//                 quant, bound_terms, ..
//             } => {
//                 if let Quantifier {
//                     kind: QuantKind::NamedQuant(name_id),
//                     ..
//                 } = parser.quantifiers[*quant]
//                 {
//                     let name = &parser.strings[name_id];
//                     let name = mk_fun_forall(&name.to_string());

//                     if inserter.forall_fun_symbols.contains(&name) {
//                         let mut ok = true;
//                         let mut instance = "\n".to_string();
//                         for bound_term in bound_terms.iter().rev() {
//                             let res = write!(instance, "\t{}\n", TermIdx(bound_term.0).with(&ctxt));
//                             if res.is_err() {
//                                 ok = false;
//                                 break;
//                             }
//                         }

//                         if ok && instance.len() < 4096 {
//                             let instance = format!(
//                                 "(assert (!(|{}| {}) :named mariposa_cid_{}))",
//                                 &name.to_string(),
//                                 instance,
//                                 inserter.max_cid,
//                             );
//                             inserter.max_cid += 1;
//                             inst_cmds.push(Command::MariposaArbitrary(instance));
//                         } else {
//                             inserter.failed_qi_count += 1;
//                         }
//                     } else {
//                         inserter.skipped_qi_count += 1;
//                     }
//                     inserter.total_qi_count += 1;
//                 }
//             }
//             _ => {}
//         }
//     }

//     let max_inst = if max_inst == 0 {
//         inst_cmds.len()
//     } else {
//         max_inst
//     };

//     println!(
//         "Total QI count: {}, Skipped QI count: {}, Failed QI count: {}",
//         inserter.total_qi_count, inserter.skipped_qi_count, inserter.failed_qi_count
//     );

//     let sample: Vec<_> = inst_cmds
//         .into_iter()
//         .choose_multiple(&mut rand::thread_rng(), max_inst);

//     commands.extend(sample);
//     commands.extend(rest);
// }

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

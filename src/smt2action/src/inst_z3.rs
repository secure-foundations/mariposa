use smt2parser::{
    concrete::{self, Command, Identifier, QualIdentifier, Sort, Symbol, Term},
    visitors::FunctionDec,
};
use smt_log_parser::{
    display_with::{DisplayCtxt, DisplayWithCtxt},
    items::{MatchKind, QuantKind, Quantifier, TermIdx},
    parsers::z3::inst,
    LogParser, Z3Parser,
};
use std::fmt::Write;
use std::{
    borrow::Borrow,
    collections::{HashMap, HashSet},
    hash::Hash,
};

use crate::{
    query_io::{
        find_goal_command_index, get_actual_asserted_term, get_mariposa_cid_usize, get_mariposa_qid,
    },
    term_match::{
        is_qf_term, match_simple_app_term, match_simple_qual_identifier, mk_simple_qual_id,
        mk_simple_qual_id_term,
    },
    term_substitute::Substituter,
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

const MARIPOSA_FORALL_FUN_PREFIX: &str = "fun_forall_mariposa_qid_";

fn get_diverted_fname(term: &Term) -> Option<String> {
    match term {
        concrete::Term::Application {
            qual_identifier, ..
        } => {
            let fname = qual_identifier.to_string();
            if fname.starts_with(MARIPOSA_FORALL_FUN_PREFIX) {
                Some(fname)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn replace_forall_body(term: &mut Term) -> Option<Command> {
    let concrete::Term::Forall {
        ref vars,
        ref mut term,
    } = term
    else {
        return None;
    };

    let term: &mut concrete::Term = &mut **term;

    let concrete::Term::Attributes {
        term: body,
        attributes,
    } = term
    else {
        panic!("Expected Attributes");
    };

    // Ignore ones that have been replaced
    if get_diverted_fname(body.as_ref()).is_some() {
        return None;
    }

    let qid = get_mariposa_qid(attributes);
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

    Some(concrete::Command::DefineFun {
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
    })
}

fn introduce_simple_forall(command: &mut concrete::Command) -> Option<concrete::Command> {
    let concrete::Command::Assert { term } = command else {
        return None;
    };
    let concrete::Term::Attributes { term, .. } = term else {
        panic!("Expected Attributes");
    };
    replace_forall_body(term)
}

fn introduce_special_forall(command: &mut concrete::Command) -> Option<concrete::Command> {
    let concrete::Command::Assert { term } = command else {
        return None;
    };
    let concrete::Term::Attributes { term: imp_term, .. } = term else {
        panic!("Expected Attributes");
    };
    let Some((fname, args)) = match_simple_app_term(imp_term) else {
        return None;
    };
    if fname.0 != "=>" {
        return None;
    }
    if !is_qf_term(&args[0]) {
        return None;
    }
    let concrete::Term::Forall { .. } = args[1] else {
        return None;
    };

    // p => q, where q is forall
    let mut q = args.pop().unwrap();
    // let p = args.pop().unwrap();

    let fun_dec = replace_forall_body(&mut q).unwrap();
    args.push(q);

    Some(fun_dec)
}

// fn check_forall(command: &concrete::Command) {
//     let concrete::Command::Assert { term } = command else {
//         return;
//     };

//     if find_forall(term) {
//         println!("Found Forall");
//         println!("{}", term);
//     }
// }

// // Check if the term has a forall not under an exist
// pub fn find_forall(term: &Term) -> bool {
//     match term {
//         concrete::Term::Application { arguments, .. } => {
//             for argument in arguments {
//                 if find_forall(argument) {
//                     return true;
//                 }
//             }
//             false
//         }
//         concrete::Term::Let { term, .. } => find_forall(term.as_ref()),
//         concrete::Term::Forall { .. } => true,
//         concrete::Term::Exists { .. } => false,
//         concrete::Term::Attributes { term, .. } => find_forall(term.as_ref()),
//         concrete::Term::Match { .. } => panic!("unsupported"),
//         concrete::Term::Constant(..) => false,
//         concrete::Term::QualIdentifier(..) => false,
//     }
// }

fn match_diverted_forall(term: &Term) -> Option<String> {
    let concrete::Term::Forall { term, .. } = term else {
        return None;
    };

    let concrete::Term::Attributes { term: body, .. } = term.as_ref() else {
        panic!("Expected Attributes");
    };

    return get_diverted_fname(body.as_ref());
}

fn find_diverted_forall(term: &Term) -> Option<(String, String)> {
    if match_diverted_forall(term).is_some() {
        let res = match_diverted_forall(term)?;
        return Some((res, term.to_string()));
    }

    match term {
        concrete::Term::Application { arguments, .. } => arguments
            .iter()
            .filter_map(|x| find_diverted_forall(x))
            .next(),
        concrete::Term::Let { term, .. } => find_diverted_forall(term.as_ref()),
        concrete::Term::Forall { term, .. } => find_diverted_forall(term.as_ref()),
        concrete::Term::Exists { .. } => None,
        concrete::Term::Attributes { term, .. } => find_diverted_forall(term.as_ref()),
        concrete::Term::Match { .. } => panic!("unsupported"),
        concrete::Term::Constant(..) => None,
        concrete::Term::QualIdentifier(..) => None,
    }
}

// pub fn postprocess_for_instantiation(commands: &mut Vec<concrete::Command>) {
//     // Look for explicit instances of the form
//     // assert (! (fun_forall_mariposa_qid_xxx ...) :cid ...)
//     // If in the definition of fun_forall_mariposa_qid_xxx, there is a nested quantifier,
//     // we expand the definition and apply pre-inst-z3 again.

//     // Find all define-fun fun_forall_mariposa_qid_xxx first
//     let qid_body_with_forall_map: HashMap<usize, (Vec<Symbol>, Term)> = commands
//         .iter()
//         .filter_map(|x| {
//             if let Command::DefineFun { sig: FunctionDec { name, parameters, ..}, term } = x {
//                 if find_forall(&term) {
//                     let params = parameters.into_iter().map(|p| p.0.clone()).collect();
//                     return Some((name.to_string().strip_prefix("fun_forall_mariposa_qid_")?.parse().ok()?, (params, term.clone())))
//                 }
//             }
//             None
//         })
//         .collect();

//     let goal_index = find_goal_command_index(commands);
//     let rest = commands.split_off(goal_index);

//     let temp = commands
//         .drain(..)
//         .into_iter()
//         .map(|x| {
//             match &x {
//                 Command::Assert { term: Term::Attributes { term, attributes } } => {
//                     if let Term::Application {
//                         qual_identifier,
//                         arguments,
//                     } = term.as_ref() {
//                         if let Some(qid) = qual_identifier.to_string().strip_prefix("fun_forall_mariposa_qid_") {
//                             if let Ok(qid) = qid.parse::<usize>() {
//                                 // TODO: substitution
//                                 if let Some((params, body)) = qid_body_with_forall_map.get(&qid) {
//                                     let mut subst = Substituter::new(params.iter().cloned().zip(arguments.iter().cloned()).collect());
//                                     let mut cloned_body = body.clone();
//                                     subst.substitute(&mut cloned_body);
//                                     return Command::Assert { term: Term::Attributes { term: Box::new(cloned_body), attributes: attributes.clone() } };
//                                 }
//                             }
//                         }
//                     }
//                     x
//                 }
//                 _ => x,
//             }
//         })
//         .collect::<Vec<_>>();

//     commands.extend(temp);
//     commands.extend(rest);
// }

pub fn preprocess_for_instantiation(commands: &mut Vec<concrete::Command>) {
    let goal_index = find_goal_command_index(commands);
    let rest = commands.split_off(goal_index);

    let temp = commands
        .drain(..)
        .into_iter()
        .map(|mut x| {
            if let Some(d) = introduce_simple_forall(&mut x) {
                vec![d, x]
            } else if let Some(d) = introduce_special_forall(&mut x) {
                vec![d, x]
            } else {
                // check_forall(&x);
                vec![x]
            }
        })
        .flatten()
        .collect::<Vec<_>>();

    commands.extend(temp);
    commands.extend(rest);
}

struct FunState {
    place_holder_body: String,
    wellformed: HashSet<String>,
    malformed_count: usize,
    original_cid: usize,
}

impl FunState {
    fn new(body: String, cid: usize) -> Self {
        FunState {
            place_holder_body: body,
            wellformed: HashSet::new(),
            malformed_count: 0,
            original_cid: cid,
        }
    }
}

struct Inserter {
    max_cid: usize,
    defined_symbols: HashMap<String, String>,
    forall_funs: HashMap<String, FunState>,
    unhandled_qids: HashMap<String, usize>,
}

impl Inserter {
    fn new(commands: &Vec<concrete::Command>) -> Self {
        let mut ins = Inserter {
            max_cid: 0,
            defined_symbols: HashMap::new(),
            forall_funs: HashMap::new(),
            unhandled_qids: HashMap::new(),
        };
        ins.init_symbols(commands);
        // since max is present, add 1
        ins.max_cid += 1;
        ins
    }

    fn init_symbols(&mut self, commands: &Vec<concrete::Command>) {
        let mut symbols = HashSet::new();
        commands.iter().for_each(|x| {
            if let Some((term, cid)) = get_actual_asserted_term(x) {
                if let Some((fun_name, sub_term)) = find_diverted_forall(term) {
                    let place_holder = term.to_string().replace(&sub_term, "MARIPOSA_PLACEHOLDER");
                    let fs = FunState::new(place_holder, cid);
                    self.forall_funs.insert(fun_name, fs);
                }
                self.max_cid = usize::max(self.max_cid, cid);
            }
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
                concrete::Command::DeclareFun { symbol, .. } => {
                    symbols.insert(symbol.clone());
                }
                concrete::Command::DefineFun { sig, .. } => {
                    let symbol = sig.name.clone();
                    symbols.insert(symbol.clone());
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
        if self.forall_funs.contains_key(&fname) {
            let mut well_formed = true;
            let mut instance = "\n".to_string();
            for bound_term in bound_terms.iter().rev() {
                let res = write!(instance, "\t{}\n", TermIdx(bound_term.0).with(&ctxt));
                if res.is_err() || instance.len() > 2048 {
                    well_formed = false;
                    break;
                }
            }

            if well_formed {
                self.forall_funs
                    .get_mut(&fname)
                    .unwrap()
                    .wellformed
                    .insert(instance);
            } else {
                self.forall_funs.get_mut(&fname).unwrap().malformed_count += 1;
            }
        } else {
            *self.unhandled_qids.entry(qid.to_string()).or_insert(0) += 1;
        }
    }

    #[allow(dead_code)]
    fn debug(&self) {
        let unhandled = self.unhandled_qids.values().sum::<usize>();

        println!("Func Symbols:");
        self.forall_funs.iter().for_each(|(x, y)| {
            println!("Func: {}", x);
            println!("\twellformed {}", y.wellformed.len());
            println!("\tmalformed {}", y.malformed_count);
        });

        println!("\nUnhandled Insts ({}):", unhandled);
        let mut qids: Vec<_> = self.unhandled_qids.iter().collect();
        qids.sort_by(|a, b| b.1.cmp(a.1));
        for (qid, count) in qids {
            println!("\t{}: {}", qid, count);
        }
    }

    fn insts_error_free(mut self, commands: &mut Vec<concrete::Command>, max_inst: usize) {
        let mut remove_cids: HashSet<usize> = HashSet::new();
        let mut selected_insts: Vec<concrete::Command> = Vec::new();
        self.debug();

        let mut temp = std::mem::replace(&mut self.forall_funs, HashMap::new());
        temp = temp
            .into_iter()
            .filter(|(_, v)| v.malformed_count == 0)
            .collect();
        let mut temp: Vec<(String, FunState)> = temp.into_iter().collect::<Vec<_>>();
        temp.sort_by(|a, b| a.1.wellformed.len().cmp(&b.1.wellformed.len()));

        for (fname, fstate) in temp.iter_mut() {
            // this will implicitly remove quantifiers that have no instances
            if selected_insts.len() >= max_inst {
                break;
            }

            let insts = fstate.wellformed.iter().collect::<Vec<_>>();
            insts.into_iter().for_each(|ins| {
                let assert_term = fstate
                    .place_holder_body
                    .clone()
                    .replace("MARIPOSA_PLACEHOLDER", &format!("(|{}| {})", fname, ins,));

                let instance = format!(
                    "(assert (! {} :named mariposa_cid_{}))",
                    assert_term, self.max_cid,
                );
                self.max_cid += 1;
                // println!("{}", instance);
                selected_insts.push(Command::MariposaArbitrary(instance));
            });
            remove_cids.insert(fstate.original_cid);
        }

        // // if we still need more instances
        // if selected_insts.len() < max_inst {
        //     for (_, insts) in temp.iter_mut() {
        //         if selected_insts.len() >= max_inst {
        //             break;
        //         }
        //         let limit = usize::min(max_inst - selected_insts.len(), insts.len());
        //         selected_insts.extend(insts.drain(..limit));
        //     }
        // }

        commands.retain(|x| {
            if let Some((_, cid)) = get_actual_asserted_term(x) {
                !remove_cids.contains(&cid)
            } else {
                true
            }
        });

        println!("Selected Insts: {}", selected_insts.len());
        println!("Removed Quantifiers: {}", remove_cids.len());

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

pub fn parse_inst_log(
    path: &std::path::Path,
    // commands: &mut Vec<concrete::Command>,
) {
    let (_metadata, parser) = Z3Parser::from_file(path).unwrap();
    let parser = parser.process_all().unwrap();
    let mut inst_counts = HashMap::new();
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
                    let name = parser.strings[name_id].to_string();
                    inst_counts.insert(name.clone(), inst_counts.get(&name).unwrap_or(&0) + 1);
                }
            }
            _ => {}
        }
    }
    // sort by count
    let mut inst_counts: Vec<_> = inst_counts.into_iter().collect();
    inst_counts.sort_by(|a, b| b.1.cmp(&a.1));
    for (name, count) in inst_counts {
        println!("{}: {}", name, count);
    }
}


// pub fn print_mariposa_funs(commands: &Vec<concrete::Command>) {
//     let inserter = Inserter::new(commands);
//     for (name, cid) in inserter.forall_funs.iter() {
//         if let Some(cid) = cid {
//             println!("{}:mariposa_cid_{}", name, cid);
//         } else {
//             println!("{}:none", name);
//         }
//     }
// }

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

//                     if inserter.forall_funs.contains(&name) {
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

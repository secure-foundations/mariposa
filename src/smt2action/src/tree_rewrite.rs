use smt2parser::concrete::{Command, Term};
use smt2parser::concrete;
// use std::collections::{HashMap, HashSet};

use crate::pretty_print::print_prop_skeleton;
use crate::term_match::{make_not_term, match_simple_app_term};
use crate::term_rewrite_flat::flatten_assert;
use crate::term_rewrite_label::remove_label_rec;
use crate::term_rewrite_prop::term_rewrite_prop;

// fn replace_symbol_rec(term: Term, old: &Symbol, new: &Term, count: &mut usize) -> Term {
//     match term {
//         Term::Constant(_) => term,
//         Term::QualIdentifier(qual_identifier) => {
//             if let concrete::QualIdentifier::Simple { identifier } = &qual_identifier {
//                 if let concrete::Identifier::Simple { symbol } = identifier {
//                     if symbol == old {
//                         *count += 1;
//                         return new.clone();
//                     }
//                 }
//                 return Term::QualIdentifier(qual_identifier);
//             } else {
//                 panic!("TODO sorted QualIdentifier")
//             }
//         }
//         Term::Application {
//             qual_identifier,
//             arguments,
//         } => {
//             let mut new_arguments = vec![];
//             for arg in arguments {
//                 let new_arg = replace_symbol_rec(arg, old, new, count);
//                 new_arguments.push(new_arg);
//             }
//             return Term::Application {
//                 qual_identifier,
//                 arguments: new_arguments,
//             };
//         }
//         Term::Let { var_bindings, term } => {
//             panic!("not supporting let in let {}", term);
//         }
//         Term::Forall { vars, term } => {
//             for v in &vars {
//                 if v.0 == *old {
//                     panic!("not supporting forall with the same symbol");
//                 }
//             }
//             let new_term = replace_symbol_rec(*term, old, new, count);
//             return Term::Forall {
//                 vars: vars,
//                 term: Box::new(new_term),
//             };
//         }
//         Term::Exists { vars, term } => {
//             for v in &vars {
//                 if v.0 == *old {
//                     panic!("not supporting forall with the same symbol");
//                 }
//             }
//             let new_term = replace_symbol_rec(*term, old, new, count);
//             return Term::Exists {
//                 vars: vars,
//                 term: Box::new(new_term),
//             };
//         }
//         Term::Match { term: _, cases: _ } => {
//             panic!("not supporting match yet");
//         }
//         Term::Attributes { term, attributes } => {
//             let new_term = replace_symbol_rec(*term, old, new, count);
//             return Term::Attributes {
//                 term: Box::new(new_term),
//                 attributes: attributes,
//             };
//         }
//     }
// }

// pub fn fun_to_assert(command: concrete::Command) -> Vec<concrete::Command> {
//     if let Command::DefineFun { sig, term } = &command {
//         if sig.parameters.len() == 0 {
//             return vec![command];
//         }
//         let vars: Vec<Term> = sig
//             .parameters
//             .iter()
//             .map(|f| {
//                 Term::QualIdentifier(QualIdentifier::Simple {
//                     identifier: concrete::Identifier::Simple {
//                         symbol: f.0.clone(),
//                     },
//                 })
//             })
//             .collect();
//         vec![
//             Command::DeclareFun {
//                 symbol: sig.name.clone(),
//                 parameters: sig.parameters.iter().map(|f| f.1.clone()).collect(),
//                 sort: sig.result.clone(),
//             },
//             Command::Assert {
//                 term: Term::Forall {
//                     vars: sig
//                         .parameters
//                         .iter()
//                         .map(|f| (f.0.clone(), f.1.clone()))
//                         .collect(),
//                     term: Box::new(Term::Application {
//                         qual_identifier: QualIdentifier::Simple {
//                             identifier: concrete::Identifier::Simple {
//                                 symbol: Symbol("=".to_string()),
//                             },
//                         },
//                         arguments: vec![
//                             Term::Application {
//                                 qual_identifier: QualIdentifier::Simple {
//                                     identifier: concrete::Identifier::Simple {
//                                         symbol: sig.name.clone(),
//                                     },
//                                 },
//                                 arguments: vars,
//                             },
//                             term.clone(),
//                         ],
//                     }),
//                 },
//             },
//         ]
//     } else {
//         vec![command]
//     }
// }

// // fn flatten_nested_implies_assert(command: concrete::Command) -> concrete::Command {
// //     if let Command::Assert { term } = &command {
// //         if let Some((l, r)) = get_bin_app_term(term, &Symbol("=".to_string())) {
// //             let mut r = get_nested_implies_terms(&r);
// //             // r.insert(0, l);
// //             let last = r.pop().unwrap();
// //             let term = Term::Application {
// //                 qual_identifier: QualIdentifier::Simple {
// //                     identifier: concrete::Identifier::Simple {
// //                         symbol: Symbol("and".to_string()),
// //                     },
// //                 },
// //                 arguments: r,
// //             };
// //             let term = Term::Application {
// //                 qual_identifier: QualIdentifier::Simple {
// //                     identifier: concrete::Identifier::Simple {
// //                         symbol: Symbol("=>".to_string()),
// //                     },
// //                 },
// //                 arguments: vec![term, last],
// //             };
// //             let term = Term::Application {
// //                 qual_identifier: QualIdentifier::Simple {
// //                     identifier: concrete::Identifier::Simple {
// //                         symbol: Symbol("=".to_string()),
// //                     },
// //                 },
// //                 arguments: vec![l, term],
// //             };
// //             return concrete::Command::Assert { term: term };
// //         }
// //     }
// //     return command;
// // }

// fn get_equal_terms(term: &concrete::Term) -> Option<(Term, Term)> {
//     if let Term::Application {
//         qual_identifier,
//         arguments,
//     } = term
//     {
//         if let QualIdentifier::Simple { identifier } = qual_identifier {
//             if let concrete::Identifier::Simple { symbol } = identifier {
//                 if symbol.0 == "=" {
//                     assert!(arguments.len() == 2);
//                     return Some((arguments[0].clone(), arguments[1].clone()));
//                 }
//             }
//         }
//     }
//     return None;
// }

// // fn find_macro(commands: &Vec<concrete::Command>) {
// //     commands.iter().for_each(|c| {
// //         if let Command::Assert { term } = c {
// //             if let Term::Forall { vars, term } = term {
// //                 if let Term::Attributes { term , attributes } = &**term {
// //                     if let Some((lhs, rhs)) = get_equal_terms(term) {
// //                         // println!("found macro?");
// //                         // println!("{}", c);
// //                         println!("lhs {}", lhs);
// //                         println!("rhs {}", rhs);
// //                         println!("");
// //                     }
// //                 }
// //             }
// //         }
// //     });
// // }

// // pub struct EqualityRewriter {
// //     lhs: HashMap<Term, (Term, usize)>,
// //     // binded: HashSet<Symbol>,
// //     // bindings: Vec<(Symbol, concrete::Term)>,
// // }

// // impl EqualityRewriter {
// //     fn new(commands: &Vec<concrete::Command>) -> EqualityRewriter {
// //         let mut lhs = HashMap::new();

// //         commands.iter().enumerate().for_each(|(i, c)| {
// //             if let Command::Assert { term } = c {
// //                 if let Some((l, r)) = get_equal_term(&term) {
// //                     lhs.insert(l, (r, i));
// //                 }
// //             }
// //         });

// //         EqualityRewriter {
// //             lhs: lhs,
// //         }
// //     }
// // }

// // fn replace_equal_terms(command: &concrete::Command, rules: &HashMap<Term, Term>) -> Option<concrete::Command>
// // {
// //     if let Command::Assert { term } = command {
// //         let mut string = format!("{}", term);
// //         for rule in rules.iter() {
// //             let lhs = rule.0.to_string();
// //             let rhs = rule.1.to_string();
// //             if string.contains(&lhs) {
// //                 string = string.replace(&lhs, &rhs);
// //             }
// //         }
// //         println!("(assert {})", string);
// //     } else {
// //         println!("{}", command);
// //     }

// //     // if let Command::DefineFun { sig: _, term } = command {
// //     //     let string = format!("{}", term);
// //     //     for rule in rules.iter() {
// //     //         let lhs = rule.0.to_string();
// //     //         let rhs = rule.1.to_string();
// //     //         if string.contains(&lhs) {
// //     //             println!("original:\n {}", string);
// //     //             let aa = string.replace(&lhs, &rhs);
// //     //             println!("replace with:\n {}", aa);
// //     //         }
// //     //     }
// //     // }
// //     return None;
// // }

// pub fn rewrite_equal(commands: Vec<concrete::Command>) -> Vec<concrete::Command> {
//     let mut lhs: HashMap<Term, Term> = HashMap::new();
//     commands.iter().for_each(|c| {
//         if let Command::Assert { term } = c {
//             if let Some((l, r)) = get_equal_terms(&term) {
//                 if r == get_true() || r == get_false() {
//                     lhs.insert(l, r);
//                 }
//             }
//         }
//     });

//     for rule in lhs.iter() {
//         let lhs = rule.0.to_string();
//         let rhs = rule.1.to_string();
//         println!("; lhs {}", lhs);
//         println!("; rhs {}", rhs);
//     }

//     commands
//         .into_iter()
//         .map(|cmd| {
//             if let Command::Assert { mut term } = cmd {
//                 for (l, r) in &lhs {
//                     term = make_substitution(term, l, r);
//                 }
//                 Command::Assert { term }
//             } else {
//                 cmd
//             }
//         })
//         .collect()

//     // let mut commands = commands;

//     // commands.into_iter().map(|x| replace_equal_terms(x, &lhs)).map(filter_none).flatten().collect();

//     // EqualityRewriter {
//     //     lhs: lhs,
//     // }

//     // let rewriter = EqualityRewriter::new(&commands);
// }

// fn cancel_implication_rec(
//     premise: &concrete::Term,
//     lhs: concrete::Term,
//     found: &mut bool,
// ) -> concrete::Term {
//     if *premise == lhs {
//         *found = true;
//         return get_true();
//     }

//     if *found {
//         return lhs;
//     }

//     // println!("canceling... {}", premise);
//     // println!("canceling... lhs {}", lhs);

//     if let Some((f, mut arguments)) = match_simple_app_terms(lhs.clone()) {
//         if f.0 == "and" {
//             assert!(arguments.len() == 2);
//             let r = arguments.pop().unwrap();
//             let l = arguments.pop().unwrap();
//             let l = cancel_implication_rec(premise, l, found);
//             let r = cancel_implication_rec(premise, r, found);
//             return Term::Application {
//                 qual_identifier: QualIdentifier::Simple {
//                     identifier: concrete::Identifier::Simple {
//                         symbol: Symbol("and".to_string()),
//                     },
//                 },
//                 arguments: vec![l, r],
//             };
//         }
//     }
//     return lhs;
// }

// fn cancel_implication(
//     premise: concrete::Term,
//     lhs: concrete::Term,
//     rhs: concrete::Term,
// ) -> Option<concrete::Term> {
//     if premise == lhs {
//         return Some(rhs);
//     }

//     let mut matched = false;
//     let lhs = cancel_implication_rec(&premise, lhs, &mut matched);
//     if !matched {
//         return None;
//     }
//     assert!(matched);
//     return Some(Term::Application {
//         qual_identifier: QualIdentifier::Simple {
//             identifier: concrete::Identifier::Simple {
//                 symbol: Symbol("and".to_string()),
//             },
//         },
//         arguments: vec![lhs, rhs],
//     });
// }

fn peel_goal_term_rec(term: &mut concrete::Term, results: &mut Vec<Command>) {
    // let cpy = term.clone();
    if let Some((f, arguments)) = match_simple_app_term(term) {
        if f.0 == "=>" {
            assert!(arguments.len() == 2);
            results.push(Command::Assert {
                term: arguments[0].clone(),
            });
            let mut rhs = arguments.pop().unwrap();
            peel_goal_term_rec(&mut rhs, results);
            return;
        }
    }

    if let Term::Forall {
        vars,
        term: sub_term,
    } = term
    {
        vars.iter().for_each(|v| {
            results.push(Command::DeclareConst {
                symbol: v.0.clone(),
                sort: v.1.clone(),
            });
        });
        peel_goal_term_rec(sub_term, results);
        return;
    }

    if let Term::Attributes { term: sub_term, .. } = term {
        // TODO: maintain attributes if there is no change
        peel_goal_term_rec(sub_term, results);
        return;
    }

    println!("(assert (not");
    print_prop_skeleton(&term, 1);
    println!("))");

    results.push(Command::Assert {
        term: make_not_term(term.clone()),
    });
}

fn peel_goal_term(term: &mut concrete::Term) -> Vec<Command> {
    let mut results = vec![];
    if let Term::Attributes { term: sub_term, .. } = term {
        if let Some((f, arguments)) = match_simple_app_term(sub_term) {
            assert!(f.0 == "not");
            assert!(arguments.len() == 1);
            let mut arg = arguments.pop().unwrap();
            peel_goal_term_rec(&mut arg, &mut results);
        }
    }
    return results;
}

fn decompose_goal(goal_command: concrete::Command) -> Vec<concrete::Command> {
    let mut commands = vec![];
    if let Command::Assert { mut term } = goal_command {
        remove_label_rec(&mut term);
        term_rewrite_prop(&mut term);
        commands.extend(peel_goal_term(&mut term));
        // let mut rw = LetBindingReWriter::new();
        // commands.extend(rw.rewrite_let_bindings(term));
    }
    return commands;
}

fn command_rewrite_prop(command: &mut concrete::Command) {
    if let Command::Assert { term } = command {
        term_rewrite_prop(term);
    }
}

pub fn tree_rewrite(commands: Vec<concrete::Command>) -> Vec<concrete::Command> {
    let mut commands = commands;
    truncate_commands(&mut commands);
    let goal_command = commands.pop().unwrap();

    commands
        .iter_mut()
        .for_each(|mut c| command_rewrite_prop(&mut c));

    commands.extend(decompose_goal(goal_command));

    commands = commands
        .into_iter()
        .map(|c| flatten_assert(c))
        .flatten()
        .collect();

    commands.push(Command::CheckSat);
    return commands;
}

pub fn remove_unused_symbols(mut commands: Vec<concrete::Command>) -> Vec<concrete::Command> {
    // println!("computing def symbols: ");
    let defs = Arc::new(get_commands_symbol_def(&commands, 100));

    // println!("computing use symbols: ");
    let uses: SymbolSet = commands
        .iter()
        .map(|c| UseTracker::new(defs.clone(), &c, true).live_symbols)
        .flatten()
        .collect();

    // remove all commands that define a symbol that is not used

    commands = commands
        .into_iter()
        .filter(|c| uses.is_disjoint(&get_command_symbol_def(c)))
        .collect();

    commands
}

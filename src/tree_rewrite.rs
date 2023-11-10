use smt2parser::{concrete, rewriter};
use smt2parser::concrete::{Command, QualIdentifier, Symbol, Term};
use std::collections::{HashMap, HashSet};

use crate::pretty_print::print_prop_skeleton;
use crate::term_match::match_simple_app_terms;
use crate::term_rewrite_label::remove_label_rec;
use crate::term_rewrite_prop::term_rewrite_prop;
use crate::term_rewrite_let::LetBindingReWriter;

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

pub fn find_goal_command_index(commands: &Vec<concrete::Command>) -> usize {
    let mut i = commands.len() - 1;
    // TODO: more robust pattern matching?
    while i > 0 {
        let command = &commands[i];
        if let Command::Assert { term: _ } = command {
            if let Command::CheckSat = &commands[i + 1] {
                // break;
            } else {
                panic!("expected check-sat after the goal assert");
            }
            break;
        }
        i -= 1;
    }
    i
}

pub fn truncate_commands(commands: &mut Vec<concrete::Command>) {
    let i = find_goal_command_index(commands);
    commands.truncate(i + 1);
}

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

// // fn get_nested_and_terms(term: &concrete::Term) -> Vec<Term> {
// //     if let Some((l, r)) = get_binary_app_term(term, &Symbol("and".to_string())) {
// //         let mut l = get_nested_and_terms(&l);
// //         let mut r = get_nested_and_terms(&r);
// //         l.append(&mut r);
// //         return l;
// //     }
// //     return vec![term.clone()];
// // }

// // fn get_nested_implies_terms(term: &concrete::Term) -> Vec<Term> {
// //     if let Some((l, r)) = get_binary_app_term(term, &Symbol("=>".to_string())) {
// //         let mut r = get_nested_implies_terms(&r);
// //         r.insert(0, l);
// //         return r;
// //     } else if let Some((l, r)) = get_binary_app_term(term, &Symbol("implies".to_string())) {
// //         let mut r = get_nested_implies_terms(&r);
// //         r.insert(0, l);
// //         return r;
// //     }
// //     return vec![term.clone()];
// // }

// // pub fn flatten_assert(command: concrete::Command) -> Vec<concrete::Command> {
// //     if let Command::Assert { term } = &command {
// //         let ts = get_nested_and_terms(&term);
// //         ts.into_iter()
// //             .map(|x| concrete::Command::Assert { term: x })
// //             .collect()
// //     } else {
// //         vec![command]
// //     }
// // }

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

// fn make_substitution(term: Term, lhs: &Term, rhs: &Term) -> Term {
//     match term {
//         Term::Constant(_) => term,
//         Term::QualIdentifier(_) => {
//             if lhs == &term {
//                 return rhs.clone();
//             } else {
//                 return term;
//             }
//         }
//         Term::Application {
//             qual_identifier,
//             arguments,
//         } => {
//             let mut new_arguments = vec![];
//             for arg in arguments {
//                 let new_arg = make_substitution(arg, lhs, rhs);
//                 new_arguments.push(new_arg);
//             }
//             return Term::Application {
//                 qual_identifier,
//                 arguments: new_arguments,
//             };
//         }
//         Term::Let { var_bindings, term } => {
//             let var_bindings = var_bindings
//                 .into_iter()
//                 .map(|(var, binding)| (var, make_substitution(binding, lhs, rhs)))
//                 .collect();
//             let term = make_substitution(*term, lhs, rhs);
//             return Term::Let {
//                 var_bindings: var_bindings,
//                 term: Box::new(term),
//             };
//         }
//         Term::Forall { vars, term } => {
//             let new_term = make_substitution(*term, lhs, rhs);
//             return Term::Forall {
//                 vars: vars,
//                 term: Box::new(new_term),
//             };
//         }
//         Term::Exists { vars, term } => {
//             let new_term = make_substitution(*term, lhs, rhs);
//             return Term::Exists {
//                 vars: vars,
//                 term: Box::new(new_term),
//             };
//         }
//         Term::Match { term: _, cases: _ } => {
//             panic!("not supporting match yet");
//         }
//         Term::Attributes { term, attributes } => {
//             let new_term = make_substitution(*term, lhs, rhs);
//             return Term::Attributes {
//                 term: Box::new(new_term),
//                 attributes: attributes,
//             };
//         }
//     }
// }

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

// fn peel_goal_term_rec(term: concrete::Term) {
//     let cpy = term.clone();
//     if let Some((f, mut arguments)) = match_simple_app_terms(term) {
//         if f.0 == "=>" {
//             assert!(arguments.len() == 2);
//             println!("(assert {})", arguments[0]);
//             let rhs = arguments.pop().unwrap();
//             peel_goal_term_rec(rhs);
//         }

//         if f.0 == "and" {
//             assert!(arguments.len() == 2);
//             let r = arguments.pop().unwrap();
//             let l = arguments.pop().unwrap();

//             if let Some((f, implies)) = match_simple_app_terms(r) {
//                 if f.0 != "=>" {
//                     println!("and lhs {}", l);
//                     println!("and rhs {} {} {}", f, implies[0], implies[1]);
//                     panic!("not supporting this yet");
//                 }
//                 // assert!(implies.len() == 2);
//                 let imp = cancel_implication(l, implies[0].clone(), implies[1].clone());
//                 if let Some(imp) = imp {
//                     peel_goal_term_rec(imp);
//                 } else {
//                     print!("(assert {})", cpy);
//                 }
//             }
//         }
//     } else {
//         panic!("???? {}", cpy);
//     }
// }

// fn peel_goal_term(term: concrete::Term) {
//     if let Some((f, arguments)) = match_simple_app_terms(term) {
//         assert!(f.0 == "not");
//         assert!(arguments.len() == 1);
//         peel_goal_term_rec(arguments[0].clone());
//     } else {
//         panic!()
//     }
// }

fn decompose_goal(goal_command: concrete::Command) -> Vec<concrete::Command> {
    let mut commands = vec![];
    if let Command::Assert { mut term } = goal_command {
        remove_label_rec(&mut term);
        term_rewrite_prop(&mut term);
        let mut rw = LetBindingReWriter::new();
        commands.extend(rw.rewrite_let_bindings(term));
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

    commands.iter_mut().for_each(|mut c| command_rewrite_prop(&mut c));
    let mut sub_commands = decompose_goal(goal_command);
    commands.append(&mut sub_commands);
    commands.push(Command::CheckSat);
    return commands;
}

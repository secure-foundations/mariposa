// use clap::command;
// use rand_chacha::rand_core::le;
// use smt2parser::concrete;
// use smt2parser::concrete::{Command, QualIdentifier, Symbol, Term};
// use std::collections::{HashMap, HashSet};

// use crate::pretty_print::print_prop_skeleton;
// use crate::term_match::match_simple_app_terms;

// fn rewrite_let_binding(var: &Symbol, term0: &concrete::Term) -> Vec<concrete::Command> {
//     if let Term::Let {
//         var_bindings: _,
//         term: _,
//     } = term0
//     {
//         panic!("not supporting another let in term0");
//     }

//     let lhs = Term::QualIdentifier(QualIdentifier::Simple {
//         identifier: concrete::Identifier::Simple {
//             symbol: var.clone(),
//         },
//     });

//     let term = Box::new(Term::Application {
//         qual_identifier: QualIdentifier::Simple {
//             identifier: concrete::Identifier::Simple {
//                 symbol: Symbol("=".to_string()),
//             },
//         },
//         arguments: vec![lhs, term0.clone()],
//     });

//     vec![
//         Command::DeclareConst {
//             symbol: var.clone(),
//             sort: concrete::Sort::Simple {
//                 identifier: concrete::Identifier::Simple {
//                     symbol: Symbol("Bool".to_owned()),
//                 },
//             },
//         },
//         Command::Assert { term: *term },
//     ]
// }

// fn get_simple_qualid_symbol(term: &Term) -> Option<Symbol> {
//     if let Term::QualIdentifier(qual_identifier) = term {
//         if let QualIdentifier::Simple { identifier } = qual_identifier {
//             if let concrete::Identifier::Simple { symbol } = identifier {
//                 return Some(symbol.clone());
//             }
//         }
//     }
//     return None;
// }

// fn match_negative_label(term: Term) -> Term {
//     let (s, mut args) = match_simple_app_terms(term).unwrap();
//     assert!(s.0 == "or");
//     assert!(args.len() == 2);
//     let r = args.pop().unwrap();
//     let l = args.pop().unwrap();
//     if let Some(label) = get_simple_qualid_symbol(&l) {
//         assert!(label.0.starts_with("%lbl%@"));
//         return r;
//     }
//     panic!()
//     // get_simple_qualid_symbol(&r).unwrap();
//     // return l;
// }

// fn match_positive_label(term: Term) -> Term {
//     let (s, mut args) = match_simple_app_terms(term).unwrap();
//     assert!(s.0 == "and");
//     assert!(args.len() == 2);
//     let r = args.pop().unwrap();
//     let l = args.pop().unwrap();
//     if let Some(label) = get_simple_qualid_symbol(&l) {
//         assert!(label.0.starts_with("%lbl%+"));
//         return r;
//     }
//     get_simple_qualid_symbol(&r).unwrap();
//     return l;
// }

// fn remove_label_rec(term: Term) -> Term {
//     match term {
//         Term::Constant(_) => term,
//         Term::QualIdentifier(_) => term,
//         Term::Application {
//             qual_identifier,
//             arguments,
//         } => {
//             let arguments = arguments
//                 .into_iter()
//                 .map(|arg| remove_label_rec(arg))
//                 .collect();
//             return Term::Application {
//                 qual_identifier,
//                 arguments,
//             };
//         }
//         Term::Let { var_bindings, term } => {
//             let var_bindings = var_bindings
//                 .into_iter()
//                 .map(|(var, binding)| (var, remove_label_rec(binding)))
//                 .collect();
//             let term = remove_label_rec(*term);
//             return Term::Let {
//                 var_bindings: var_bindings,
//                 term: Box::new(term),
//             };
//         }
//         Term::Forall { vars, term } => {
//             let term = remove_label_rec(*term);
//             return Term::Forall {
//                 vars: vars,
//                 term: Box::new(term),
//             };
//         }
//         Term::Exists { vars, term } => {
//             let term = remove_label_rec(*term);
//             return Term::Exists {
//                 vars: vars,
//                 term: Box::new(term),
//             };
//         }
//         Term::Match { term: _, cases: _ } => {
//             panic!("not supporting match yet");
//         }
//         Term::Attributes { term, attributes } => {
//             let mut lblneg = false;
//             let mut lblpos = false;
//             let mut term = *term;

//             attributes.iter().for_each(|f| {
//                 let concrete::Keyword(k) = &f.0;
//                 if k == "lblneg" {
//                     lblneg = true;
//                 } else if k == "lblpos" {
//                     lblpos = true;
//                 }
//             });

//             if lblneg {
//                 return match_negative_label(term);
//             } else if lblpos {
//                 return match_positive_label(term);
//             } else {
//                 term = remove_label_rec(term);
//             }

//             return Term::Attributes {
//                 term: Box::new(term),
//                 attributes: attributes,
//             };
//         }
//     }
// }

// pub struct LetBindingReWriter {
//     let_bindings: HashMap<Symbol, (concrete::Term, usize)>,
//     order: Vec<Symbol>,
//     other_bindings: HashSet<Symbol>,
// }

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

// impl LetBindingReWriter {
//     pub fn new() -> LetBindingReWriter {
//         LetBindingReWriter {
//             let_bindings: HashMap::new(),
//             order: vec![],
//             other_bindings: HashSet::new(),
//         }
//     }

//     // fn add_other_binding(&mut self, var: Symbol, binding: concrete::Term) {
//     //     assert!(!self.binded.contains(&var));
//     //     self.binded.insert(var.clone());
//     //     self.bindings.insert(var, binding, 0);
//     // }

//     fn add_let_binding(&mut self, var: Symbol, binding: concrete::Term) {
//         assert!(!self.other_bindings.contains(&var));
//         let exists = self.let_bindings.insert(var.clone(), (binding, 0));
//         self.order.push(var);
//         assert!(exists.is_none());
//     }

//     fn increment_let_binding(&mut self, qual_identifier: &concrete::QualIdentifier) {
//         if let concrete::QualIdentifier::Simple { identifier } = qual_identifier {
//             if let concrete::Identifier::Simple { symbol } = identifier {
//                 if let Some((binding, count)) = self.let_bindings.get_mut(symbol) {
//                     *count += 1;
//                 }
//             }
//         }
//     }

//     fn rewrite_let_bindings_rec(&mut self, term: Term) -> Term {
//         match term {
//             Term::Constant(_) => term,
//             Term::QualIdentifier(qual_identifier) => {
//                 self.increment_let_binding(&qual_identifier);
//                 Term::QualIdentifier(qual_identifier)
//             }
//             Term::Application {
//                 qual_identifier,
//                 arguments,
//             } => {
//                 let arguments = arguments
//                     .into_iter()
//                     .map(|arg| self.rewrite_let_bindings_rec(arg))
//                     .collect();
//                 return Term::Application {
//                     qual_identifier,
//                     arguments: arguments,
//                 };
//             }
//             Term::Let { var_bindings, term } => {
//                 for (var, binding) in var_bindings {
//                     let binding = self.rewrite_let_bindings_rec(binding);
//                     self.add_let_binding(var, binding);
//                 }
//                 return self.rewrite_let_bindings_rec(*term);
//             }
//             Term::Forall { vars, term } => {
//                 let term = self.rewrite_let_bindings_rec(*term);
//                 return Term::Forall {
//                     vars: vars,
//                     term: Box::new(term),
//                 };
//             }
//             Term::Exists { vars, term } => {
//                 let term = self.rewrite_let_bindings_rec(*term);
//                 return Term::Exists {
//                     vars: vars,
//                     term: Box::new(term),
//                 };
//             }
//             Term::Match { term: _, cases: _ } => {
//                 panic!("not supporting match yet");
//             }
//             Term::Attributes { term, attributes } => {
//                 let term = self.rewrite_let_bindings_rec(*term);
//                 return Term::Attributes {
//                     term: Box::new(term),
//                     attributes: attributes,
//                 };
//             }
//         }
//     }

//     fn rewrite_let_bindings(&mut self, command: concrete::Command) -> Vec<concrete::Command> {
//         let mut commands = vec![];
//         if let Command::Assert { term } = command {
//             let mut term = self.rewrite_let_bindings_rec(term);
//             self.order.reverse();
//             let def_fun = rewrite_let_binding(&var, &binding);
//             commands.extend(def_fun);
//             commands.push(Command::Assert { term: term });
//         }
//         return commands;
//     }
// }

// pub fn find_goal_command_index(commands: &Vec<concrete::Command>) -> usize {
//     let mut i = commands.len() - 1;
//     // TODO: more robust pattern matching?
//     while i > 0 {
//         let command = &commands[i];
//         if let Command::Assert { term: _ } = command {
//             if let Command::CheckSat = &commands[i + 1] {
//                 // break;
//             } else {
//                 panic!("expected check-sat after the goal assert");
//             }
//             break;
//         }
//         i -= 1;
//     }
//     i
// }

// pub fn truncate_commands(commands: &mut Vec<concrete::Command>) {
//     let i = find_goal_command_index(commands);
//     commands.truncate(i + 1);
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

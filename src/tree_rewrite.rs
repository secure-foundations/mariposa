use smt2parser::concrete;
use smt2parser::concrete::{AttributeValue, Command, QualIdentifier, Symbol, Term};
use std::collections::{HashMap, HashSet};

// fn is_and(term: &concrete::Term) -> Option<(Term, Term)> {
//     if let Term::Application { qual_identifier, arguments } = term {
//         if let QualIdentifier::Simple { identifier } = qual_identifier {
//             if let concrete::Identifier::Simple { symbol } = identifier {
//                 if symbol.0 == "and" {
//                     assert!(arguments.len() == 2);
//                     return Some((arguments[0].clone(), arguments[1].clone()));
//                 }
//             }
//         }
//     }
//     return None;
// }

// fn is_nested_and(term: &concrete::Term) -> Vec<Term> {
//     if let Some((l, r)) = is_and(term) {
//         let mut l = is_nested_and(&l);
//         let mut r = is_nested_and(&r);
//         l.append(&mut r);
//         return l;
//     }
//     return vec![term.clone()];
// }

// fn flatten_nested_and(command: concrete::Command) -> Vec<concrete::Command>
// {
//     if let Command::Assert { term } = &command {
//         let ts = is_nested_and(&term);
//         ts.into_iter().map(|x| concrete::Command::Assert { term: x }).collect()
//     } else {
//         vec![command]
//     }
// }

// fn rewrite_true_implies()

fn rewrite_let_binding(var: &Symbol, term0: &concrete::Term) -> concrete::Command {
    let sig = concrete::FunctionDec {
        name: var.clone(),
        parameters: vec![],
        result: concrete::Sort::Simple {
            identifier: concrete::Identifier::Simple {
                symbol: Symbol("Bool".to_owned()),
            },
        },
    };

    if let Term::Let {
        var_bindings: _,
        term: _,
    } = term0
    {
        panic!("not supporting another let in term0");
    }

    Command::DefineFun {
        sig: sig,
        term: term0.clone(),
    }
}

pub struct LetBindingReWriter {
    binded: HashSet<Symbol>,
    bindings: Vec<(Symbol, concrete::Term)>,
}

impl LetBindingReWriter {
    pub fn new() -> LetBindingReWriter {
        LetBindingReWriter {
            binded: HashSet::new(),
            bindings: Vec::new(),
        }
    }

    fn add_bindiing(&mut self, var: Symbol, binding: concrete::Term) {
        assert!(!self.binded.contains(&var));
        self.binded.insert(var.clone());
        self.bindings.push((var, binding));
    }

    fn rewrite_let_bindings_rec(&mut self, term: Term) -> Term {
        match term {
            Term::Constant(_) => term,
            Term::QualIdentifier(_) => term,
            Term::Application {
                qual_identifier,
                arguments,
            } => {
                let mut new_arguments = vec![];
                for arg in arguments {
                    let new_arg = self.rewrite_let_bindings_rec(arg);
                    new_arguments.push(new_arg);
                }
                return Term::Application {
                    qual_identifier,
                    arguments: new_arguments,
                };
            }
            Term::Let { var_bindings, term } => {
                for (var, binding) in var_bindings {
                    self.add_bindiing(var, binding);
                    // let res = self.bindings.insert(var, binding);
                    // assert!(res.is_none());
                }
                return self.rewrite_let_bindings_rec(*term);
            }
            Term::Forall { vars, term } => {
                let new_term = self.rewrite_let_bindings_rec(*term);
                return Term::Forall {
                    vars: vars,
                    term: Box::new(new_term),
                };
            }
            Term::Exists { vars, term } => {
                let new_term = self.rewrite_let_bindings_rec(*term);
                return Term::Exists {
                    vars: vars,
                    term: Box::new(new_term),
                };
            }
            Term::Match { term: _, cases: _ } => {
                panic!("not supporting match yet");
            }
            Term::Attributes { term, attributes } => {
                let new_term = self.rewrite_let_bindings_rec(*term);
                return Term::Attributes {
                    term: Box::new(new_term),
                    attributes: attributes,
                };
            }
        }
    }

    fn bindings_to_commands(&self) -> Vec<concrete::Command> {
        let mut commands = vec![];
        for (var, binding) in &self.bindings {
            let def_fun = rewrite_let_binding(&var, &binding);
            commands.push(def_fun);
        }
        return commands;
    }

    pub fn rewrite(&mut self, command: concrete::Command) -> Vec<concrete::Command> {
        if let Command::Assert { term } = command {
            let term = self.rewrite_let_bindings_rec(term);
            let mut commands = self.bindings_to_commands();
            let assert = Command::Assert { term: term };
            commands.push(assert);
            return commands;
        } else {
            return vec![command];
        }
    }
}

pub fn find_goal_command_index(commands: &Vec<concrete::Command>) -> usize {
    let mut i = commands.len() - 1;
    // TODO: more robust pattern matching?
    while i > 0 {
        let command = &commands[i];
        if let Command::Assert { term: _ } = command {
            if let Command::CheckSat = &commands[i + 1] {
                // break;
            } else {
                panic!("expected check-sat after assert");
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

pub fn tree_rewrite(commands: Vec<concrete::Command>) -> Vec<concrete::Command> {
    let mut commands = commands;
    truncate_commands(&mut commands);
    let goal_command = commands.pop().unwrap();

    let mut rewriter = LetBindingReWriter::new();
    let mut sub_commands = rewriter.rewrite(goal_command);
    commands.append(&mut sub_commands);
    commands.push(concrete::Command::CheckSat);

    return commands;
}

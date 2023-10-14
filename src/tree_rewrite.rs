use smt2parser::concrete;
use smt2parser::concrete::{AttributeValue, Command, QualIdentifier, Symbol, Term};
use std::collections::{HashMap, HashSet};

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

pub fn tree_rewrite(commands: Vec<concrete::Command>) -> Vec<concrete::Command> {
    let mut commands = commands;
    truncate_commands(&mut commands);
    let goal_command = commands.pop().unwrap();

    commands = commands
        .into_iter()
        .map(|x| flatten_assert(x))
        .flatten()
        .collect();
    // commands = rewrite_equal(commands);

    let mut rewriter = LetBindingReWriter::new();
    let mut sub_commands = rewriter.rewrite(goal_command);
    commands.append(&mut sub_commands);
    commands.push(concrete::Command::CheckSat);

    return commands;
}

pub fn fun_to_assert(command: concrete::Command) -> Vec<concrete::Command> {
    if let Command::DefineFun { sig, term } = &command {
        if sig.parameters.len() == 0 {
            return vec![command];
        }
        let vars: Vec<Term> = sig
            .parameters
            .iter()
            .map(|f| {
                Term::QualIdentifier(QualIdentifier::Simple {
                    identifier: concrete::Identifier::Simple {
                        symbol: f.0.clone(),
                    },
                })
            })
            .collect();
        vec![
            Command::DeclareFun {
                symbol: sig.name.clone(),
                parameters: sig.parameters.iter().map(|f| f.1.clone()).collect(),
                sort: sig.result.clone(),
            },
            Command::Assert {
                term: Term::Forall {
                    vars: sig
                        .parameters
                        .iter()
                        .map(|f| (f.0.clone(), f.1.clone()))
                        .collect(),
                    term: Box::new(Term::Application {
                        qual_identifier: QualIdentifier::Simple {
                            identifier: concrete::Identifier::Simple {
                                symbol: Symbol("=".to_string()),
                            },
                        },
                        arguments: vec![
                            Term::Application {
                                qual_identifier: QualIdentifier::Simple {
                                    identifier: concrete::Identifier::Simple {
                                        symbol: sig.name.clone(),
                                    },
                                },
                                arguments: vars,
                            },
                            term.clone(),
                        ],
                    }),
                },
            },
        ]
    } else {
        vec![command]
    }
}

fn get_and_term(term: &concrete::Term) -> Option<(Term, Term)> {
    if let Term::Application {
        qual_identifier,
        arguments,
    } = term
    {
        if let QualIdentifier::Simple { identifier } = qual_identifier {
            if let concrete::Identifier::Simple { symbol } = identifier {
                if symbol.0 == "and" {
                    assert!(arguments.len() == 2);
                    return Some((arguments[0].clone(), arguments[1].clone()));
                }
            }
        }
    }
    return None;
}

fn get_nested_and_terms(term: &concrete::Term) -> Vec<Term> {
    if let Some((l, r)) = get_and_term(term) {
        let mut l = get_nested_and_terms(&l);
        let mut r = get_nested_and_terms(&r);
        l.append(&mut r);
        return l;
    }
    return vec![term.clone()];
}

pub fn flatten_assert(command: concrete::Command) -> Vec<concrete::Command> {
    if let Command::Assert { term } = &command {
        let ts = get_nested_and_terms(&term);
        ts.into_iter()
            .map(|x| concrete::Command::Assert { term: x })
            .collect()
    } else {
        vec![command]
    }
}

fn get_equal_term(term: &concrete::Term) -> Option<(Term, Term)> {
    if let Term::Application {
        qual_identifier,
        arguments,
    } = term
    {
        if let QualIdentifier::Simple { identifier } = qual_identifier {
            if let concrete::Identifier::Simple { symbol } = identifier {
                if symbol.0 == "=" {
                    assert!(arguments.len() == 2);
                    return Some((arguments[0].clone(), arguments[1].clone()));
                }
            }
        }
    }
    return None;
}

// pub struct EqualityRewriter {
//     lhs: HashMap<Term, (Term, usize)>,
//     // binded: HashSet<Symbol>,
//     // bindings: Vec<(Symbol, concrete::Term)>,
// }

// impl EqualityRewriter {
//     fn new(commands: &Vec<concrete::Command>) -> EqualityRewriter {
//         let mut lhs = HashMap::new();

//         commands.iter().enumerate().for_each(|(i, c)| {
//             if let Command::Assert { term } = c {
//                 if let Some((l, r)) = get_equal_term(&term) {
//                     lhs.insert(l, (r, i));
//                 }
//             }
//         });  

//         EqualityRewriter {
//             lhs: lhs,
//         }
//     }
// }


fn replace_equal_terms(command: &concrete::Command, rules: &HashMap<Term, Term>) -> Option<concrete::Command>
{
    if let Command::Assert { term } = command {
        let mut string = format!("{}", term);
        for rule in rules.iter() {
            let lhs = rule.0.to_string();
            let rhs = rule.1.to_string();
            if string.contains(&lhs) {
                string = string.replace(&lhs, &rhs);
            }
        }
        println!("(assert {})", string);
    } else {
        println!("{}", command);
    }

    // if let Command::DefineFun { sig: _, term } = command {
    //     let string = format!("{}", term);
    //     for rule in rules.iter() {
    //         let lhs = rule.0.to_string();
    //         let rhs = rule.1.to_string();
    //         if string.contains(&lhs) {
    //             println!("original:\n {}", string);
    //             let aa = string.replace(&lhs, &rhs);
    //             println!("replace with:\n {}", aa);
    //         }
    //     }
    // }
    return None;
}

pub fn rewrite_equal(mut commands: Vec<concrete::Command>) -> Vec<concrete::Command>
{
    let mut lhs: HashMap<Term, Term> = HashMap::new();

    commands.retain(|c| {
        if let Command::Assert { term } = c {
            if let Some((l, r)) = get_equal_term(&term) {
                lhs.insert(l, r);
                return false;
            }
        }
        return true;
    });

    // for rule in lhs.iter() {
    //     let lhs = rule.0.to_string();
    //     let rhs = rule.1.to_string();
    //     println!("lhs {}", lhs);
    //     println!("rhs {}", rhs);
    // }

    for cmd in commands.iter() {
        replace_equal_terms(cmd, &lhs);
    }

    // let mut commands = commands;
    
    // commands.into_iter().map(|x| replace_equal_terms(x, &lhs)).map(filter_none).flatten().collect();


    // EqualityRewriter {
    //     lhs: lhs,
    // }

    // let rewriter = EqualityRewriter::new(&commands);
    vec![]
}   

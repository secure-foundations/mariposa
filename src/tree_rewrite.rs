use smt2parser::concrete;
use smt2parser::concrete::{AttributeValue, Command, QualIdentifier, Symbol, Term};
use std::collections::{HashMap, HashSet};

fn get_binary_app_term(term: &concrete::Term, fun_symbol: &Symbol) -> Option<(Term, Term)> {
    if let Term::Application {
        qual_identifier,
        arguments,
    } = term
    {
        if let QualIdentifier::Simple { identifier } = qual_identifier {
            if let concrete::Identifier::Simple { symbol } = identifier {
                if symbol == fun_symbol {
                    assert!(arguments.len() == 2);
                    return Some((arguments[0].clone(), arguments[1].clone()));
                }
            }
        }
    }
    return None;
}

fn get_unary_app_term(term: &concrete::Term, fun_symbol: &Symbol) -> Option<Term> {
    if let Term::Application {
        qual_identifier,
        arguments,
    } = term
    {
        if let QualIdentifier::Simple { identifier } = qual_identifier {
            if let concrete::Identifier::Simple { symbol } = identifier {
                if symbol == fun_symbol {
                    assert!(arguments.len() == 1);
                    return Some(arguments[0].clone());
                }
            }
        }
    }
    return None;
}

fn rewrite_let_binding(var: &Symbol, term0: &concrete::Term) -> Vec<concrete::Command> {
    if let Term::Let {
        var_bindings: _,
        term: _,
    } = term0
    {
        panic!("not supporting another let in term0");
    }

    let lhs = Term::QualIdentifier(QualIdentifier::Simple {
        identifier: concrete::Identifier::Simple {
            symbol: var.clone(),
        },
    });

    let term = Box::new(Term::Application {
        qual_identifier: QualIdentifier::Simple {
            identifier: concrete::Identifier::Simple {
                symbol: Symbol("=".to_string()),
            },
        },
        arguments: vec![lhs, term0.clone()],
    });

    vec![
        Command::DeclareConst {
            symbol: var.clone(),
            sort: concrete::Sort::Simple {
                identifier: concrete::Identifier::Simple {
                    symbol: Symbol("Bool".to_owned()),
                },
            },
        },
        Command::Assert { term: *term },
    ]
}

pub struct LetBindingReWriter {
    binded: HashSet<Symbol>,
    bindings: Vec<(Symbol, concrete::Term)>,
}

fn replace_symbol_rec(term: Term, old: &Symbol, new: &Term) -> Term {
    match term {
        Term::Constant(_) => term,
        Term::QualIdentifier(qual_identifier) => {
            if let concrete::QualIdentifier::Simple { identifier } = &qual_identifier {
                if let concrete::Identifier::Simple { symbol } = identifier {
                    if symbol == old {
                        return new.clone();
                    }
                }
                return  Term::QualIdentifier(qual_identifier);
            } else {
                panic!("TODO sorted QualIdentifier")
            }
        }
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            let mut new_arguments = vec![];
            for arg in arguments {
                let new_arg = replace_symbol_rec(arg, old, new);
                new_arguments.push(new_arg);
            }
            return Term::Application {
                qual_identifier,
                arguments: new_arguments,
            };
        }
        Term::Let { var_bindings, term } => {
            panic!("not supporting let in let {}", term);
            // let mut new_var_bindings = vec![];
            // for (var, binding) in var_bindings {
            //     if var == *old {
            //         panic!("not supporting forall with the same symbol");
            //     }
            //     let new_binding = replace_symbol_rec(binding, old, new);
            //     new_var_bindings.push((var, new_binding));
            // }
            // let new_term = replace_symbol_rec(*term, old, new);
            // return Term::Let {
            //     var_bindings: new_var_bindings,
            //     term: Box::new(new_term),
            // };
        }
        Term::Forall { vars, term } => {
            for v in &vars {
                if v.0 == *old {
                    panic!("not supporting forall with the same symbol");
                }
            }
            let new_term = replace_symbol_rec(*term, old, new);
            return Term::Forall {
                vars: vars,
                term: Box::new(new_term),
            };
        }
        Term::Exists { vars, term } => {
            for v in &vars {
                if v.0 == *old {
                    panic!("not supporting forall with the same symbol");
                }
            }
            let new_term = replace_symbol_rec(*term, old, new);
            return Term::Exists {
                vars: vars,
                term: Box::new(new_term),
            };
        }
        Term::Match { term: _, cases: _ } => {
            panic!("not supporting match yet");
        }
        Term::Attributes { term, attributes } => {
            let new_term = replace_symbol_rec(*term, old, new);
            return Term::Attributes {
                term: Box::new(new_term),
                attributes: attributes,
            };
        }
    }
}

impl LetBindingReWriter {
    pub fn new() -> LetBindingReWriter {
        LetBindingReWriter {
            binded: HashSet::new(),
            bindings: Vec::new(),
        }
    }

    fn add_binding(&mut self, var: Symbol, binding: concrete::Term) {
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
                    let binding = self.rewrite_let_bindings_rec(binding);
                    self.add_binding(var, binding);
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
            commands.extend(def_fun);
        }
        return commands;
    }

    pub fn rewrite_as_asserts(&mut self, command: concrete::Command) -> Vec<concrete::Command> {
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

    fn rewrite_as_inline(&mut self, command: concrete::Command) -> concrete::Command {
        if let Command::Assert { term } = command {
            let mut term = self.rewrite_let_bindings_rec(term);
            self.bindings.reverse();
            for (var, binding) in &self.bindings {
                term = replace_symbol_rec(term, var, binding);
            }
            Command::Assert { term: term }
        } else {
            command
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

fn get_nested_and_terms(term: &concrete::Term) -> Vec<Term> {
    if let Some((l, r)) = get_binary_app_term(term, &Symbol("and".to_string())) {
        let mut l = get_nested_and_terms(&l);
        let mut r = get_nested_and_terms(&r);
        l.append(&mut r);
        return l;
    }
    return vec![term.clone()];
}

fn get_nested_implies_terms(term: &concrete::Term) -> Vec<Term> {
    if let Some((l, r)) = get_binary_app_term(term, &Symbol("=>".to_string())) {
        let mut r = get_nested_implies_terms(&r);
        r.insert(0, l);
        return r;
    } else if let Some((l, r)) = get_binary_app_term(term, &Symbol("implies".to_string())) {
        let mut r = get_nested_implies_terms(&r);
        r.insert(0, l);
        return r;
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

// fn flatten_nested_implies_assert(command: concrete::Command) -> concrete::Command {
//     if let Command::Assert { term } = &command {
//         if let Some((l, r)) = get_bin_app_term(term, &Symbol("=".to_string())) {
//             let mut r = get_nested_implies_terms(&r);
//             // r.insert(0, l);
//             let last = r.pop().unwrap();
//             let term = Term::Application {
//                 qual_identifier: QualIdentifier::Simple {
//                     identifier: concrete::Identifier::Simple {
//                         symbol: Symbol("and".to_string()),
//                     },
//                 },
//                 arguments: r,
//             };
//             let term = Term::Application {
//                 qual_identifier: QualIdentifier::Simple {
//                     identifier: concrete::Identifier::Simple {
//                         symbol: Symbol("=>".to_string()),
//                     },
//                 },
//                 arguments: vec![term, last],
//             };
//             let term = Term::Application {
//                 qual_identifier: QualIdentifier::Simple {
//                     identifier: concrete::Identifier::Simple {
//                         symbol: Symbol("=".to_string()),
//                     },
//                 },
//                 arguments: vec![l, term],
//             };
//             return concrete::Command::Assert { term: term };
//         }
//     }
//     return command;
// }

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

fn rewrite_term_trivial_rec(term: concrete::Term) -> concrete::Term {
    if let Some((l, r)) = get_binary_app_term(&term, &Symbol("=>".to_string())) {
        let l = rewrite_term_trivial_rec(l);
        let r = rewrite_term_trivial_rec(r);
        if l.to_string() == "true" {
            return r;
        }
        if r.to_string() == "true" {
            return r;
        }
        if l.to_string() == "false" {
            return l;
        }
        if r.to_string() == "false" {
            return r;
        }

        return Term::Application {
            qual_identifier: QualIdentifier::Simple {
                identifier: concrete::Identifier::Simple {
                    symbol: Symbol("=>".to_string()),
                },
            },
            arguments: vec![l, r],
        };
    }

    if let Some((l, r)) = get_binary_app_term(&term, &Symbol("and".to_string())) {
        let l = rewrite_term_trivial_rec(l);
        let r = rewrite_term_trivial_rec(r);
        if l.to_string() == "true" {
            return r;
        }
        if r.to_string() == "true" {
            return l;
        }
        if l.to_string() == "false" {
            return l;
        }
        if r.to_string() == "false" {
            return r;
        }

        return Term::Application {
            qual_identifier: QualIdentifier::Simple {
                identifier: concrete::Identifier::Simple {
                    symbol: Symbol("and".to_string()),
                },
            },
            arguments: vec![l, r],
        };
    }

    if let Some((l, r)) = get_binary_app_term(&term, &Symbol("or".to_string())) {
        let l = rewrite_term_trivial_rec(l);
        let r = rewrite_term_trivial_rec(r);
        if l.to_string() == "false" {
            return r;
        }
        if r.to_string() == "false" {
            return l;
        }
        if l.to_string() == "true" {
            return l;
        }
        if r.to_string() == "true" {
            return r;
        }
        return Term::Application {
            qual_identifier: QualIdentifier::Simple {
                identifier: concrete::Identifier::Simple {
                    symbol: Symbol("or".to_string()),
                },
            },
            arguments: vec![l, r],
        };
    }

    match term {
        Term::Constant(_) => term,
        Term::QualIdentifier(_) => term,
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            let mut new_arguments = vec![];
            for arg in arguments {
                let new_arg = rewrite_term_trivial_rec(arg);
                new_arguments.push(new_arg);
            }
            return Term::Application {
                qual_identifier,
                arguments: new_arguments,
            };
        }
        Term::Let { var_bindings, term } => {
            let var_bindings = var_bindings
                .into_iter()
                .map(|(var, binding)| (var, rewrite_term_trivial_rec(binding)))
                .collect();
            let term = rewrite_term_trivial_rec(*term);
            return Term::Let {
                var_bindings: var_bindings,
                term: Box::new(term),
            };
        }
        Term::Forall { vars, term } => {
            let new_term = rewrite_term_trivial_rec(*term);
            return Term::Forall {
                vars: vars,
                term: Box::new(new_term),
            };
        }
        Term::Exists { vars, term } => {
            let new_term = rewrite_term_trivial_rec(*term);
            return Term::Exists {
                vars: vars,
                term: Box::new(new_term),
            };
        }
        Term::Match { term: _, cases: _ } => {
            panic!("not supporting match yet");
        }
        Term::Attributes { term, attributes } => {
            let new_term = rewrite_term_trivial_rec(*term);
            if new_term.to_string() == "true" || new_term.to_string() == "false" {
                return new_term;
            }
            return Term::Attributes {
                term: Box::new(new_term),
                attributes: attributes,
            };
        }
    }
}

// fn rewrite_trivial(mut commands: Vec<concrete::Command>) -> Vec<concrete::Command> {
//     commands.iter_mut().for_each(|c| {
//         if let Command::Assert { term } = c {
//             *term = rewrite_term_trivial_rec(term.clone());
//         }
//     });
//     commands
// }

// fn find_macro(commands: &Vec<concrete::Command>) {
//     commands.iter().for_each(|c| {
//         if let Command::Assert { term } = c {
//             if let Term::Forall { vars, term } = term {
//                 if let Term::Attributes { term , attributes } = &**term {
//                     if let Some((lhs, rhs)) = get_equal_terms(term) {
//                         // println!("found macro?");
//                         // println!("{}", c);
//                         println!("lhs {}", lhs);
//                         println!("rhs {}", rhs);
//                         println!("");
//                     }
//                 }
//             }
//         }
//     });
// }

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

// fn replace_equal_terms(command: &concrete::Command, rules: &HashMap<Term, Term>) -> Option<concrete::Command>
// {
//     if let Command::Assert { term } = command {
//         let mut string = format!("{}", term);
//         for rule in rules.iter() {
//             let lhs = rule.0.to_string();
//             let rhs = rule.1.to_string();
//             if string.contains(&lhs) {
//                 string = string.replace(&lhs, &rhs);
//             }
//         }
//         println!("(assert {})", string);
//     } else {
//         println!("{}", command);
//     }

//     // if let Command::DefineFun { sig: _, term } = command {
//     //     let string = format!("{}", term);
//     //     for rule in rules.iter() {
//     //         let lhs = rule.0.to_string();
//     //         let rhs = rule.1.to_string();
//     //         if string.contains(&lhs) {
//     //             println!("original:\n {}", string);
//     //             let aa = string.replace(&lhs, &rhs);
//     //             println!("replace with:\n {}", aa);
//     //         }
//     //     }
//     // }
//     return None;
// }

// pub fn rewrite_equal(mut commands: Vec<concrete::Command>) -> Vec<concrete::Command>
// {
//     let mut lhs: HashMap<Term, Term> = HashMap::new();

//     commands.retain(|c| {
//         if let Command::Assert { term } = c {
//             if let Some((l, r)) = get_equal_term(&term) {
//                 lhs.insert(l, r);
//                 return false;
//             }
//         }
//         return true;
//     });

//     // for rule in lhs.iter() {
//     //     let lhs = rule.0.to_string();
//     //     let rhs = rule.1.to_string();
//     //     println!("lhs {}", lhs);
//     //     println!("rhs {}", rhs);
//     // }

//     for cmd in commands.iter() {
//         replace_equal_terms(cmd, &lhs);
//     }

//     // let mut commands = commands;

//     // commands.into_iter().map(|x| replace_equal_terms(x, &lhs)).map(filter_none).flatten().collect();

//     // EqualityRewriter {
//     //     lhs: lhs,
//     // }

//     // let rewriter = EqualityRewriter::new(&commands);
//     vec![]
// }

fn print_prop_skeleton(term: &concrete::Term, indent: usize) {
    if let Term::Application {
        qual_identifier,
        arguments,
    } = term
    {
        if let QualIdentifier::Simple { identifier } = qual_identifier {
            if let concrete::Identifier::Simple { symbol } = identifier {
                if symbol.0 == "=>" {
                    assert!(arguments.len() == 2);
                    print!("{}(=>\n", " ".repeat(indent));
                    print_prop_skeleton(&arguments[0], indent + 1);
                    print_prop_skeleton(&arguments[1], indent + 1);
                    print!("{})\n", " ".repeat(indent));
                    return;
                }
                if symbol.0 == "and" {
                    print!("{}(and\n", " ".repeat(indent));
                    for arg in arguments {
                        print_prop_skeleton(arg, indent + 1);
                    }
                    print!("{})\n", " ".repeat(indent));
                    return;
                }
                if symbol.0 == "not" {
                    assert!(arguments.len() == 1);
                    print!("{}(not\n", " ".repeat(indent));
                    print_prop_skeleton(&arguments[0], indent + 1);
                    print!("{})\n", " ".repeat(indent));
                    return;
                }
                if symbol.0 == "or" {
                    print!("{}(or\n", " ".repeat(indent));
                    for arg in arguments {
                        print_prop_skeleton(arg, indent + 1);
                    }
                    print!("{})\n", " ".repeat(indent));
                    return;
                }
            }
        }
    }
    println!("{}{}", " ".repeat(indent), term);
}

fn decompose_goal(goal_command: concrete::Command) -> Vec<concrete::Command> {
    let mut rewriter = LetBindingReWriter::new();

    let goal_command = rewriter.rewrite_as_inline(goal_command);
    if let Command::Assert { term } = goal_command {
        let term = get_unary_app_term(&term, &Symbol("not".to_string())).unwrap();
        let mut terms = get_nested_implies_terms(&term);
        let goal_term = terms.pop().unwrap();
        let goal_term = Term::Application {
            qual_identifier: QualIdentifier::Simple {
                identifier: concrete::Identifier::Simple {
                    symbol: Symbol("not".to_string()),
                },
            },
            arguments: vec![goal_term],
        };
        let mut cmds: Vec<concrete::Command> = terms.into_iter().map(|term| {
            Command::Assert { term: term }
        }).collect();

        cmds = cmds
            .into_iter()
            .map(|x| flatten_assert(x))
            .flatten()
            .collect();

        let goal_term = rewrite_term_trivial_rec(goal_term);
        print_prop_skeleton(&goal_term, 0);
        cmds.push(Command::Assert { term: goal_term });
        return cmds;
    }
    vec![]
}

pub fn tree_rewrite(commands: Vec<concrete::Command>) -> Vec<concrete::Command> {
    let mut commands = commands;
    truncate_commands(&mut commands);
    let goal_command = commands.pop().unwrap();

    // commands = rewrite_trivial(commands);
    // find_macro(&commands);

    // commands = commands
    //     .into_iter()
    //     .map(|x| flatten_assert(x))
    //     .flatten()
    //     .collect();
    // commands = rewrite_equal(commands);

    let mut sub_commands = decompose_goal(goal_command);
    commands.append(&mut sub_commands);

    commands.push(concrete::Command::CheckSat);

    return commands;
}

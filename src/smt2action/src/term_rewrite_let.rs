use std::collections::{HashMap, HashSet};

use smt2parser::concrete;
use smt2parser::concrete::{QualIdentifier, Symbol, Term};

use crate::term_match::match_simple_qual_identifier;

fn let_binding_as_command(var: &Symbol, term0: &concrete::Term) -> Vec<concrete::Command> {
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
        concrete::Command::DeclareConst {
            symbol: var.clone(),
            sort: concrete::Sort::Simple {
                identifier: concrete::Identifier::Simple {
                    symbol: Symbol("Bool".to_owned()),
                },
            },
        },
        concrete::Command::Assert { term: *term },
    ]
}

#[allow(dead_code)]
pub struct LetBindingReWriter {
    let_bindings: HashMap<Symbol, (concrete::Term, usize)>,
    order: Vec<Symbol>,
    other_bindings: HashSet<Symbol>,
}

impl LetBindingReWriter {
    #[allow(dead_code)]
    pub fn new() -> LetBindingReWriter {
        LetBindingReWriter {
            let_bindings: HashMap::new(),
            order: vec![],
            other_bindings: HashSet::new(),
        }
    }

    // fn add_other_binding(&mut self, var: Symbol, binding: concrete::Term) {
    //     assert!(!self.binded.contains(&var));
    //     self.binded.insert(var.clone());
    //     self.bindings.insert(var, binding, 0);
    // }

    fn add_let_binding(&mut self, var: Symbol, binding: concrete::Term) {
        assert!(!self.other_bindings.contains(&var));
        let exists = self.let_bindings.insert(var.clone(), (binding, 0));
        self.order.push(var);
        assert!(exists.is_none());
    }

    fn increment_let_binding(&mut self, qual_identifier: &concrete::QualIdentifier) {
        if let Some(symbol) = match_simple_qual_identifier(qual_identifier) {
            if let Some((_, count)) = self.let_bindings.get_mut(symbol) {
                *count += 1;
            }
        }
    }

    fn rewrite_let_bindings_rec(&mut self, term: &mut Term) {
        match term {
            Term::Constant(_) => {}
            Term::QualIdentifier(qual_identifier) => {
                self.increment_let_binding(&qual_identifier);
            }
            Term::Application { arguments, .. } => {
                arguments
                    .iter_mut()
                    .for_each(|arg| self.rewrite_let_bindings_rec(arg));
            }
            Term::Let {
                var_bindings,
                term: sub_term,
            } => {
                // probably not the best way to write it
                let bindings = std::mem::replace(var_bindings, vec![]);
                bindings.into_iter().for_each(|(var, mut binding)| {
                    self.rewrite_let_bindings_rec(&mut binding);
                    self.add_let_binding(var, binding);
                });

                let mut temp = std::mem::replace(
                    sub_term,
                    Box::new(Term::Constant(concrete::Constant::String("0".to_string()))),
                );
                self.rewrite_let_bindings_rec(&mut temp);
                *term = *temp;
            }
            Term::Forall { term, .. } => {
                self.rewrite_let_bindings_rec(term);
            }
            Term::Exists { term, .. } => {
                self.rewrite_let_bindings_rec(term);
            }
            Term::Match { .. } => {
                panic!("not supporting match yet");
            }
            Term::Attributes { term, .. } => {
                self.rewrite_let_bindings_rec(term);
            }
        }
    }

    #[allow(dead_code)]
    pub fn rewrite_let_bindings(&mut self, mut term: concrete::Term) -> Vec<concrete::Command> {
        let mut commands = vec![];
        self.rewrite_let_bindings_rec(&mut term);
        for var in self.order.iter() {
            let (binding, count) = self.let_bindings.get(var).unwrap();
            if *count > 0 {
                let def_fun = let_binding_as_command(var, binding);
                commands.extend(def_fun);
            }
        }
        commands.push(concrete::Command::Assert { term: term });
        return commands;
    }
}

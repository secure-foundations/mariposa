use std::collections::HashMap;

use smt2parser::concrete;
use smt2parser::concrete::{Symbol, Term};

use crate::term_match::{match_simple_qual_identifier_term, SymbolSet};

pub struct Substituter {
    mapping: HashMap<Symbol, Term>,
    local_symbols: SymbolSet,
}

#[allow(dead_code)]
impl Substituter {
    pub fn new(mapping: HashMap<Symbol, Term>) -> Self {
        Substituter {
            mapping,
            local_symbols: SymbolSet::new(),
        }
    }

    fn add_local_binding(&mut self, symbol: &concrete::Symbol) {
        self.local_symbols.insert(symbol.clone());
    }

    fn remove_local_binding(&mut self, symbol: &concrete::Symbol) {
        self.local_symbols.remove(symbol);
    }

    pub fn substitute(&mut self, term: &mut Term) {
        match term {
            concrete::Term::Application {
                qual_identifier: _,
                arguments,
            } => {
                for argument in arguments.iter_mut() {
                    self.substitute(argument);
                }
            }
            concrete::Term::Let {
                var_bindings,
                term: sub_term,
            } => {
                var_bindings.iter_mut().for_each(|x| {
                    self.add_local_binding(&x.0);
                    self.substitute(&mut x.1);
                });
                self.substitute(sub_term);
                var_bindings.iter().for_each(|x| {
                    self.remove_local_binding(&x.0);
                });
            }
            concrete::Term::Forall { vars, term: sub_term } => {
                vars.iter().for_each(|x| {
                    self.add_local_binding(&x.0);
                });
                self.substitute(sub_term);
                vars.iter().for_each(|x| {
                    self.remove_local_binding(&x.0);
                });
            }
            concrete::Term::Exists { vars, term: sub_term } => {
                vars.iter().for_each(|x| {
                    self.add_local_binding(&x.0);
                });
                self.substitute(sub_term);
                vars.iter().for_each(|x| {
                    self.remove_local_binding(&x.0);
                });
            }
            concrete::Term::Attributes { term: sub_term, attributes: _ } => {
                self.substitute(sub_term);
            }
            concrete::Term::Match { .. } => {
                panic!("TODO match cases")
            }
            concrete::Term::Constant(_) => (),
            concrete::Term::QualIdentifier(..) => {
                let id = match_simple_qual_identifier_term(term);
                if id.is_none() {
                    return;
                }
                let id = (*id.unwrap()).clone();
                if self.mapping.contains_key(&id) && !self.local_symbols.contains(&id) {
                    *term = self.mapping[&id].clone();

                    let mut bound_vars = SymbolSet::new();
                    if !get_free_variables(&term, &mut bound_vars).is_disjoint(&self.local_symbols) {
                        panic!("bound variable substitution not supported");
                    }
                }
            },
        }
    }
}

fn get_free_variables(term: &Term, bound_vars: &mut SymbolSet) -> SymbolSet {
    match term {
        concrete::Term::Application {
            qual_identifier: _,
            arguments,
        } => {
            let mut free_vars = SymbolSet::new();

            for argument in arguments {
                free_vars.extend(get_free_variables(argument, bound_vars));
            }

            free_vars
        }
        concrete::Term::Let {
            var_bindings,
            term: sub_term,
        } => {
            let mut free_vars = SymbolSet::new();

            var_bindings.into_iter().for_each(|x| {
                bound_vars.insert(x.0.clone());
                free_vars.extend(get_free_variables(&x.1, bound_vars));
            });
            free_vars.extend(get_free_variables(sub_term, bound_vars));
            var_bindings.into_iter().for_each(|x| {
                bound_vars.remove(&x.0);
            });

            free_vars
        }
        concrete::Term::Exists { vars, term: sub_term } |
        concrete::Term::Forall { vars, term: sub_term } => {
            let mut free_vars = SymbolSet::new();

            vars.into_iter().for_each(|x| {
                bound_vars.insert(x.0.clone());
            });
            free_vars.extend(get_free_variables(sub_term, bound_vars));
            vars.into_iter().for_each(|x| {
                bound_vars.remove(&x.0);
            });

            free_vars
        }
        concrete::Term::Attributes { term: sub_term, attributes: _ } => get_free_variables(sub_term, bound_vars),
        concrete::Term::Match { .. } => panic!("TODO match cases"),
        concrete::Term::Constant(_) => SymbolSet::new(),
        concrete::Term::QualIdentifier(..) => {
            let id = match_simple_qual_identifier_term(term);
            if id.is_none() {
                return SymbolSet::new();
            }
            let id = (*id.unwrap()).clone();
            if !bound_vars.contains(&id) {
                return SymbolSet::from([id]);
            }

            SymbolSet::new()
        },
    }
}

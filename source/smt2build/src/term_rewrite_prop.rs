use smt2parser::concrete;
use smt2parser::concrete::{QualIdentifier, Symbol, Term};
use std::collections::{HashMap, HashSet};

use crate::term_match::{
    make_bool_term, make_false_term, make_not_term, make_true_term, match_bool_term,
    match_simple_qual_identifier,
};

fn rewrite_prop_app(identifier: &QualIdentifier, arguments: &mut Vec<Term>) -> Option<Term> {
    let id = match_simple_qual_identifier(identifier)?;

    if id.0 == "=>" || id.0 == "implies" {
        let p = match_bool_term(&arguments[0]);
        let q = match_bool_term(&arguments[1]);

        if p == Some(false) {
            // false => q = true
            return Some(make_true_term());
        } else if p == Some(true) {
            // true => q = q
            return Some(arguments[1].clone());
        } else if q == Some(false) {
            // p => false = not p
            return Some(make_not_term(arguments[0].clone()));
        } else if q == Some(true) {
            // p => true = true
            return Some(make_true_term());
        }
    } else if id.0 == "and" {
        arguments.retain(|arg| match_bool_term(arg) != Some(true));
        if arguments
            .iter()
            .any(|arg| match_bool_term(arg) == Some(false))
        {
            return Some(make_false_term());
        }
        if arguments.len() == 1 {
            return arguments.pop();
        }
    } else if id.0 == "or" {
        arguments.retain(|arg| match_bool_term(arg) != Some(false));
        if arguments
            .iter()
            .any(|arg| match_bool_term(arg) == Some(true))
        {
            return Some(make_true_term());
        }
        if arguments.len() == 1 {
            return arguments.pop();
        }
    } else if id.0 == "not" {
        assert!(arguments.len() == 1);
        let arg = &arguments[0];

        if *arg == make_true_term() {
            return Some(make_false_term());
        } else if *arg == make_false_term() {
            return Some(make_true_term());
        }
    }
    return None;
}

pub struct PropRewriter {
    bindings: HashMap<Symbol, bool>,
}

impl PropRewriter {
    fn rewrite_prop_rec(&mut self, term: &mut concrete::Term) -> Option<bool> {
        match term {
            Term::Constant(_) => None,
            Term::QualIdentifier(identifier) => {
                let id = match_simple_qual_identifier(identifier)?;
                if let Some(binding) = self.bindings.get(&id) {
                    return Some(*binding);
                } else if id.0 == "true" {
                    return Some(true);
                } else if id.0 == "false" {
                    return Some(false);
                }
                return None;
            }
            Term::Application {
                qual_identifier,
                arguments,
            } => {
                let temp = vec![];
                let arg_terms = std::mem::replace(arguments, temp);
                let mut arg_terms: Vec<Term> = arg_terms
                    .into_iter()
                    .map(|mut arg| {
                        if let Some(b) = self.rewrite_prop_rec(&mut arg) {
                            make_bool_term(b)
                        } else {
                            arg
                        }
                    })
                    .collect();
                if let Some(new_term) = rewrite_prop_app(qual_identifier, &mut arg_terms) {
                    let trivial = match_bool_term(&new_term);
                    *term = new_term;
                    return trivial;
                } else {
                    *arguments = arg_terms;
                    return None;
                }
            }
            Term::Let {
                var_bindings,
                term: sub_term,
            } => {
                let mut locals = HashSet::new();

                // if we a binding is trivial, add it to the bindings map
                var_bindings.iter_mut().for_each(|(var, binding)| {
                    if let Some(trivial) = self.rewrite_prop_rec(binding) {
                        self.bindings.insert(var.clone(), trivial);
                        locals.insert(var.clone());
                    }
                });

                let mut result = None;
                if let Some(trivial) = self.rewrite_prop_rec(sub_term) {
                    *term = make_bool_term(trivial);
                    result = Some(trivial);
                }

                // remove local bindings after rewriting sub_term
                locals.iter().for_each(|v| {
                    let _ = self.bindings.remove(v);
                });
                return result;
            }
            Term::Forall {
                vars: _,
                term: sub_term,
            } => {
                let trivial = self.rewrite_prop_rec(sub_term)?;
                *term = make_bool_term(trivial);
                return Some(trivial);
            }
            Term::Exists {
                vars: _,
                term: sub_term,
            } => {
                let trivial = self.rewrite_prop_rec(sub_term)?;
                *term = make_bool_term(trivial);
                return Some(trivial);
            }
            Term::Attributes {
                term: sub_term,
                attributes: _,
            } => {
                let trivial = self.rewrite_prop_rec(sub_term)?;
                *term = make_bool_term(trivial);
                return Some(trivial);
            }
            _ => None,
        }
    }
}

pub fn term_rewrite_prop(term: &mut concrete::Term) {
    let mut rewriter = PropRewriter {
        bindings: HashMap::new(),
    };
    rewriter.rewrite_prop_rec(term);
}

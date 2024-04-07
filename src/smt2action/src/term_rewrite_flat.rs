use smt2parser::concrete;
use smt2parser::concrete::{Command, Term};

use crate::term_match::match_simple_app_term;

fn flatten_nested_and_terms(term: &mut Term, results: &mut Vec<Term>) {
    if let Some((symbol, args)) = match_simple_app_term(term) {
        if symbol.0 == "and" {
            args.iter_mut().for_each(|arg| {
                flatten_nested_and_terms(arg, results);
            });
            return;
        }
    }
    results.push(term.clone());
}

pub fn flatten_assert(command: concrete::Command) -> Vec<concrete::Command> {
    let Command::Assert { mut term } = command else {
        return vec![command];
    };
    let mut ts = Vec::new();

    if let concrete::Term::Attributes { mut term, attributes: _ } = term {
        flatten_nested_and_terms(&mut term, &mut ts);
        // flatten_nested_and_terms(&mut term, &mut ts);
    } else {
        flatten_nested_and_terms(&mut term, &mut ts);
    }
    ts.into_iter()
    .map(|x| concrete::Command::Assert { term: x })
    .collect()
}

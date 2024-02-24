use smt2parser::concrete;
use smt2parser::concrete::{Command, Term};

use crate::term_match::match_simple_app_term;

fn flatten_nested_and_terms(term: &mut Term, results: &mut Vec<Term>) -> bool {
    if let Some((symbol, args)) = match_simple_app_term(term) {
        if symbol.0 == "and" {
            args.iter_mut().for_each(|arg| {
                flatten_nested_and_terms(arg, results);
            });
            return true;
        }
    } else if let Term::Attributes { term: sub_term, .. } = term {
        if flatten_nested_and_terms(sub_term, results) {
            return true;
        }
    }
    results.push(term.clone());
    return false;
}

pub fn flatten_assert(command: concrete::Command) -> Vec<concrete::Command> {
    if let Command::Assert { mut term } = command {
        let mut ts = Vec::new();
        flatten_nested_and_terms(&mut term, &mut ts);
        ts.into_iter()
            .map(|x| concrete::Command::Assert { term: x })
            .collect()
    } else {
        vec![command]
    }
}

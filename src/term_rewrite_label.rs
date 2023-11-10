use crate::term_match::{match_simple_app_term, match_simple_qual_identifier_term};
use smt2parser::concrete;
use smt2parser::concrete::Term;

fn remove_negative_label(term: &mut Term) {
    let (s, args) = match_simple_app_term(term).unwrap();
    assert!(s.0 == "or" && args.len() == 2);
    let r = args.pop().unwrap();
    let l = args.pop().unwrap();
    if let Some(label) = match_simple_qual_identifier_term(&l) {
        assert!(label.0.starts_with("%lbl%@"));
        *term = r;
    } else {
        panic!("unexpected negative label term")
    }
}

fn remove_positive_label(term: &mut Term) {
    let (s, args) = match_simple_app_term(term).unwrap();
    assert!(s.0 == "and" && args.len() == 2);
    let r = args.pop().unwrap();
    let l = args.pop().unwrap();
    if let Some(label) = match_simple_qual_identifier_term(&l) {
        assert!(label.0.starts_with("%lbl%+"));
        *term = r;
    } else {
        panic!("unexpected positive label term")
    }
}

pub fn remove_label_rec(term: &mut Term) {
    match term {
        Term::Constant(_) => {}
        Term::QualIdentifier(_) => {}
        Term::Application { arguments, .. } => {
            arguments.iter_mut().for_each(|arg| remove_label_rec(arg));
        }
        Term::Forall { vars: _, term } => {
            remove_label_rec(term);
        }
        Term::Exists { vars: _, term } => {
            remove_label_rec(term);
        }
        Term::Let { var_bindings, term } => {
            var_bindings.iter_mut().for_each(|(_, term)| {
                remove_label_rec(term);
            });
            remove_label_rec(term);
        }
        Term::Match { term: _, cases: _ } => {
            panic!("not supporting match yet");
        }
        Term::Attributes { term, attributes } => {
            let mut lblneg = false;
            let mut lblpos = false;

            attributes.iter().for_each(|f| {
                let concrete::Keyword(k) = &f.0;
                if k == "lblneg" {
                    lblneg = true;
                } else if k == "lblpos" {
                    lblpos = true;
                }
            });

            if lblneg {
                remove_negative_label(term);
            } else if lblpos {
                remove_positive_label(term);
            } else {
                remove_label_rec(term);
            }
        }
    }
}

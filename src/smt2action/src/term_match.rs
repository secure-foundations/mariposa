use std::collections::HashSet;

use smt2parser::concrete;
use smt2parser::concrete::{QualIdentifier, Symbol, Term};

#[allow(dead_code)]
pub fn make_true_term() -> concrete::Term {
    return Term::QualIdentifier(QualIdentifier::Simple {
        identifier: concrete::Identifier::Simple {
            symbol: concrete::Symbol("true".to_string()),
        },
    });
}

#[allow(dead_code)]
pub fn make_false_term() -> concrete::Term {
    return Term::QualIdentifier(QualIdentifier::Simple {
        identifier: concrete::Identifier::Simple {
            symbol: concrete::Symbol("false".to_string()),
        },
    });
}

#[allow(dead_code)]
pub fn make_bool_term(b: bool) -> concrete::Term {
    if b {
        return make_true_term();
    } else {
        return make_false_term();
    }
}

#[allow(dead_code)]
pub fn make_not_term(term: concrete::Term) -> concrete::Term {
    return Term::Application {
        qual_identifier: QualIdentifier::Simple {
            identifier: concrete::Identifier::Simple {
                symbol: concrete::Symbol("not".to_string()),
            },
        },
        arguments: vec![term],
    };
}

#[allow(dead_code)]
pub fn match_bool_term(term: &concrete::Term) -> Option<bool> {
    if let Term::QualIdentifier(QualIdentifier::Simple { identifier }) = term {
        if let concrete::Identifier::Simple { symbol } = identifier {
            if symbol.0 == "true" {
                return Some(true);
            } else if symbol.0 == "false" {
                return Some(false);
            }
        }
    }
    return None;
}

#[inline]
pub fn match_simple_qual_identifier(identifier: &concrete::QualIdentifier) -> Option<&Symbol> {
    if let QualIdentifier::Simple { identifier } = identifier {
        if let concrete::Identifier::Simple { symbol } = identifier {
            return Some(symbol);
        }
    }
    return None;
}

#[inline]
pub fn match_simple_qual_identifier_term(term: &Term) -> Option<&Symbol> {
    if let Term::QualIdentifier(qual_identifier) = term {
        return match_simple_qual_identifier(qual_identifier);
    }
    return None;
}

#[inline]
pub fn mk_simple_qual_id_term(symbol: Symbol) -> concrete::Term {
    return Term::QualIdentifier(mk_simple_qual_id(symbol));
}

#[inline]
pub fn mk_simple_qual_id(symbol: Symbol) -> concrete::QualIdentifier {
    return QualIdentifier::Simple {
        identifier: concrete::Identifier::Simple { symbol },
    };
}

// pub fn get_binary_app_term(term: &concrete::Term, fun_symbol: &Symbol) -> Option<(Term, Term)> {
//     if let Term::Application {
//         qual_identifier,
//         arguments,
//     } = term
//     {
//         if let QualIdentifier::Simple { identifier } = qual_identifier {
//             if let concrete::Identifier::Simple { symbol } = identifier {
//                 if symbol == fun_symbol {
//                     assert!(arguments.len() == 2);
//                     return Some((arguments[0].clone(), arguments[1].clone()));
//                 }
//             }
//         }
//     }
//     return None;
// }

pub fn match_simple_app_term(
    term: &mut concrete::Term,
) -> Option<(&Symbol, &mut Vec<concrete::Term>)> {
    if let Term::Application {
        qual_identifier,
        arguments,
    } = term
    {
        if let Some(symbol) = match_simple_qual_identifier(qual_identifier) {
            return Some((symbol, arguments));
        }
    }
    return None;
}

pub fn get_identifier_symbols(identifier: &concrete::Identifier) -> Symbol {
    match identifier {
        concrete::Identifier::Simple { symbol } => symbol.clone(),
        concrete::Identifier::Indexed { symbol, indices: _ } => symbol.clone(),
    }
}

pub type SymbolSet = HashSet<Symbol>;

pub fn format_symbol_set(symbols: &SymbolSet) -> String {
    let mut s = String::new();
    s.push_str("{\n\t");
    let joined = symbols
        .iter()
        .map(|x| x.0.clone())
        .collect::<Vec<String>>()
        .join("\n\t");
    s.push_str(&joined);
    s.push_str("\n}");
    return s;
}

pub fn get_sexpr_symbols(e: &concrete::SExpr) -> SymbolSet {
    let mut symbols = HashSet::new();
    match e {
        concrete::SExpr::Constant(..) => (),
        concrete::SExpr::Symbol(symbol) => {
            symbols.insert(symbol.clone());
        }
        concrete::SExpr::Application(app) => {
            app.iter()
                .for_each(|x| symbols.extend(get_sexpr_symbols(x)));
        }
        _ => panic!("TODO SExpr {:?}", e),
    }
    symbols
}

pub fn is_qf_term(term: &Term) -> bool {
    match term {
        Term::Constant(_) => true,
        Term::QualIdentifier(_) => true,
        Term::Application { arguments, .. } => arguments.iter().all(|arg| is_qf_term(arg)),
        Term::Let { var_bindings, term } => {
            var_bindings.iter().all(|(_, binding)| is_qf_term(binding)) && is_qf_term(term)
        }
        Term::Forall { .. } => false,
        Term::Exists { .. } => false,
        Term::Attributes { term, .. } => is_qf_term(term),
        Term::Match { .. } => panic!("TODO Match {:?}", term),
    }
}

pub fn is_prop_term(term: &concrete::Term) -> bool {
    match term {
        concrete::Term::Attributes {
            term,
            attributes: _,
        } => is_prop_term(term),
        concrete::Term::Forall { .. } => true,
        concrete::Term::Exists { .. } => true,
        concrete::Term::Let { term, .. } => is_prop_term(term),
        concrete::Term::Match { .. } => false,
        concrete::Term::Constant(_) => false,
        concrete::Term::QualIdentifier(_) => false,
        concrete::Term::Application {
            qual_identifier, ..
        } => {
            if let Some(fname) = match_simple_qual_identifier(qual_identifier) {
                let fname = &fname.0;
                fname == "=" || fname == "not" || fname == "and" || fname == "or" || fname == "=>"
            } else {
                false
            }
        }
    }
}

pub fn get_attr_qid(
    attributes: &Vec<(concrete::Keyword, concrete::AttributeValue)>,
) -> Option<&String> {
    let mut qid = None;
    attributes.iter().for_each(|(key, value)| {
        if key != &concrete::Keyword("qid".to_owned()) {
            return;
        }
        let concrete::AttributeValue::Symbol(concrete::Symbol(name)) = value else {
            return;
        };
        qid = Some(name);
    });
    qid
}

pub fn remove_attr_qid_skolemid(
    attributes: &mut Vec<(concrete::Keyword, concrete::AttributeValue)>,
) {
    attributes.retain(|(key, _)| {
        let concrete::Keyword(k) = key;
        k != "qid" && k != "skolemid"
    });
}

pub fn get_attr_cid(
    attributes: &Vec<(concrete::Keyword, concrete::AttributeValue)>,
) -> Option<&String> {
    let mut cid = None;
    attributes.iter().for_each(|(key, value)| {
        if key != &concrete::Keyword("named".to_owned()) {
            return;
        }
        let concrete::AttributeValue::Symbol(concrete::Symbol(name)) = value else {
            return;
        };
        cid = Some(name);
    });
    cid
}

fn dedup_patterns_rec(cur_term: &mut concrete::Term, enable: bool) {
    match cur_term {
        concrete::Term::Application {
            qual_identifier: _,
            arguments,
        } => {
            for argument in arguments.iter_mut() {
                dedup_patterns_rec(argument, false)
            }
        }
        concrete::Term::Let { var_bindings, term } => {
            for var_binding in var_bindings.iter_mut() {
                dedup_patterns_rec(&mut var_binding.1, false)
            }
            dedup_patterns_rec(&mut *term, false)
        }
        concrete::Term::Forall { vars: _, term } | concrete::Term::Exists { vars: _, term } => {
            let mut enable = true;
            if !matches!(&**term, concrete::Term::Attributes { .. }) {
                // this is for the case where the quantified term has no attributes
                enable = false;
            }
            dedup_patterns_rec(&mut *term, enable)
        }
        concrete::Term::Attributes { term, attributes } => {
            dedup_patterns_rec(term, false);

            if !enable {
                return;
            }

            attributes.iter_mut().for_each(|x| {
                if x.0 != concrete::Keyword("pattern".to_owned()) {
                    return;
                }
                let mut seen_patterns = HashSet::new();

                match &mut x.1 {
                    concrete::AttributeValue::Terms(terms) => {
                        terms.retain(|term| {
                            let pattern = format!("{}", term.clone());
                            if seen_patterns.contains(&pattern) {
                                return false;
                            }
                            seen_patterns.insert(pattern);
                            return true;
                        });
                        // for term in terms.iter() {
                        //     let pattern = format!("{}", term.clone());
                        //     if seen_patterns.contains(&pattern) {
                        //         println!("removing pattern: {}", pattern);
                        //     }
                        //     seen_patterns.insert(pattern);
                        // }
                    },
                    _ => {}
                    // _ => panic!("unexpected pattern value: {:?}", x.1),
                }
            });
        }
        concrete::Term::Constant(_) => (),
        concrete::Term::QualIdentifier(_) => (),
        concrete::Term::Match { term, cases: _ } => {
            panic!("unsupported term: {:?}", term)
        }
    }
}


pub fn dedup_patterns(commands: &mut Vec<concrete::Command>) {
    commands.iter_mut().for_each(|c| match c {
        concrete::Command::Assert { term } => {
            dedup_patterns_rec(term, false);
        }
        concrete::Command::MariposaArbitrary(_) => panic!("unexpected mariposa-arbitrary"),
        _ => {}
    });
}
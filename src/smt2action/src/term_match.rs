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

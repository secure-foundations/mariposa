use smt2parser::concrete;
use smt2parser::concrete::{QualIdentifier, Symbol, Term};

pub fn make_true_term() -> concrete::Term {
    return Term::QualIdentifier(QualIdentifier::Simple {
        identifier: concrete::Identifier::Simple {
            symbol: concrete::Symbol("true".to_string()),
        },
    });
}

pub fn make_false_term() -> concrete::Term {
    return Term::QualIdentifier(QualIdentifier::Simple {
        identifier: concrete::Identifier::Simple {
            symbol: concrete::Symbol("false".to_string()),
        },
    });
}

pub fn make_bool_term(b: bool) -> concrete::Term {
    if b {
        return make_true_term();
    } else {
        return make_false_term();
    }
}

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

pub fn match_simple_app_term(term: &mut concrete::Term) -> Option<(&Symbol, &mut Vec<concrete::Term>)> {
    if let Term::Application {
        qual_identifier,
        arguments,
    } = term
    {
        if let QualIdentifier::Simple { identifier } = qual_identifier {
            if let concrete::Identifier::Simple { symbol } = identifier {
                return Some((symbol, arguments));
            }
        }
    }
    return None;
}

// pub fn match_forall_term(term: &mut concrete::Term) -> Option<(&mut Vec<(Symbol, concrete::Sort)>, &mut concrete::Term)> {
//     if let Term::Forall { vars, term } = term {
//         return Some((vars, term));
//     }
//     return None;
// }
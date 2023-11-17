use smt2parser::concrete;
use smt2parser::concrete::{AttributeValue, Command, Symbol, Term};
use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::sync::Arc;

use crate::term_match::{get_identifier_symbols, get_sexpr_symbols, SymbolSet};
use crate::tree_shake;

type SymbolCount = HashMap<Symbol, usize>;

struct UseCounter {
    defined_symbols: Arc<SymbolSet>,
    local_bindings: SymbolSet,
    counts: SymbolCount,
    df_counts: SymbolCount,
    include_patterns: bool,
}

impl UseCounter {
    fn new(defined_symbols: Arc<SymbolSet>, include_patterns: bool) -> Self {
        Self {
            defined_symbols,
            local_bindings: SymbolSet::new(),
            counts: HashMap::new(),
            df_counts: HashMap::new(),
            include_patterns,
        }
    }

    fn increment_symbol_count(&mut self, symbol: &Symbol) {
        if let Some(count) = self.counts.get_mut(symbol) {
            *count += 1;
            return;
        }

        if self.local_bindings.contains(symbol) {
            return;
        }

        if self.defined_symbols.contains(symbol) {
            *self.counts.entry(symbol.clone()).or_insert(0) += 1;
        }
    }

    fn add_local_binding(&mut self, symbol: &concrete::Symbol) {
        self.local_bindings.insert(symbol.clone());
    }

    fn remove_local_binding(&mut self, symbol: &concrete::Symbol) {
        self.local_bindings.remove(symbol);
    }

    fn count_symbol_uses_rec(&mut self, term: &Term) {
        match term {
            Term::Constant(..) => (),
            Term::QualIdentifier(qual_identifier) => {
                if let concrete::QualIdentifier::Simple { identifier } = qual_identifier {
                    self.increment_symbol_count(&get_identifier_symbols(identifier));
                } else {
                    panic!("TODO sorted QualIdentifier")
                }
            }
            Term::Application {
                qual_identifier,
                arguments,
            } => {
                if let concrete::QualIdentifier::Simple { identifier } = qual_identifier {
                    self.increment_symbol_count(&get_identifier_symbols(identifier));
                } else {
                    panic!("TODO sorted QualIdentifier")
                }
                arguments.iter().for_each(|x| self.count_symbol_uses_rec(x));
            }
            Term::Let { var_bindings, term } => {
                // remove local bindings
                var_bindings.iter().for_each(|x| {
                    self.add_local_binding(&x.0);
                    self.count_symbol_uses_rec(&x.1);
                });
                self.count_symbol_uses_rec(term);
                var_bindings
                    .iter()
                    .for_each(|x| self.remove_local_binding(&x.0));
            }
            Term::Forall { vars, term } | Term::Exists { vars, term } => {
                // no need for sort symbols right?
                vars.iter().for_each(|x| self.add_local_binding(&x.0));
                self.count_symbol_uses_rec(term);
                vars.iter().for_each(|x| self.remove_local_binding(&x.0));
            }
            Term::Match { term: _, cases: _ } => {
                panic!("TODO match cases")
            }
            Term::Attributes { term, attributes } => {
                self.count_symbol_uses_rec(term);

                if self.include_patterns {
                    attributes.into_iter().for_each(|f| {
                        let concrete::Keyword(k) = &f.0;
                        if k == "pattern" || k == "no-pattern" {
                            match &f.1 {
                                AttributeValue::None => (),
                                AttributeValue::Constant(..) => (),
                                AttributeValue::Symbol(symbol) => {
                                    self.increment_symbol_count(symbol);
                                }
                                AttributeValue::Terms(terms) => {
                                    terms.iter().for_each(|x| self.count_symbol_uses_rec(&x));
                                }
                                AttributeValue::SExpr(ses) => {
                                    ses.iter().for_each(|se| {
                                        get_sexpr_symbols(se)
                                            .iter()
                                            .for_each(|x| self.increment_symbol_count(x));
                                    });
                                }
                            }
                        }
                    });
                }
            }
        }
    }

    fn process_command(&mut self, command: &Command) {
        if let Command::Assert { term } = command {
            self.count_symbol_uses_rec(term);
        }


    } 
}

pub fn count_symbol_uses(term: &Term, defined_symbols: Arc<SymbolSet>) -> SymbolCount {
    let mut counter = UseCounter::new(defined_symbols, false);
    counter.count_symbol_uses_rec(term);
    counter.counts
}

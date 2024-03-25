use smt2parser::concrete;
use smt2parser::concrete::{AttributeValue, Command, Symbol, Term};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::term_match::{get_identifier_symbols, get_sexpr_symbols, SymbolSet};

type SymbolCount = HashMap<Symbol, usize>;

// get the symbols defined in a command
pub fn get_command_symbol_def(command: &concrete::Command) -> SymbolSet {
    let mut symbols = HashSet::new();
    match command {
        Command::DeclareConst { symbol, sort: _ } => {
            symbols.insert(symbol.clone());
        }
        Command::DeclareDatatypes { datatypes } => {
            datatypes.iter().for_each(|x| {
                symbols.insert(x.0.clone());
                assert_eq!(x.2.parameters.len(), 0);
                x.2.constructors.iter().for_each(|y| {
                    symbols.insert(y.symbol.clone());
                    y.selectors.iter().for_each(|z| {
                        symbols.insert(z.0.clone());
                    });
                });
            });
        }
        Command::DeclareFun { symbol, .. } => {
            symbols.insert(symbol.clone());
        }
        Command::DefineFun { sig, .. } => {
            symbols.insert(sig.name.clone());
        }
        Command::DeclareSort { .. } => {
            // println!("Sort symbol not considered");
            // symbols.insert(symbol.0.clone());
        }
        _ => (),
    }

    // if DEBUG_DEFS && symbols.len() > 0 {
    //     println!("{}", command);
    //     for s in &symbols {
    //         println!("\t{}", s);
    //     }
    // }
    symbols
}

fn get_commands_symbol_def_plain(commands: &Vec<concrete::Command>) -> SymbolSet {
    let defs: SymbolSet = commands
        .iter()
        .map(|x| get_command_symbol_def(x))
        .flatten()
        .collect();
    return defs;
}

pub struct AltSymbolSet {
    trivial: SymbolSet,
    pub defined: SymbolSet,

    ref_trivial: Arc<SymbolSet>,
    ref_defined: Arc<SymbolSet>,
}

impl AltSymbolSet {
    pub fn new(
        init: SymbolSet,
        ref_trivial: Arc<SymbolSet>,
        ref_defined: Arc<SymbolSet>,
    ) -> Self {
        let trivial = SymbolSet::new();
        let defined = SymbolSet::new();

        let mut result = Self {
            trivial,
            defined,
            ref_trivial,
            ref_defined,
        };

        result.extend(init);
        return result;
    }

    pub fn extend(&mut self, other: SymbolSet) {
        assert!(self.defined.is_superset(&self.trivial));
        for symbol in other.into_iter() {
            if self.ref_defined.contains(&symbol) {
                self.defined.insert(symbol.clone());
                if self.ref_trivial.contains(&symbol) {
                    self.trivial.insert(symbol);
                }
            }
        }
    }

    pub fn is_superset(&self, other: &SymbolSet) -> bool {
        if other.is_subset(&self.trivial) {
            return false;
        }

        return other.is_subset(&self.defined);
    }

    // pub fn is_disjoint(&self, other: &SymbolSet) -> bool {
    //     return other.is_disjoint(&self.defined);
    // }

    pub fn has_overlap(&self, other: &SymbolSet) -> bool {
        // TODO: optimize
        let overlap: SymbolSet = self
            .defined
            .intersection(other)
            .map(|x| x.clone())
            .collect();

        if overlap.is_subset(&self.trivial) {
            return false;
        }

        return overlap.len() > 0;
    }

    pub fn debug(&self) {
        println!("[sb] trivial:");
        for s in &self.trivial {
            println!("[sb] {}", s);
        }
        println!("[sb] defined:");
        for s in &self.defined {
            println!("[sb] {}", s);
        }
    }

}

pub fn get_commands_symbol_def_alt(
    commands: &Vec<concrete::Command>,
    max_symbol_frequency: usize,
) -> (SymbolSet, SymbolSet) {
    assert!(max_symbol_frequency <= 100);

    let (cmd_freq, use_cmd_count) = count_commands_symbol_frequency(commands, false);

    let (under, over): (_, Vec<_>) = cmd_freq
        .into_iter()
        .partition(|(_, count)| count * 100 / use_cmd_count <= max_symbol_frequency);

    let mut under: SymbolSet = under.into_iter().map(|(symbol, _)| symbol).collect();
    let over: SymbolSet = over.into_iter().map(|(symbol, _)| symbol).collect();
    under.extend(over.clone());
    (over, under)
}

// pub fn get_commands_symbol_def(
//     commands: &Vec<concrete::Command>,
//     max_symbol_frequency: usize,
// ) -> SymbolSet {
//     assert!(max_symbol_frequency <= 100);

//     if max_symbol_frequency == 100 {
//         return get_commands_symbol_def_plain(commands);
//     }

//     let (cmd_freq, use_cmd_count) = count_commands_symbol_frequency(commands, false);

//     cmd_freq
//         .into_iter()
//         .filter(|(_, count)| count * 100 / use_cmd_count <= max_symbol_frequency)
//         .map(|(symbol, _)| symbol)
//         .collect()
// }

struct CommandUseCounter {
    defined_symbols: Arc<SymbolSet>,
    local_bindings: SymbolSet,
    symbol_counts: SymbolCount,
    include_patterns: bool,
}

impl CommandUseCounter {
    fn new(defined_symbols: Arc<SymbolSet>, include_patterns: bool) -> Self {
        Self {
            defined_symbols,
            local_bindings: SymbolSet::new(),
            symbol_counts: HashMap::new(),
            include_patterns,
        }
    }

    fn increment_symbol_count(&mut self, symbol: &Symbol) {
        if let Some(count) = self.symbol_counts.get_mut(symbol) {
            *count += 1;
            return;
        }

        if self.local_bindings.contains(symbol) {
            return;
        }

        if self.defined_symbols.contains(symbol) {
            *self.symbol_counts.entry(symbol.clone()).or_insert(0) += 1;
        }
    }

    fn add_local_binding(&mut self, symbol: &concrete::Symbol) {
        self.local_bindings.insert(symbol.clone());
    }

    fn remove_local_binding(&mut self, symbol: &concrete::Symbol) {
        self.local_bindings.remove(symbol);
    }

    fn count_symbol_use_rec(&mut self, term: &Term) {
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
                arguments.iter().for_each(|x| self.count_symbol_use_rec(x));
            }
            Term::Let { var_bindings, term } => {
                // remove local bindings
                var_bindings.iter().for_each(|x| {
                    self.add_local_binding(&x.0);
                    self.count_symbol_use_rec(&x.1);
                });
                self.count_symbol_use_rec(term);
                var_bindings
                    .iter()
                    .for_each(|x| self.remove_local_binding(&x.0));
            }
            Term::Forall { vars, term } | Term::Exists { vars, term } => {
                // no need for sort symbols right?
                vars.iter().for_each(|x| self.add_local_binding(&x.0));
                self.count_symbol_use_rec(term);
                vars.iter().for_each(|x| self.remove_local_binding(&x.0));
            }
            Term::Match { term: _, cases: _ } => {
                panic!("TODO match cases")
            }
            Term::Attributes { term, attributes } => {
                self.count_symbol_use_rec(term);

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
                                    terms.iter().for_each(|x| self.count_symbol_use_rec(&x));
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
}

pub fn count_command_symbol_use(
    command: &Command,
    defined_symbols: Arc<SymbolSet>,
    include_patterns: bool,
) -> SymbolCount {
    let mut counter = CommandUseCounter::new(defined_symbols, include_patterns);

    if let Command::Assert { term } = command {
        counter.count_symbol_use_rec(term);
    } else if let Command::DefineFun { sig, term } = command {
        sig.parameters
            .iter()
            .for_each(|arg| counter.add_local_binding(&arg.0));
        counter.count_symbol_use_rec(term);
        sig.parameters
            .iter()
            .for_each(|arg| counter.remove_local_binding(&arg.0));
    }
    return counter.symbol_counts;
}

pub fn count_commands_symbol_frequency(
    commands: &Vec<Command>,
    include_patterns: bool,
) -> (SymbolCount, usize) {
    let defined_symbols = Arc::new(get_commands_symbol_def_plain(commands));
    let mut use_cmd_count = 0;

    // this will only count each symbol at most once per command
    let mut cmd_freq = HashMap::new();

    commands.iter().for_each(|c| {
        let uses = count_command_symbol_use(c, defined_symbols.clone(), include_patterns);
        if uses.len() > 0 {
            use_cmd_count += 1;
        }
        uses.iter().for_each(|(symbol, _)| {
            *cmd_freq.entry(symbol.clone()).or_insert(0) += 1;
        });
    });
    return (cmd_freq, use_cmd_count);
}

pub fn print_commands_symbol_frequency(commands: &Vec<Command>, include_patterns: bool) {
    let (cmd_freq, use_cmd_count) = count_commands_symbol_frequency(commands, include_patterns);

    let mut symbols: Vec<_> = cmd_freq.iter().collect();
    symbols.sort_by(|a, b| b.1.cmp(a.1));

    println!("MARIPOSA_USE_CMD_COUNT {}", use_cmd_count);
    for (symbol, count) in symbols {
        println!("{} {} {}", symbol, count, count * 100 / use_cmd_count);
    }
}

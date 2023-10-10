use smt2parser::concrete;
use smt2parser::concrete::{AttributeValue, Command, QualIdentifier, Symbol, Term};
use std::collections::HashSet;

use crate::tree_rewrite;

const DEBUG_DEFS: bool = false;

// get the symbols defined in a command
fn get_global_symbol_defs(command: &concrete::Command) -> HashSet<String> {
    let mut symbols = HashSet::new();
    match command {
        Command::DeclareConst { symbol, sort: _ } => {
            symbols.insert(symbol.0.clone());
        }
        Command::DeclareDatatype {
            symbol: _,
            datatype: _,
        } => {
            // symbols.insert(symbol.0.clone());
            panic!("TODO datatype")
        }
        Command::DeclareDatatypes { datatypes } => {
            datatypes.iter().for_each(|x| {
                symbols.insert(x.0 .0.clone());
                assert_eq!(x.2.parameters.len(), 0);
                x.2.constructors.iter().for_each(|y| {
                    symbols.insert(y.symbol.0.clone());
                    y.selectors.iter().for_each(|z| {
                        symbols.insert(z.0 .0.clone());
                    });
                });
            });
        }
        Command::DeclareFun {
            symbol,
            parameters: _,
            sort: _,
        } => {
            symbols.insert(symbol.0.clone());
        }
        Command::DeclareSort {
            symbol: _,
            arity: _,
        } => {
            println!("Sort symbol not considered");
            // symbols.insert(symbol.0.clone());
        }
        Command::DefineFun { sig, term: _ } => {
            symbols.insert(sig.name.0.clone());
        }
        Command::DefineFunRec { sig: _, term: _ } => {
            panic!("TODO define fun rec")
        }
        Command::DefineFunsRec { funs: _ } => {
            panic!("TODO define funs rec")
        }
        Command::DefineSort {
            symbol: _,
            parameters: _,
            sort: _,
        } => {
            panic!("TODO define sort")
        }
        _ => (),
    }
    if DEBUG_DEFS && symbols.len() > 0 {
        println!("{}", command);
        for s in &symbols {
            println!("\t{}", s);
        }
    }
    symbols
}

fn get_identifier_symbols(identifier: &concrete::Identifier) -> HashSet<Symbol> {
    let mut symbols = HashSet::new();
    match identifier {
        concrete::Identifier::Simple { symbol } => {
            symbols.insert(symbol.clone());
        }
        concrete::Identifier::Indexed { symbol, indices: _ } => {
            symbols.insert(symbol.clone());
            // panic!("TODO indexed identifier {}", symbol)
        }
    }
    symbols
}

struct SymbolUseTracker {
    // local symbols (e.g. bound variables forall, exists, let)
    local_symbols: Vec<HashSet<Symbol>>,
    // global symbols (e.g. defined functions, constants)
    non_pattern_symbols: HashSet<Symbol>,
    pattern_symbols: Vec<HashSet<Symbol>>,
    in_pattern: bool,
    collect_all: bool,
}

impl SymbolUseTracker {
    fn new(collet_all: bool) -> SymbolUseTracker {
        SymbolUseTracker {
            local_symbols: Vec::new(),
            non_pattern_symbols: HashSet::new(),
            pattern_symbols: Vec::new(),
            in_pattern: false,
            collect_all: collet_all,
        }
    }

    fn push_term_scope(&mut self) {
        self.local_symbols.push(HashSet::new());
    }

    fn pop_term_scope(&mut self) {
        self.local_symbols.pop();
    }

    fn try_add_pattern_group(&mut self) {
        if self.in_pattern {
            return;
        }
        self.in_pattern = true;
        self.pattern_symbols.push(HashSet::new());
    }

    fn exit_pattern_group(&mut self) {
        assert!(self.in_pattern);
        self.in_pattern = false;
    }

    fn try_add_use(&mut self, symbol: &concrete::Symbol) {
        // ignore if defined in local scope
        for scope in self.local_symbols.iter_mut().rev() {
            if scope.contains(symbol) {
                return;
            }
        }
        if self.in_pattern {
            let index = self.pattern_symbols.len() - 1;
            self.pattern_symbols[index].insert(symbol.clone());
        } else {
            self.non_pattern_symbols.insert(symbol.clone());
        }
    }

    fn add_local_binding(&mut self, symbol: &concrete::Symbol) {
        let index = self.local_symbols.len() - 1;
        self.local_symbols[index].insert(symbol.clone());
    }

    fn get_symbol_uses(&mut self, term: &concrete::Term) {
        match term {
            Term::Constant(..) => (),
            Term::QualIdentifier(qual_identifier) => {
                if let concrete::QualIdentifier::Simple { identifier } = qual_identifier {
                    get_identifier_symbols(identifier)
                        .iter()
                        .for_each(|x| self.try_add_use(x));
                } else {
                    panic!("TODO sorted QualIdentifier")
                }
            }
            Term::Application {
                qual_identifier,
                arguments,
            } => {
                if let concrete::QualIdentifier::Simple { identifier } = qual_identifier {
                    get_identifier_symbols(identifier)
                        .iter()
                        .for_each(|x| self.try_add_use(x));
                } else {
                    panic!("TODO sorted QualIdentifier")
                }
                arguments.iter().for_each(|x| self.get_symbol_uses(x));
            }
            Term::Let { var_bindings, term } => {
                self.push_term_scope();
                var_bindings.iter().for_each(|x| {
                    self.add_local_binding(&x.0);
                    self.get_symbol_uses(&x.1);
                });
                self.get_symbol_uses(term);
                self.pop_term_scope();
            }
            Term::Forall { vars, term } => {
                self.push_term_scope();
                // no need for sort symbols right?
                vars.iter().for_each(|x| self.add_local_binding(&x.0));
                self.get_symbol_uses(&term);
                self.pop_term_scope();
            }
            Term::Exists { vars, term } => {
                self.push_term_scope();
                vars.iter().for_each(|x| self.add_local_binding(&x.0));
                self.get_symbol_uses(&term);
                self.pop_term_scope();
            }
            Term::Match { term: _, cases: _ } => {
                panic!("TODO match cases")
            }
            Term::Attributes { term, attributes } => {
                let mut use_pattern = false;
                attributes.into_iter().for_each(|f| {
                    let concrete::Keyword(k) = &f.0;
                    // if pattern is given, ignore the term
                    if k == "pattern" {
                        use_pattern = true;
                        // self.in_pattern = true;
                        self.try_add_pattern_group();
                        match &f.1 {
                            AttributeValue::None => (),
                            AttributeValue::Constant(..) => (),
                            AttributeValue::Symbol(symbol) => self.try_add_use(symbol),
                            AttributeValue::Terms(terms) => {
                                terms.iter().for_each(|x| self.get_symbol_uses(x))
                            }
                            _ => panic!("TODO attribute value {:?}", &f.1),
                        }
                        self.exit_pattern_group();
                    } else if k == "named"
                        || k == "qid"
                        || k == "skolemid"
                        || k == "weight"
                        || k == "lblpos"
                        || k == "lblneg"
                        || k == "no-pattern"
                    {
                        // println!("{}", f.1);
                    } else {
                        panic!("TODO attribute keyword {}", k)
                    }
                });
                if !use_pattern || self.collect_all {
                    self.get_symbol_uses(term);
                }
            }
        }
    }
}

struct SymbolUsage {
    non_pattern_symbols: HashSet<String>,
    pattern_symbols: Vec<HashSet<String>>,
}

impl SymbolUsage {
    fn flattened_pattern_symbols(&self) -> HashSet<String> {
        self.pattern_symbols.iter().flatten().cloned().collect()
    }

    fn flattened_all_symbols(&self) -> HashSet<String> {
        let mut all_symbols = self.non_pattern_symbols.clone();
        all_symbols.extend(self.flattened_pattern_symbols());
        all_symbols
    }

    fn check_overlap(&self, other: &mut HashSet<String>) -> bool {
        if self.flattened_all_symbols().intersection(other).count() != 0 {
            other.extend(self.flattened_all_symbols());
            return true;
        }
        // if self.non_pattern_symbols.intersection(other).count() != 0 {
        //     let m = self.flattened_all_symbols();
        //     other.extend(m);
        //     return true;
        // }
        // if self.pattern_symbols
        //     .iter()
        //     .any(|x| x.intersection(other).count() != 0) {
        //     // other.extend(self.non_pattern_symbols.clone());
        //     other.extend(self.flattened_all_symbols());
        //     return true;
        // }
        return false;
    }
}

fn get_command_symbol_uses(
    command: &concrete::Command,
    defs: &HashSet<String>,
    collet: bool,
) -> SymbolUsage {
    let mut tracker = SymbolUseTracker::new(collet);
    match command {
        Command::Assert { term } => {
            tracker.get_symbol_uses(term);
        }
        _ => {}
    }
    let mut np_symbols: HashSet<String> = tracker
        .non_pattern_symbols
        .into_iter()
        .map(|f| f.0)
        .collect();
    np_symbols.retain(|x| defs.contains(x));

    for i in &mut tracker.pattern_symbols {
        i.retain(|x| defs.contains(&x.0));
    }

    let p_symbols: Vec<HashSet<String>> = tracker
        .pattern_symbols
        .into_iter()
        .map(|f| f.into_iter().map(|x| x.0).collect())
        .collect();

    if np_symbols.len() > 0 || p_symbols.len() > 0 {
        println!("{}", command);
        println!("Non-pattern symbols:");

        for i in &np_symbols {
            println!("\t{}", i);
        }

        println!("Pattern symbols:");

        for i in &p_symbols {
            for j in i {
                println!("\t{}", j);
            }
            println!();
        }
    }
    SymbolUsage {
        non_pattern_symbols: np_symbols,
        pattern_symbols: p_symbols,
    }
}

pub fn fun_to_assert(command: concrete::Command) -> Vec<concrete::Command> {
    if let Command::DefineFun { sig, term } = &command {
        if sig.parameters.len() == 0 {
            return vec![command];
        }
        let vars: Vec<Term> = sig
            .parameters
            .iter()
            .map(|f| {
                Term::QualIdentifier(QualIdentifier::Simple {
                    identifier: concrete::Identifier::Simple {
                        symbol: f.0.clone(),
                    },
                })
            })
            .collect();
        vec![
            Command::DeclareFun {
                symbol: sig.name.clone(),
                parameters: sig.parameters.iter().map(|f| f.1.clone()).collect(),
                sort: sig.result.clone(),
            },
            Command::Assert {
                term: Term::Forall {
                    vars: sig
                        .parameters
                        .iter()
                        .map(|f| (f.0.clone(), f.1.clone()))
                        .collect(),
                    term: Box::new(Term::Application {
                        qual_identifier: QualIdentifier::Simple {
                            identifier: concrete::Identifier::Simple {
                                symbol: Symbol("=".to_string()),
                            },
                        },
                        arguments: vec![
                            Term::Application {
                                qual_identifier: QualIdentifier::Simple {
                                    identifier: concrete::Identifier::Simple {
                                        symbol: sig.name.clone(),
                                    },
                                },
                                arguments: vars,
                            },
                            term.clone(),
                        ],
                    }),
                },
            },
        ]
    } else {
        vec![command]
    }
}

pub fn tree_shake(mut commands: Vec<concrete::Command>) -> Vec<concrete::Command> {
    // commands = commands.into_iter().map(|x| flatten_nested_and(x)).flatten().collect();
    tree_rewrite::truncate_commands(&mut commands);

    let defs: HashSet<String> = commands
        .iter()
        .map(|x| get_global_symbol_defs(x))
        .flatten()
        .collect();

    let goal_command = commands.pop().unwrap();

    let mut snowball = get_command_symbol_uses(&goal_command, &defs, true).flattened_all_symbols();

    print!("Snowball: {:?} ", snowball);

    let symbols: Vec<SymbolUsage> = commands
        .iter()
        .map(|c| get_command_symbol_uses(&c, &defs, false))
        .collect();

    let mut poss = HashSet::new();
    let mut pposs = HashSet::new();
    poss.insert(0);

    while poss != pposs {
        pposs = poss.clone();
        for (pos, ss) in symbols.iter().enumerate() {
            if ss.check_overlap(&mut snowball) {
                // snowball.extend(ss.0.iter().cloned());
                poss.insert(pos);
            } else {
                if let Command::Assert { term: _ } = &commands[pos] {
                } else {
                    poss.insert(pos);
                }
            }
        }
    }

    commands = commands
        .into_iter()
        .enumerate()
        .filter(|(pos, _)| poss.contains(pos))
        .map(|(_, x)| x)
        .collect();
    commands.push(goal_command);
    commands.push(Command::CheckSat);
    commands
}

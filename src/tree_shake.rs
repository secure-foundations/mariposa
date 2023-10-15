use smt2parser::concrete;
use smt2parser::concrete::{AttributeValue, Command, QualIdentifier, Symbol, Term};
use std::collections::{HashMap, HashSet};

use crate::tree_rewrite;

const DEBUG_DEFS: bool = false;
const DEBUG_USES: bool = false;

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
            // println!("Sort symbol not considered");
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

fn get_identifier_symbols(identifier: &concrete::Identifier) -> Symbol {
    match identifier {
        concrete::Identifier::Simple { symbol } => symbol.clone(),
        concrete::Identifier::Indexed { symbol, indices: _ } => {
            symbol.clone()
            // panic!("TODO indexed identifier {}", symbol)
        }
    }
}

type SymbolSet = HashSet<Symbol>;

struct SymbolUseTracker {
    defined_symbols: SymbolSet,
    // local symbols (e.g. bound variables forall, exists, let)
    local_symbols: Vec<SymbolSet>,
    // global symbols (e.g. defined functions, constants)
    pattern_symbols: Vec<(SymbolSet, SymbolSet)>,
    non_pattern_symbols: SymbolSet,
}

impl SymbolUseTracker {
    fn new(defs: &SymbolSet) -> SymbolUseTracker {
        SymbolUseTracker {
            defined_symbols: defs.clone(),
            local_symbols: Vec::new(),
            pattern_symbols: Vec::new(),
            non_pattern_symbols: HashSet::new(),
        }
    }

    fn push_term_scope(&mut self) {
        self.local_symbols.push(HashSet::new());
    }

    fn pop_term_scope(&mut self) {
        self.local_symbols.pop();
    }

    // fn try_add_pattern_group(&mut self) {
        // if self.in_pattern {
        //     return;
        // }
        // self.in_pattern = true;
        // self.pattern_symbols.push(HashSet::new());
    // }

    // fn exit_pattern_group(&mut self) {
    //     assert!(self.in_pattern);
    //     self.in_pattern = false;
    // }

    // fn try_add_use(&mut self, symbol: &concrete::Symbol) {
    //     // ignore if defined in local scope
    //     for scope in self.local_symbols.iter_mut().rev() {
    //         if scope.contains(symbol) {
    //             return;
    //         }
    //     }
    //     if self.in_pattern {
    //         let index = self.pattern_symbols.len() - 1;
    //         self.pattern_symbols[index].insert(symbol.clone());
    //     } else {
    //         self.non_pattern_symbols.insert(symbol.clone());
    //     }
    // }

    fn add_local_binding(&mut self, symbol: &concrete::Symbol) {
        let index = self.local_symbols.len() - 1;
        self.local_symbols[index].insert(symbol.clone());
    }

    fn get_symbol_uses(&mut self, term: &concrete::Term) -> SymbolSet {
        let mut uses = HashSet::new();
        match term {
            Term::Constant(..) => { () },
            Term::QualIdentifier(qual_identifier) => {
                if let concrete::QualIdentifier::Simple { identifier } = qual_identifier {
                    uses.insert(get_identifier_symbols(identifier));
                } else {
                    panic!("TODO sorted QualIdentifier")
                }
            }
            Term::Application {
                qual_identifier,
                arguments,
            } => {
                if let concrete::QualIdentifier::Simple { identifier } = qual_identifier {
                    uses.insert(get_identifier_symbols(identifier));
                } else {
                    panic!("TODO sorted QualIdentifier")
                }
                arguments
                    .into_iter()
                    .map(|x| self.get_symbol_uses(x))
                    .for_each(|x| uses.extend(x));
            }
            Term::Let { var_bindings, term } => {
                // remove local bindings
                self.push_term_scope();
                var_bindings.iter().for_each(|x| {
                    self.add_local_binding(&x.0);
                    uses.extend(self.get_symbol_uses(&x.1).iter().cloned());
                });
                uses.extend(self.get_symbol_uses(term).iter().cloned());
                self.pop_term_scope();
            }
            Term::Forall { vars, term } => {
                self.push_term_scope();
                // no need for sort symbols right?
                vars.iter().for_each(|x| self.add_local_binding(&x.0));
                uses.extend(self.get_symbol_uses(term).iter().cloned());
                self.pop_term_scope();
            }
            Term::Exists { vars, term } => {
                self.push_term_scope();
                vars.iter().for_each(|x| self.add_local_binding(&x.0));
                uses.extend(self.get_symbol_uses(term).iter().cloned());
                self.pop_term_scope();
            }
            Term::Match { term: _, cases: _ } => {
                panic!("TODO match cases")
            }
            Term::Attributes { term, attributes } => {
                let mut pattern_sets = Vec::new();
                attributes.into_iter().for_each(|f| {
                    let concrete::Keyword(k) = &f.0;
                    // if pattern is given, ignore the term
                    if k == "pattern" {
                        // self.in_pattern = true;
                        // self.try_add_pattern_group();
                        match &f.1 {
                            AttributeValue::None => (),
                            AttributeValue::Constant(..) => (),
                            AttributeValue::Symbol(symbol) => {
                                panic!("TODO pattern symbol {:?}", &f.1);
                                // uses.insert(symbol.clone());
                            },
                            AttributeValue::Terms(terms) => {
                                // assert!(terms.len() == 1);
                                terms.iter().for_each(|x| pattern_sets.push(self.get_symbol_uses(&x)));
                            }
                            _ => panic!("TODO attribute value {:?}", &f.1),
                        }
                        // self.exit_pattern_group();
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
                uses = self.get_symbol_uses(term);
                if pattern_sets.len() >= 1 {
                    pattern_sets.iter().for_each(|x| 
                        self.pattern_symbols.push((x.clone(), uses.clone()))
                    );
                    uses = HashSet::new();
                    pattern_sets.iter().for_each(|x| uses.extend(x.iter().cloned()));
                }
            }
        }
        // remove local bindings
        uses.retain(|x| {
            for scope in self.local_symbols.iter() {
                if scope.contains(x) {
                    return false;
                }
            }
            self.defined_symbols.contains(x)
        });
        uses
    }

    fn check_overlap(&self, other: &mut SymbolSet) -> bool {
        let mut overlap = false;
        if self.non_pattern_symbols.intersection(other).count() != 0 {
            other.extend(self.non_pattern_symbols.clone());
            overlap = true;
        }
        for (xs, ys) in self.pattern_symbols.iter() {
            if xs.intersection(other).count() != 0 {
                other.extend(ys.clone());
                overlap = true;
            }
        }
        return overlap;
    }

    fn debug(&self) {
                 // remove defs
            // uses.retain(|x| def.contains(x));

        for s in &self.non_pattern_symbols {
            println!("\t{}", s);
        }
        let mut i = 0;
        for (xs, ys) in self.pattern_symbols.iter() {
            println!("Pattern group {}", i);
            println!("Pattern symbols:");

            for s in xs {
                println!("\t{}", s);
            }
            println!("Mapped non-pattern symbols:");
            for s in ys {
                println!("\t{}", s);
            }
            i += 1;
            println!();
        }
    }
}

// struct SymbolUsage {
//     non_pattern_symbols: SymbolSet,
//     pattern_symbols: HashMap<SymbolSet, SymbolSet>,
// }

// impl SymbolUsage {
//     // fn flattened_pattern_symbols(&self) -> HashSet<String> {
//     //     self.pattern_symbols.iter().flatten().cloned().collect()
//     // }

//     // fn flattened_all_symbols(&self) -> HashSet<String> {
//     //     let mut all_symbols = self.non_pattern_symbols.clone();
//     //     all_symbols.extend(self.flattened_pattern_symbols());
//     //     all_symbols
//     // }

//     // fn check_overlap(&self, other: &mut HashSet<String>) -> bool {
//     //     if self.flattened_all_symbols().intersection(other).count() != 0 {
//     //         other.extend(self.flattened_all_symbols());
//     //         return true;
//     //     }
//     //     // if self.non_pattern_symbols.intersection(other).count() != 0 {
//     //     //     let m = self.flattened_all_symbols();
//     //     //     other.extend(m);
//     //     //     return true;
//     //     // }
//     //     // if self.pattern_symbols
//     //     //     .iter()
//     //     //     .any(|x| x.intersection(other).count() != 0) {
//     //     //     // other.extend(self.non_pattern_symbols.clone());
//     //     //     other.extend(self.flattened_all_symbols());
//     //     //     return true;
//     //     // }
//     //     return false;
//     // }
// }

fn get_command_symbol_uses(
    command: &concrete::Command,
    defs: &SymbolSet,
) -> SymbolUseTracker {
    let mut tracker = SymbolUseTracker::new(defs);
    match command {
        Command::Assert { term } => {
            // println!("assert {}", term);
            let uses = tracker.get_symbol_uses(term);
            tracker.non_pattern_symbols = uses;
            tracker.defined_symbols = HashSet::new();
            tracker.local_symbols = Vec::new();
        }
        Command::DefineFun { sig, term } => 
        {
            let uses = tracker.get_symbol_uses(term);
            tracker.non_pattern_symbols = uses;
            tracker.non_pattern_symbols.insert(sig.name.clone());
            tracker.defined_symbols = HashSet::new();
            tracker.local_symbols = Vec::new();
        }
        _ => {}
    }
    if DEBUG_USES {
        println!("{}", command);
        tracker.debug();
    }
    tracker
}

pub fn tree_shake(mut commands: Vec<concrete::Command>) -> Vec<concrete::Command> {
    tree_rewrite::truncate_commands(&mut commands);

    // commands = tree_rewrite::tree_rewrite(commands); 
    // commands = commands
    //     .into_iter()
    //     .map(|x| tree_rewrite::flatten_assert(x))
    //     .flatten()
    //     .collect();

    // println!("flattened command count: {}", commands.len());
    let goal_command = commands[commands.len() - 1].clone();

    let defs: HashSet<String> = commands
        .iter()
        .map(|x| get_global_symbol_defs(x))
        .flatten()
        .collect();

    let defs: SymbolSet = defs.iter().map(|x| Symbol(x.clone())).collect();

    let mut snowball = get_command_symbol_uses(&goal_command, &defs).non_pattern_symbols.clone();

    if DEBUG_USES {
        println!("[sb]Snowball:");
        for s in &snowball {
            println!("[sb]\t{}", s);
        }
    }

    let symbols: Vec<SymbolUseTracker> = commands
        .iter()
        .map(|c| get_command_symbol_uses(&c, &defs))
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

    if DEBUG_USES {
        println!("[sb]Snowball:");
        for s in &snowball {
            println!("[sb]\t{}", s);
        }    
    }

    commands = commands
        .into_iter()
        .enumerate()
        .filter(|(pos, _)| poss.contains(pos))
        .map(|(_, x)| x)
        .collect();
    // commands.push(goal_command);
    commands.push(Command::CheckSat);
    commands
}

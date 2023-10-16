use rand_chacha::rand_core::le;
use smt2parser::concrete;
use smt2parser::concrete::{AttributeValue, Command, QualIdentifier, Symbol, Term};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

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

struct MatchState {
    local_symbols: SymbolSet,
    hidden_term: Arc<Term>,
    patterns: Vec<SymbolSet>,
}


impl MatchState {
    fn new(locals: &SymbolSet, term: Arc<Term>, patterns: Vec<SymbolSet>) -> MatchState {
        MatchState {
            local_symbols: locals.clone(),
            hidden_term: term,
            patterns: patterns,
        }
    }

    fn check_match(&self, symbols: &SymbolSet) -> bool {
        let mut check_match = false;
        for p in &self.patterns {
            if p.is_subset(symbols) {
                check_match = true;
                break;
            }
        }
        check_match
    }

    fn debug(&self) {
        println!("\tHidden term:\n\t{}", self.hidden_term);
        for (i, s) in self.patterns.iter().enumerate() {
            println!("\tPatterns {}:", i);
            for s in s {
                println!("\t\t{}", s);
            }
        }
        println!("\tLocal symbols:");
        for s in &self.local_symbols {
            println!("\t\t{}", s);
        }
    }
}

struct UseTracker {
    defined_symbols: Arc<SymbolSet>,
    // local symbols (e.g. bound variables forall, exists, let)
    local_symbols: SymbolSet,
    match_states: Vec<MatchState>,
    live_symbols: SymbolSet,
    exhaustive: bool,
}

impl UseTracker {
    fn new(defs: Arc<SymbolSet>, command: &concrete::Command, exhaustive: bool) -> UseTracker {
       let mut tracker = UseTracker {
            defined_symbols: defs.clone(),
            local_symbols: HashSet::new(),
            match_states: Vec::new(),
            live_symbols: HashSet::new(),
            exhaustive: exhaustive,
        };

        tracker.process_command(command);
        tracker
    }

    // fork is used to create a new tracker for its sub terms
    fn fork(&self, locals: SymbolSet) -> UseTracker {
        UseTracker {
            defined_symbols: self.defined_symbols.clone(),
            local_symbols: locals,
            match_states: Vec::new(),
            live_symbols: HashSet::new(),
            exhaustive: false,
        }
    }

    fn add_local_binding(&mut self, symbol: &concrete::Symbol) {
        self.local_symbols.insert(symbol.clone());
    }

    fn remove_local_binding(&mut self, symbol: &concrete::Symbol) {
        self.local_symbols.remove(symbol);
    }

    fn get_symbol_uses(&mut self, term: &concrete::Term) -> SymbolSet {
        let mut uses = HashSet::new();
        match term {
            Term::Constant(..) => (),
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
                var_bindings.iter().for_each(|x| {
                    self.add_local_binding(&x.0);
                    uses.extend(self.get_symbol_uses(&x.1).into_iter())
                });
                uses.extend(self.get_symbol_uses(term).into_iter());
                var_bindings
                    .iter()
                    .for_each(|x| self.remove_local_binding(&x.0));
            }
            Term::Forall { vars, term } => {
                // no need for sort symbols right?
                vars.iter().for_each(|x| self.add_local_binding(&x.0));
                uses.extend(self.get_symbol_uses(term).into_iter());
                vars.iter().for_each(|x| self.remove_local_binding(&x.0));
            }
            Term::Exists { vars, term } => {
                vars.iter().for_each(|x| self.add_local_binding(&x.0));
                uses.extend(self.get_symbol_uses(term).into_iter());
                vars.iter().for_each(|x| self.remove_local_binding(&x.0));
            }
            Term::Match { term: _, cases: _ } => {
                panic!("TODO match cases")
            }
            Term::Attributes { term, attributes } => {
                let mut pattern_sets = Vec::new();
                if !self.exhaustive {
                    attributes.into_iter().for_each(|f| {
                        let concrete::Keyword(k) = &f.0;
                        // if pattern is given, ignore the term
                        if k == "pattern" {
                            match &f.1 {
                                AttributeValue::None => (),
                                AttributeValue::Constant(..) => (),
                                AttributeValue::Symbol(symbol) => {
                                    panic!("TODO pattern symbol {:?}", symbol);
                                }
                                AttributeValue::Terms(terms) => {
                                    terms
                                        .iter()
                                        .for_each(|x| pattern_sets.push(self.get_symbol_uses(&x)));
                                }
                                _ => panic!("TODO attribute value {:?}", &f.1),
                            }
                            // self.in_pattern = false;
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
                }
                if pattern_sets.len() != 0 {
                    let match_state =
                        MatchState::new(&self.local_symbols, term.clone().into(), pattern_sets);
                    self.match_states.push(match_state);
                //     pattern_sets.iter().for_each(|x| uses.extend(x.iter().cloned()));
                } else {
                    uses.extend(self.get_symbol_uses(term).into_iter());
                }
            }
        }
        // remove local bindings
        uses.retain(|x| (!self.local_symbols.contains(x)) && self.defined_symbols.contains(x));
        uses
    }

    fn process_command(&mut self, command: &concrete::Command) {
        match command {
            Command::Assert { term } => {
                let uses = self.get_symbol_uses(term);
                self.live_symbols = uses;
            }
            Command::DefineFun { sig, term } => {
                for p in &sig.parameters {
                    self.add_local_binding(&p.0);
                }
                let uses = self.get_symbol_uses(term);
                self.live_symbols = uses;
                self.live_symbols.insert(sig.name.clone());
            }
            _ => {}
        }
    }

    fn aggregate(&mut self, snowball: &mut SymbolSet) -> bool {
        let mut keep_going = true;
        let mut included = false;

        for s in &self.live_symbols {
            if snowball.contains(s) {
                included = true;
                break;
            }
        }

        if included {
            snowball.extend(self.live_symbols.iter().cloned());
        }

        while keep_going {
            keep_going = false;

            let mut cur_match_states = Vec::new();
            std::mem::swap(&mut self.match_states, &mut cur_match_states);

            let (matched, mut non_matched): (_, Vec<_>) = cur_match_states
                .into_iter()
                .partition(|s| s.check_match(snowball));

            matched.into_iter().for_each(|m| {
                let MatchState {
                    local_symbols,
                    hidden_term,
                    patterns: _,
                } = m;
                let mut child = self.fork(local_symbols);
                let child_symbols = child.get_symbol_uses(&hidden_term);
                let UseTracker {
                    mut match_states, ..
                } = child;
                self.live_symbols.extend(child_symbols.iter().cloned());
                snowball.extend(child_symbols.into_iter());
                non_matched.append(&mut match_states);
                keep_going = true;
                included = true;
            });

            self.match_states = non_matched;
        }
        if included {
            snowball.extend(self.live_symbols.iter().cloned());
        }
        included
    }

    fn debug(&self) {
        println!("Live symbols:");
        for s in &self.live_symbols {
            println!("\t{}", s);
        }
        println!("Local symbols:");
        for s in &self.local_symbols {
            println!("\t{}", s);
        }
        println!("Match states:");
        for (i, s) in self.match_states.iter().enumerate() {
            println!("\tMatch state {}", i);
            s.debug();
        }
    }
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
    // let goal_command = commands.pop().unwrap();
    // let mut rewriter = tree_rewrite::LetBindingReWriter::new();
    // let mut sub_commands = rewriter.rewrite(goal_command);
    // commands.append(&mut sub_commands);

    let goal_command = commands.pop().unwrap();
    // [commands.len() - 1].clone();
    // print!("{} ", goal_command);

    let defs: HashSet<String> = commands
        .iter()
        .map(|x| get_global_symbol_defs(x))
        .flatten()
        .collect();

    let defs: SymbolSet = defs.iter().map(|x| Symbol(x.clone())).collect();
    let defs = Arc::new(defs);
    let tracker = UseTracker::new(defs.clone(), &goal_command, true);
    let mut snowball = tracker.live_symbols;

    let mut trackers: Vec<UseTracker> = commands
        .iter()
        .map(|c|  UseTracker::new(defs.clone(), &c, false))
        .collect();

    let mut poss = HashSet::new();
    let mut pposs = HashSet::new();
    poss.insert(0);

    while poss != pposs {
        pposs = poss.clone();
        for (pos, tracker) in trackers.iter_mut().enumerate() {
            if tracker.aggregate(&mut snowball) {
                // snowball.extend(ss.0.iter().cloned());
                poss.insert(pos);
            } else {
                if let Command::Assert { term: _ } = &commands[pos] {
                } else {
                    poss.insert(pos);
                }
            }
            // if pos == 18543 {
            //     // println!("Command:\n{}:", commands[pos]);
            //     println!("\n\n");
            //     tracker.debug();
            // }
        }
    }

    if DEBUG_USES {
        for (i, tracker) in trackers.iter().enumerate() {
            if let Command::Assert { term: _ } = &commands[i] {
                // println!("Command:\n{}:", commands[i]);
                tracker.debug();
            } else {
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
        commands.push(goal_command);
    commands.push(Command::CheckSat);
    commands
}

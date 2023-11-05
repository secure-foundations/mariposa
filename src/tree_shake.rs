use smt2parser::concrete::{self};
use smt2parser::concrete::{AttributeValue, Command, Symbol, Term};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::io::Write;

use crate::tree_rewrite;

const DEBUG_DEFS: bool = false;
const DEBUG_USES: bool = false;

type SymbolSet = HashSet<Symbol>;

// get the symbols defined in a command
fn get_global_symbol_defs(command: &concrete::Command) -> SymbolSet {
    let mut symbols = HashSet::new();
    match command {
        Command::DeclareConst { symbol, sort: _ } => {
            symbols.insert(symbol.clone());
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
        Command::DeclareFun {
            symbol,
            parameters: _,
            sort: _,
        } => {
            symbols.insert(symbol.clone());
        }
        Command::DeclareSort {
            symbol: _,
            arity: _,
        } => {
            // println!("Sort symbol not considered");
            // symbols.insert(symbol.0.clone());
        }
        Command::DefineFun { sig, term: _ } => {
            symbols.insert(sig.name.clone());
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

fn get_sexpr_symbols(e: &concrete::SExpr) -> SymbolSet {
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

struct PatternState {
    local_symbols: SymbolSet,
    hidden_term: Arc<Term>,
    patterns: Vec<SymbolSet>,
}

struct NoPatternState {
    hidden_symbols: SymbolSet,
    filtered_symbols: SymbolSet,
}

enum MatchState {
    PatternState(PatternState),
    NoPatternState(NoPatternState),
}

impl MatchState {
    fn check_match(&self, symbols: &SymbolSet) -> bool {
        let mut check_match = false;
        match self {
            MatchState::PatternState(s) => {
                for p in &s.patterns {
                    if p.is_subset(symbols) {
                        check_match = true;
                        break;
                    }
                }
                check_match
            }
            MatchState::NoPatternState(s) => !s.filtered_symbols.is_disjoint(symbols),
        }
    }

    fn debug(&self) {
        match self {
            MatchState::PatternState(ps) => {
                println!("\tHidden term:\n\t{}", ps.hidden_term);
                for (i, s) in ps.patterns.iter().enumerate() {
                    println!("\tPatterns {}:", i);
                    for s in s {
                        println!("\t\t{}", s);
                    }
                }
                println!("\tLocal symbols:");
                for s in &ps.local_symbols {
                    println!("\t\t{}", s);
                }
            }
            MatchState::NoPatternState(s) => {
                println!("\tHidden symbols:");
                for s in &s.hidden_symbols {
                    println!("\t\t{}", s);
                }
                println!("\tFiltered symbols:");
                for s in &s.filtered_symbols {
                    println!("\t\t{}", s);
                }
            }
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
                let mut no_pattern = HashSet::new();
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
                        } else if k == "no-pattern" {
                            match &f.1 {
                                AttributeValue::None => (),
                                AttributeValue::Constant(..) => (),
                                AttributeValue::Symbol(symbol) => {
                                    no_pattern.insert(symbol.clone());
                                }
                                AttributeValue::Terms(terms) => {
                                    terms.iter().for_each(|x| {
                                        no_pattern.extend(self.get_symbol_uses(&x));
                                    });
                                }
                                AttributeValue::SExpr(ses) => {
                                    ses.iter()
                                        .for_each(|se| no_pattern.extend(get_sexpr_symbols(se)));
                                }
                            }
                        } else if k == "named"
                            || k == "qid"
                            || k == "skolemid"
                            || k == "weight"
                            || k == "lblpos"
                            || k == "lblneg"
                        {
                            // println!("{}", f.1);
                        } else {
                            panic!("TODO attribute keyword {}", k)
                        }
                    });
                }

                no_pattern.retain(|x| {
                    (!self.local_symbols.contains(x)) && self.defined_symbols.contains(x)
                });

                if pattern_sets.len() != 0 {
                    // drop no pattern if pattern is given
                    let match_state = PatternState {
                        local_symbols: self.local_symbols.clone(),
                        hidden_term: term.clone().into(),
                        patterns: pattern_sets,
                    };
                    self.match_states
                        .push(MatchState::PatternState(match_state));
                } else if no_pattern.len() != 0 {
                    let live = self.get_symbol_uses(term);
                    let filtered_symbols = live.difference(&no_pattern).cloned().collect();
                    // println!("no pattern: {:?}", &filtered_symbols);
                    let match_state = NoPatternState {
                        hidden_symbols: live,
                        filtered_symbols: filtered_symbols,
                    };
                    self.match_states
                        .push(MatchState::NoPatternState(match_state));
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
        let mut modified = !self.live_symbols.is_disjoint(&snowball);

        if modified {
            snowball.extend(self.live_symbols.iter().cloned());
        }

        while keep_going {
            let mut cur_match_states = Vec::new();
            std::mem::swap(&mut self.match_states, &mut cur_match_states);

            let (matched, mut non_matched): (_, Vec<_>) = cur_match_states
                .into_iter()
                .partition(|s| s.check_match(snowball));

            keep_going = matched.len() != 0;

            matched.into_iter().for_each(|m| match m {
                MatchState::PatternState(s) => {
                    let PatternState {
                        local_symbols,
                        hidden_term,
                        ..
                    } = s;
                    let mut child = self.fork(local_symbols);
                    let child_symbols = child.get_symbol_uses(&hidden_term);
                    let UseTracker {
                        mut match_states, ..
                    } = child;
                    self.live_symbols.extend(child_symbols.iter().cloned());
                    snowball.extend(child_symbols.into_iter());
                    non_matched.append(&mut match_states);
                    modified = true;
                }
                MatchState::NoPatternState(s) => {
                    let NoPatternState { hidden_symbols, .. } = s;
                    self.live_symbols.extend(hidden_symbols.iter().cloned());
                    snowball.extend(hidden_symbols.into_iter());
                    modified = true;
                }
            });

            self.match_states = non_matched;
        }

        if modified {
            snowball.extend(self.live_symbols.iter().cloned());
        }

        modified
    }

    fn delayed_aggregate(&mut self, snowball: &SymbolSet, delayed: &mut SymbolSet) -> bool {
        let mut modified = !self.live_symbols.is_disjoint(&snowball);

        if modified {
            delayed.extend(self.live_symbols.iter().cloned());
        }

        let mut cur_match_states = Vec::new();
        std::mem::swap(&mut self.match_states, &mut cur_match_states);

        let (matched, mut non_matched): (_, Vec<_>) = cur_match_states
            .into_iter()
            .partition(|s| s.check_match(snowball));

        modified = modified || matched.len() != 0;

        matched.into_iter().for_each(|m| match m {
            MatchState::PatternState(s) => {
                let PatternState {
                    local_symbols,
                    hidden_term,
                    ..
                } = s;
                let mut child = self.fork(local_symbols);
                let child_symbols = child.get_symbol_uses(&hidden_term);
                let UseTracker {
                    mut match_states, ..
                } = child;
                self.live_symbols.extend(child_symbols.iter().cloned());
                delayed.extend(child_symbols.into_iter());
                non_matched.append(&mut match_states);
            }
            MatchState::NoPatternState(s) => {
                let NoPatternState { hidden_symbols, .. } = s;
                self.live_symbols.extend(hidden_symbols.iter().cloned());
                delayed.extend(hidden_symbols.into_iter());
            }
        });

        self.match_states = non_matched;

        modified
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

pub fn remove_unused_symbols(mut commands: Vec<concrete::Command>) -> Vec<concrete::Command> {
    // println!("computing def symbols: ");
    let mut defs = HashSet::new();
    let cmd_defs: Vec<SymbolSet> = commands
        .iter()
        .map(|x| {
            let d = get_global_symbol_defs(x);
            defs.extend(d.iter().cloned());
            d
        })
        .collect();

    let defs = Arc::new(defs);

    // println!("computing use symbols: ");
    let uses: SymbolSet = commands
        .iter()
        .map(|c| UseTracker::new(defs.clone(), &c, true).live_symbols)
        .flatten()
        .collect();

    // println!("building remove set: ");
    let mut remove_indices = HashSet::new();

    cmd_defs.iter().enumerate().for_each(|(i, x)| {
        if x.len() != 0 && !uses.is_disjoint(x) {
            remove_indices.insert(i);
        }
    });

    // println!("removing use symbols: ");
    commands = commands
        .into_iter()
        .enumerate()
        .filter(|(pos, _)| !remove_indices.contains(pos))
        .map(|(_, x)| x)
        .collect();

    commands
}

pub fn tree_shake(
    mut commands: Vec<concrete::Command>,
    shake_max_depth: u32,
    shake_log_path: Option<String>,
) -> Vec<concrete::Command> {
    tree_rewrite::truncate_commands(&mut commands);
    let goal_command = commands.pop().unwrap();
    // let goal_command = commands[commands.len() - 1].clone();
    // print!("{} ", goal_command);

    let defs: SymbolSet = commands
        .iter()
        .map(|x| get_global_symbol_defs(x))
        .flatten()
        .collect();

    let defs = Arc::new(defs);
    let tracker = UseTracker::new(defs.clone(), &goal_command, true);
    let mut snowball = tracker.live_symbols;

    let mut trackers: Vec<UseTracker> = commands
        .iter()
        .map(|c| UseTracker::new(defs.clone(), &c, false))
        .collect();

    let mut poss = HashSet::new();
    let mut pposs = HashSet::new();
    poss.insert(0);

    let mut iteration = 1;
    let mut stamps = HashMap::new();

    while poss != pposs {
        let mut delayed = HashSet::new();
        pposs = poss.clone();
        for (pos, tracker) in trackers.iter_mut().enumerate() {
            if tracker.delayed_aggregate(&snowball, &mut delayed) {
                poss.insert(pos);
                if !stamps.contains_key(&pos) {
                    stamps.insert(pos, iteration);
                }
            } else {
                if let Command::Assert { term: _ } = &commands[pos] {
                } else {
                    poss.insert(pos);
                }
            }
        }

        snowball.extend(delayed.into_iter());
        iteration += 1;

        if iteration > shake_max_depth {
            break;
        }
    }

    if shake_log_path.is_none() {
        for (pos, stamp) in stamps.iter() {
            println!("{}|||{}", stamp, &commands[*pos]);
        }
        println!("0|||{}", &goal_command);
    } else {
        let mut log_file = std::fs::File::create(shake_log_path.unwrap()).unwrap();
        for (pos, stamp) in stamps.iter() {
            writeln!(log_file, "{}|||{}", stamp, &commands[*pos]).unwrap();
        }
        writeln!(log_file, "0|||{}", &goal_command).unwrap();
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

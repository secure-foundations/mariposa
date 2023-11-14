use core::panic;
use smt2parser::concrete;
use smt2parser::concrete::{AttributeValue, Command, Symbol, Term};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fs::read_to_string;
use std::io::Write;
use std::process::id;
use std::sync::Arc;

use crate::term_match::match_simple_qual_identifier;
use crate::{tree_rewrite, pretty_print};
use crate::tree_shake::get_global_symbol_defs;

struct IDFShaker {
    plain_idfs: HashMap<Symbol, u32>,
    processed_idfs: HashMap<Symbol, f64>,
    local_bindings: HashSet<Symbol>,
    local_processed: HashSet<Symbol>,
    symbol_command_count: u32,
}

impl IDFShaker {
    fn new() -> Self {
        Self {
            plain_idfs: HashMap::new(),
            processed_idfs: HashMap::new(),
            local_bindings: HashSet::new(),
            local_processed: HashSet::new(),
            symbol_command_count: 0,
        }
    }

    fn process_command(&mut self, command: &Command) {
        let defs = get_global_symbol_defs(command);
        defs.into_iter().for_each(|symbol| {
            assert_eq!(self.plain_idfs.insert(symbol, 0), None);
        });

        if let Command::Assert { term } = command {
            self.get_symbol_uses(term);
            self.symbol_command_count += 1;
        } else if let Command::DefineFun { sig, term } = command {
            for p in &sig.parameters {
                self.local_bindings.insert(p.0.clone());
            }
            self.add_symbol_use(&sig.name);
            self.get_symbol_uses(term);
            for p in &sig.parameters {
                self.local_bindings.remove(&p.0);
            }
            self.symbol_command_count += 1;
        }
        self.local_bindings.clear();
        self.local_processed.clear();
    }

    fn add_symbol_use(&mut self, symbol: &Symbol) {
        // if we have a local binding, we don't need to count it
        if self.local_bindings.contains(symbol) {
            return;
        }

        // for idf, we only need to process once per symbol per command
        if self.local_processed.contains(symbol) {
            return;
        }

        // only count if we have a definition
        if let Some(count) = self.plain_idfs.get_mut(symbol) {
            *count += 1;
            self.local_processed.insert(symbol.clone());
        }
    }

    fn get_symbol_uses(&mut self, term: &concrete::Term) {
        match term {
            Term::Constant(..) => (),
            Term::QualIdentifier(qual_identifier) => {
                let symbol = match_simple_qual_identifier(qual_identifier).unwrap();
                self.add_symbol_use(symbol);
            }
            Term::Application {
                qual_identifier,
                arguments,
            } => {
                if let Some(symbol) = match_simple_qual_identifier(qual_identifier) {
                    self.add_symbol_use(symbol);
                    arguments.iter().for_each(|x| self.get_symbol_uses(x))
                }
            }
            Term::Let { var_bindings, term } => {
                // remove local bindings
                var_bindings.iter().for_each(|x| {
                    self.local_bindings.insert(x.0.clone());
                    self.get_symbol_uses(&x.1);
                });
                self.get_symbol_uses(term);
                var_bindings.iter().for_each(|x| {
                    self.local_bindings.remove(&x.0);
                });
            }
            Term::Forall { vars, term } => {
                // no need for sort symbols right?
                vars.iter().for_each(|x| {
                    self.local_bindings.insert(x.0.clone());
                });
                self.get_symbol_uses(term);
                vars.iter().for_each(|x| {
                    self.local_bindings.remove(&x.0);
                });
            }
            Term::Exists { vars, term } => {
                vars.iter().for_each(|x| {
                    self.local_bindings.insert(x.0.clone());
                });
                self.get_symbol_uses(term);
                vars.iter().for_each(|x| {
                    self.local_bindings.remove(&x.0);
                });
            }
            Term::Match { term: _, cases: _ } => {
                panic!("TODO match cases")
            }
            Term::Attributes {
                term,
                attributes: _,
            } => {
                // ignore attributes for now?
                self.get_symbol_uses(term);
            }
        }
    }

    fn compute_idfs(&mut self) {
        // let log_n = (self.plain_idfs.len() as f64).log10();
        let n = self.symbol_command_count;
        self.plain_idfs.iter().for_each(|(symbol, count)| {
            if *count != 0 {
                let idf = (n as f64 / (n as f64 - *count as f64)).log10();
                // let idf = (*count as f64) / n as f64;
                self.processed_idfs.insert(symbol.clone(), idf);
            }
        });
    }

    fn dump_to_file(&self, symbol_score_path: String) {
        let mut file = std::fs::File::create(symbol_score_path).unwrap();
        let mut idfs: Vec<_> = self.plain_idfs.iter().collect();
        idfs.sort_by_key(|x| x.1);
        for (symbol, count) in idfs {
            let score = self.processed_idfs.get(symbol).unwrap_or(&f64::INFINITY);
            file.write_all(format!("{}:\t{}\t{}\n", symbol, count, score).as_bytes())
                .unwrap();
        }
    }
}

type SymbolSet = HashSet<Symbol>;

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
    fn check_match(&self, symbols: &SymbolSet) -> Option<SymbolSet> {
        match self {
            MatchState::PatternState(s) => {
                // let mut all_patterns = SymbolSet::new();
                // s.patterns.iter().for_each(|x| {
                //     all_patterns.extend(x.iter().cloned());
                // });

                // if all_patterns.is_subset(symbols) {
                //     return Some(all_patterns);
                // }
                for p in &s.patterns {
                    if p.is_subset(symbols) {
                        return Some(p.clone());
                    }
                }
            }
            MatchState::NoPatternState(s) => {
                if !s.filtered_symbols.is_disjoint(symbols) {
                    return Some(s.hidden_symbols.intersection(symbols).cloned().collect());
                }
            }
        }
        return None;
    }

    fn debug(&self) {
        match self {
            MatchState::PatternState(ps) => {
                println!("\tHidden term:\n\t{}", ps.hidden_term);
                for (i, s) in ps.patterns.iter().enumerate() {
                    print!("\t\tPatterns {}: (", i);
                    for s in s {
                        print!(" {} ", s);
                    }
                    println!(")");
                }
                print!("\tLocal symbols: (");
                for s in &ps.local_symbols {
                    print!(" {}", s);
                }
                println!(")");
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
    // local symbols (e.g. bound variables forall, exists, let)
    local_symbols: SymbolSet,
    match_states: Vec<MatchState>,
    live_symbols: SymbolSet,
    exhaustive: bool,
}

impl UseTracker {
    fn new(
        command: &concrete::Command,
        defs: &HashMap<Symbol, f64>,
        exhaustive: bool,
    ) -> UseTracker {
        let mut tracker = UseTracker {
            local_symbols: HashSet::new(),
            match_states: Vec::new(),
            live_symbols: HashSet::new(),
            exhaustive: exhaustive,
        };

        tracker.process_command(command, defs);
        tracker
    }

    // fork is used to create a new tracker for its sub terms
    fn fork(&self, locals: SymbolSet) -> UseTracker {
        UseTracker {
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

    fn get_symbol_uses(
        &mut self,
        term: &concrete::Term,
        defs: &HashMap<concrete::Symbol, f64>,
    ) -> SymbolSet {
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
                    .map(|x| self.get_symbol_uses(x, defs))
                    .for_each(|x| uses.extend(x));
            }
            Term::Let { var_bindings, term } => {
                // remove local bindings
                var_bindings.iter().for_each(|x| {
                    self.add_local_binding(&x.0);
                    uses.extend(self.get_symbol_uses(&x.1, defs).into_iter())
                });
                uses.extend(self.get_symbol_uses(term, defs).into_iter());
                var_bindings
                    .iter()
                    .for_each(|x| self.remove_local_binding(&x.0));
            }
            Term::Forall { vars, term } => {
                // no need for sort symbols right?
                vars.iter().for_each(|x| self.add_local_binding(&x.0));
                uses.extend(self.get_symbol_uses(term, defs).into_iter());
                vars.iter().for_each(|x| self.remove_local_binding(&x.0));
            }
            Term::Exists { vars, term } => {
                vars.iter().for_each(|x| self.add_local_binding(&x.0));
                uses.extend(self.get_symbol_uses(term, defs).into_iter());
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
                                    let mut pattern_set = HashSet::new();
                                    terms.iter().for_each(|x| {
                                        pattern_set.extend(self.get_symbol_uses(&x, defs));
                                    });
                                    pattern_sets.push(pattern_set);
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
                                        no_pattern.extend(self.get_symbol_uses(&x, defs));
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
                } else {
                    attributes.into_iter().for_each(|f| {
                        let concrete::Keyword(k) = &f.0;
                        if k == "pattern" || k == "no-pattern" {
                            match &f.1 {
                                AttributeValue::None => (),
                                AttributeValue::Constant(..) => (),
                                AttributeValue::Symbol(symbol) => {
                                    panic!("TODO symbol {:?}", symbol);
                                }
                                AttributeValue::Terms(terms) => {
                                    terms
                                        .iter()
                                        .for_each(|x| uses.extend(self.get_symbol_uses(&x, defs)));
                                }
                                AttributeValue::SExpr(ses) => {
                                    ses.iter().for_each(|se| uses.extend(get_sexpr_symbols(se)));
                                }
                            }
                        }
                    });
                }

                no_pattern.retain(|x| (!self.local_symbols.contains(x)) && defs.contains_key(x));

                if pattern_sets.len() != 0 {
                    let match_state = PatternState {
                        local_symbols: self.local_symbols.clone(),
                        hidden_term: term.clone().into(),
                        patterns: pattern_sets,
                    };
                    self.match_states
                        .push(MatchState::PatternState(match_state));
                } else if no_pattern.len() != 0 {
                    // drop no pattern if pattern is given
                    let live = self.get_symbol_uses(term, defs);
                    let filtered_symbols = live.difference(&no_pattern).cloned().collect();
                    // println!("no pattern: {:?}", &filtered_symbols);
                    let match_state = NoPatternState {
                        hidden_symbols: live,
                        filtered_symbols: filtered_symbols,
                    };
                    self.match_states
                        .push(MatchState::NoPatternState(match_state));
                } else {
                    uses.extend(self.get_symbol_uses(term, defs).into_iter());
                }
            }
        }
        // remove local bindings
        uses.retain(|x| (!self.local_symbols.contains(x)) && defs.contains_key(x));
        uses
    }

    fn process_command(&mut self, command: &concrete::Command, defs: &HashMap<Symbol, f64>) {
        match command {
            Command::Assert { term } => {
                let uses = self.get_symbol_uses(term, defs);
                self.live_symbols = uses;
            }
            Command::DefineFun { sig, term } => {
                for p in &sig.parameters {
                    self.add_local_binding(&p.0);
                }
                let uses = self.get_symbol_uses(term, defs);
                self.live_symbols = uses;
                self.live_symbols.insert(sig.name.clone());
            }
            _ => {}
        }
    }

    fn delayed_aggregate(
        &mut self,
        snowball: &SymbolSet,
        defs: &HashMap<Symbol, f64>,
        debug: bool,
    ) -> (bool, SymbolSet, f64) {
        let mut delayed = SymbolSet::new();
        let intersection = self.live_symbols.intersection(&snowball);
        let mut score = 0.0;

        let mut modified = !self.live_symbols.is_disjoint(&snowball);

        let mut count = 0;
        intersection.for_each(|x| {
            // use the matched symbol's score
            // println!("{} ", x);
            let x_score = defs.get(x).unwrap();
            // score = score.min(*x_score);
            score += *x_score;
            count += 1;
        });

        if modified {
            delayed.extend(self.live_symbols.iter().cloned());
        }

        let mut cur_match_states = Vec::new();
        std::mem::swap(&mut self.match_states, &mut cur_match_states);

        let (matched, mut non_matched): (_, Vec<_>) = cur_match_states.into_iter().partition(|s| {
            if let Some(symbols) = s.check_match(&snowball) {
                symbols.iter().for_each(|x| {
                    // use the matched symbol's score
                    let x_score = defs.get(x).unwrap();
                    // score = score.min(*x_score);
                    score += *x_score;
                    count += 1;
                });
                true
            } else {
                false
            }
        });



        modified = modified || matched.len() != 0;

        if debug {
            println!("{}", matched.len());
            println!("{}", modified);

            print!("Live symbols:\n\t(");
            for s in &self.live_symbols {
                println!("{}", s);
            }
            println!(")");
        }

        matched.into_iter().for_each(|m| match m {
            MatchState::PatternState(s) => {
                let PatternState {
                    local_symbols,
                    hidden_term,
                    ..
                } = s;
                let mut child = self.fork(local_symbols);
                let child_symbols = child.get_symbol_uses(&hidden_term, defs);
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

        if count > 1 {
            score /= count as f64;
        }

        (modified, delayed, score)
    }

    fn debug(&self) {
        print!("Live symbols:\n\t(");
        for s in &self.live_symbols {
            print!(" {} ", s);
        }
        println!(")");
        print!("Local symbols:\n\t(");
        for s in &self.local_symbols {
            print!(" {} ", s);
        }
        println!(")");
        println!("Match states:");
        for (i, s) in self.match_states.iter().enumerate() {
            println!("\tMatch state {}", i);
            s.debug();
        }
        println!()
    }
}

pub fn tree_shake_idf(
    mut commands: Vec<Command>,
    symbol_score_path: Option<String>,
    command_score_path: Option<String>,
) -> Vec<Command> {
    tree_rewrite::truncate_commands(&mut commands);

    let mut shaker = IDFShaker::new();
    commands.iter().for_each(|x| shaker.process_command(x));
    shaker.compute_idfs();

    if let Some(path) = symbol_score_path {
        shaker.dump_to_file(path);
    }

    let goal_command = commands.pop().unwrap();

    let mut defs = shaker.processed_idfs;
    let tracker = UseTracker::new(&goal_command, &defs, true);
    let mut snowball = tracker.live_symbols;

    let mut trackers: Vec<UseTracker> = commands
        .iter()
        .map(|c| UseTracker::new(&c, &defs, false))
        .collect();

    let mut poss = HashSet::new();
    let mut pposs = HashSet::new();
    poss.insert(0);

    let mut iteration = 1;
    let mut stamps: HashMap<usize, (u32, f64)> = HashMap::new();

    // for s in &snowball {
    //     println!("[isb]\t{}", s);
    // }

    while poss != pposs {
        let mut iteration_delayed = HashMap::new();
        pposs = poss.clone();
        for (pos, tracker) in trackers.iter_mut().enumerate() {
            let debug = false;
            let (modified, delayed, score) = tracker.delayed_aggregate(&snowball, &defs, debug);

            if modified {
                poss.insert(pos);
                delayed.into_iter().for_each(|x| {
                    iteration_delayed.insert(x, score);
                });
                if !stamps.contains_key(&pos) {
                    stamps.insert(pos, (iteration, score));
                }
            } else {
                if let Command::Assert { term: _ } = &commands[pos] {
                } else {
                    poss.insert(pos);
                }
            }
        }

        iteration_delayed.iter().for_each(|(symbol, score)| {
            if !snowball.contains(symbol) {
                // let new_score = defs.get(symbol).unwrap() + *score;
                // defs.insert(symbol.clone(), new_score);

                // if symbol == &Symbol("Tclass._System.___hFunc8_1".to_string()) {
                //     println!("new score {} {}?", iteration, new_score);
                // }

                snowball.insert(symbol.clone());
            }
        });

        iteration += 1;
    }

    if let Some(path) = command_score_path {
        let mut log_file = std::fs::File::create(path).unwrap();
        for (pos, (it, sc)) in stamps.iter() {
            writeln!(log_file, "{}|||{}|||{}", it, sc, &commands[*pos]).unwrap();
        }
        writeln!(log_file, "0|||0|||{}", &goal_command).unwrap();
    }

    // for s in &snowball {
    //     println!("[fsb]\t{}", s);
    // }

    // for (i, tr) in trackers.iter().enumerate() {
    //     if commands[i].to_string().contains("_module.__default.DoesTraceDemonstrateSHA256 ") {
    //         // println!("{} {}", i, commands[i]);
    //         pretty_print::print_command(&commands[i]);
    //         tr.debug();
    //     }
    // }

    commands = commands
        .into_iter()
        .enumerate()
        .filter(|(pos, _)| 
        {
            poss.contains(pos) 
        }
        )
        .map(|(_, x)| x)
        .collect();
    commands.push(goal_command);
    commands.push(Command::CheckSat);
    commands
}

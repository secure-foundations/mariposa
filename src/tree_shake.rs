use smt2parser::concrete;
use smt2parser::concrete::{AttributeValue, Command, Term};
use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::sync::Arc;

use crate::term_match::{get_identifier_symbols, get_sexpr_symbols, SymbolSet};
use crate::tree_rewrite;
use crate::tree_shake_idf::{get_command_symbol_def, get_commands_symbol_def, get_commands_symbol_def_alt, AltSymbolSet};

struct PatternState {
    local_symbols: SymbolSet,
    hidden_term: Arc<Term>,
    matchable_patterns: Vec<SymbolSet>,
}

fn print_symbol_set(prefix: &str, s: &SymbolSet) {
    print!("{} (", prefix);
    for s in s {
        print!(" {} ", s);
    }
    println!(")");
}

impl PatternState {
    fn check_match(&self, symbols: &AltSymbolSet) -> bool {
        // not using .any because we might want to debug ...
        for p in &self.matchable_patterns {
            if symbols.is_superset(p) {
                return true;
            }
        }
        return false;
    }

    fn debug(&self) {
        println!("[tr] Hidden Term:\t{}", self.hidden_term);
        let count = self.matchable_patterns.len();
        for (i, s) in self.matchable_patterns.iter().enumerate() {
            print_symbol_set(
                format!("[tr] Pattern Group {}/{}:", i + 1, count).as_str(),
                s,
            );
        }
        // print_symbol_set("\tLocal symbols:", &self.local_symbols);
    }
}

struct NoPatternState {
    hidden_symbols: SymbolSet,
    matchable_symbols: SymbolSet,
}

impl NoPatternState {
    fn check_match(&self, symbols: &AltSymbolSet) -> bool {
        // if there is any overlap with the matchable symbols
        symbols.has_overlap(&self.matchable_symbols)
        // !self.matchable_symbols.is_disjoint(symbols)
    }

    fn debug(&self) {
        print_symbol_set("[tr] Hidden Symbols:", &self.hidden_symbols);
        print_symbol_set("[tr] Matchable Symbols:", &self.hidden_symbols);
    }
}

struct UseTracker {
    defined_symbols: Arc<SymbolSet>,
    // local symbols (e.g. bound variables forall, exists, let)
    local_symbols: SymbolSet,
    pattern_states: Vec<PatternState>,
    no_pattern_states: Vec<NoPatternState>,
    live_symbols: SymbolSet,
    exhaustive: bool,
}

impl UseTracker {
    fn new(defs: Arc<SymbolSet>, command: &concrete::Command, exhaustive: bool) -> UseTracker {
        let mut tracker = UseTracker {
            defined_symbols: defs.clone(),
            local_symbols: HashSet::new(),
            pattern_states: Vec::new(),
            no_pattern_states: Vec::new(),
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
            pattern_states: Vec::new(),
            no_pattern_states: Vec::new(),
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
                    .iter()
                    .for_each(|x| uses.extend(self.get_symbol_uses(x)));
            }
            Term::Let { var_bindings, term } => {
                // remove local bindings
                var_bindings.iter().for_each(|x| {
                    self.add_local_binding(&x.0);
                    uses.extend(self.get_symbol_uses(&x.1))
                });
                uses.extend(self.get_symbol_uses(term));
                var_bindings
                    .iter()
                    .for_each(|x| self.remove_local_binding(&x.0));
            }
            Term::Forall { vars, term } | Term::Exists { vars, term } => {
                // no need for sort symbols right?
                vars.iter().for_each(|x| self.add_local_binding(&x.0));
                uses.extend(self.get_symbol_uses(term));
                vars.iter().for_each(|x| self.remove_local_binding(&x.0));
            }
            Term::Match { term: _, cases: _ } => {
                panic!("TODO match cases")
            }
            Term::Attributes { term, attributes } => {
                if self.exhaustive {
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
                                        .for_each(|x| uses.extend(self.get_symbol_uses(&x)));
                                }
                                AttributeValue::SExpr(ses) => {
                                    ses.iter().for_each(|se| uses.extend(get_sexpr_symbols(se)));
                                }
                            }
                        }
                    });
                    uses.extend(self.get_symbol_uses(term));
                } else {
                    uses = self.get_attr_term_symbol_uses(attributes, term);
                }
            }
        }
        // remove local bindings
        uses.retain(|x| (!self.local_symbols.contains(x)) && self.defined_symbols.contains(x));
        uses
    }

    fn get_attr_term_symbol_uses(
        &mut self,
        attributes: &Vec<(concrete::Keyword, AttributeValue)>,
        term: &Box<Term>,
    ) -> SymbolSet {
        let uses = HashSet::new();

        let patterns = self.get_pattern_uses(attributes);

        if patterns.len() != 0 {
            let match_state = PatternState {
                local_symbols: self.local_symbols.clone(),
                hidden_term: term.clone().into(),
                matchable_patterns: patterns,
            };
            self.pattern_states.push(match_state);
            // note that no-pattern is dropped if any pattern is given
            return uses;
        }

        let no_pattern = self.get_no_pattern_uses(attributes);

        if no_pattern.len() != 0 {
            // the live-set is under no-pattern
            let live_symbols = self.get_symbol_uses(term);
            // remove the no-pattern symbols from the live-set
            let matchable_symbols = live_symbols.difference(&no_pattern).cloned().collect();

            let match_state = NoPatternState {
                hidden_symbols: live_symbols,
                matchable_symbols,
            };

            self.no_pattern_states.push(match_state);
            return uses;
        }

        return self.get_symbol_uses(term);
    }

    fn get_pattern_uses(
        &mut self,
        attributes: &Vec<(concrete::Keyword, AttributeValue)>,
    ) -> Vec<SymbolSet> {
        let mut patterns = Vec::new();

        attributes.into_iter().for_each(|f| {
            let concrete::Keyword(k) = &f.0;
            if k == "pattern" {
                match &f.1 {
                    AttributeValue::None => (),
                    AttributeValue::Constant(..) => (),
                    AttributeValue::Terms(terms) => {
                        // if there are multiple terms in the pattern
                        // it is multi-pattern (not multiple patterns)
                        // current strategy is to treat each term individually
                        // e.g. :pattern ((f x) (g x)) is treat as two patterns
                        terms
                            .iter()
                            .for_each(|x| patterns.push(self.get_symbol_uses(&x)));
                    }
                    _ => panic!("TODO attribute value {:?}", &f.1),
                }
            }
        });

        return patterns;
    }

    fn get_no_pattern_uses(
        &mut self,
        attributes: &Vec<(concrete::Keyword, AttributeValue)>,
    ) -> SymbolSet {
        let mut no_pattern = HashSet::new();

        // all the no pattern symbols are combined
        attributes.into_iter().for_each(|f| {
            let concrete::Keyword(k) = &f.0;

            if k == "no-pattern" {
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
            }
        });

        no_pattern
            .retain(|x| (!self.local_symbols.contains(x)) && self.defined_symbols.contains(x));

        return no_pattern;
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
                // do not remove local bindings
                // for p in &sig.parameters {
                //     self.remove_local_binding(&p.0);
                // }
                self.live_symbols = uses;
                self.live_symbols.insert(sig.name.clone());
            }
            _ => {}
        }
    }

    fn delayed_aggregate(&mut self, snowball: &AltSymbolSet) -> bool {
        let mut should_include = false;

        let mut cur_pattern_states = Vec::new();
        std::mem::swap(&mut self.pattern_states, &mut cur_pattern_states);

        let (matched, mut non_matched): (_, Vec<_>) = cur_pattern_states
            .into_iter()
            .partition(|s| s.check_match(snowball));

        if matched.len() != 0 {
            should_include = true;
        }

        matched.into_iter().for_each(|m| {
            let mut child = self.fork(m.local_symbols);
            let child_symbols = child.get_symbol_uses(&m.hidden_term);
            let UseTracker {
                mut pattern_states,
                no_pattern_states,
                ..
            } = child;

            // no-pattern hiding under pattern?
            // assert_eq!(no_pattern_states.len(), 0);

            self.live_symbols.extend(child_symbols.iter().cloned());
            // delayed.extend(child_symbols.into_iter());
            non_matched.append(&mut pattern_states);
            self.no_pattern_states.extend(no_pattern_states);
        });

        self.pattern_states = non_matched;

        let mut cur_no_pattern_states = Vec::new();
        std::mem::swap(&mut self.no_pattern_states, &mut cur_no_pattern_states);

        let (matched, non_matched): (_, Vec<_>) = cur_no_pattern_states
            .into_iter()
            .partition(|s| s.check_match(snowball));

        if matched.len() != 0 {
            should_include = true;
        }

        matched.into_iter().for_each(|m| {
            self.live_symbols.extend(m.hidden_symbols.iter().cloned());
            // delayed.extend(m.hidden_symbols);
        });

        self.no_pattern_states = non_matched;

        if snowball.has_overlap(&self.live_symbols) {
            should_include = true;
        }

        return should_include;
    }

    fn debug(&self) {
        print_symbol_set("[tr] Live Symbols:\t", &self.live_symbols);
        print_symbol_set("[tr] Local Symbols:\t", &self.local_symbols);
        let count = self.pattern_states.len();
        for (i, s) in self.pattern_states.iter().enumerate() {
            println!("[tr] Pattern State {}/{}", i + 1, count);
            s.debug();
        }
        let count = self.no_pattern_states.len();
        for (i, s) in self.no_pattern_states.iter().enumerate() {
            println!("[tr] No-pattern State {}/{}", i + 1, count);
            s.debug();
        }
    }
}

pub fn tree_shake(
    mut commands: Vec<concrete::Command>,
    shake_max_depth: u32,
    shake_max_symbol_frequency: usize,
    shake_init_strategy: u32,
    shake_log_path: Option<String>,
    debug: bool,
) -> Vec<concrete::Command> {
    tree_rewrite::truncate_commands(&mut commands);
    let (ref_trivial, ref_defined) = get_commands_symbol_def_alt(&commands, shake_max_symbol_frequency);
    let ref_trivial = Arc::new(ref_trivial);
    let defs = Arc::new(ref_defined);

    // let defs = Arc::new(get_commands_symbol_def(
    //     &commands,
    //     alt_defs.defined,
    // ));

    let goal_command = commands.pop().unwrap();

    let live = if shake_init_strategy == 0 {
        // lazy evaluation match states on goal
        let tracker = UseTracker::new(defs.clone(), &goal_command, false);
        // put the goal back immediately
        commands.push(goal_command.clone());
        tracker.live_symbols
    } else {
        assert_eq!(shake_init_strategy, 1);
        // eager evaluation match states on goal
        let tracker = UseTracker::new(defs.clone(), &goal_command, true);
        tracker.live_symbols
    };

    let mut snowball = AltSymbolSet::new(live, ref_trivial, defs.clone());

    if debug {
        snowball.debug();
    }

    let mut trackers: Vec<UseTracker> = commands
        .iter()
        .map(|c| UseTracker::new(defs.clone(), &c, false))
        .collect();

    let mut poss = HashSet::new();
    // let mut pposs = HashSet::new();
    poss.insert(0);

    let mut iteration = 1;
    let mut stamps = HashMap::new();
    let mut modified = true;

    while modified {
        let mut delayed = HashSet::new();
        modified = false;
        let prev_len = snowball.defined.len();
        let prev_poss_len = poss.len();

        for (pos, tracker) in trackers.iter_mut().enumerate() {
            let should_include = tracker.delayed_aggregate(&snowball);
            // if commands[pos].to_string().contains("binder_x_39cef6c8a4c32c00bec831967af0f4b9_3") {
            //     println!("debugging");
            //     let contains = snowball.contains(&concrete::Symbol("HasType".to_string()));
            //     println!("{}", contains);
            //     tracker.debug();
            //     println!("should add?? {}", should_add);
            // }
            if should_include {
                delayed.extend(tracker.live_symbols.iter().cloned());
                poss.insert(pos);
                if !stamps.contains_key(&pos) {
                    stamps.insert(pos, iteration);
                }
                // println!("{} modified {}", iteration, &commands[pos]);
            } else {
                if let Command::Assert { term: _ } = &commands[pos] {
                } else {
                    poss.insert(pos);
                }
            }
        }

        snowball.extend(delayed);

        if snowball.defined.len() != prev_len || poss.len() != prev_poss_len {
            modified = true;
        }

        iteration += 1;

        if iteration > shake_max_depth {
            break;
        }
    }

    if let Some(shake_log_path) = shake_log_path {
        let mut log_file = std::fs::File::create(shake_log_path).unwrap();
        for (pos, stamp) in stamps.iter() {
            writeln!(log_file, "{}|||{}", stamp, &commands[*pos]).unwrap();
        }
        writeln!(log_file, "0|||{}", &goal_command).unwrap();
    }

    if debug {
        let count = trackers.len();
        for (i, tracker) in trackers.iter().enumerate() {
            if let Command::Assert { .. } = &commands[i] {
                println!("[tr] Command {}/{}: {}", i, count, commands[i]);
                tracker.debug();
            } else if let Command::DefineFun { .. } = &commands[i] {
                println!("[tr] Command {}/{}: {}", i, count, commands[i]);
                tracker.debug();
            }
        }

        snowball.debug();
    }

    commands = commands
        .into_iter()
        .enumerate()
        .filter(|(pos, _)| poss.contains(pos))
        .map(|(_, x)| x)
        .collect();

    if shake_init_strategy == 1 {
        // reintroduce the goal
        commands.push(goal_command.clone());
    }

    commands.push(Command::CheckSat);
    commands
}

pub fn remove_unused_symbols(mut commands: Vec<concrete::Command>) -> Vec<concrete::Command> {
    // println!("computing def symbols: ");
    let defs = Arc::new(get_commands_symbol_def(&commands, 100));

    // println!("computing use symbols: ");
    let uses: SymbolSet = commands
        .iter()
        .map(|c| UseTracker::new(defs.clone(), &c, true).live_symbols)
        .flatten()
        .collect();

    // remove all commands that define a symbol that is not used

    commands = commands
        .into_iter()
        .filter(|c| uses.is_disjoint(&get_command_symbol_def(c)))
        .collect();

    commands
}

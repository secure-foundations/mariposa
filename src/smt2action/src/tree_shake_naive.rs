use smt2parser::concrete;
use smt2parser::concrete::{AttributeValue, Command, Term};
use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::sync::Arc;
use std::time::Instant;

use crate::query_io;
use crate::term_match::{get_identifier_symbols, get_sexpr_symbols, SymbolSet};
use crate::tree_shake_idf::{
    get_command_symbol_def, get_all_symbol_defs, get_commands_symbol_def_alt, AltSymbolSet
};

struct UseTracker {
    defined_symbols: Arc<SymbolSet>,
    // local symbols (e.g. bound variables forall, exists, let)
    local_symbols: SymbolSet,
    live_symbols: SymbolSet,
    exhaustive: bool,
}

impl UseTracker {
    fn new(defs: Arc<SymbolSet>, command: &concrete::Command, exhaustive: bool) -> UseTracker {
        let mut tracker = UseTracker {
            defined_symbols: defs.clone(),
            local_symbols: HashSet::new(),
            live_symbols: HashSet::new(),
            exhaustive: exhaustive,
        };

        tracker.process_command(command);
        tracker
    }

    // // fork is used to create a new tracker for its sub terms
    // fn fork(&self, locals: SymbolSet) -> UseTracker {
    //     UseTracker {
    //         defined_symbols: self.defined_symbols.clone(),
    //         local_symbols: locals,
    //         pattern_states: Vec::new(),
    //         no_pattern_states: Vec::new(),
    //         live_symbols: HashSet::new(),
    //         exhaustive: false,
    //     }
    // }

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
        // let uses = HashSet::new();

        // let patterns = self.get_pattern_uses(attributes);

        // if patterns.len() != 0 {
        //     let match_state = PatternState {
        //         local_symbols: self.local_symbols.clone(),
        //         hidden_term: term.clone().into(),
        //         matchable_patterns: patterns,
        //     };
        //     self.pattern_states.push(match_state);
        //     // note that no-pattern is dropped if any pattern is given
        //     return uses;
        // }

        // let no_pattern = self.get_no_pattern_uses(attributes);

        // if no_pattern.len() != 0 {
        //     // the live-set is under no-pattern
        //     let live_symbols = self.get_symbol_uses(term);
        //     // remove the no-pattern symbols from the live-set
        //     let matchable_symbols = live_symbols.difference(&no_pattern).cloned().collect();

        //     return uses;
        // }

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
                let local = self.local_symbols.clone();
                let name = sig.name.clone();
                // self.pattern_states.push(rl_ps);
                // if self.exhaustive {
                let mut uses = self.get_symbol_uses(term);
                uses.insert(name);
                self.live_symbols = uses;
            }
            _ => {}
        }
    }

    fn delayed_aggregate(&mut self, snowball: &AltSymbolSet) -> bool {
        return snowball.has_overlap(&self.live_symbols);
    }
}

pub fn tree_shake_naive(
    mut commands: Vec<concrete::Command>,
    shake_max_depth: u32,
    shake_max_symbol_frequency: usize,
    shake_init_strategy: u32,
    shake_log_path: Option<String>,
    debug: bool,
) -> Vec<concrete::Command> {
    let now = Instant::now();
    query_io::truncate_commands(&mut commands);
    let (ref_trivial, ref_defined) =
        get_commands_symbol_def_alt(&commands, shake_max_symbol_frequency);
    // println!("trivial {:?}", ref_trivial);
    let ref_trivial = Arc::new(ref_trivial);
    let defs = Arc::new(ref_defined);
    let cmds_info = query_io::load_mariposa_ids(&commands);
    let goal_index = commands.len() - 1;
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
            // if commands[pos].to_string().contains("Tm_refine_414d0a9f578ab0048252f8c8f552b99f") {
            //     println!("debugging");
            //     // let contains = snowball.contains(&concrete::Symbol("HasType".to_string()));
            //     snowball.debug();
            //     // println!("{}", contains);
            //     tracker.debug();
            //     println!("should add?? {} {}", should_include, pos);
            // }
            if should_include {
                // FIXME: the live symbols are already changed here
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
        let shake_log_path = std::path::Path::new(&shake_log_path);
        let prefix = shake_log_path.parent().unwrap();
        std::fs::create_dir_all(prefix).unwrap();
        let mut log_file = std::fs::File::create(shake_log_path).unwrap();
        for (pos, stamp) in stamps.iter() {
            if !cmds_info.contains_key(pos) {
                if let Command::Assert { .. } = &commands[*pos] {
                    panic!("{} not found", pos);
                }
            } else {
                writeln!(log_file, "{}:{}", stamp, cmds_info[pos].cid).unwrap();
            }
        }
        for pos in cmds_info.keys() {
            if !stamps.contains_key(pos) {
                writeln!(log_file, "{}:{}", usize::MAX, cmds_info[pos].cid).unwrap();
            }
        }
        writeln!(log_file, "0:{}", cmds_info[&goal_index].cid).unwrap();
    }

    // if debug {
    //     let count = trackers.len();
    //     for (i, tracker) in trackers.iter().enumerate() {
    //         if let Command::Assert { .. } = &commands[i] {
    //             println!("[tr] Command {}/{}: {}", i, count, commands[i]);
    //             tracker.debug();
    //         } else if let Command::DefineFun { .. } = &commands[i] {
    //             println!("[tr] Command {}/{}: {}", i, count, commands[i]);
    //             tracker.debug();
    //         }
    //     }

    //     snowball.debug();
    // }

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
    println!("shake time: {}", now.elapsed().as_millis());
    commands
}

pub fn remove_unused_symbols(commands: &mut Vec<concrete::Command>) {
    // println!("computing def symbols: ");
    let defs = Arc::new(get_all_symbol_defs(&commands));

    let uses: SymbolSet = commands
        .iter()
        .map(|c| 
            {
                let ut = UseTracker::new(defs.clone(), &c, true);
                // println!("{}", c);
                // for u in &ut.live_symbols {
                //     println!("{}", u);
                // }
                // println!();
                ut.live_symbols
            })
        .flatten()
        .collect();

    // remove all commands that define a symbol that is not used
    commands.retain(|c| {
        let defs = get_command_symbol_def(c);
        (defs.is_empty() || !defs.is_disjoint(&uses)) && c.to_string() != "(assert true)"
    })
}

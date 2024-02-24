use std::sync::Arc;

use rand::Rng;
use rand_chacha::ChaCha8Rng;
use rand::SeedableRng;
use smt2parser::concrete;

use crate::{term_match::SymbolSet, tree_shake_idf::get_commands_symbol_def};

struct PatternRemover {
    defs: Arc<SymbolSet>,
    rng: ChaCha8Rng,
    pattern_threshold: u32,
    removed_patterns: u64,
    total_patterns: u64,
}

impl PatternRemover {
    fn new(defs: Arc<SymbolSet>, seed: u64, th: f32) -> Self {
        let th = th * 100.0;
        Self {
            defs,
            rng: ChaCha8Rng::seed_from_u64(seed),
            pattern_threshold: th as u32,
            removed_patterns: 0,
            total_patterns: 0,
        }
    }

    fn remove_pattern_rec_helper(&mut self, cur_term: &mut concrete::Term) {
        match cur_term {
            concrete::Term::Application {
                qual_identifier: _,
                arguments,
            } => {
                for argument in arguments.iter_mut() {
                    self.remove_pattern_rec_helper(argument)
                }
            }
            concrete::Term::Let { var_bindings, term } => {
                for var_binding in var_bindings.iter_mut() {
                    self.remove_pattern_rec_helper(&mut var_binding.1)
                }
                self.remove_pattern_rec_helper(&mut *term)
            }
            concrete::Term::Forall { vars: _, term } => self.remove_pattern_rec_helper(&mut *term),
            concrete::Term::Exists { vars: _, term } => self.remove_pattern_rec_helper(&mut *term),
            concrete::Term::Match { term, cases: _ } => self.remove_pattern_rec_helper(&mut *term),
            concrete::Term::Attributes { term, attributes } => {
                self.remove_pattern_rec_helper(term);
                let mut removed = false;

                attributes.retain(|x| {
                    if x.0 == concrete::Keyword("pattern".to_owned()) {
                        self.total_patterns += 1;
                        let random = self.rng.gen_range(1..10001);
                        if random <= self.pattern_threshold {
                            removed = true;
                            self.removed_patterns += 1;
                            false
                        } else {
                            true
                        }
                    } else {
                        true
                    }
                });
                removed = true;

                if removed && attributes.len() == 0 {
                    attributes.push((
                        concrete::Keyword("qid".to_owned()),
                        concrete::AttributeValue::Symbol(concrete::Symbol(
                            "mariposa-attribute-placeholder".to_owned(),
                        )),
                    ));
                }
            }
            concrete::Term::Constant(_) => (),
            concrete::Term::QualIdentifier(_) => (),
        }
    }

    // patterns
    fn remove_patterns(&mut self, commands: &mut Vec<concrete::Command>) {
        commands.iter_mut().for_each(|x| {
            if let concrete::Command::Assert { term } = x {
                self.remove_pattern_rec_helper(term);
            }
        });
        println!(
            "[INFO] removed {} patterns out of {}",
            self.removed_patterns, self.total_patterns
        );
    }
}

pub fn remove_patterns(commands: &mut Vec<concrete::Command>, seed: u64, pattern_threshold: f32) {
    let defs = Arc::new(get_commands_symbol_def(commands, 100));
    let mut remover = PatternRemover::new(defs, seed, pattern_threshold);
    remover.remove_patterns(commands);
}
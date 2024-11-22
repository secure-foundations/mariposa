use smt2parser::concrete::{self, Symbol};
use smt2parser::concrete::{AttributeValue, Command, Term};
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::sync::Arc;

use crate::term_match::{
    format_symbol_set, get_attr_cid, get_attr_qid, get_identifier_symbols, SymbolSet,
};
use crate::tree_shake_idf::get_commands_symbol_def_alt;

struct FormulaState {
    cid: String,

    qid: Option<String>,

    is_quantifier: bool,

    live_symbols: SymbolSet,

    patterns: Vec<SymbolSet>,
}

impl FormulaState {
    fn new(cid: String, is_quantifier: bool, live_symbols: SymbolSet) -> Self {
        FormulaState {
            cid,
            qid: None,
            is_quantifier,
            // live_symbols: live_symbols.clone(),
            patterns: Vec::new(),
            live_symbols,
        }
    }

    fn get_id(&self) -> &str {
        if self.is_quantifier {
            self.qid.as_ref().unwrap()
        } else {
            &self.cid
        }
    }

    fn debug(&self) {
        println!("cid: {}", self.cid);

        if !self.is_quantifier {
            assert!(self.patterns.is_empty());
        } else {
            println!("qid: {}", self.qid.as_ref().unwrap());
        }

        println!("live_symbols: {}", format_symbol_set(&self.live_symbols));

        if !self.is_quantifier {
            return;
        }

        let num_patterns = self.patterns.len();
        for (i, p) in self.patterns.iter().enumerate() {
            println!(
                "pattern {}/{}: {}",
                i + 1,
                num_patterns,
                format_symbol_set(p)
            );
        }
    }

    fn awakens(&self, other: &FormulaState) -> bool {
        for p in other.patterns.iter() {
            if p.is_subset(&self.live_symbols) {
                return true;
            }
        }
        return false;
    }
}

struct FormalExpander {
    cid: String,

    defined_symbols: Arc<SymbolSet>,
    // local symbols (e.g. bound variables forall, exists, let)
    local_symbols: SymbolSet,

    formals: Vec<FormulaState>,

    live_stack: Vec<SymbolSet>,

    // union of symbols in the current live stack
    live_symbols: SymbolSet,
}

impl FormalExpander {
    fn new(cid: String, defined_symbols: Arc<SymbolSet>) -> Self {
        let live = SymbolSet::new();
        FormalExpander {
            cid,
            defined_symbols,
            local_symbols: SymbolSet::new(),
            formals: Vec::new(),
            live_symbols: SymbolSet::new(),
            live_stack: vec![live],
        }
    }

    fn get_symbol(&self, qual_identifier: &concrete::QualIdentifier) -> Option<Symbol> {
        if let concrete::QualIdentifier::Simple { identifier } = qual_identifier {
            let identifier = get_identifier_symbols(identifier);
            if self.defined_symbols.contains(&identifier)
                && !self.local_symbols.contains(&identifier)
            {
                return Some(identifier);
            }
            return None;
        } else {
            panic!("TODO sorted QualIdentifier")
        }
    }

    fn add_live_symbol(&mut self, qual_identifier: &concrete::QualIdentifier) {
        if let Some(symbol) = self.get_symbol(qual_identifier) {
            self.live_symbols.insert(symbol.clone());
            let last = self.live_stack.len() - 1;
            // println!("{}->{}", symbol, last);
            self.live_stack[last].insert(symbol);
        }
    }

    fn peek_live(&self) -> &SymbolSet {
        let last = self.live_stack.len() - 1;
        &self.live_stack[last]
    }

    fn push_live_scop(&mut self) {
        self.live_stack.push(SymbolSet::new());
    }

    fn pop_live_scope(&mut self) -> SymbolSet {
        let scoped = self.live_stack.pop().unwrap();
        scoped.iter().for_each(|x| {
            self.live_symbols.remove(x);
        });
        scoped
    }

    fn add_local_binding(&mut self, symbol: &concrete::Symbol) {
        self.local_symbols.insert(symbol.clone());
    }

    fn remove_local_binding(&mut self, symbol: &concrete::Symbol) {
        self.local_symbols.remove(symbol);
    }

    fn _expand_to_formula_states(&mut self, term: &concrete::Term) {
        match term {
            Term::Constant(c) => {
                let s = Symbol(format!("const_{}", c));
                let last = self.live_stack.len() - 1;
                self.live_stack[last].insert(s);
            }
            Term::QualIdentifier(qual_identifier) => {
                self.add_live_symbol(qual_identifier);
            }
            Term::Application {
                qual_identifier,
                arguments,
            } => {
                self.add_live_symbol(qual_identifier);
                arguments
                    .iter()
                    .for_each(|x| self._expand_to_formula_states(x));
            }
            Term::Let {
                var_bindings: vars,
                term,
            } => {
                vars.iter().for_each(|x| {
                    self.add_local_binding(&x.0);
                    self._expand_to_formula_states(&x.1)
                });
                self._expand_to_formula_states(term);
                vars.iter().for_each(|x| self.remove_local_binding(&x.0));
            }
            Term::Forall { vars, term } | Term::Exists { vars, term } => {
                vars.iter().for_each(|x| self.add_local_binding(&x.0));
                if let Term::Attributes { term, attributes } = &**term {
                    let qid = get_attr_qid(&attributes).unwrap();
                    let mut qs =
                        FormulaState::new(self.cid.clone(), true, self.peek_live().clone());
                    qs.qid = Some(qid.clone());
                    qs.patterns = self.init_patterns(&attributes);
                    self.push_live_scop();
                    self._expand_to_formula_states(term);
                    qs.live_symbols.extend(self.pop_live_scope().into_iter());
                    self.formals.push(qs);
                } else {
                    panic!("expected attributes in quant body");
                }
                vars.iter().for_each(|x| self.remove_local_binding(&x.0));
            }
            _ => {
                panic!("unexpected term in expand_to_quantifiers");
            }
        }
    }

    fn init_patterns(
        &mut self,
        attributes: &Vec<(concrete::Keyword, concrete::AttributeValue)>,
    ) -> Vec<SymbolSet> {
        let mut patterns = Vec::new();
        attributes.iter().for_each(|f| {
            let concrete::Keyword(k) = &f.0;
            if k == "pattern" {
                match &f.1 {
                    AttributeValue::Terms(terms) => {
                        let mut pattern = SymbolSet::new();
                        terms
                            .iter()
                            .for_each(|x| self._init_pattern(x, &mut pattern));
                        patterns.push(pattern);
                    }
                    _ => {
                        panic!("unexpected pattern attribute {:?}", f.1);
                    }
                }
            }
        });
        return patterns;
    }

    fn _init_pattern(&mut self, term: &concrete::Term, pattern: &mut SymbolSet) {
        match term {
            Term::Constant(c) => {
                pattern.insert(Symbol(format!("const_{}", c)));
            }
            Term::QualIdentifier(qual_identifier) => {
                if let Some(symbol) = self.get_symbol(qual_identifier) {
                    pattern.insert(symbol);
                }
            }
            Term::Application {
                qual_identifier,
                arguments,
            } => {
                // self.add_interesting_symbol(qual_identifier, acc);
                if let Some(symbol) = self.get_symbol(qual_identifier) {
                    pattern.insert(symbol);
                }
                arguments
                    .iter()
                    .for_each(|x| self._init_pattern(x, pattern));
            }
            _ => {
                panic!("unexpected term in pattern");
            }
        }
    }

    fn expand_to_formulas(mut self, term: &concrete::Term) -> Vec<FormulaState> {
        self._expand_to_formula_states(term);
        if self.formals.is_empty() && !self.live_symbols.is_empty() {
            let qf = FormulaState::new(self.cid.clone(), false, self.live_symbols.clone());
            self.formals.push(qf);
        }
        self.formals
    }
}

struct GraphBuilder {
    defined_symbols: Arc<SymbolSet>,
    formulas: HashMap<String, FormulaState>,
    qf_scores: HashMap<String, usize>,
    qt_scores: HashMap<String, usize>,
}

impl GraphBuilder {
    fn new(commands: &Vec<concrete::Command>) -> Self {
        // query_io::truncate_commands(&mut commands);
        let (_, mut defined_symbols) = get_commands_symbol_def_alt(&commands, 100);
        defined_symbols.remove(&concrete::Symbol("fuel_bool".to_string()));
        defined_symbols.remove(&concrete::Symbol("fuel_bool_default".to_string()));
        let defined_symbols: Arc<HashSet<concrete::Symbol>> = Arc::new(defined_symbols);

        let mut gb = GraphBuilder {
            defined_symbols,
            formulas: HashMap::new(),
            qf_scores: HashMap::new(),
            qt_scores: HashMap::new(),
        };

        for command in commands.iter() {
            gb.init_formal_states(command);
        }
        gb
    }

    fn init_formal_states(&mut self, command: &concrete::Command) {
        match command {
            Command::Assert { term } => {
                if let Term::Attributes { term, attributes } = term {
                    let cid = get_attr_cid(&attributes).unwrap();

                    let fs = FormalExpander::new(cid.clone(), self.defined_symbols.clone())
                        .expand_to_formulas(term);

                    fs.into_iter().for_each(|f| {
                        self.formulas.insert(f.get_id().to_string(), f);
                    });
                } else {
                    panic!("expected command attributes");
                }
            }
            Command::DefineFun { sig, .. } => {
                panic!("TODO define fun {:?}", sig);
            }
            _ => (),
        }
    }

    fn get_state(&self, id: &str) -> Option<&FormulaState> {
        self.formulas.get(id)
    }

    fn compute_scores(&mut self) {
        for (id1, f1) in self.formulas.iter() {
            for (id2, f2) in self.formulas.iter() {
                if f1.cid == f2.cid {
                    // skip formulas from the same root
                    continue;
                }

                if f1.awakens(f2) {
                    println!("{}->{}", id1, id2);
                }
            }
            // self.qf_scores.insert(k.clone(), qf_score);
            // self.qt_scores.insert(k.clone(), qt_score);
        }

        // let mut scores: Vec<(&String, &usize)> = self.qt_scores.iter().collect();
        // scores.sort_by(|a, b| b.1.cmp(a.1));

        // for (k, v) in scores {
        //     println!("{}:{},{}", k, v, self.qf_scores.get(k).unwrap());
        // }
    }
}

// impl Debug for GraphBuilder {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         writeln!(f, "GraphBuilder")?;
//         writeln!(f, "formals {:?}", self.formals.len())?;
//         Ok(())
//     }
// }

pub fn tree_shake_graph(mut commands: Vec<concrete::Command>) {
    // print!("defs {:?}", defs);
    let mut gb = GraphBuilder::new(&commands);
    gb.compute_scores();

    // println!("{:?}", gb);

    // for (k, v) in gb.formals.iter() {
    //     v.debug();
    // }

    // gb.get_state("internal_lib!page_organization.valid_ll.?_definition")
    //     .unwrap()
    //     .debug();

    // gb.get_state("user_lib__page_organization__valid_ll_150")
    //     .unwrap()
    //     .debug();

    gb.get_state("internal_tuple__2./tuple__2_constructor_definition")
        .unwrap()
        .debug();

    // fs.debug();
}

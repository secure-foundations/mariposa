use smt2parser::concrete::{self, Symbol};
use smt2parser::concrete::{AttributeValue, Command, Term};
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::sync::Arc;

use crate::term_match::{
    get_attr_cid, get_attr_qid, get_identifier_symbols, pprint_symbol_set, SymbolSet,
};
use crate::tree_shake_idf::get_commands_symbol_def_alt;

struct NonQuantState {
    id: String,
    live_symbols: SymbolSet,
}

impl NonQuantState {
    fn is_relevant(&self, other: &FormalState) -> bool {
        match other {
            FormalState::Quant(qs) => {
                for p in &qs.patterns {
                    if p.is_subset(&self.live_symbols) {
                        return true;
                    }
                }
                return false;
            }
            FormalState::NonQuant(qs) => {
                if self.live_symbols.is_disjoint(&qs.live_symbols) {
                    return false;
                }
                return true;
            }
        }
    }
}

struct QuantiState {
    id: String,

    defined_symbols: Arc<SymbolSet>,

    local_symbols: SymbolSet,

    live_symbols: SymbolSet,

    // quant_body: concrete::Term,
    patterns: Vec<SymbolSet>,

    hidden_context: SymbolSet,
}

impl QuantiState {
    fn new(
        defined_symbols: Arc<SymbolSet>,
        local_symbols: SymbolSet,
        live_symbols: SymbolSet,
        quant_body: concrete::Term,
    ) -> Self {
        if let Term::Attributes { term, attributes } = quant_body {
            let qid = get_attr_qid(&attributes).unwrap();

            let mut qis = QuantiState {
                id: qid.clone(),
                defined_symbols: defined_symbols.clone(),
                local_symbols: local_symbols.clone(),
                live_symbols,
                patterns: Vec::new(),
                hidden_context: SymbolSet::new(),
            };

            attributes.iter().for_each(|f| {
                let concrete::Keyword(k) = &f.0;
                if k == "pattern" {
                    match &f.1 {
                        AttributeValue::None => (),
                        AttributeValue::Constant(..) => (),
                        AttributeValue::Symbol(symbol) => {
                            panic!("TODO symbol {:?}", symbol);
                        }
                        AttributeValue::Terms(terms) => {
                            let mut acc = SymbolSet::new();
                            terms.iter().for_each(|x| qis.init_pattern(x, &mut acc));
                            qis.patterns.push(acc);
                        }
                        AttributeValue::SExpr(ses) => {
                            panic!("TODO SExpr {:?}", ses);
                        }
                    }
                }
            });

            // let exp = TermExpander {
            //     defined_symbols: defined_symbols.clone(),
            //     local_symbols: local_symbols.clone(),
            //     formals: Vec::new(),
            //     live_symbols: SymbolSet::new(),
            // };

            // let hidden = exp.expand_to_symbols(&term);
            // qis.hidden_context = hidden;
            qis
        } else {
            panic!("expected attributes in quant body");
        }
    }

    fn init_pattern(&mut self, term: &concrete::Term, acc: &mut SymbolSet) {
        match term {
            Term::Constant(..) => (),
            Term::QualIdentifier(qual_identifier) => {
                self.add_interesting_symbol(qual_identifier, acc);
            }
            Term::Application {
                qual_identifier,
                arguments,
            } => {
                self.add_interesting_symbol(qual_identifier, acc);
                arguments.iter().for_each(|x| self.init_pattern(x, acc));
            }
            _ => {
                panic!("unexpected term in pattern");
            }
        }
    }

    fn add_interesting_symbol(
        &mut self,
        qual_identifier: &concrete::QualIdentifier,
        acc: &mut SymbolSet,
    ) {
        if let concrete::QualIdentifier::Simple { identifier } = qual_identifier {
            let identifier = get_identifier_symbols(identifier);
            if self.defined_symbols.contains(&identifier)
                && !self.local_symbols.contains(&identifier)
            {
                acc.insert(identifier);
            }
        } else {
            panic!("TODO sorted QualIdentifier")
        }
    }

    fn is_relevant(&self, other: &FormalState) -> bool {
        match other {
            FormalState::Quant(qs) => {
                if self.id == qs.id {
                    return true;
                }
                // let mut temp = self.hidden_context.clone();
                // temp.extend(qs.live_symbols.iter().cloned());
                for p in &qs.patterns {
                    if p.is_subset(&self.hidden_context) {
                        return true;
                    }
                }
            }
            FormalState::NonQuant(qs) => {
                if self.hidden_context.is_disjoint(&qs.live_symbols) {
                    return false;
                }
                return true;
            }
        }
        false
    }
}

enum FormalState {
    Quant(QuantiState),
    NonQuant(NonQuantState),
}

impl FormalState {
    fn debug(&self) {
        match self {
            FormalState::Quant(qs) => {
                println!("qid: {}", qs.id);
                println!("live symbols:\n\t{}", pprint_symbol_set(&qs.live_symbols));
                let num_patterns = qs.patterns.len();
                for (i, p) in qs.patterns.iter().enumerate() {
                    println!(
                        "pattern {}/{}\n\t{}",
                        i + 1,
                        num_patterns,
                        pprint_symbol_set(p)
                    );
                }
                println!("context:\n\t{}", pprint_symbol_set(&qs.hidden_context));
                println!();
            }
            FormalState::NonQuant(qs) => {
                println!("cid(QF): {}", qs.id);
                println!("live symbols\n\t{}", pprint_symbol_set(&qs.live_symbols));
                println!();
            }
        }
    }

    fn get_id(&self) -> String {
        match self {
            FormalState::Quant(qs) => qs.id.clone(),
            FormalState::NonQuant(qs) => qs.id.clone(),
        }
    }

    fn is_relevant(&self, other: &FormalState) -> bool {
        match self {
            FormalState::Quant(qs) => qs.is_relevant(other),
            FormalState::NonQuant(qs) => qs.is_relevant(other),
        }
    }
}

struct TermExpander {
    defined_symbols: Arc<SymbolSet>,
    // local symbols (e.g. bound variables forall, exists, let)
    local_symbols: SymbolSet,

    formals: Vec<FormalState>,

    live_symbols: SymbolSet,
}

impl TermExpander {
    fn new(defined_symbols: Arc<SymbolSet>) -> Self {
        TermExpander {
            defined_symbols,
            local_symbols: SymbolSet::new(),
            formals: Vec::new(),
            live_symbols: SymbolSet::new(),
        }
    }

    fn add_local_binding(&mut self, symbol: &concrete::Symbol) {
        self.local_symbols.insert(symbol.clone());
    }

    fn remove_local_binding(&mut self, symbol: &concrete::Symbol) {
        self.local_symbols.remove(symbol);
    }

    fn _expand_to_formula_states(&mut self, term: &concrete::Term) {
        match term {
            Term::Constant(..) => (),
            Term::QualIdentifier(qual_identifier) => {
                self.add_live_symbol(qual_identifier);
            }
            Term::Application {
                qual_identifier,
                arguments,
            } => {
                self.add_live_symbol(qual_identifier);
                arguments.iter().for_each(|x| self._expand_to_formula_states(x));
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
                if let Term::Attributes { term, attributes } = quant_body {
                    let qid = get_attr_qid(&attributes).unwrap();
                    self.formals.push(FormalState::Quant(QuantiState::new(
                        self.defined_symbols.clone(),
                        self.local_symbols.clone(),
                        self.live_symbols.clone(),
                        *term.clone(),
                    )));
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

    fn expand_to_formulas(
        mut self,
        term: &concrete::Term,
        cid: Option<String>,
    ) -> Vec<FormalState> {
        self._expand_to_formula_states(term);
        if !self.live_symbols.is_empty() {
            for qi in self.formals.iter_mut() {
                match qi {
                    FormalState::Quant(qs) => {
                        qs.live_symbols.extend(self.live_symbols.iter().cloned());
                    }
                    _ => panic!("expected quantifier"),
                }
            }
            if self.formals.is_empty() {
                let qf = NonQuantState {
                    id: cid.unwrap(),
                    live_symbols: self.live_symbols.clone(),
                };
                self.formals.push(FormalState::NonQuant(qf));
            }
        }
        self.formals
    }

    fn expand_to_symbols(mut self, term: &concrete::Term) -> SymbolSet {
        self._expand_to_formula_states(term);
        let mut res = SymbolSet::new();
        res.extend(self.live_symbols.into_iter());
        for qi in self.formals.into_iter() {
            match qi {
                FormalState::Quant(qs) => {
                    res.extend(qs.live_symbols.into_iter());
                }
                FormalState::NonQuant(qs) => {
                    res.extend(qs.live_symbols.into_iter());
                }
            }
        }
        res
    }

    fn add_live_symbol(&mut self, qual_identifier: &concrete::QualIdentifier) {
        if let concrete::QualIdentifier::Simple { identifier } = qual_identifier {
            let identifier = get_identifier_symbols(identifier);
            if self.defined_symbols.contains(&identifier)
                && !self.local_symbols.contains(&identifier)
            {
                self.live_symbols.insert(identifier);
            }
        } else {
            panic!("TODO sorted QualIdentifier")
        }
    }
}

struct GraphBuilder {
    defined_symbols: Arc<SymbolSet>,
    formals: HashMap<String, FormalState>,
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
            formals: HashMap::new(),
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
                    let formals = TermExpander::new(self.defined_symbols.clone())
                        .expand_to_formulas(term, Some(cid.clone()));
                    formals.into_iter().for_each(|qi| {
                        self.formals.insert(qi.get_id(), qi);
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

    fn get_formal(&self, id: &str) -> Option<&FormalState> {
        self.formals.get(id)
    }

    fn compute_scores(&mut self) {
        for (k, v) in self.formals.iter() {
            // let mut qf_score = 0;
            // let mut qt_score = 0;
            for (k2, v2) in self.formals.iter() {
                if k == k2 {
                    continue;
                }
                if v.is_relevant(v2) {
                    println!("{}->{}", k, k2);
                    // match v2 {
                    //     FormalState::Quant(_) => {
                    //         qt_score += 1;
                    //     }
                    //     FormalState::NonQuant(_) => {
                    //         qf_score += 1;
                    //     }
                    // }
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

impl Debug for GraphBuilder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "GraphBuilder")?;
        writeln!(f, "formals {:?}", self.formals.len())?;
        Ok(())
    }
}

pub fn tree_shake_graph(mut commands: Vec<concrete::Command>) {
    // print!("defs {:?}", defs);
    let mut gb = GraphBuilder::new(&commands);
    gb.compute_scores();

    // println!("{:?}", gb);

    // for (k, v) in gb.formals.iter() {
    //     // println!("{}:", k);
    //     v.debug();
    // }

    // let fs = gb
    //     .get_formal("internal_lib!page_organization.valid_ll.?_definition")
    //     .unwrap();

    // fs.debug();

    // let mut scores: HashMap<String, usize> = HashMap::new();

    // let mut general: SymbolSet = SymbolSet::new();

    // for qi in formal_states.iter() {
    //     general.extend(match qi {
    //         FormalState::Quant(qs) => qs.live_symbols.iter().cloned(),
    //         FormalState::NonQuant(NonQuantState { symbols, .. }) => symbols.iter().cloned(),
    //     });
    // }
}

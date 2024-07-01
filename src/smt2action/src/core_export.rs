use smt2parser::{concrete, visitors};
use std::collections::HashSet;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::vec;

use crate::{query_io, term_match};

const PRODUCE_CORE_OPTION: &str = "produce-unsat-cores";

fn load_core_symbols(file_path: &String) -> HashSet<String> {
    // read lines from file
    let file = File::open(file_path).unwrap();
    let reader = BufReader::new(file);
    let lines = reader
        .lines()
        .map(|x| x.unwrap())
        .collect::<vec::Vec<String>>();
    if &lines[0] != "unsat" {
        panic!("Expected 'unsat' as the first line of the core file");
        // return HashSet::new();
    }
    // get the last line of the file
    let last_line = &lines[lines.len() - 1];
    // strip the first and last character
    let last_line = &last_line[1..last_line.len() - 1];
    // split on spaces
    let core: HashSet<String> = last_line.split(" ").map(|x| x.to_owned()).collect();
    core
}

pub fn label_asserts(commands: &mut Vec<concrete::Command>, reassign: bool) {
    let produce = concrete::Command::SetOption {
        keyword: concrete::Keyword(PRODUCE_CORE_OPTION.to_owned()),
        value: visitors::AttributeValue::Symbol(concrete::Symbol("true".to_owned())),
    };

    commands.insert(0, produce);

    if !reassign {
        let _ = query_io::load_mariposa_ids(&commands);
    } else {
        query_io::add_cids(commands, true);
    }

    // if (set-option :produce-unsat-cores false) is present, remove it
    let mut i = 0;
    while i < commands.len() {
        let command = &commands[i];
        if let concrete::Command::SetOption {
            keyword: concrete::Keyword(k),
            value: visitors::AttributeValue::Symbol(concrete::Symbol(v)),
        } = command
        {
            if k == PRODUCE_CORE_OPTION && v == "false" {
                commands.remove(i);
                continue;
            }
        }
        i += 1;
    }

    // add (get-unsat-core) after the last check-sat
    // find index of last check-sat, starting from the end
    let mut i = commands.len() - 1;
    while i > 0 {
        let command = &commands[i];
        if let concrete::Command::CheckSat = command {
            break;
        }
        i -= 1;
    }
    // insert get-unsat-core after last check-sat
    // if no check-sat, insert at end
    i += 1;
    commands.insert(i, concrete::Command::GetUnsatCore);
}

fn should_keep_command(command: &concrete::Command, core: &HashSet<String>, keep_quantified: bool) -> bool {
    let concrete::Command::Assert { term } = command else {
        return true;
    };

    if keep_quantified && !term_match::is_qf_term(term) {
        // keep quantified asserts
        return true;
    }

    if let concrete::Term::Attributes {
        term: _,
        attributes,
    } = term
    {
        for (key, value) in attributes {
            if key == &concrete::Keyword("named".to_owned()) {
                if let visitors::AttributeValue::Symbol(concrete::Symbol(name)) = value {
                    return core.contains(name);
                }
            }
        }
    }
    false
}

pub fn reduce_asserts(commands: &mut Vec<concrete::Command>, core_file_path: &String, keep_quantified: bool) -> bool {
    let core = load_core_symbols(core_file_path);

    if core.len() == 0 {
        return false;
    }

    let temp = commands
        .drain(..)
        .into_iter()
        .filter(|x| should_keep_command(x, &core, keep_quantified))
        .collect::<Vec<concrete::Command>>();

    commands.extend(temp);

    if let concrete::Command::SetOption {
        keyword: concrete::Keyword(k),
        ..
    } = &commands[0]
    {
        if k == PRODUCE_CORE_OPTION {
            commands.remove(0);
        }
    }
    true
}

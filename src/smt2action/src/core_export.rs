use smt2parser::{concrete, visitors};
use std::collections::HashSet;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::vec;

const CORE_DUMP_PREFIX: &str = "mariposa-core-id-";
const PRODUCE_CORE_OPTION: &str = "produce-unsat-cores";

fn load_core_symbols(file_path: &String) -> HashSet<String> {
    // read lines from file
    let file = File::open(file_path).unwrap();
    let reader = BufReader::new(file);
    let lines = reader
        .lines()
        .map(|x| x.unwrap())
        .collect::<vec::Vec<String>>();
    // get the last line of the file
    if &lines[0] != "unsat" {
        return HashSet::new();
    }
    let last_line = &lines[lines.len() - 1];
    // strip the first and last character
    let last_line = &last_line[1..last_line.len() - 1];
    // split on spaces
    let core: HashSet<String> = last_line.split(" ").map(|x| x.to_owned()).collect();
    core
}

fn should_keep_command(command: &concrete::Command, core: &HashSet<String>) -> bool {
    let concrete::Command::Assert { term } = command else {
        return true;
    };

    if let concrete::Term::Attributes {
        term: _,
        attributes,
    } = term
    {
        for (key, value) in attributes {
            if key == &concrete::Keyword("named".to_owned()) {
                if let visitors::AttributeValue::Symbol(concrete::Symbol(name)) = value {
                    if core.contains(name) {
                        return true;
                    }
                }
            }
        }
    }
    false
}

fn remove_label(command: &mut concrete::Command) {
    let concrete::Command::Assert { term } = command else {
        return;
    };
    let mut temp = concrete::Term::Constant(concrete::Constant::String("".to_string()));
    let mut flag = false;

    if let concrete::Term::Attributes {
        term: new_term,
        attributes,
    } = term
    {
        for (key, value) in attributes {
            if key == &concrete::Keyword("named".to_owned()) {
                if let visitors::AttributeValue::Symbol(concrete::Symbol(name)) = value {
                    // check if name starts with "unsat-cores-dump-name-"
                    if name.starts_with(CORE_DUMP_PREFIX) {
                        // yuck but doesn't seem to affect performance significantly
                        temp = *new_term.clone();
                        flag = true;
                    }
                }
            }
        }
    }
    if flag {
        *command = concrete::Command::Assert { term: temp };
    }
}

fn label_assert(command: &mut concrete::Command, ct: usize) {
    let concrete::Command::Assert { term } = command else {
        return;
    };

    let named = concrete::Keyword("named".to_owned());
    let new_name = CORE_DUMP_PREFIX.to_owned() + &ct.to_string();
    let new_name = visitors::AttributeValue::Symbol(concrete::Symbol(new_name));

    // does assert have attributes?
    if let concrete::Term::Attributes {
        term: _,
        attributes,
    } = term
    {
        for (key, _) in attributes.iter() {
            if key == &named {
                // if name already exists, don't mess with it
                return;
            }
        }
        // otherwise, add the new name
        attributes.push((named, new_name));
    } else {
        // if no attributes, create a new one
        let attributes = vec![(named, new_name)];
        let mut temp = concrete::Term::Constant(concrete::Constant::String("".to_string()));
        std::mem::swap(term, &mut temp);
        *term = concrete::Term::Attributes {
            term: Box::new(temp),
            attributes,
        };
    }
}

pub fn label_asserts(commands: &mut Vec<concrete::Command>) {
    let produce = concrete::Command::SetOption {
        keyword: concrete::Keyword(PRODUCE_CORE_OPTION.to_owned()),
        value: visitors::AttributeValue::Symbol(concrete::Symbol("true".to_owned())),
    };

    commands.insert(0, produce);

    commands
        .iter_mut()
        .enumerate()
        .for_each(|(i, x)| label_assert(x, i));

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

pub fn reduce_asserts(commands: &mut Vec<concrete::Command>, core_file_path: &String) -> bool {
    let core = load_core_symbols(core_file_path);

    if core.len() == 0 {
        return false;
    }

    let temp = commands
        .drain(..)
        .into_iter()
        .filter(|x| should_keep_command(x, &core))
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

    // cleans names that were put in by mariposa
    commands.iter_mut().for_each(|x| remove_label(x));
    true
}

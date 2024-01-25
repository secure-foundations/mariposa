use std::collections::HashSet;
use smt2parser::{concrete, visitors};
use core::panic;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::vec;

// fn ensure_no_conflicts(symbols1: HashSet<String>, symbols2: HashSet<String>) {
//     // symbols used in commands1 and commands2 should be disjoint
//     let intersection: Vec<String> = symbols1.intersection(&symbols2).cloned().collect();
//     if intersection.len() > 0 {
//         panic!("symbols used in both commands1 and commands2: {:?}", intersection);
//     }
// }

// // temporary while should_keep_command keeps all non-asserts
// fn should_keep_command_noncore(command: &concrete::Command, core: &HashSet<String>) -> bool {
//     let concrete::Command::Assert { term } = command else { 
//         // excludes check-sats
//         if let concrete::Command::CheckSat = command {
//             return false;
//         }
//         return true;
//     };
//     let named = concrete::Keyword("named".to_owned());

//     if let concrete::Term::Attributes {
//         term: _,
//         attributes,
//     } = term
//     {
//         for (key, value) in attributes {
//             if key == &named {
//                 if let visitors::AttributeValue::Symbol(concrete::Symbol(name)) = value {
//                     if core.contains(name) {
//                         return false;
//                     }
//                 }
//             }
//         }
//     }
//     return true;
// }

// fn parse_noncore_from_file(commands: Vec<concrete::Command>, file_path: String) -> Vec<concrete::Command> {
//     let core = core_to_hashset(file_path);

//     // filter out commands that are not in the core
//     let new_commands = commands
//         .into_iter()
//         .filter(|x| should_keep_command_noncore(x, &core))
//         .collect::<Vec<concrete::Command>>();
//     return new_commands;
// }

fn core_to_hashset(file_path: String) -> HashSet<String> {
    // read lines from file
    let file = File::open(file_path).unwrap();
    let reader = BufReader::new(file);
    let lines = reader.lines().map(|x| x.unwrap());
    // get the last line of the file
    let last_line = lines.last().unwrap();
    // last_line could be timeout -- if so, throw error
    if last_line == "timeout" {
        return HashSet::new();
        // panic!("file timed out")
    }
    // strip the first and last character
    let last_line = &last_line[1..last_line.len() - 1];
    // split on spaces
    let core: HashSet<String> = last_line.split(" ").map(|x| x.to_owned()).collect();
    return core;
}



fn should_keep_command(command: &concrete::Command, core: &HashSet<String>) -> bool {
    let concrete::Command::Assert { term } = command else { 
        return true;
    };
    let named = concrete::Keyword("named".to_owned());

    if let concrete::Term::Attributes {
        term: _,
        attributes,
    } = term
    {
        for (key, value) in attributes {
            if key == &named {
                if let visitors::AttributeValue::Symbol(concrete::Symbol(name)) = value {
                    if core.contains(name) {
                        return true;
                    }
                }
            }
        }
    }
    return false;
}

const CORE_DUMP_PREFIX: &str = "unsat-cores-dump-name-";
const PRODUCE_CORE_OPTION: &str = "produce-unsat-cores";

fn remove_label(command: &mut concrete::Command) {
    let concrete::Command::Assert { term } = command else { return; };
    let named = concrete::Keyword("named".to_owned());
    let mut temp = concrete::Term::Constant(concrete::Constant::String("".to_string()));
    let mut flag = false;

    // does assert have a named attribute?
    if let concrete::Term::Attributes {
        term: new_term,
        attributes,
    } = term
    {
        for (key, value) in attributes {
            if key == &named {
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

pub fn remove_labels(commands: &mut Vec<concrete::Command>) {
    commands.iter_mut().for_each(|x| remove_label(x));
}

fn label_assert(command: &mut concrete::Command, ct: usize) {
    let concrete::Command::Assert { term } = command else { return; };
    // does assert have attributes?
    if let concrete::Term::Attributes {
        term: _,
        attributes: _,
    } = term
    {
        // if name already exists, don't mess with it
    } else {
        let new_name = CORE_DUMP_PREFIX.to_owned() + &ct.to_string();
        let attributes = vec![(
            concrete::Keyword("named".to_owned()),
            visitors::AttributeValue::Symbol(concrete::Symbol(new_name)),
        )];
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
            if k == "produce-unsat-cores" && v == "false" {
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

pub fn reduce_asserts(commands: Vec<concrete::Command>, core_file_path: String) -> Vec<concrete::Command> {
    let core = core_to_hashset(core_file_path);
    if core.len() == 0 {
        return commands;
    }
    let mut commands = commands
        .into_iter()
        .filter(|x| should_keep_command(x, &core))
        .collect::<Vec<concrete::Command>>();

    // cleans names that were put in by mariposa
    remove_labels(&mut commands);
    commands[1..commands.len() - 1].to_vec()
}
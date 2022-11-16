use std::collections::{BTreeMap, HashMap};
use std::fs::File;
use std::io::{BufReader, BufWriter};
use rand::thread_rng;
use rand::seq::SliceRandom;
use smt2parser::{CommandStream, concrete, renaming, visitors};
use rustop::opts;

fn print_non_info_command(commands: &Vec<concrete::Command>) {
    for command in commands {
        if let concrete::Command::SetInfo {..} = command {
        } else {
            println!("{}", command);
        }
    }
}

fn get_assert_intervals(commands: &Vec<concrete::Command>) -> Vec<usize>
{
    let mut indices = Vec::new();
    for (pos, command) in commands.iter().enumerate() {
        if let concrete::Command::Assert {..} = command {
            indices.push(pos);
        }
    }

    let mut i = 0;
    let mut prev = usize::MAX-1;
    let mut inter = false;

    // sentinel index
    indices.push(prev);
    let mut intervals = Vec::new();

    while i < indices.len()
    {
        let cur = indices[i];
        let con = prev + 1 == cur;
        if !inter && con {
            intervals.push(prev);
            inter = true;
        } else if inter && !con {
            intervals.push(prev);
            inter = false;
        }
        prev = cur;
        i += 1;
    }

    intervals
}

fn shuffle_asserts(commands: &mut Vec<concrete::Command>) {
    let intervals = get_assert_intervals(&commands);
    let mut i = 0;
    while i < intervals.len()
    {
        let start = intervals[i];
        let end = intervals[i+1] + 1;
        // sanity check the interval
        for j in start..end {
            assert!(matches!(commands[j], concrete::Command::Assert{..}));
        }
        (&mut (*commands)[start..end]).shuffle(&mut thread_rng());
        i += 2;
    }
}

fn normalize_commands(commands: Vec<concrete::Command>) -> Vec<concrete::Command> {
    let randomization_seed = 121210;
    let randomization_space = BTreeMap::from([
        (visitors::SymbolKind::Variable, 100000),
        (visitors::SymbolKind::Constant, 100000),
        (visitors::SymbolKind::Function, 100000),
        (visitors::SymbolKind::Sort, 100000),
        (visitors::SymbolKind::Datatype, 100000),
        (visitors::SymbolKind::TypeVar, 100000),
        (visitors::SymbolKind::Constructor, 100000),
        (visitors::SymbolKind::Selector, 100000),
    ]);
    let config = renaming::SymbolNormalizerConfig {
        randomization_space,
        randomization_seed,
    };
    let mut normalizer = renaming::SymbolNormalizer::new(concrete::SyntaxBuilder, config);
    let mut ncommand = Vec::<concrete::Command>::new();
    for command in commands {
        let command = command.accept(&mut normalizer).unwrap();
        ncommand.push(command)
    }
    ncommand
}

fn parse_commands_from_file(file_path: String) -> Vec<concrete::Command> {
    let file = File::open(file_path).unwrap();
    let reader = BufReader::new(file);

    let stream = CommandStream::new(
        reader,
        concrete::SyntaxBuilder,
        None,
    );

    stream.collect::<Result<Vec<_>, _>>().unwrap()
}

fn parse_model_file(file_path: String, query: &Vec<concrete::Command>) {
    let commands = parse_commands_from_file(file_path);
    
    let mut defined:HashMap<String, &concrete::Command> = HashMap::new();

    for command in &commands {
        if let concrete::Command::DefineFun { sig,..} = command {
            defined.insert(sig.name.0.clone(), command);
        } else {
            panic!("unhandled command in model");
        }
    }

    for command in query {
        if let concrete::Command::DeclareFun { symbol,..} = command {
            let name = &symbol.0;
            if defined.contains_key(name) {
                let command = defined.get(name).unwrap();
                println!("{}", command);
            }
        } else if let concrete::Command::SetInfo {..} = command {

        } else {
            println!("{}", command);
        }
    }
}

fn main() {
    let (args, _rest) = opts! {
        synopsis "mariposa is a smtlib2 query mutator";
        opt in_file_path:String,
            desc: "the input file path";
        opt model_file_path:Option<String>,
            desc: "model file with the query";
        opt process:String=String::from("none"),
            desc: "the mutation";
        opt silent:bool=false,
            desc: "process without printing";
        opt out_file_path:Option<String>,
            desc: "the output file path";
    }.parse_or_exit();

    let mut commands :Vec<concrete::Command> = 
    parse_commands_from_file(args.in_file_path);

    if args.process == "none" {
        println!("{}", commands.len());
    } else if args.process  == "shuffle" {
        shuffle_asserts(&mut commands);
    } else if args.process == "normalize" {
        commands = normalize_commands(commands);
    }

    if let Some(file_path) = args.model_file_path {
        println!("parse model file {}", file_path);
        parse_model_file(file_path, &commands);
    }

    if !args.silent {
        print_non_info_command(&commands);
    }
}


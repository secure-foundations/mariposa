use std::collections::BTreeMap;
use std::fs::File;
use std::io::BufReader;
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

fn main() {
    let (args, rest) = opts! {
        synopsis "mariposa is a smtlib2 query mutator";
        opt in_file_path:String,
            desc: "the input file path";
        opt mutation:String=String::from("none"),
            desc: "the mutation";
        opt silent:bool=false,
            desc: "process without printing";
    }.parse_or_exit();

    let file = File::open(args.in_file_path).unwrap();
    let reader = BufReader::new(file);

    let stream = CommandStream::new(
        reader,
        concrete::SyntaxBuilder,
        None,
    );

    let mut commands :Vec<concrete::Command> =
        stream.collect::<Result<Vec<_>, _>>().unwrap();

    if args.mutation == "none" {
        println!("{}", commands.len());
    } else if args.mutation == "shuffle" {
        shuffle_asserts(&mut commands);
    } else if args.mutation == "normalize" {
        commands = normalize_commands(commands);
    }

    if !args.silent {
        print_non_info_command(&commands);
    }
}


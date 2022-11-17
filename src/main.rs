use std::collections::{BTreeMap, HashMap};
use std::fs::File;
use std::io::{BufReader, BufWriter, Write, stdout};
use rand::seq::SliceRandom;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use smt2parser::{CommandStream, concrete, renaming, visitors};
use rustop::opts;

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

fn get_assert_intervals(commands: &Vec<concrete::Command>) -> Vec<usize> {
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

fn shuffle_asserts(commands: &mut Vec<concrete::Command>, seed: u64) {
    let mut rng = ChaCha8Rng::seed_from_u64(seed);

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
        (&mut (*commands)[start..end]).shuffle(&mut rng);
        i += 2;
    }
}

fn normalize_commands(commands: Vec<concrete::Command>, seed: u64) -> Vec<concrete::Command> {
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
        randomization_seed: seed,
    };
    let mut normalizer = renaming::SymbolNormalizer::new(concrete::SyntaxBuilder, config);
    commands.into_iter().map(|c| c.accept(&mut normalizer).unwrap()).collect()
}

struct Manager {
    writer: BufWriter<Box<dyn std::io::Write>>,
    seed: u64,
}

impl Manager {
    fn new(out_file_path: Option<String>, seed: u64) -> Manager {
        let writer: BufWriter<Box<dyn std::io::Write>> = match out_file_path {
            Some(path) => {
                let file = File::create(path).unwrap();
                BufWriter::new(Box::new(file))
            },
            None => {
                BufWriter::new(Box::new(stdout().lock()))
            }
        };
        Manager {writer, seed}
    }

    fn dump_non_info_commands(&mut self, commands: &Vec<concrete::Command>) {
        for command in commands {
            if let concrete::Command::SetInfo {..} = command {
            } else {
                writeln!(self.writer, "{}", command).unwrap();
            }
        }
    }

    fn dump_model_test(&mut self, model: &Vec<concrete::Command>, query: &Vec<concrete::Command>) {    
        let mut defined:HashMap<String, &concrete::Command> = HashMap::new();

        for command in model {
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
                    writeln!(self.writer, "{}", command).unwrap();
                }
            } else if let concrete::Command::SetInfo {..} = command {
                // skip
            } else {
                writeln!(self.writer, "{}", command).unwrap();
            }
        }
    }
}

fn main() {
    let (args, _rest) = opts! {
        synopsis "mariposa is a smtlib2 query mutator";
        opt in_file_path:String,
            desc: "input file path";
        opt model_file_path:Option<String>,
            desc: "model file with the query";
        opt process:String=String::from("none"),
            desc: "mutation to perform";
        opt quiet:bool=false,
            desc: "process without printing";
        opt out_file_path:Option<String>,
            desc: "output file path";
        opt seed:u64=12345,
        desc: "seed for randomness";
    }.parse_or_exit();

    let mut manager = Manager::new(args.out_file_path, args.seed);

    let mut commands :Vec<concrete::Command> = 
    parse_commands_from_file(args.in_file_path);

    if let Some(file_path) = args.model_file_path {
        let model = parse_commands_from_file(file_path);
        manager.dump_model_test(&model, &commands);
    } else {
        if args.process == "none" {
            manager.dump_non_info_commands(&commands);
        } else if args.process  == "shuffle" {
            shuffle_asserts(&mut commands, manager.seed);
            manager.dump_non_info_commands(&commands);
        } else if args.process == "normalize" {
            commands = normalize_commands(commands, manager.seed);
            manager.dump_non_info_commands(&commands);
        }
    }
}


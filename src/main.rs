use rand::seq::SliceRandom;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use rustop::opts;
use smt2parser::{concrete, renaming, visitors, CommandStream};
use std::collections::{BTreeMap, HashMap};
use std::fs::File;
use std::io::{stdout, BufReader, BufWriter, Write};

const DEFAULT_SEED: u64 = 1234567890;

fn parse_commands_from_file(file_path: String) -> Vec<concrete::Command> {
    let file = File::open(file_path).unwrap();
    let reader = BufReader::new(file);

    let stream = CommandStream::new(reader, concrete::SyntaxBuilder, None);

    stream.collect::<Result<Vec<_>, _>>().unwrap()
}

fn get_assert_intervals(commands: &Vec<concrete::Command>) -> Vec<usize> {
    let mut indices = Vec::new();
    for (pos, command) in commands.iter().enumerate() {
        if let concrete::Command::Assert { .. } = command {
            indices.push(pos);
        }
    }

    let mut i = 0;
    let mut prev = usize::MAX - 1;
    let mut inter = false;

    // sentinel index
    indices.push(prev);
    let mut intervals = Vec::new();

    while i < indices.len() {
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
    while i < intervals.len() {
        let start = intervals[i];
        let end = intervals[i + 1] + 1;
        // sanity check the interval
        for j in start..end {
            assert!(matches!(commands[j], concrete::Command::Assert { .. }));
        }
        (&mut (*commands)[start..end]).shuffle(&mut rng);
        i += 2;
    }
}

fn normalize_commands(commands: Vec<concrete::Command>, seed: u64) -> Vec<concrete::Command> {
    let randomization_space = BTreeMap::from([
        (visitors::SymbolKind::Variable, usize::MAX),
        (visitors::SymbolKind::Constant, usize::MAX),
        (visitors::SymbolKind::Function, usize::MAX),
        (visitors::SymbolKind::Sort, usize::MAX),
        (visitors::SymbolKind::Datatype, usize::MAX),
        (visitors::SymbolKind::TypeVar, usize::MAX),
        (visitors::SymbolKind::Constructor, usize::MAX),
        (visitors::SymbolKind::Selector, usize::MAX),
    ]);
    let config = renaming::SymbolNormalizerConfig {
        randomization_space,
        randomization_seed: seed,
    };
    let mut normalizer = renaming::SymbolNormalizer::new(concrete::SyntaxBuilder, config);
    commands
        .into_iter()
        .map(|c| c.accept(&mut normalizer).unwrap())
        .collect()
}

fn remove_pattern_non_rec(command: &mut concrete::Command) {
    if let concrete::Command::Assert { term } = command {
        if let concrete::Term::Forall {
            vars: _,
            term: attributed_term,
        } = term
        {
            if let concrete::Term::Attributes { term: _, attributes } = &mut **attributed_term {
                attributes.retain(|x| x.0 != concrete::Keyword("pattern".to_owned()));
            }
        }
    }
}

// patterns
fn remove_patterns(commands: &mut Vec<concrete::Command>) {
    // let vector = vec!(1, 2, 3);
    // let result = vector.into_iter().map(|x| x * 2).collect::<Vec<i32>>();
    // println!("{:?}", vector);
    // println!("{:?}", result);

    commands.iter_mut().for_each(|x| remove_pattern_non_rec(x));
    // println!("{:?}", commands);
    // println!("{:?}", result);

    // for command in &mut commands {
    //     // println!("assert: {}", command);

    // }
    // commands
}

struct Manager {
    writer: BufWriter<Box<dyn std::io::Write>>,
    seed: u64,
}

impl Manager {
    fn new(out_file_path: Option<String>, seed: u64) -> Manager {
        let writer: BufWriter<Box<dyn std::io::Write>> = match out_file_path {
            Some(path) => {
                let path = std::path::Path::new(&path);
                let prefix = path.parent().unwrap();
                std::fs::create_dir_all(prefix).unwrap();
                let file = File::create(path).unwrap();
                BufWriter::new(Box::new(file))
            }
            None => BufWriter::new(Box::new(stdout().lock())),
        };
        Manager { writer, seed }
    }

    fn dump(&mut self, s: &String) {
        write!(self.writer, "{}", s).unwrap();
    }

    fn dump_non_info_commands(&mut self, commands: &Vec<concrete::Command>) {
        for command in commands {
            if let concrete::Command::SetInfo { .. } = command {
            } else {
                writeln!(self.writer, "{}", command).unwrap();
            }
        }
    }

    fn dump_model_test(&mut self, model: &Vec<concrete::Command>, query: &Vec<concrete::Command>) {
        let mut defined: HashMap<String, &concrete::Command> = HashMap::new();

        for command in model {
            if let concrete::Command::DefineFun { sig, .. } = command {
                defined.insert(sig.name.0.clone(), command);
            } else {
                // panic!("unhandled command in model {}", command);
            }
        }

        for command in query {
            if let concrete::Command::DeclareFun { symbol, .. } = command {
                let name = &symbol.0;
                if defined.contains_key(name) {
                    let command = defined.get(name).unwrap();
                    writeln!(self.writer, "{}", command).unwrap();
                }
            } else if let concrete::Command::SetInfo { .. } = command {
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
        opt perturbation:String=String::from("none"),
            desc: "mutation to perform";
        opt quiet:bool=false,
            desc: "perturbation without printing";
        opt out_file_path:Option<String>,
            desc: "output file path";
        opt seed:u64=DEFAULT_SEED,
        desc: "seed for randomness";
    }
    .parse_or_exit();

    let mut commands: Vec<concrete::Command> = parse_commands_from_file(args.in_file_path);

    if let Some(file_path) = args.model_file_path {
        let model = parse_commands_from_file(file_path);
        let mut manager = Manager::new(args.out_file_path, args.seed);
        manager.dump_model_test(&model, &commands);
    } else {
        let mut manager = Manager::new(args.out_file_path, args.seed);

        if args.perturbation == "none" {
            return; // parse then exit
        }

        if args.perturbation == "shuffle" {
            shuffle_asserts(&mut commands, manager.seed);
        } else if args.perturbation == "rename" {
            commands = normalize_commands(commands, manager.seed);
        } else if args.perturbation == "sseed" {
            if manager.seed != DEFAULT_SEED {
                let solver_seed = manager.seed as u32;
                manager.dump(&format!("(set-option :random-seed {solver_seed})\n"));
            };
        } else if args.perturbation == "patterns" {
            remove_patterns(&mut commands);
        }
        manager.dump_non_info_commands(&commands);
    }
}

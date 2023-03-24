use rand::seq::SliceRandom;
use rand::SeedableRng;
use rand::Rng;
use rand_chacha::ChaCha8Rng;
use rustop::opts;
use smt2parser::{concrete, renaming, visitors, CommandStream};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fs::File;
use std::path::Path;
use std::io::{stdout, BufRead, BufReader, BufWriter, Write};
use std::mem;

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

fn remove_pattern_rec_helper(curr_term: &mut concrete::Term, rng: &mut ChaCha8Rng, threshold: u64) {
    match curr_term {
        concrete::Term::Application { qual_identifier:_, arguments } => 
            for argument in arguments.iter_mut(){
                remove_pattern_rec_helper(argument, rng, threshold)
            },
        concrete::Term::Let { var_bindings:_, term } => remove_pattern_rec_helper(&mut *term, rng, threshold),
        concrete::Term::Forall { vars:_, term } => remove_pattern_rec_helper(&mut *term, rng, threshold),
        concrete::Term::Exists { vars:_, term } => remove_pattern_rec_helper(&mut *term, rng, threshold),
        concrete::Term::Match { term, cases:_ } => remove_pattern_rec_helper(&mut *term, rng, threshold),
        concrete::Term::Attributes { term, attributes } => {
            remove_pattern_rec_helper(term, rng, threshold);
            let random = rng.gen_range(1..101);
            if random <= threshold {
                attributes.retain(|x| x.0 != concrete::Keyword("pattern".to_owned()))
            }
        }
        concrete::Term::Constant(_) => (),
        concrete::Term::QualIdentifier(_) => (),
    }
}

fn remove_pattern_rec(command: &mut concrete::Command, rng: &mut ChaCha8Rng, threshold: u64) {
    if let concrete::Command::Assert { term } = command {
        remove_pattern_rec_helper(term, rng, threshold);
    }
}

// patterns
fn remove_patterns(commands: &mut Vec<concrete::Command>, seed: u64, threshold: u64) {
    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    commands.iter_mut().for_each(|x| remove_pattern_rec(x, &mut rng, threshold));
}


fn name_assert(command: &mut concrete::Command, ct: usize) {
    let concrete::Command::Assert { term } = command else { return; };
    // does assert have attributes?
    if let concrete::Term::Attributes { term: _, attributes: _ } = term {
        // if name already exists, don't mess with it
    }
    else {
        let new_name = "unsat-cores-dump-name-".to_owned() + &ct.to_string();
        let attributes = vec![(concrete::Keyword("named".to_owned()), visitors::AttributeValue::Symbol(concrete::Symbol(new_name)))];
        let mut temp = concrete::Term::Constant(concrete::Constant::String("".to_string()));
        mem::swap(term, &mut temp);
        *term = concrete::Term::Attributes { term: Box::new(temp), attributes };
    }
}

fn name_asserts(commands: &mut Vec<concrete::Command>) {
    commands.iter_mut().enumerate().for_each(|(i, x)| name_assert(x, i));
    commands.insert(0, concrete::Command::SetOption { keyword: concrete::Keyword("produce-unsat-cores".to_owned()), value: visitors::AttributeValue::Symbol(concrete::Symbol("true".to_owned())) });
    commands.push(concrete::Command::GetUnsatCore)
}

fn should_keep_command(command: &concrete::Command, core: &HashSet<String>) -> bool {
    let concrete::Command::Assert { term } = command else { 
        return true;
    };
    let named = concrete::Keyword("named".to_owned());

    if let concrete::Term::Attributes { term: _, attributes } = term {
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

// return a Vec<String> where each element is the name of an assert from the unsat core
fn parse_core_from_file(commands: Vec<concrete::Command>, file_path: String) -> Vec<concrete::Command> {
    // read lines from file
    let file = File::open(file_path).unwrap();
    let reader = BufReader::new(file);
    let lines = reader.lines().map(|x| x.unwrap());
    // get the last line of the file
    let last_line = lines.last().unwrap();
    // strip the first and last character 
    let last_line = &last_line[1..last_line.len()-1];
    // split the last line into a vector of strings 
    let core = last_line.split(" ").map(|x| x.to_string()).collect::<Vec<String>>();
    // convert core to a HashSet
    let core = core.into_iter().collect::<HashSet<String>>();

    // filter out commands that are not in the core
    let new_commands = commands.into_iter().filter(|x| should_keep_command(x, &core)).collect::<Vec<concrete::Command>>();
    return new_commands;
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
        opt threshold:u64=100,
            desc: "threshold for pattern removal";
        opt core_file:Option<String>,
            desc: "file containing unsat cores";
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
            remove_patterns(&mut commands, manager.seed, args.threshold);
        } else if args.perturbation == "unsat-core" {
            name_asserts(&mut commands);
        } else if args.perturbation == "minimize-query" {
            commands = parse_core_from_file(commands, args.core_file.unwrap());
        }
        manager.dump_non_info_commands(&commands);
    }
}

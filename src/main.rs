use std::collections::{BTreeMap, HashMap};
use std::fs::File;
use std::io::{BufReader, BufWriter, Write, stdout};
use rand::seq::SliceRandom;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use smt2parser::{CommandStream, concrete, renaming, visitors};
use rustop::opts;

const DEFAULT_SEED: u64 = 1234567890;

fn parse_commands_from_file(file_path: String) -> Vec<concrete::Command> {
    let file = File::open(file_path).unwrap();
    let reader = BufReader::new(file);

    let stream = CommandStream::new(
        reader,
        concrete::SyntaxBuilder,
        None,
    );

    let mut builder = renaming::TesterModernizer::new(concrete::SyntaxBuilder);
    let commands = stream.collect::<Result<Vec<_>, _>>().unwrap();
    commands.into_iter().map(|c| c.accept(&mut builder).unwrap()).collect()
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

fn lower_shuffle_asserts(mut commands: Vec<concrete::Command>, seed: u64) -> Vec<concrete::Command> 
{
    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    let check_sat_index = &commands.iter().position(|x| 
        matches!(x, concrete::Command::CheckSat { .. })).unwrap();

    // truncate at the first check-sat
    commands.truncate(*check_sat_index);

    let (mut asserts, mut others): (_,Vec<_>) = commands
        .into_iter()
        .partition(|x|
            matches!(x, concrete::Command::Assert { .. }));

    (&mut asserts).shuffle(&mut rng);
    others.append(&mut asserts);

    // append a check-sat (the one above was truncated)
    others.push(concrete::Command::CheckSat);
    others
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
    commands.into_iter().map(|c| c.accept(&mut normalizer).unwrap()).collect()
}

fn remove_target_cmds(commands: &mut Vec<concrete::Command>) {
    let mut i = 0;
    while i < commands.len() {
        let command = &commands[i];
        if let concrete::Command::SetOption { keyword: concrete::Keyword(k) , value: _ } = command {
            if k == "rlimit" || k == "echo" || k == "RLIMIT" || k == "timeout" || k == "TIMEOUT" || k == "fixedpoint.TIMEOUT" {
                commands.remove(i);
                continue;
            }
        }
        i += 1;
    }
}

fn split_commands(commands: &mut Vec<concrete::Command>, in_file_path: String, out_dir: String) {
    // remove target commands
    remove_target_cmds(commands);
    let mut depth = 0;
    let mut stack = Vec::new();
    stack.push(Vec::new());
    let mut splits = 0;

    let file_name = in_file_path.split("/").last().unwrap();
    // make sure out_dir ends with a slash
    let out_dir = if out_dir.ends_with("/") { out_dir } else { out_dir + "/" };
    // remove .smt2 suffix if it exists
    let out_file_name = match file_name.strip_suffix(".smt2") {
        Some(s) => out_dir + s,
        None => out_dir + file_name,
    };

    for command in commands {
        if let concrete::Command::Push{ level:_ } = command {
            depth += 1;
            stack.push(Vec::new());
        } else if let concrete::Command::Pop{ level:_ } = command {
            depth -= 1;
            stack.pop();
        } else {
            stack[depth].push(command.clone());
        }
        if let concrete::Command::CheckSat = command {
            splits += 1;
            // write out to file
            let out_file_path = format!("{}-{}.smt2", out_file_name, splits);
            let mut manager = Manager::new(Some(out_file_path.clone()), 0);
            manager.dump_non_info_commands(&stack.concat());
        }
    }
    println!("Successfully split into {} files:", splits);
    let mut i = 0;
    while i < splits {
        println!("\t{}-{}.smt2", out_file_name, i+1);
        i += 1;
    }
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
            },
            None => {
                BufWriter::new(Box::new(stdout().lock()))
            }
        };
        Manager {writer, seed}
    }

    fn dump(&mut self, s: &String) {
        write!(self.writer, "{}", s).unwrap();
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
                // panic!("unhandled command in model {}", command);
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
        opt perturbation:String=String::from("none"),
            desc: "mutation to perform";
        opt quiet:bool=false,
            desc: "perturbation without printing";
        opt out_file_path:Option<String>,
            desc: "output file path";
        opt seed:u64=DEFAULT_SEED,
        desc: "seed for randomness";
        opt split:bool=false,
            desc: "split the input file into multiple files based on check-sats";
        opt split_dir:Option<String>,
            desc: "directory to put split files in";
    }.parse_or_exit();

    let infilepath = args.in_file_path.clone();
    let mut commands :Vec<concrete::Command> = parse_commands_from_file(args.in_file_path);

    if let Some(file_path) = args.model_file_path {
        let model = parse_commands_from_file(file_path);
        let mut manager = Manager::new(args.out_file_path, args.seed);
        manager.dump_model_test(&model, &commands);
    } else {
        let mut manager = Manager::new(args.out_file_path, args.seed);

        if args.split && args.perturbation != "none" {
            panic!("split and perturbation are incompatible");
        } else if args.split {
            split_commands(&mut commands, infilepath, args.split_dir.unwrap_or_default());
            return;
        } 
            
        if args.perturbation == "none"{
//          return; 
        }

        if args.perturbation  == "shuffle" {
            shuffle_asserts(&mut commands, manager.seed);
        } else if args.perturbation == "rename" {
            commands = normalize_commands(commands, manager.seed);
        } else if args.perturbation == "sseed" {
            if manager.seed != DEFAULT_SEED {
                let solver_seed = manager.seed as u32;
                manager.dump(&format!("(set-option :random-seed {solver_seed})\n"));
            };
        } else if args.perturbation == "rseed" {
            let smt_seed = manager.seed as u32;
            let sat_seed = (manager.seed >> 32) as u32;
            manager.dump(&format!("(set-option :smt.random_seed {smt_seed})\n"));
            manager.dump(&format!("(set-option :sat.random_seed {sat_seed})\n"));
        } else if args.perturbation  == "lower_shuffle" {
            commands = lower_shuffle_asserts(commands, manager.seed);
        } 
        manager.dump_non_info_commands(&commands);
    }
}

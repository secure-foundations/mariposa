use clap::Parser;
use rand::seq::SliceRandom;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
// use smt2parser::shaking::SymbolCollector;
use core::panic;
use rand::Rng;
use smt2parser::{concrete, renaming, visitors, CommandStream};
use std::collections::{BTreeMap, HashSet};
use std::fs::File;
use std::io::{stdout, BufRead, BufReader, BufWriter, Write};
use std::vec;
mod tree_shake;
mod core_export;
mod tree_rewrite;

const DEFAULT_SEED: u64 = 1234567890;

fn convert_comments(file_path: &String) -> Vec<u8> {
    let file = File::open(file_path).unwrap();
    let reader = BufReader::new(file);

    let mut processed_lines: Vec<String> = Vec::new();
    let mut level = 0;
    let mut in_quote = false;
    let mut in_string = false;

    for line in reader.lines() {
        let line = line.unwrap();
        let mut nline = line.clone();
        let mut index = 0;

        for c in line.chars() {
            if c == '\\' {
                index += 1;
                continue;
            }

            if c == '"' {
                in_string = !in_string;
            } else if c == '|' {
                in_quote = !in_quote;
            } else if c == ';' && !in_quote && !in_string {
                // ';' is a comment only if it is not in a quote or string
                if level == 0 {
                    // only convert comment if it is at the top level
                    // filter out the '"'
                    nline = line[index..]
                        .chars()
                        .filter_map(|a| if a == '"' { None } else { Some(a) })
                        .collect::<Vec<char>>()
                        .into_iter()
                        .collect();
                    nline = format!("(set-info :comment \"{}\")", nline);
                }
                // rest of the line is just comment
                break;
            } else if c == '(' {
                level += 1;
            } else if c == ')' {
                level -= 1;
            }
            index += 1;
        }
        processed_lines.push(nline);
    }

    processed_lines.join("\n").as_bytes().to_vec()
}

fn parse_commands_from_file(file_path: &String, convert: bool) -> Vec<concrete::Command> {
    if std::path::Path::new(file_path).exists() == false {
        panic!("[ERROR] input {} does not exist", file_path);
    }

    if convert {
        let content = convert_comments(&file_path);
        let reader = BufReader::new(content.as_slice());
        parse_commands_from_reader(reader)
    } else {
        let file = File::open(file_path).unwrap();
        let reader = BufReader::new(file);
        parse_commands_from_reader(reader)
    }
}

fn parse_commands_from_reader<R>(reader: R) -> Vec<concrete::Command>
where
    R: std::io::BufRead,
{
    let stream = CommandStream::new(reader, concrete::SyntaxBuilder, None);
    let mut builder = renaming::TesterModernizer::new(concrete::SyntaxBuilder);
    let commands = stream.collect::<Result<Vec<_>, _>>().unwrap();
    commands
        .into_iter()
        .map(|c| c.accept(&mut builder).unwrap())
        .collect()
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

fn normalize_symbols(commands: Vec<concrete::Command>, seed: u64) -> Vec<concrete::Command> {
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

fn should_remove_command(command: &concrete::Command) -> bool {
    if let concrete::Command::SetOption {
        keyword: concrete::Keyword(k),
        value: _,
    } = command
    {
        if k == "rlimit"
            || k == "echo"
            || k == "RLIMIT"
            || k == "timeout"
            || k == "TIMEOUT"
            || k == "fixedpoint.TIMEOUT"
        {
            return true;
        }
    }
    if let concrete::Command::GetModel = command {
        return true;
    }
    if let concrete::Command::GetUnsatCore = command {
        return true;
    }
    if let concrete::Command::GetInfo { flag: _ } = command {
        return true;
    }
    return false;
}

fn remove_debug_commands(commands: &mut Vec<concrete::Command>) -> usize {
    let mut depth: u32 = 0;
    let mut max_depth: u32 = 0;

    let mut check_sat_depth_zero = false;
    let mut main_check_sat = false;
    let mut in_debug = false;
    let mut indices = HashSet::new();

    let mut ignored = 0;

    for (index, command) in commands.iter().enumerate() {
        max_depth = std::cmp::max(max_depth, depth);
        match command {
            concrete::Command::Push { level: _ } => {
                depth += 1;
                main_check_sat = false;
                in_debug = false;
                indices.insert(index);
            }
            concrete::Command::Pop { level: _ } => {
                depth -= 1;
                main_check_sat = false;
                in_debug = false;
                indices.insert(index);
            }
            concrete::Command::CheckSat => {
                if !main_check_sat {
                    main_check_sat = true;
                    indices.insert(index);
                } else {
                    assert!(in_debug);
                    ignored += 1;
                }
                if depth == 0 {
                    check_sat_depth_zero = true;
                }
            }
            concrete::Command::GetModel
            | concrete::Command::GetValue { terms: _ }
            | concrete::Command::GetInfo { flag: _ } => {
                in_debug = true;
            }
            _ => {
                if !in_debug {
                    indices.insert(index);
                }
            }
        }
    }

    assert!(!check_sat_depth_zero || max_depth == 0);
    assert!(max_depth <= 1);

    let mut index = 0;
    commands.retain(|_| {
        index += 1;
        indices.contains(&(index - 1))
    });

    return ignored;
}

fn split_commands(
    commands: &mut Vec<concrete::Command>,
    out_file_path: &String,
    remove_debug: bool,
) -> (usize, usize) {
    let mut ignored = 0;

    if remove_debug {
        ignored = remove_debug_commands(commands);
    }

    // also remove target commands
    commands.retain(|command| !should_remove_command(command));

    let mut depth = 0;
    let mut stack = Vec::new();
    stack.push(Vec::new());
    let mut splits = 0;

    let out_file_pre = out_file_path.strip_suffix(".smt2").unwrap();
    // print!("{}", &out_file_pre);

    for command in commands {
        if let concrete::Command::Push { level: _ } = command {
            depth += 1;
            stack.push(Vec::new());
            stack[depth].push(command.clone());
        } else if let concrete::Command::Pop { level: _ } = command {
            depth -= 1;
            stack.pop();
            // stack[depth].push(command.clone());
        } else if let concrete::Command::CheckSat = command {
            splits += 1;
            // write out to file
            let out_file_name = format!("{}.{}.smt2", &out_file_pre, splits);
            let mut manager = Manager::new(Some(out_file_name), 0, 100);
            manager.dump_non_info_commands(&stack.concat());
            manager.dump_non_info_commands(&vec![concrete::Command::CheckSat]);
        } else {
            stack[depth].push(command.clone());
        }
    }
    return (splits, ignored);
}


struct Manager {
    writer: BufWriter<Box<dyn std::io::Write>>,
    seed: u64,
    rng: ChaCha8Rng,
    pattern_threshold: u64,
    removed_patterns: u64,
    total_patterns: u64,
}

impl Manager {
    fn new(out_file_path: Option<String>, seed: u64, pattern_threshold: u64) -> Manager {
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
        Manager {
            writer,
            seed,
            rng: ChaCha8Rng::seed_from_u64(seed),
            pattern_threshold,
            removed_patterns: 0,
            total_patterns: 0,
        }
    }

    fn dump(&mut self, s: &String) {
        write!(self.writer, "{}", s).unwrap();
    }

    fn flush(&mut self) {
        self.writer.flush().unwrap();
    }

    fn dump_non_info_commands(&mut self, commands: &Vec<concrete::Command>) {
        for command in commands {
            if let concrete::Command::SetInfo {
                keyword: concrete::Keyword(k),
                ..
            } = command
            {
                if k != "comment" {
                    continue;
                }
            }
            writeln!(self.writer, "{}", command).unwrap();
        }
    }

    fn remove_pattern_rec_helper(&mut self, curr_term: &mut concrete::Term) {
        match curr_term {
            concrete::Term::Application {
                qual_identifier: _,
                arguments,
            } => {
                for argument in arguments.iter_mut() {
                    self.remove_pattern_rec_helper(argument)
                }
            }
            concrete::Term::Let {
                var_bindings: _,
                term,
            } => self.remove_pattern_rec_helper(&mut *term),
            concrete::Term::Forall { vars: _, term } => self.remove_pattern_rec_helper(&mut *term),
            concrete::Term::Exists { vars: _, term } => self.remove_pattern_rec_helper(&mut *term),
            concrete::Term::Match { term, cases: _ } => self.remove_pattern_rec_helper(&mut *term),
            concrete::Term::Attributes { term, attributes } => {
                self.remove_pattern_rec_helper(term);
                let random = self.rng.gen_range(1..101);
                let mut removed = false;
                if random <= self.pattern_threshold {
                    attributes.retain(|x| x.0 != concrete::Keyword("pattern".to_owned()));
                    self.removed_patterns += 1;
                    removed = true;
                }
                if removed && attributes.len() == 0 {
                    attributes.push((
                        concrete::Keyword("qid".to_owned()),
                        visitors::AttributeValue::Symbol(concrete::Symbol(
                            "mariposa-attribute-placeholder".to_owned(),
                        )),
                    ));
                }
                self.total_patterns += 1;
            }
            concrete::Term::Constant(_) => (),
            concrete::Term::QualIdentifier(_) => (),
        }
    }

    // patterns
    fn remove_patterns(&mut self, commands: &mut Vec<concrete::Command>) {
        commands.iter_mut().for_each(|x| {
            if let concrete::Command::Assert { term } = x {
                self.remove_pattern_rec_helper(term);
            }
        });
        println!(
            "[INFO] removed {} patterns out of {}",
            self.removed_patterns, self.total_patterns
        );
    }
}

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = "mariposa query mutator")]
struct Args {
    /// input file path
    #[arg(short, long)]
    in_file_path: String,

    /// mutation to perform
    #[arg(short, long, default_value = "none")]
    mutation: String,

    /// output file path
    #[arg(short, long)]
    out_file_path: Option<String>,

    /// seed for randomness
    #[arg(short, long, default_value_t = DEFAULT_SEED)]
    seed: u64,

    /// split the input file into multiple files based on check-sats
    #[arg(long, default_value = "false", conflicts_with = "mutation")]
    chop: bool,

    /// remove debug commands from input file (Verus/Dafny)
    #[arg(long, default_value = "false", conflicts_with = "mutation")]
    remove_debug: bool,

    ///the threshold (percentage of) patterns to be removed
    #[arg(long, default_value_t = 100)]
    pattern_threshold: u64,

    /// file containing unsat core (produced by Z3)
    #[arg(long)]
    core_file_path: Option<String>,
}

fn main() {
    let args = Args::parse();

    let in_file_path = args.in_file_path;

    let mut commands: Vec<concrete::Command> = parse_commands_from_file(&in_file_path, args.chop);

    if args.chop {
        if args.mutation != "none" {
            panic!("[ERROR] chop and mutate are incompatible");
        }
        if (&args.out_file_path).is_none() {
            panic!("[ERROR] chop requires an output file path");
        }
        let out_file_path = args.out_file_path.unwrap();
        let (splits, ignored) = split_commands(&mut commands, &out_file_path, args.remove_debug);
        println!(
            "[INFO] {} is split into {} file(s), ignored {} check-sat",
            &in_file_path, splits, ignored
        );
        return;
    }

    let pattern_threshold = args.pattern_threshold;

    if pattern_threshold > 100 {
        panic!("[INFO] pattern threshold must be between 0 and 100");
    }

    let mut manager = Manager::new(args.out_file_path, args.seed, pattern_threshold);

    if args.mutation == "shuffle" {
        shuffle_asserts(&mut commands, manager.seed);
    } else if args.mutation == "rename" {
        commands = normalize_symbols(commands, manager.seed);
    } else if args.mutation == "reseed" {
        let smt_seed = manager.seed as u32;
        let sat_seed = (manager.seed >> 32) as u32;
        manager.dump(&format!("(set-option :smt.random_seed {smt_seed})\n"));
        manager.dump(&format!("(set-option :sat.random_seed {sat_seed})\n"));
    } else if args.mutation == "all" {
        shuffle_asserts(&mut commands, manager.seed);
        commands = normalize_symbols(commands, manager.seed);
        let smt_seed = manager.seed as u32;
        let sat_seed = (manager.seed >> 32) as u32;
        manager.dump(&format!("(set-option :smt.random_seed {smt_seed})\n"));
        manager.dump(&format!("(set-option :sat.random_seed {sat_seed})\n"));
    } else if args.mutation == "unsat-core-label-assert" {
        core_export::label_asserts(&mut commands);
    } else if args.mutation == "unsat-core-reduce-assert" {
        let core_path = args.core_file_path.unwrap();
        commands = core_export::reduce_asserts(commands, core_path)
    } else if args.mutation == "unsat-core-remove-label" {
        core_export::remove_labels(&mut commands);
    } else if args.mutation == "remove-trigger" {
        manager.remove_patterns(&mut commands);
    } else if args.mutation == "parse-only" {
        // parse and do nothing
        return;
    } else if args.mutation == "tree-shake" {
        commands = tree_shake::tree_shake(commands);
    } else if args.mutation == "tree-rewrite" {
        commands = tree_rewrite::tree_rewrite(commands);
    } else if args.mutation == "remove-unused" {
        commands = tree_shake::remove_unused_symbols(commands);
    } else if args.mutation == "fun-assert" {
        commands = commands
            .into_iter()
            .map(|x| tree_rewrite::fun_to_assert(x))
            .flatten()
            .collect();
    }

    manager.dump_non_info_commands(&commands);
    manager.flush();
}

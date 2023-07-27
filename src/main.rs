use clap::Parser;
use rand::seq::SliceRandom;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use smt2parser::{concrete, renaming, visitors, CommandStream};
use std::collections::{BTreeMap, HashSet};
use std::fs::File;
use std::io::{stdout, BufRead, BufReader, BufWriter, Write};

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

fn lower_shuffle_asserts(
    mut commands: Vec<concrete::Command>,
    seed: u64,
) -> Vec<concrete::Command> {
    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    let check_sat_index = &commands
        .iter()
        .position(|x| matches!(x, concrete::Command::CheckSat { .. }))
        .unwrap();

    // truncate at the first check-sat
    commands.truncate(*check_sat_index);

    let (mut asserts, mut others): (_, Vec<_>) = commands
        .into_iter()
        .partition(|x| matches!(x, concrete::Command::Assert { .. }));

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

fn is_unsat_core_related(command: &concrete::Command) -> bool {
    if let concrete::Command::SetOption {
        keyword: concrete::Keyword(k),
        value: _,
    } = command
    {
        if k == "produce-unsat-cores" {
            return true;
        }
    }
    if let concrete::Command::GetUnsatCore = command {
        return true;
    }
    return false;
}

fn remove_target_cmds(commands: &mut Vec<concrete::Command>) {
    commands.retain(|command| !should_remove_command(command));
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
            },
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
            },
            concrete::Command::GetModel | 
                concrete::Command::GetValue { terms: _ } =>
            {
                in_debug = true;
            },
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
    commands.retain(|_| { index+=1; indices.contains(&(index-1)) });

    return ignored;
}

fn split_commands(commands: &mut Vec<concrete::Command>, out_file_path: &String, remove_debug: bool) -> (usize, usize) {
    let mut ignored = 0;

    if remove_debug {
        ignored = remove_debug_commands(commands);
    }
    // also remove target commands
    remove_target_cmds(commands);

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
            let mut manager = Manager::new(Some(out_file_name), 0);
            manager.dump_non_info_commands(&stack.concat());
            manager.dump_non_info_commands(&vec![concrete::Command::CheckSat]);
        } else {
            stack[depth].push(command.clone());
        }
    }
    return (splits, ignored);
}

fn name_assert(command: &mut concrete::Command, ct: usize) {
    let concrete::Command::Assert { term } = command else { return; };
    // does assert have attributes?
    if let concrete::Term::Attributes {
        term: _,
        attributes: _,
    } = term
    {
        // if name already exists, don't mess with it
    } else {
        let new_name = "unsat-cores-dump-name-".to_owned() + &ct.to_string();
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

fn name_asserts(commands: &mut Vec<concrete::Command>) {
    commands
        .iter_mut()
        .enumerate()
        .for_each(|(i, x)| name_assert(x, i));
    commands.insert(
        0,
        concrete::Command::SetOption {
            keyword: concrete::Keyword("produce-unsat-cores".to_owned()),
            value: visitors::AttributeValue::Symbol(concrete::Symbol("true".to_owned())),
        },
    );
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
//  commands.push(concrete::Command::GetUnsatCore)
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

// temporary while should_keep_command keeps all non-asserts
fn should_keep_command_noncore(command: &concrete::Command, core: &HashSet<String>) -> bool {
    let concrete::Command::Assert { term } = command else { 
        // excludes check-sats
        if let concrete::Command::CheckSat = command {
            return false;
        }
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
                        return false;
                    }
                }
            }
        }
    }
    return true;
}
fn core_to_hashset(file_path: String) -> HashSet<String> {
    // read lines from file
    let file = File::open(file_path).unwrap();
    let reader = BufReader::new(file);
    let lines = reader.lines().map(|x| x.unwrap());
    // get the last line of the file
    let last_line = lines.last().unwrap();
    // last_line could be timeout -- if so, throw error
    if last_line == "timeout" {
        panic!("file timed out")
    }
    // strip the first and last character
    let last_line = &last_line[1..last_line.len() - 1];
    // split on spaces
    let core: HashSet<String> = last_line.split(" ").map(|x| x.to_owned()).collect();
    return core;
}

fn ensure_no_conflicts(symbols1: HashSet<String>, symbols2: HashSet<String>) {
    // symbols used in commands1 and commands2 should be disjoint
    let intersection: Vec<String> = symbols1.intersection(&symbols2).cloned().collect();
    if intersection.len() > 0 {
        panic!("symbols used in both commands1 and commands2: {:?}", intersection);
    }
}

fn parse_noncore_from_file(commands: Vec<concrete::Command>, file_path: String) -> Vec<concrete::Command> {
    let core = core_to_hashset(file_path);

    // filter out commands that are not in the core
    let new_commands = commands
        .into_iter()
        .filter(|x| should_keep_command_noncore(x, &core))
        .collect::<Vec<concrete::Command>>();
    return new_commands;
}

// return a Vec<String> where each element is the name of an assert from the unsat core
fn parse_core_from_file(
    commands: Vec<concrete::Command>,
    file_path: String,
) -> Vec<concrete::Command> {
    let core = core_to_hashset(file_path);

    // filter out commands that are not in the core
    let new_commands = commands
        .into_iter()
        .filter(|x| should_keep_command(x, &core))
        .collect::<Vec<concrete::Command>>();
    return new_commands;
}

fn clean_name(command: &mut concrete::Command) {
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
                    if name.starts_with("unsat-cores-dump-name-") {
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

fn clean_names(commands: &mut Vec<concrete::Command>) {
    commands.iter_mut().for_each(|x| clean_name(x));
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
        println!("[INFO] {} is split into {} file(s), ignored {} check-sat", &in_file_path, splits, ignored);
        return;
    }

    let mut manager = Manager::new(args.out_file_path, args.seed);

    if args.mutation == "shuffle" {
        shuffle_asserts(&mut commands, manager.seed);
    } else if args.mutation == "rename" {
        commands = normalize_commands(commands, manager.seed);
    } else if args.mutation == "reseed" {
        let smt_seed = manager.seed as u32;
        let sat_seed = (manager.seed >> 32) as u32;
        manager.dump(&format!("(set-option :smt.random_seed {smt_seed})\n"));
        manager.dump(&format!("(set-option :sat.random_seed {sat_seed})\n"));
    } else if args.mutation == "lower_shuffle" {
        commands = lower_shuffle_asserts(commands, manager.seed);
    } else if args.mutation == "all" {
        shuffle_asserts(&mut commands, manager.seed);
        commands = normalize_commands(commands, manager.seed);
        let smt_seed = manager.seed as u32;
        let sat_seed = (manager.seed >> 32) as u32;
        manager.dump(&format!("(set-option :smt.random_seed {smt_seed})\n"));
        manager.dump(&format!("(set-option :sat.random_seed {sat_seed})\n"));
    } else if args.mutation == "unsat-core" {
        name_asserts(&mut commands);
    } else if args.mutation == "minimize-query" {
        commands = parse_core_from_file(commands, args.core_file_path.unwrap());
        // minimize-query will now also clean names by default
        // cleans names that were put in by mariposa
        clean_names(&mut commands);
        // remove produce unsat core at top and get-unsat-core from the bottom
        commands = commands[1..commands.len() - 1].to_vec();
    } else if args.mutation == "clean-names" {
        clean_names(&mut commands);
    } else if args.mutation == "unsat-core-alpha-rename" { 
        // given core file + primed original file, produce a new file with unsat
        // core combined with a random subset of the original file (alpha renamed so
        // no definitions conflict with the unsat core file)

        // remove produce unsat core at top and get-unsat-core from the bottom
        commands.retain(|command| !is_unsat_core_related(command));

        let mut noncore_commands = parse_noncore_from_file(commands.clone(), args.core_file_path.clone().unwrap());
        // cleans names put in by mariposa
        clean_names(&mut noncore_commands);
        noncore_commands = normalize_commands(noncore_commands, manager.seed);

        // get symbols from noncore commands
        let mut noncore_symbol_tracker = renaming::SymbolTracker::new(concrete::SyntaxBuilder);
        noncore_commands = noncore_commands
            .into_iter()
            .map(|c| c.accept(&mut noncore_symbol_tracker).unwrap())
            .collect();
        let noncore_symbols = noncore_symbol_tracker.symbols();
//      println!("noncore symbols: {:?}", noncore_symbols);
        
        let mut core_commands = parse_core_from_file(commands.clone(), args.core_file_path.clone().unwrap());
        // cleans names put in by mariposa
        clean_names(&mut core_commands);

        // get symbols from core commands
        let mut core_symbol_tracker = renaming::SymbolTracker::new(concrete::SyntaxBuilder);
        core_commands = core_commands
            .into_iter()
            .map(|c| c.accept(&mut core_symbol_tracker).unwrap())
            .collect();
        let core_symbols = core_symbol_tracker.symbols();
//      println!("core symbols: {:?}", core_symbols);
        
        ensure_no_conflicts(noncore_symbols.clone(), core_symbols.clone());
        // combine commands somehow...
        commands = [noncore_commands, core_commands].concat();
        clean_names(&mut commands);
    } 

    manager.dump_non_info_commands(&commands);
}

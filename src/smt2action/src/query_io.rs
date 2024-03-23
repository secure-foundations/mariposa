use smt2parser::{concrete, renaming, CommandStream};
use std::io::{stdout, BufRead, BufReader, BufWriter, Write};
use std::{collections::HashSet, fs::File};

const QID_PREFIX: &str = "mariposa_qid_";

fn should_remove_command(command: &concrete::Command) -> bool {
    match command {
        concrete::Command::Assert { .. }
        | concrete::Command::CheckSat
        | concrete::Command::DeclareConst { .. }
        | concrete::Command::DeclareDatatype { .. }
        | concrete::Command::DeclareDatatypes { .. }
        | concrete::Command::DeclareFun { .. }
        | concrete::Command::DeclareSort { .. }
        | concrete::Command::DefineFun { .. }
        | concrete::Command::Push { .. }
        | concrete::Command::Pop { .. } => false,
        concrete::Command::GetModel
        | concrete::Command::GetUnsatCore
        | concrete::Command::Echo { .. }
        | concrete::Command::Exit
        | concrete::Command::GetInfo { .. }
        | concrete::Command::GetOption { .. } => true,
        concrete::Command::SetOption {
            keyword: concrete::Keyword(k),
            value: _,
        } => {
            k == "rlimit"
                || k == "RLIMIT"
                || k == "timeout"
                || k == "TIMEOUT"
                || k == "fixedpoint.TIMEOUT"
        }
        concrete::Command::SetInfo {
            keyword: concrete::Keyword(k),
            ..
        } => k != "comment",
        concrete::Command::SetLogic { .. } => false,
        _ => {
            panic!("unexpected command: {:?}", command)
        }
    }
}

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
            }
            if c == '(' {
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

struct ParseResult {
    commands: Vec<concrete::Command>,
    plain_total: usize,
}

pub fn parse_commands_from_file(
    file_path: &String,
    keep_comments: bool,
) -> (Vec<concrete::Command>, usize) {
    if !std::path::Path::new(file_path).exists() {
        return (vec![], usize::MAX);
    }

    let mut commands = if keep_comments {
        let content = convert_comments(&file_path);
        let reader = BufReader::new(content.as_slice());
        parse_commands_from_reader(reader)
    } else {
        let file = File::open(file_path).unwrap();
        let reader = BufReader::new(file);
        parse_commands_from_reader(reader)
    };

    let plain_total = commands.len();
    commands.retain(|command| !should_remove_command(command));
    (commands, plain_total)
}

// pub fn format_check_file(file_path: &String) -> bool {
//     let file = File::open(file_path).unwrap();
//     let reader = BufReader::new(file);
//     for line in reader.lines() {
//         let line = line.unwrap();
//         if !line.starts_with("(") {
//             return false;
//         }
//     }
//     true
// }

pub fn find_goal_command_index(commands: &Vec<concrete::Command>) -> usize {
    let mut i = commands.len() - 1;
    // TODO: more robust pattern matching?
    while i > 0 {
        let command = &commands[i];
        if let concrete::Command::Assert { term: _ } = command {
            if let concrete::Command::CheckSat = &commands[i + 1] {
                // break;
            } else {
                panic!("expected check-sat after the goal assert");
            }
            break;
        }
        i -= 1;
    }
    i
}

pub fn truncate_commands(commands: &mut Vec<concrete::Command>) {
    let i = find_goal_command_index(commands);
    commands.truncate(i + 1);
}

pub struct QueryPrinter {
    writer: BufWriter<Box<dyn std::io::Write>>,
    out_file_path: Option<String>,
    dirty: bool,
    pretty: bool,
}

impl QueryPrinter {
    pub fn new(out_file_path: Option<String>) -> QueryPrinter {
        let writer: BufWriter<Box<dyn std::io::Write>> = match &out_file_path {
            Some(path) => {
                let path = std::path::Path::new(&path);
                let prefix = path.parent().unwrap();
                std::fs::create_dir_all(prefix).unwrap();
                let file = File::create(path).unwrap();
                BufWriter::new(Box::new(file))
            }
            None => BufWriter::new(Box::new(stdout().lock())),
        };
        QueryPrinter {
            writer,
            out_file_path,
            dirty: false,
            pretty: false,
        }
    }

    fn write(&mut self, s: &String) {
        self.dirty = true;
        write!(self.writer, "{}", s).unwrap();
    }

    pub fn dump_commands(&mut self, commands: &Vec<concrete::Command>) {
        self.dirty = true;
        for command in commands {
            writeln!(self.writer, "{}", command).unwrap();
        }
    }
}

impl Drop for QueryPrinter {
    fn drop(&mut self) {
        self.writer.flush().unwrap();

        if !self.dirty && self.out_file_path.is_some() {
            std::fs::remove_file(self.out_file_path.as_ref().unwrap()).unwrap();
        }
    }
}

fn remove_debug_commands(commands: &mut Vec<concrete::Command>) -> (usize, usize) {
    let mut depth: u32 = 0;
    let mut max_depth: u32 = 0;

    let mut check_sat_depth_zero = false;
    let mut skip = false;

    let mut included_indices = HashSet::new();
    let mut included_checks = 0;
    let mut skipped_checks = 0;

    for (index, command) in commands.iter().enumerate() {
        max_depth = std::cmp::max(max_depth, depth);
        match command {
            concrete::Command::Push { level: _ } => {
                depth += 1;
                // not expecting nested push after a check-sat
                assert!(skip == false);
                included_indices.insert(index);
            }
            concrete::Command::Pop { level: _ } => {
                depth -= 1;
                // reset skip flag
                skip = false;
                included_indices.insert(index);
            }
            concrete::Command::CheckSat => {
                if !skip {
                    skip = true;
                    included_indices.insert(index);
                    included_checks += 1;
                } else {
                    skipped_checks += 1;
                }

                if depth == 0 {
                    check_sat_depth_zero = true;
                }
            }
            _ => {
                if !skip {
                    included_indices.insert(index);
                }
            }
        }
    }

    assert!(!check_sat_depth_zero || max_depth == 0);
    assert!(max_depth <= 1);

    let mut index = 0;
    commands.retain(|_| {
        index += 1;
        included_indices.contains(&(index - 1))
    });

    (included_checks, skipped_checks)
}

pub fn split_commands(
    mut commands: Vec<concrete::Command>,
    out_file_path: &String,
) -> (usize, usize) {
    let (included_checks, skipped_checks) = remove_debug_commands(&mut commands);

    let mut depth = 0;
    let mut stack = Vec::new();
    stack.push(Vec::new());
    let mut splits = 0;

    let out_file_pre = out_file_path.strip_suffix(".smt2").unwrap();

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

            let out_file_name = if included_checks == 1 {
                format!("{}.smt2", &out_file_pre)
            } else {
                format!("{}.{}.smt2", &out_file_pre, splits)
            };

            // write out to file
            let mut printer = QueryPrinter::new(Some(out_file_name));
            printer.dump_commands(&stack.concat());
            printer.dump_commands(&vec![concrete::Command::CheckSat]);
        } else {
            stack[depth].push(command.clone());
        }
    }
    assert!(splits == included_checks);
    (included_checks, skipped_checks)
}

fn add_missing_qids_rec(cur_term: &mut concrete::Term, count: &mut usize, enable: bool) {
    match cur_term {
        concrete::Term::Application {
            qual_identifier: _,
            arguments,
        } => {
            for argument in arguments.iter_mut() {
                add_missing_qids_rec(argument, count, false)
            }
        }
        concrete::Term::Let { var_bindings, term } => {
            for var_binding in var_bindings.iter_mut() {
                add_missing_qids_rec(&mut var_binding.1, count, false)
            }
            add_missing_qids_rec(&mut *term, count, false)
        }
        concrete::Term::Forall { vars: _, term } => {
            // TODO: maybe refactor 
            if !matches!(&**term, concrete::Term::Attributes { .. }) {
                // this is for the case where the quantified term has no attributes
                let mut temp = Box::new(concrete::Term::Constant(concrete::Constant::String("".to_string())));
                std::mem::swap(term, &mut temp);
                **term = concrete::Term::Attributes {
                    term: temp,
                    attributes: vec![],
                };
            }
            add_missing_qids_rec(&mut *term, count, true)
        },
        concrete::Term::Exists { vars: _, term } => {
            if !matches!(&**term, concrete::Term::Attributes { .. }) {
                // this is for the case where the quantified term has no attributes
                let mut temp = Box::new(concrete::Term::Constant(concrete::Constant::String("".to_string())));
                std::mem::swap(term, &mut temp);
                **term = concrete::Term::Attributes {
                    term: temp,
                    attributes: vec![],
                };
            }
            add_missing_qids_rec(&mut *term, count, true)
        },
        concrete::Term::Match { term, cases: _ } => add_missing_qids_rec(&mut *term, count, false),
        concrete::Term::Attributes { term, attributes } => {
            add_missing_qids_rec(term, count, false);
            let mut enable = enable;
            attributes.iter().for_each(|f| {
                let concrete::Keyword(k) = &f.0;
                if k == "qid" {
                    enable = false;
                }
            });
            if enable {
                attributes.push((
                    concrete::Keyword("qid".to_owned()),
                    concrete::AttributeValue::Symbol(concrete::Symbol(format!(
                        "{}{}",
                        QID_PREFIX, count
                    ))),
                ));
                *count += 1;
            }
        }
        concrete::Term::Constant(_) => (),
        concrete::Term::QualIdentifier(_) => (),
    }
}

pub fn add_missing_qids(commands: &mut Vec<concrete::Command>) {
    let mut qid = 0;
    for command in commands.iter_mut() {
        match command {
            concrete::Command::Assert { term } => {
                add_missing_qids_rec(term, &mut qid, false);
            }
            _ => {}
        }
    }
}

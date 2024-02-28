use std::{process::exit, str::FromStr};
use strum::{EnumMessage, IntoEnumIterator};
use strum_macros::{Display, EnumIter, EnumMessage, EnumString};

use clap::Parser;
// use pattern_removal::remove_patterns;
use smt2parser::{concrete, renaming, visitors, CommandStream};

// use std::collections::{BTreeMap, HashSet};
// use std::vec;
// mod pretty_print;
// mod term_rewrite_flat;
// mod term_rewrite_label;
// mod term_rewrite_let;
// mod term_rewrite_prop;
// mod pattern_removal;
mod core_export;
mod query_io;
mod query_mutate;
mod term_match;

mod tree_shake;
mod tree_shake_idf;

const DEFAULT_SEED: u64 = 1234567890;

#[derive(Display, EnumIter, PartialEq, EnumString, EnumMessage)]
enum Action {
    #[strum(
        serialize = "check",
        message = "check the query can be parsed (do nothing if no error)"
    )]
    Check,

    #[strum(serialize = "format", message = "parse and format the query")]
    Format,

    #[strum(
        serialize = "split",
        message = "split the query based on check-sat command(s)"
    )]
    Split,

    #[strum(serialize = "shuffle", message = "shuffle the assertions in the query")]
    Shuffle,

    #[strum(
        serialize = "rename",
        message = "rename the global symbols in the query"
    )]
    Rename,

    #[strum(
        serialize = "reseed",
        message = "set query option to reseed the random number"
    )]
    Reseed,

    #[strum(
        serialize = "compose",
        message = "compose (shuffle, rename, reseed) mutations"
    )]
    Compose,

    #[strum(
        serialize = "label-core",
        message = "label query assertions for (z3) unsat core log"
    )]
    LabelCore,

    #[strum(
        serialize = "reduce-core",
        message = "reduce the query based on (z3) unsat core log"
    )]
    ReduceCore,

    #[strum(
        serialize = "shake",
        message = "prune the query using the shake algorithm"
    )]
    Shake,

    // #[strum(
    //     serialize = "convert",
    //     message = "convert the query file from z3 to cvc5 compatible format"
    // )]
    // Convert,

    #[strum(serialize = "help", message = "get help on the allowed actions")]
    Help,
}

fn print_actions_help() {
    println!("--action option should be set to one of the following:");
    for a in Action::iter() {
        println!("\t{}: {}", a, a.get_message().unwrap());
    }
}

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = "mariposa query processor")]
struct Args {
    /// input query path
    #[arg(short, long)]
    in_query_path: String,

    /// output query path
    #[arg(short, long)]
    out_query_path: Option<String>,

    /// action to perform
    #[arg(short, long, default_value = "check")]
    action: String,

    /// convert comments into set-info (limited support)
    #[arg(long, default_value_t = false)]
    convert_comments: bool,

    // /// remove debug commands (limited support)
    // #[arg(long, default_value_t = true)]
    // remove_debug: bool,
    /// lower the asserts to check-sat (experimental)
    #[arg(long, default_value_t = false)]
    lower_asserts: bool,

    /// seed for randomness
    #[arg(long, default_value_t = DEFAULT_SEED)]
    seed: u64,

    /// (z3) unsat core log path (not a query!)
    #[arg(long)]
    core_log_path: Option<String>,

    /// the threshold (percentage of) patterns to be removed
    #[arg(long, default_value_t = 100.0)]
    pattern_threshold: f32,

    /// the max depth of tree-shake
    #[arg(long, default_value_t = u32::MAX)]
    shake_max_depth: u32,

    #[arg(long)]
    shake_debug: bool,

    #[arg(long, default_value_t = 1)]
    shake_init_strategy: u32,

    #[arg(long, default_value_t = 100)]
    shake_max_symbol_frequency: usize,

    /// file to log the shake depth
    #[arg(long)]
    shake_log_path: Option<String>,
    // /// file to log the symbol score
    // #[arg(long)]
    // symbol_score_path: Option<String>,
}

fn parse_action(args: &Args) -> Action {
    let action = Action::from_str(&args.action);

    if action.is_err() {
        println!("error: unrecognized action: {}", &args.action);
        print_actions_help();
        exit(1);
    }

    action.unwrap()
}

fn parse_query(args: &Args) -> (Vec<concrete::Command>, usize) {
    let (commands, plain_total) =
        query_io::parse_commands_from_file(&args.in_query_path, args.convert_comments);

    if plain_total == usize::MAX {
        println!("error: no such query file {}", args.in_query_path);
        exit(1);
    }

    if commands.is_empty() {
        println!("error: no command found in the query");
        exit(1);
    }

    (commands, plain_total)
}

fn main() {
    let args = Args::parse();
    let action = parse_action(&args);

    if action == Action::Help {
        print_actions_help();
        return;
    }

    let (mut commands, plain_total) = parse_query(&args);

    if action == Action::Check {
        println!(
            "query file parsed, {}/{} commands kept",
            commands.len(),
            plain_total
        );
        return;
    }

    if action == Action::Split {
        if args.out_query_path.is_none() {
            println!("error: split action requires an output query path");
            exit(1);
        }

        let (included_checks, skipped_checks) =
            query_io::split_commands(commands, &args.out_query_path.unwrap());

        println!(
            "query file {} check-sat command(s) ignored, rest is split into {} file(s)",
            skipped_checks, included_checks
        );
        return;
    }

    let mut printer = query_io::QueryPrinter::new(args.out_query_path.clone());

    if action == Action::Format {
        printer.dump_commands(&commands);
        return;
    }

    match action {
        Action::Shuffle => {
            query_mutate::shuffle_commands(&mut commands, args.seed, args.lower_asserts);
        }
        Action::Rename => {
            query_mutate::rename_symbols(&mut commands, args.seed);
        }
        Action::Compose => {
            query_mutate::shuffle_commands(&mut commands, args.seed, args.lower_asserts);
            query_mutate::rename_symbols(&mut commands, args.seed);
        }
        Action::LabelCore => {
            core_export::label_asserts(&mut commands);
        }
        Action::ReduceCore => {
            if args.core_log_path.is_none() {
                println!("error: reduce-core requires a (z3) core log file");
                exit(1);
            }
            let core_file_path = args.core_log_path.unwrap();
            if !core_export::reduce_asserts(&mut commands, &core_file_path) {
                println!(
                    "error: nonexistent or empty (z3) core log file {}",
                    core_file_path
                );
                exit(1);
            }
        }
        Action::Shake => {
            assert!(args.shake_init_strategy < 2);
            assert!(args.shake_max_symbol_frequency <= 100);
            commands = tree_shake::tree_shake(
                commands,
                args.shake_max_depth,
                args.shake_max_symbol_frequency,
                args.shake_init_strategy,
                args.shake_log_path,
                args.shake_debug,
            );
        }
        _ => {
            panic!("unimplemented action: {}", action);
        }
    }

    printer.dump_commands(&commands);

    // } else if args.action == "reseed" {
    //     let smt_seed = manager.seed as u32;
    //     let sat_seed = (manager.seed >> 32) as u32;
    //     manager.dump(&format!("(set-option :smt.random_seed {smt_seed})\n"));
    //     manager.dump(&format!("(set-option :sat.random_seed {sat_seed})\n"));
    // } else if args.action == "remove-trigger" {
    //     // manager.remove_patterns(&mut commands);
    //     remove_patterns(&mut commands, manager.seed, pattern_threshold);
    // } else if args.action == "tree-shake-idf" {
    //     let (cmd_freq, use_cmd_count) =
    //         tree_shake_idf::count_commands_symbol_frequency(&commands, false);
    //     let mut symbols: Vec<_> = cmd_freq.iter().collect();
    //     symbols.sort_by(|a, b| b.1.cmp(a.1));
    //     manager.dump(&format!("MARIPOSA_USE_CMD_COUNT {}\n", use_cmd_count));
    //     for (symbol, count) in symbols {
    //         manager.dump(&format!(
    //             "{} {} {}\n",
    //             symbol,
    //             count,
    //             count * 100 / use_cmd_count
    //         ));
    //     }
    //     return;
    // } else if args.action == "tree-rewrite" {
    //     commands = tree_rewrite::tree_rewrite(commands);
    // } else if args.action == "remove-unused" {
    //     commands = tree_shake::remove_unused_symbols(commands);
    // } else {
    //     panic!("[ERROR] unknown action {}", args.action);
    // }
}

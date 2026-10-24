use std::{collections::BTreeSet, env};

use hemlis_lib::review::{self, ReviewOptions};
use hemlis_lib::{list_warnings, parse_and_resolve_names, parse_modules, version, Flag as LibFlag};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
enum Flag {
    Resolve,
    Parse,
    Version,
    Warnings,
    Review,
}

/// Options that take a value in the following argument.
#[derive(Debug, Clone, Copy)]
enum Pending {
    Config,
    Rule,
    BeamEdges,
}

fn main() {
    let mut flags = BTreeSet::new();
    let mut lib_flags = BTreeSet::new();
    let mut review = ReviewOptions::default();
    let mut files = Vec::new();
    let mut parsing_options = true;
    let mut pending: Option<Pending> = None;
    for arg in env::args().skip(1) {
        if let Some(p) = pending.take() {
            match p {
                Pending::Config => review.config = Some(arg),
                Pending::Rule => review.rules.push(arg),
                Pending::BeamEdges => review.beam_edges = Some(arg),
            }
            continue;
        }
        if arg == "--" {
            parsing_options = true;
            continue;
        }
        if parsing_options && arg.starts_with("-") && arg != "-" {
            match arg.as_ref() {
                "-t" | "--tokens" => lib_flags.insert(LibFlag::Tokens),
                "-a" | "--tree" => lib_flags.insert(LibFlag::Tree),
                "-n" | "--names" => lib_flags.insert(LibFlag::Usages),
                "-e" | "--exports" => lib_flags.insert(LibFlag::Exports),
                "-i" | "--imports" => lib_flags.insert(LibFlag::Imports),
                "-x" | "--xx" => lib_flags.insert(LibFlag::Resolved),
                "-f" | "--format" => lib_flags.insert(LibFlag::Format),
                "-w" | "--write" => lib_flags.insert(LibFlag::Write),
                "-c" | "--check" => lib_flags.insert(LibFlag::Check),
                "--ignore-missing" => lib_flags.insert(LibFlag::IgnoreMissing),
                "-r" | "--resolve" => flags.insert(Flag::Resolve),
                "-p" | "--parse" => flags.insert(Flag::Parse),
                "-v" | "--version" => flags.insert(Flag::Version),
                "-W" | "--warnings" => flags.insert(Flag::Warnings),
                // `hemlis --review [--config F] [--rule R]... [--module-rules-only] [--json]
                //                 [--beam-edges F] [--update-baseline] [--list-rules] [files...]`
                "--review" => flags.insert(Flag::Review),
                "--config" => {
                    pending = Some(Pending::Config);
                    true
                }
                "--rule" => {
                    pending = Some(Pending::Rule);
                    true
                }
                "--beam-edges" => {
                    pending = Some(Pending::BeamEdges);
                    true
                }
                "--module-rules-only" => {
                    review.module_rules_only = true;
                    true
                }
                "--json" => {
                    review.json = true;
                    true
                }
                "--update-baseline" => {
                    review.update_baseline = true;
                    true
                }
                "--list-rules" => {
                    review.list_rules = true;
                    true
                }
                _ => {
                    eprintln!("Not a valid argument {} - aborting", arg);
                    continue;
                }
            };
        } else {
            parsing_options = false;
            files.push(arg);
        }
    }
    if let Some(p) = pending {
        eprintln!("Missing value for {:?} - aborting", p);
        std::process::exit(review::EXIT_ERROR);
    }

    if flags.contains(&Flag::Version) {
        println!("version: {}", version());
        return;
    }
    if flags.contains(&Flag::Review) {
        std::process::exit(review::run_cli(review, files));
    }
    if flags.contains(&Flag::Warnings) {
        list_warnings(files);
        return;
    }
    if flags.contains(&Flag::Resolve) {
        parse_and_resolve_names(lib_flags, files);
    } else {
        parse_modules(lib_flags, files);
    }
}

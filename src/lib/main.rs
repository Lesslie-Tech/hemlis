use std::{collections::BTreeSet, env};

use hemlis_lib::{Flag as LibFlag, parse_and_resolve_names, parse_modules, version};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
enum Flag {
    Resolve,
    Parse,
    Version,
}

fn main() {
    let mut flags = BTreeSet::new();
    let mut lib_flags = BTreeSet::new();
    let mut files = Vec::new();
    let mut parsing_options = true;
    for arg in env::args().skip(1) {
        if arg == "--" {
            parsing_options = true;
            continue;
        }
        if parsing_options && arg.starts_with("-") {
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
                "-r" | "--resolve" => flags.insert(Flag::Resolve),
                "-p" | "--parse" => flags.insert(Flag::Parse),
                "-v" | "--version" => flags.insert(Flag::Version),
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

    if flags.contains(&Flag::Version) {
        println!("version: {}", version());
        return;
    }
    if flags.contains(&Flag::Resolve) {
        parse_and_resolve_names(lib_flags, files);
    } else {
        parse_modules(lib_flags, files);
    }
}

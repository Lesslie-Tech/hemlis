use std::{collections::BTreeSet, env};

use hemlis_lib::{Flag as LibFlag, list_warnings, parse_and_resolve_names, parse_modules, version};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
enum Flag {
    Resolve,
    Parse,
    Version,
    Warnings,
}

const USAGE: &str = "\
Usage: hemlis [OPTIONS] <FILES>...

Options:
  -f, --format          Format files and print the result
  -w, --write           With -f: write formatted output back to the files
  -c, --check           With -f: check formatting without changing files
      --ignore-missing  With -f -c: ignore files that don't exist
  -r, --resolve         Parse and resolve names across modules
  -p, --parse           Parse only (default)
  -W, --warnings        List style warnings for the files
  -t, --tokens          Dump tokens
  -a, --tree            Dump the syntax tree
  -n, --names           Dump name usages
  -e, --exports         Dump exports
  -i, --imports         Dump imports
  -x, --xx              Dump resolved names
  -v, --version         Print version
  -h, --help            Print this help

Use `-` as a file to read from stdin, and `--` to end option parsing.
";

fn main() {
    if env::args().len() == 1 {
        print!("{USAGE}");
        return;
    }
    let mut flags = BTreeSet::new();
    let mut lib_flags = BTreeSet::new();
    let mut files = Vec::new();
    let mut parsing_options = true;
    for arg in env::args().skip(1) {
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
                "-h" | "--help" => {
                    print!("{USAGE}");
                    return;
                }
                "-W" | "--warnings" => flags.insert(Flag::Warnings),
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

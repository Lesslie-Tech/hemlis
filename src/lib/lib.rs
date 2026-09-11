use std::{
    collections::{BTreeMap, BTreeSet},
    env,
    fs::{self},
    io::{self, Read},
};

use dashmap::DashMap;

pub mod ast;
pub mod lexer;
pub mod nr;
pub mod parser;
pub mod print;
pub mod source;
pub mod style;

use crate::ast::Ast;

pub fn version() -> String {
    let hash = option_env!("GIT_COMMIT").unwrap_or("DEV-BUILD");
    let date = option_env!("BUILT_AT").unwrap_or("NO-BUILD-DATE");
    format!("hemlis-{}-{}", hash, date)
}
pub fn build_builtins() -> (
    DashMap<ast::Ud, Vec<nr::Export>>,
    ast::Ud,
    DashMap<ast::Ud, String>,
) {
    use nr::Scope;
    use nr::Scope::*;
    let names = DashMap::new();

    let prim = ast::Ud::new("Prim");

    // Record labels have no owning module; `nr` tags them with `Ud::zero()`.
    // Register a readable name so name/usage dumps don't try to look up an
    // unregistered sentinel.
    names.insert(ast::Ud::zero(), "<label>".to_string());

    let h = |a: Scope, n: &'static str, s: &'static str| -> (Scope, ast::Ud, ast::Ud) {
        let s_ud = ast::Ud::new(s);
        names.insert(s_ud, s.into());

        let n_ud = ast::Ud::new(n);
        names.insert(n_ud, n.into());
        (a, n_ud, s_ud)
    };

    let compiler_defines = [
        // https://pursuit.purerl.fun/builtins/docs/Prim
        h(Module, "Prim", "Prim"),
        h(Type, "Prim", "Int"),
        h(Type, "Prim", "Number"),
        h(Type, "Prim", "Record"),
        h(Type, "Prim", "Symbol"),
        h(Type, "Prim", "Array"),
        h(Type, "Prim", "Boolean"),
        h(Type, "Prim", "String"),
        h(Type, "Prim", "Char"),
        h(Type, "Prim", "->"),
        h(Type, "Prim", "Function"),
        h(Class, "Prim", "Partial"),
        h(Type, "Prim", "Type"),
        h(Type, "Prim", "Constraint"),
        h(Type, "Prim", "Symbol"),
        h(Type, "Prim", "Row"),
        //
        h(Module, "Prim.Boolean", "Prim.Boolean"),
        h(Type, "Prim.Boolean", "True"),
        h(Type, "Prim.Boolean", "False"),
        //
        h(Module, "Prim.Coerce", "Prim.Coerce"),
        h(Class, "Prim.Coerce", "Coercible"),
        //
        h(Module, "Prim.Ordering", "Prim.Ordering"),
        h(Type, "Prim.Ordering", "Ordering"),
        h(Type, "Prim.Ordering", "LT"),
        h(Type, "Prim.Ordering", "GT"),
        h(Type, "Prim.Ordering", "EQ"),
        //
        h(Module, "Prim.Row", "Prim.Row"),
        h(Class, "Prim.Row", "Union"),
        h(Class, "Prim.Row", "Nub"),
        h(Class, "Prim.Row", "Lacks"),
        h(Class, "Prim.Row", "Cons"),
        //
        h(Module, "Prim.RowList", "Prim.RowList"),
        h(Type, "Prim.RowList", "RowList"),
        h(Type, "Prim.RowList", "Cons"),
        h(Type, "Prim.RowList", "Nil"),
        h(Class, "Prim.RowList", "RowToList"),
        //
        h(Module, "Prim.Symbol", "Prim.Symbol"),
        h(Class, "Prim.Symbol", "Append"),
        h(Class, "Prim.Symbol", "Compare"),
        h(Class, "Prim.Symbol", "Cons"),
        //
        h(Module, "Prim.TypeError", "Prim.TypeError"),
        h(Class, "Prim.TypeError", "Warn"),
        h(Class, "Prim.TypeError", "Fail"),
        h(Type, "Prim.TypeError", "Doc"),
        h(Type, "Prim.TypeError", "Text"),
        h(Type, "Prim.TypeError", "Quote"),
        h(Type, "Prim.TypeError", "QuoteLabel"),
        h(Type, "Prim.TypeError", "Beside"),
        h(Type, "Prim.TypeError", "Above"),
        //
        h(Module, "Prim.Int", "Prim.Int"),
        h(Class, "Prim.Int", "Add"),
        h(Class, "Prim.Int", "Compare"),
        h(Class, "Prim.Int", "Mul"),
        h(Class, "Prim.Int", "ToString"),
        //
    ];

    let exports = DashMap::new();
    for (s, m, n) in compiler_defines {
        exports
            .entry(m)
            .or_insert(Vec::new())
            .push(nr::Export::Just(nr::Name(s, m, n, nr::Visibility::Public)))
    }

    (exports, prim, names)
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub enum Flag {
    Tokens,
    Tree,
    Usages,
    Imports,
    Exports,
    Resolved,
    Format,
    Write,
    Check,
    IgnoreMissing,
}

pub fn parse_and_resolve_names(flags: BTreeSet<Flag>, files: Vec<String>) {
    let (exports, prim, names) = build_builtins();

    let deps: Vec<_> = files
        .iter()
        .enumerate()
        .filter_map(|(i, arg)| match fs::read_to_string(arg.clone()) {
            Err(e) => {
                panic!("ERR: {} {:?}", arg, e);
            }
            Ok(src) => {
                let (l, _comments) = lexer::lex(&src, ast::Fi(i));
                let mut p = parser::P::new(&l, &names);
                if let Some(m) = parser::module(&mut p) {
                    let header = m.0.clone()?;
                    let me = header.0 .0 .0;
                    Some((
                        m,
                        me,
                        header
                            .2
                            .iter()
                            .map(|x| x.from.0 .0)
                            .collect::<BTreeSet<_>>(),
                    ))
                } else {
                    None
                }
            }
        })
        .collect();

    let names_: BTreeMap<_, _> = names
        .iter()
        .map(|k| (*k.key(), k.value().clone()))
        .collect();
    let mut done: BTreeSet<_> = exports.iter().map(|k| *k.key()).collect();
    let mut imports = BTreeMap::new();
    let mut usages = BTreeMap::new();
    let mut resolved = BTreeMap::new();

    let mut errors = Vec::new();
    loop {
        let todo: Vec<_> = deps
            .iter()
            .filter(|(_, me, deps)| (!done.contains(me)) && deps.is_subset(&done))
            .collect();
        // println!("DOING: {:?}", todo.iter().map(|(_, me, _)| names_.get(me).unwrap()).collect::<Vec<_>>());
        if todo.is_empty() {
            if let Some((m, x)) = deps
                .iter()
                .map(|(_, me, deps)| (me, deps.difference(&done).cloned().collect::<Vec<_>>()))
                .find(|(_, aa)| !aa.is_empty())
            {
                println!(
                    "DEADLOCKED! {:?} {:?}",
                    names_.get(m).unwrap(),
                    x.iter().map(|x| names_.get(x).unwrap()).collect::<Vec<_>>()
                );
            }
            break;
        }
        for (m, me, _) in todo.iter() {
            let mut n = nr::N::new(*me, &exports);
            nr::resolve_names(&mut n, prim, m);
            errors.append(&mut n.errors);
            exports.insert(*me, n.exports);
            imports.insert(*me, n.imports);
            for (name, x) in n.global_usages.iter() {
                for (span, sort) in x.iter() {
                    usages
                        .entry(name.module())
                        .or_insert(BTreeMap::new())
                        .entry(*name)
                        .or_insert(BTreeSet::new())
                        .insert((*span, *sort));
                }
            }
            usages.insert(*me, n.references);
            resolved.insert(*me, n.resolved);
        }
        done.append(&mut todo.into_iter().map(|(_, me, _)| *me).collect());
    }
    for e in errors.iter() {
        println!("{:?}", e);
    }

    for (m, name, _) in deps.iter() {
        if flags.contains(&Flag::Tree) {
            let name = names_.get(name).unwrap();
            use std::io::BufWriter;
            let mut buf = BufWriter::new(Vec::new());
            m.show(0, &mut buf).unwrap();
            let inner =
                String::from_utf8(buf.into_inner().map_err(|x| format!("{:?}", x)).unwrap());
            println!("TREE: {}\n{}", name, inner.unwrap());
        }
    }

    if flags.contains(&Flag::Usages) {
        println!("NAMES");
        for (name, uses) in usages.iter() {
            let name = names_.get(name).unwrap();
            if name.starts_with("Prim") {
                continue;
            }
            println!("> {}", name);
            for (nr::Name(s, m, n, v), spans) in uses.iter() {
                println!(
                    "   {:?} {} {} {:?}: {:?}",
                    s,
                    names_.get(m).unwrap(),
                    names_.get(n).unwrap(),
                    v,
                    spans.iter().map(|s| format!("{:?}", s)).collect::<Vec<_>>()
                );
            }
        }
    }

    if flags.contains(&Flag::Resolved) {
        println!("RESOLVED");
        for (name, resolved) in resolved.iter() {
            let name = names_.get(name).unwrap();
            if name.starts_with("Prim") {
                continue;
            }
            println!("> {}", name);
            for ((lo, hi), nr::Name(s, m, n, v)) in resolved.iter() {
                println!(
                    "   {:?}->{:?}: {:?} {} {} {:?}",
                    lo,
                    hi,
                    s,
                    names_.get(m).unwrap(),
                    names_.get(n).unwrap(),
                    v
                );
            }
        }
    }

    if flags.contains(&Flag::Exports) {
        println!("EXPORTS");
        let mut ee = exports
            .iter()
            .map(|a| (*a.key(), a.value().clone()))
            .collect::<Vec<_>>();
        ee.sort();
        for (k, v) in ee.iter() {
            let name = names_.get(k).unwrap();
            if name.starts_with("Prim") {
                continue;
            }
            println!("> {}", name);
            for v in v.iter() {
                println!("   {}", v.show(&|u| names_.get(u).unwrap().clone()));
            }
        }
    }

    if flags.contains(&Flag::Imports) {
        println!("IMPORTS");
        for (k, v) in imports.iter() {
            let name = names_.get(k).unwrap();
            if name.starts_with("Prim") {
                continue;
            }
            println!("> {}", name);
            for (_, v) in v.iter() {
                for (k, v) in v.iter() {
                    println!("   import: {}", names_.get(k).unwrap().clone());
                    for v in v.iter() {
                        println!("     * {}", v.show(&|u| names_.get(u).unwrap().clone()));
                    }
                }
            }
        }
    }
}

/// Reads `arg` as a file path, except `"-"`, which reads stdin instead
/// (matches `purs-tidy` and most other CLI formatters).
fn read_source(arg: &str) -> io::Result<String> {
    if arg == "-" {
        let mut buf = String::new();
        io::stdin().read_to_string(&mut buf)?;
        Ok(buf)
    } else {
        fs::read_to_string(arg)
    }
}

enum CheckOutcome {
    Formatted,
    Unformatted,
    ParseError,
    ReadError(io::Error),
}

fn check_one_file(i: usize, arg: &str) -> CheckOutcome {
    let src = match read_source(arg) {
        Ok(s) => s,
        Err(e) => return CheckOutcome::ReadError(e),
    };

    let (l, comments) = lexer::lex(&src, ast::Fi(i));
    let n = DashMap::new();
    let mut p = parser::P::new(&l, &n);
    let out = parser::module(&mut p);
    if p.i < p.tokens.len() {
        p.errors.push(parser::Serror::NotAtEOF(p.span(), p.peekt()));
    }

    match (&out, p.errors.is_empty()) {
        (Some(m), true) => {
            let formatted = print::print_module(&src, m, &comments);
            if formatted == src {
                CheckOutcome::Formatted
            } else {
                CheckOutcome::Unformatted
            }
        }
        _ => CheckOutcome::ParseError,
    }
}

/// Checks whether each file is already formatted, without writing anything.
/// Files are checked in parallel (one rayon task per file). Prints which
/// files are not formatted and exits with status 1 if any file is
/// unformatted, fails to parse, or fails to read.
fn check_format(files: Vec<String>, ignore_missing: bool) {
    use rayon::iter::{IndexedParallelIterator, IntoParallelRefIterator, ParallelIterator};

    let outcomes: Vec<CheckOutcome> = files
        .par_iter()
        .enumerate()
        .map(|(i, arg)| check_one_file(i, arg))
        .collect();

    let mut any_bad = false;
    for (arg, outcome) in files.iter().zip(outcomes.iter()) {
        match outcome {
            CheckOutcome::Unformatted => {
                println!("not formatted: {}", arg);
                any_bad = true;
            }
            CheckOutcome::ParseError => {
                eprintln!("ERR: {} did not parse cleanly, cannot format", arg);
                any_bad = true;
            }
            CheckOutcome::ReadError(e) if ignore_missing && e.kind() == io::ErrorKind::NotFound => {}
            CheckOutcome::ReadError(e) => {
                let abs = env::current_dir()
                    .map(|cwd| cwd.join(arg).display().to_string())
                    .unwrap_or_else(|_| arg.clone());
                eprintln!(
                    "ERR: could not read '{}': {:?} (looked relative to the current directory, at '{}')",
                    arg, e, abs
                );
                any_bad = true;
            }
            CheckOutcome::Formatted => {}
        }
    }

    if any_bad {
        std::process::exit(1);
    }
}

enum FormatResult {
    Ok { formatted: String, changed: bool },
    ParseError,
}

/// Everything `parse_modules`'s per-file loop needs to print/write for one
/// file, computed in parallel (see `parse_modules`) - only the actual
/// stdout/stderr/disk side effects stay sequential, so output stays in file
/// order the way it did before parallelizing.
struct FileResult {
    read_err: Option<String>,
    format_result: Option<FormatResult>,
    debug_dump: Option<String>,
}

fn process_one_file(flags: &BTreeSet<Flag>, i: usize, arg: &str) -> FileResult {
    use std::io::BufWriter;

    let src = match read_source(arg) {
        Err(e) => {
            return FileResult {
                read_err: Some(e.to_string()),
                format_result: None,
                debug_dump: None,
            };
        }
        Ok(src) => src,
    };

    let (l, comments) = lexer::lex(&src, ast::Fi(i));
    let n = DashMap::new();
    let mut p = parser::P::new(&l, &n);

    let out = parser::module(&mut p);
    if p.i < p.tokens.len() {
        p.errors.push(parser::Serror::NotAtEOF(p.span(), p.peekt()))
    }

    let format_result = flags.contains(&Flag::Format).then(|| {
        match (&out, p.errors.is_empty()) {
            (Some(m), true) => {
                let formatted = print::print_module(&src, m, &comments);
                let changed = formatted != src;
                FormatResult::Ok { formatted, changed }
            }
            _ => FormatResult::ParseError,
        }
    });

    let debug_dump = (flags.contains(&Flag::Tokens) || flags.contains(&Flag::Tree) || !p.errors.is_empty())
        .then(|| {
            let mut buf = BufWriter::new(Vec::new());
            out.show(0, &mut buf).unwrap();
            let inner =
                String::from_utf8(buf.into_inner().map_err(|x| format!("{:?}", x)).unwrap())
                    .map_err(|x| format!("{:?}", x))
                    .unwrap();
            format!(
                "{} of {}\n===\n{}\n===\n{}\n===\n{}",
                p.i,
                p.tokens.len(),
                p.errors
                    .iter()
                    .map(|x| { format!("{:?}\n", x) })
                    .collect::<Vec<_>>()
                    .join("\n"),
                if flags.contains(&Flag::Tokens) {
                    p.tokens
                        .iter()
                        .map(|(a, s)| format!("{:?} {:?}", a, s))
                        .collect::<Vec<_>>()
                        .join("\n")
                } else {
                    "".to_string()
                },
                if flags.contains(&Flag::Tree) { inner } else { "".to_string() }
            )
        });

    FileResult { read_err: None, format_result, debug_dump }
}

pub fn parse_modules(flags: BTreeSet<Flag>, files: Vec<String>) {
    if flags.contains(&Flag::Format) && flags.contains(&Flag::Check) {
        check_format(files, flags.contains(&Flag::IgnoreMissing));
        return;
    }

    use rayon::iter::{IndexedParallelIterator, IntoParallelRefIterator, ParallelIterator};

    // Lexing/parsing/formatting is the expensive part and each file is
    // independent, so it runs in parallel (one rayon task per file, same
    // pattern as `check_format`) - only the actual stdout/stderr/disk
    // effects below stay sequential, in original file order.
    let results: Vec<FileResult> = files
        .par_iter()
        .enumerate()
        .map(|(i, arg)| process_one_file(&flags, i, arg))
        .collect();

    let mut any_bad = false;

    for (arg, result) in files.iter().zip(results) {
        if let Some(e) = result.read_err {
            let abs = env::current_dir()
                .map(|cwd| cwd.join(arg).display().to_string())
                .unwrap_or_else(|_| arg.clone());
            eprintln!(
                "ERR: could not read '{}': {} (looked relative to the current directory, at '{}')",
                arg, e, abs
            );
            if flags.contains(&Flag::Format) {
                any_bad = true;
            }
            continue;
        }

        if let Some(fr) = result.format_result {
            match fr {
                FormatResult::Ok { formatted, changed } => {
                    if flags.contains(&Flag::Write) {
                        if arg == "-" {
                            eprintln!("ERR: cannot use -w with stdin ('-') input");
                            any_bad = true;
                        } else if changed {
                            match fs::write(arg, &formatted) {
                                Ok(()) => println!("formatted {}", arg),
                                Err(e) => {
                                    eprintln!("ERR: {} failed to write: {:?}", arg, e);
                                    any_bad = true;
                                }
                            }
                        }
                    } else {
                        print!("{}", formatted);
                    }
                }
                FormatResult::ParseError => {
                    eprintln!("ERR: {} did not parse cleanly, cannot format", arg);
                    any_bad = true;
                }
            }
        }

        if let Some(dump) = result.debug_dump {
            println!("{}", dump);
        }
    }

    if any_bad {
        std::process::exit(1);
    }
}

//! Whole-project loading and name resolution, shared by every CLI driver that
//! needs more than one file: `-r`, `-W` and `--review`.

use std::collections::{BTreeMap, BTreeSet};
use std::{fs, io};

use rayon::iter::{IndexedParallelIterator, IntoParallelRefIterator, ParallelIterator};

use crate::{ast, build_builtins, lexer, nr, parser};

/// One successfully read and parsed module.
pub struct ParsedModule {
    /// The path exactly as given on the command line.
    pub path: String,
    pub fi: ast::Fi,
    pub src: String,
    pub module: ast::Module,
    pub me: ast::Ud,
    /// The modules this module imports.
    pub deps: BTreeSet<ast::Ud>,
}

/// Everything name resolution knows about a set of files, folded up per module.
pub struct ProjectData {
    /// Parsed modules in command-line order. Files that failed to read or parse are absent.
    pub modules: Vec<ParsedModule>,
    /// Interned name -> text.
    pub names: BTreeMap<ast::Ud, String>,
    pub prim: ast::Ud,
    /// Exports per module, including the compiler builtins.
    pub exports: BTreeMap<ast::Ud, Vec<nr::Export>>,
    pub imports: BTreeMap<ast::Ud, BTreeMap<Option<ast::Ud>, BTreeMap<ast::Ud, Vec<nr::Export>>>>,
    /// Per module: every name the module mentions, plus every reference from other modules to
    /// names defined in it.
    pub usages: BTreeMap<ast::Ud, BTreeMap<nr::Name, BTreeSet<(ast::Span, nr::Sort)>>>,
    pub resolved: BTreeMap<ast::Ud, BTreeMap<(ast::Pos, ast::Pos), nr::Name>>,
    /// Top-level definitions per module, with name, signature and body spans.
    pub defines: BTreeMap<ast::Ud, BTreeMap<nr::Name, nr::DefineSpans>>,
    /// Resolver errors and warnings, in resolution order.
    pub errors: Vec<nr::NRerrors>,
    /// Modules that never resolved because a dependency never became available, with the
    /// missing dependencies. Command-line order.
    pub deadlocked: Vec<(ast::Ud, Vec<ast::Ud>)>,
    /// Files that could not be read, command-line order.
    pub read_errors: Vec<(String, io::Error)>,
}

impl ProjectData {
    pub fn name(&self, ud: ast::Ud) -> &str {
        self.names.get(&ud).map(String::as_str).unwrap_or("?")
    }

    pub fn path_of(&self, fi: ast::Fi) -> Option<&str> {
        self.modules.iter().find(|m| m.fi == fi).map(|m| m.path.as_str())
    }
}

enum ParseOutcome {
    Ok(ParsedModule),
    ReadError(io::Error),
    Skipped,
}

/// Reads, parses and resolves `files` as one project. Modules resolve in import order; a wave
/// of modules whose dependencies are all done resolves in parallel, and the merge afterwards is
/// sequential in command-line order, so the folded maps are identical to a sequential run.
pub fn resolve_project(files: &[String]) -> ProjectData {
    let (exports, prim, names) = build_builtins();

    let outcomes: Vec<ParseOutcome> = files
        .par_iter()
        .enumerate()
        .map(|(i, path)| match fs::read_to_string(path) {
            Err(e) => ParseOutcome::ReadError(e),
            Ok(src) => {
                let fi = ast::Fi(i);
                let (l, _comments) = lexer::lex(&src, fi);
                let mut p = parser::P::new(&l, &names);
                let parsed = parser::module(&mut p).and_then(|module| {
                    let header = module.0.clone()?;
                    let me = header.0 .0 .0;
                    let deps = header.2.iter().map(|x| x.from.0 .0).collect();
                    Some(ParsedModule { path: path.clone(), fi, src, module, me, deps })
                });
                parsed.map_or(ParseOutcome::Skipped, ParseOutcome::Ok)
            }
        })
        .collect();

    let mut modules = Vec::new();
    let mut read_errors = Vec::new();
    for (path, outcome) in files.iter().zip(outcomes) {
        match outcome {
            ParseOutcome::Ok(m) => modules.push(m),
            ParseOutcome::ReadError(e) => read_errors.push((path.clone(), e)),
            ParseOutcome::Skipped => {}
        }
    }

    let mut done: BTreeSet<_> = exports.iter().map(|k| *k.key()).collect();
    let mut imports = BTreeMap::new();
    let mut usages: BTreeMap<ast::Ud, BTreeMap<nr::Name, BTreeSet<(ast::Span, nr::Sort)>>> =
        BTreeMap::new();
    let mut resolved = BTreeMap::new();
    let mut defines = BTreeMap::new();
    let mut errors = Vec::new();

    let mut remaining: Vec<&ParsedModule> = modules.iter().collect();
    loop {
        let (todo, rest): (Vec<_>, Vec<_>) = remaining
            .into_iter()
            .partition(|m| !done.contains(&m.me) && m.deps.is_subset(&done));
        remaining = rest;
        if todo.is_empty() {
            break;
        }
        let wave: Vec<nr::N> = todo
            .par_iter()
            .map(|m| {
                let mut n = nr::N::new(m.me, &exports);
                nr::resolve_names(&mut n, prim, &m.module);
                n
            })
            .collect();
        for (m, mut n) in todo.iter().zip(wave) {
            errors.append(&mut n.errors);
            exports.insert(m.me, n.exports);
            imports.insert(m.me, n.imports);
            for (name, x) in n.global_usages.iter() {
                for (span, sort) in x.iter() {
                    usages
                        .entry(name.module())
                        .or_default()
                        .entry(*name)
                        .or_default()
                        .insert((*span, *sort));
                }
            }
            usages.insert(m.me, n.references);
            resolved.insert(m.me, n.resolved);
            defines.insert(m.me, n.defines);
            done.insert(m.me);
        }
    }

    let deadlocked = remaining
        .iter()
        .map(|m| (m.me, m.deps.difference(&done).copied().collect::<Vec<_>>()))
        .filter(|(_, missing)| !missing.is_empty())
        .collect();

    ProjectData {
        modules,
        names: names.iter().map(|k| (*k.key(), k.value().clone())).collect(),
        prim,
        exports: exports.into_iter().collect(),
        imports,
        usages,
        resolved,
        defines,
        errors,
        deadlocked,
        read_errors,
    }
}

use std::{
    collections::{BTreeMap, BTreeSet},
    fs::{self},
};

use dashmap::DashMap;

pub mod ast;
pub mod lexer;
pub mod nr;
pub mod parser;

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
                let l = lexer::lex(&src, ast::Fi(i as usize));
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

pub fn parse_modules(flags: BTreeSet<Flag>, files: Vec<String>) {
    files
        .iter()
        .enumerate()
        .for_each(|(i, arg)| match fs::read_to_string(arg.clone()) {
            Err(e) => {
                panic!("ERR: {} {:?}", arg, e);
            }
            Ok(src) => {
                use std::io::BufWriter;

                let l = lexer::lex(&src, ast::Fi(i as usize));
                let n = DashMap::new();
                let mut p = parser::P::new(&l, &n);

                let out = parser::module(&mut p);
                if p.i < p.tokens.len() {
                    p.errors.push(parser::Serror::NotAtEOF(p.span(), p.peekt()))
                }

                if flags.contains(&Flag::Tokens)
                    || flags.contains(&Flag::Tree)
                    || !p.errors.is_empty()
                {
                    let mut buf = BufWriter::new(Vec::new());
                    out.show(0, &mut buf).unwrap();
                    let inner = String::from_utf8(
                        buf.into_inner().map_err(|x| format!("{:?}", x)).unwrap(),
                    )
                    .map_err(|x| format!("{:?}", x))
                    .unwrap();
                    println!(
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
                        if flags.contains(&Flag::Tree) {
                            inner
                        } else {
                            "".to_string()
                        }
                    );
                }
            }
        });
}

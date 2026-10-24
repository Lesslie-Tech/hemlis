//! Textual scan of Elixir and Erlang sources for calls into PureScript that the BEAM call graph
//! cannot see: `.exs` scripts are never compiled, and router tuples or `Util.psm(...)` values are
//! dispatched dynamically. Recognised shapes:
//!
//! * `psm(Mod.Path).fun(...)` — function root; `psm(Mod.Path)` alone — module root
//! * `aliasps(Mod.Path, as: A)` then `A.fun(...)` — function root
//! * `:mod_path@ps.fun(...)`, `'mod_path@ps':fun(...)`, `{:mod_path@ps, :fun}` — function root;
//!   a bare `mod_path@ps` — module root
//!
//! A module root exempts every export of that module.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use super::beam;

#[derive(Debug, Default)]
pub struct Roots {
    pub modules: BTreeSet<String>,
    pub functions: BTreeSet<(String, String)>,
}

pub fn scan(globs: &[String], dir: &Path) -> Result<Roots, String> {
    let mut roots = Roots::default();
    for pattern in globs {
        let full = dir.join(pattern);
        let full = full.to_string_lossy().into_owned();
        let paths = glob::glob(&full).map_err(|e| format!("bad glob '{}': {}", full, e))?;
        for entry in paths {
            let path = entry.map_err(|e| format!("glob '{}': {}", full, e))?;
            if !path.is_file() {
                continue;
            }
            let bytes = fs::read(&path).map_err(|e| format!("could not read '{}': {}", path.display(), e))?;
            scan_text(&String::from_utf8_lossy(&bytes), &mut roots);
        }
    }
    Ok(roots)
}

fn is_ident(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

fn is_path(c: char) -> bool {
    is_ident(c) || c == '.'
}

fn starts_upper(s: &str) -> bool {
    s.starts_with(|c: char| c.is_ascii_uppercase())
}

fn starts_lower(s: &str) -> bool {
    s.starts_with(|c: char| c.is_ascii_lowercase())
}

/// The longest prefix of `s` whose chars all satisfy `pred` (ASCII predicates only).
fn take_while(s: &str, pred: fn(char) -> bool) -> &str {
    let end = s.find(|c: char| !pred(c)).unwrap_or(s.len());
    &s[..end]
}

fn last_segment(path: &str) -> String {
    path.rsplit('.').next().unwrap_or(path).to_string()
}

pub fn scan_text(text: &str, roots: &mut Roots) {
    for (idx, _) in text.match_indices("psm(") {
        let rest = &text[idx + 4..];
        let path = take_while(rest, is_path);
        if !starts_upper(path) {
            continue;
        }
        let Some(rest) = rest[path.len()..].strip_prefix(')') else {
            continue;
        };
        if let Some(after_dot) = rest.strip_prefix('.') {
            let fun = take_while(after_dot, is_ident);
            if starts_lower(fun) {
                roots.functions.insert((path.to_string(), fun.to_string()));
                continue;
            }
        }
        roots.modules.insert(path.to_string());
    }

    let mut aliases: Vec<(String, String)> = Vec::new();
    for (idx, _) in text.match_indices("aliasps(") {
        let rest = &text[idx + 8..];
        let path = take_while(rest, is_path);
        if !starts_upper(path) {
            continue;
        }
        let rest = rest[path.len()..].trim_start();
        let alias = match rest.strip_prefix(',').map(str::trim_start).and_then(|r| r.strip_prefix("as:")) {
            Some(r) => take_while(r.trim_start(), is_ident).to_string(),
            None => last_segment(path),
        };
        if starts_upper(&alias) {
            aliases.push((alias, path.to_string()));
        }
    }
    for (alias, module) in aliases {
        let needle = format!("{}.", alias);
        for (idx, _) in text.match_indices(&needle) {
            let preceded_by_path_char = text[..idx].chars().next_back().is_some_and(is_path);
            if preceded_by_path_char {
                continue;
            }
            let fun = take_while(&text[idx + needle.len()..], is_ident);
            if starts_lower(fun) {
                roots.functions.insert((module.clone(), fun.to_string()));
            }
        }
    }

    for (idx, _) in text.match_indices("@ps") {
        let before = &text[..idx];
        let module_start = before
            .char_indices()
            .rev()
            .find(|(_, c)| !is_ident(*c))
            .map(|(i, c)| i + c.len_utf8())
            .unwrap_or(0);
        let module = &before[module_start..];
        if module.is_empty() {
            continue;
        }
        let ps_module = beam::ps_module_name(module);
        let rest = &text[idx + 3..];
        let rest = rest.strip_prefix('\'').unwrap_or(rest);
        let fun = if let Some(r) = rest.strip_prefix('.').or_else(|| rest.strip_prefix(':')) {
            take_while(r, is_ident)
        } else if let Some(r) = rest.strip_prefix(',') {
            r.trim_start().strip_prefix(':').map(|r| take_while(r, is_ident)).unwrap_or("")
        } else {
            ""
        };
        if starts_lower(fun) {
            roots.functions.insert((ps_module, fun.to_string()));
        } else {
            roots.modules.insert(ps_module);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scanned(text: &str) -> Roots {
        let mut r = Roots::default();
        scan_text(text, &mut r);
        r
    }

    #[test]
    fn psm_and_aliasps() {
        let r = scanned(
            r#"
            Util.psm(CM1.Flow).mtls_Elixir.()
            alias psm(unquote(module_name)), as: App
            x = Util.psm(Dev.Totp)
            aliasps(Accountec.Api, as: Acc)
            Acc.listUsers_Elixir(1)
            Foo.Acc.notAlias()
            aliasps(Shell)
            Shell.run()
            "#,
        );
        assert!(r.functions.contains(&("CM1.Flow".into(), "mtls_Elixir".into())));
        assert!(r.functions.contains(&("Accountec.Api".into(), "listUsers_Elixir".into())));
        assert!(r.functions.contains(&("Shell".into(), "run".into())));
        assert!(!r.functions.iter().any(|(_, f)| f == "notAlias"));
        assert!(r.modules.contains("Dev.Totp"));
        assert!(!r.modules.iter().any(|m| m.contains("unquote")));
    }

    #[test]
    fn beam_atoms() {
        let r = scanned(
            r#"
            get "/v1/user", PursApiController, {:api_user@ps, :getUserData_Elixir}
            :shell@ps.run()
            'dev_totp@ps':addSecret(X)
            Module.concat(:accessRight_storage@ps)
            "#,
        );
        assert!(r.functions.contains(&("Api.User".into(), "getUserData_Elixir".into())));
        assert!(r.functions.contains(&("Shell".into(), "run".into())));
        assert!(r.functions.contains(&("Dev.Totp".into(), "addSecret".into())));
        assert!(r.modules.contains("AccessRight.Storage"));
    }
}

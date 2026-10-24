//! `no-unused-exports`: an export that no other module references.
//!
//! A name is used when another module's source references it (directly, through an operator
//! alias, or through qualified `do`/`ado` desugaring, all recorded by the resolver), when the BEAM
//! call graph has a call into it from another module, or when it is a root: named or suffixed in
//! the config, listed explicitly, or found by scanning Elixir/Erlang sources. Values and operators
//! are reported by default; types and classes only with `report-types`, because the compiled
//! code cannot confirm them. Constructors are left to `no-unused-constructors`.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use serde::Deserialize;

use super::{beam, roots, Finding};
use crate::project::{ParsedModule, ProjectData};
use crate::{ast, nr};

pub const NAME: &str = "no-unused-exports";

#[derive(Debug, Default, Deserialize)]
#[serde(default, rename_all = "kebab-case", deny_unknown_fields)]
pub struct Options {
    /// Exports ending in one of these are entry points, e.g. `_Elixir`.
    pub roots_suffixed_by: Vec<String>,
    /// Exports with exactly one of these names are entry points, e.g. `main`.
    pub roots_named: Vec<String>,
    /// `Module.name` entries for dynamic dispatch nothing can see.
    pub extra_roots: Vec<String>,
    /// Module-name globs (`Data.*`) whose exports are never reported.
    pub library_modules: Vec<String>,
    /// File globs, relative to the config, scanned for calls into PureScript (see `roots`).
    pub scan_beam_roots: Vec<String>,
    /// Edge file from xref, relative to the config; `--beam-edges` overrides it.
    pub beam_edges: Option<String>,
    pub report_types: bool,
}

pub struct Outcome {
    pub findings: Vec<Finding>,
    pub warnings: Vec<String>,
}

pub fn check(
    project: &ProjectData,
    opts: &Options,
    config_dir: &Path,
    beam_edges: Option<&Path>,
) -> Outcome {
    let mut warnings = Vec::new();
    let edges = beam_edges.and_then(|path| match beam::BeamEdges::load(path) {
        Ok(edges) => Some(edges),
        Err(e) => {
            warnings.push(format!("{}; continuing without BEAM edges", e));
            None
        }
    });
    let scanned = match roots::scan(&opts.scan_beam_roots, config_dir) {
        Ok(roots) => roots,
        Err(e) => {
            warnings.push(format!("{}; continuing without scanned roots", e));
            roots::Roots::default()
        }
    };

    let mut alias_ops: BTreeMap<nr::Name, Vec<nr::Name>> = BTreeMap::new();
    for (op, target) in project.operator_aliases.iter() {
        alias_ops.entry(*target).or_default().push(*op);
    }
    let extra_roots: BTreeSet<&str> = opts.extra_roots.iter().map(String::as_str).collect();

    let mut findings = Vec::new();
    for m in project.modules.iter() {
        let Some(header) = m.module.0.as_ref() else { continue };
        let Some(export_list) = header.1.as_ref() else { continue };
        let module_name = project.name(m.me);
        if opts.library_modules.iter().any(|g| glob_match(g, module_name))
            || scanned.modules.contains(module_name)
        {
            continue;
        }
        let Some(exports) = project.exports.get(&m.me) else { continue };
        let export_spans = export_spans(export_list);

        let mut seen = BTreeSet::new();
        for export in exports.iter() {
            let name = match export {
                nr::Export::Just(n) => *n,
                nr::Export::ConstructorsAll(t, _, _) | nr::Export::ConstructorsSome(t, _, _) => *t,
            };
            if name.module() != m.me || !seen.insert(name) {
                continue;
            }
            let text = project.name(name.name());
            let kind = match name.scope() {
                nr::Scope::Term if text.starts_with(|c: char| c.is_uppercase()) => continue,
                nr::Scope::Term if text.starts_with(|c: char| c.is_alphabetic() || c == '_') => "value",
                nr::Scope::Term => "operator",
                nr::Scope::Type if opts.report_types => "type",
                nr::Scope::Class if opts.report_types => "class",
                _ => continue,
            };

            let is_root = opts.roots_named.iter().any(|n| n == text)
                || opts.roots_suffixed_by.iter().any(|s| text.ends_with(s.as_str()))
                || extra_roots.contains(format!("{}.{}", module_name, text).as_str())
                || scanned.functions.contains(&(module_name.to_string(), text.to_string()));
            if is_root
                || referenced_elsewhere(project, m, name)
                || alias_ops
                    .get(&name)
                    .is_some_and(|ops| ops.iter().any(|op| referenced_elsewhere(project, m, *op)))
                || edges.as_ref().is_some_and(|e| e.is_used(module_name, text))
            {
                continue;
            }

            let span = export_spans
                .get(&(name.scope(), name.name()))
                .copied()
                .or_else(|| project.defines.get(&m.me)?.get(&name).map(|d| d.name))
                .unwrap_or(ast::Span::Known(m.fi, (0, 0), (0, 0)));
            findings.push(Finding {
                rule: NAME,
                span,
                message: format!("Exported {} `{}` is not used by any other module", kind, text),
            });
        }
    }
    Outcome { findings, warnings }
}

/// Any `Ref` to `name` from a file other than `m`'s.
fn referenced_elsewhere(project: &ProjectData, m: &ParsedModule, name: nr::Name) -> bool {
    project
        .usages
        .get(&name.module())
        .and_then(|u| u.get(&name))
        .is_some_and(|spans| {
            spans.iter().any(|(span, sort)| {
                *sort == nr::Sort::Ref && span.fi().is_some_and(|fi| fi != m.fi)
            })
        })
}

fn export_spans(list: &[ast::Export]) -> BTreeMap<(nr::Scope, ast::Ud), ast::Span> {
    let mut out = BTreeMap::new();
    for e in list {
        let (scope, s) = match e {
            ast::Export::Value(n) => (nr::Scope::Term, n.0),
            ast::Export::Symbol(s) => (nr::Scope::Term, s.0),
            ast::Export::Typ(p) | ast::Export::TypDat(p, _) => (nr::Scope::Type, p.0),
            ast::Export::TypSymbol(s) => (nr::Scope::Type, s.0),
            ast::Export::Class(p) => (nr::Scope::Class, p.0),
            ast::Export::Module(_) => continue,
        };
        out.insert((scope, s.0), s.1);
    }
    out
}

/// `*` matches any run of characters; everything else is literal.
pub fn glob_match(pattern: &str, s: &str) -> bool {
    let parts: Vec<&str> = pattern.split('*').collect();
    if parts.len() == 1 {
        return pattern == s;
    }
    let mut rest = s;
    for (i, part) in parts.iter().enumerate() {
        if i == 0 {
            match rest.strip_prefix(part) {
                Some(r) => rest = r,
                None => return false,
            }
        } else if i == parts.len() - 1 {
            return rest.ends_with(part);
        } else {
            match rest.find(part) {
                Some(at) => rest = &rest[at + part.len()..],
                None => return false,
            }
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::glob_match;

    #[test]
    fn globs() {
        assert!(glob_match("Data.*", "Data.Maybe"));
        assert!(!glob_match("Data.*", "Erl.Data.Maybe"));
        assert!(glob_match("*Test*", "Accountec.ApiTest"));
        assert!(glob_match("Math", "Math"));
        assert!(!glob_match("Math", "Mathematics"));
    }
}

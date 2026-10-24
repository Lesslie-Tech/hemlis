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

#[derive(Debug, Default, Clone, Deserialize)]
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

/// Roots and evidence shared by the project rules: the config roots, the Elixir/Erlang scan and
/// the BEAM call graph.
pub struct Context<'a> {
    pub opts: &'a Options,
    scanned: roots::Roots,
    edges: Option<beam::BeamEdges>,
    extra_roots: BTreeSet<&'a str>,
    pub warnings: Vec<String>,
}

impl<'a> Context<'a> {
    pub fn load(opts: &'a Options, config_dir: &Path, beam_edges: Option<&Path>) -> Self {
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
        Self {
            opts,
            scanned,
            edges,
            extra_roots: opts.extra_roots.iter().map(String::as_str).collect(),
            warnings,
        }
    }

    /// Library modules and modules the Elixir scan names as a whole are never reported.
    pub fn skip_module(&self, module_name: &str) -> bool {
        self.opts.library_modules.iter().any(|g| glob_match(g, module_name))
            || self.scanned.modules.contains(module_name)
    }

    /// Entry points: by name, suffix, explicit list, scanned call, or a BEAM call from another
    /// module.
    pub fn is_root(&self, module_name: &str, text: &str) -> bool {
        self.opts.roots_named.iter().any(|n| n == text)
            || self.opts.roots_suffixed_by.iter().any(|s| text.ends_with(s.as_str()))
            || self.extra_roots.contains(format!("{}.{}", module_name, text).as_str())
            || self.scanned.functions.contains(&(module_name.to_string(), text.to_string()))
            || self.edges.as_ref().is_some_and(|e| e.is_used(module_name, text))
    }
}

/// What kind of thing a name is for the report, or `None` when the rules leave it alone:
/// constructors always, types and classes unless `report-types`.
pub fn reportable_kind(opts: &Options, scope: nr::Scope, text: &str) -> Option<&'static str> {
    match scope {
        nr::Scope::Term if text.starts_with(|c: char| c.is_uppercase()) => None,
        nr::Scope::Term if text.starts_with(|c: char| c.is_alphabetic() || c == '_') => Some("value"),
        nr::Scope::Term => Some("operator"),
        nr::Scope::Type if opts.report_types => Some("type"),
        nr::Scope::Class if opts.report_types => Some("class"),
        _ => None,
    }
}

pub fn check(project: &ProjectData, ctx: &Context) -> Vec<Finding> {
    let mut alias_ops: BTreeMap<nr::Name, Vec<nr::Name>> = BTreeMap::new();
    for (op, target) in project.operator_aliases.iter() {
        alias_ops.entry(*target).or_default().push(*op);
    }

    let mut findings = Vec::new();
    for m in project.modules.iter() {
        let Some(header) = m.module.0.as_ref() else { continue };
        let Some(export_list) = header.1.as_ref() else { continue };
        let module_name = project.name(m.me);
        if ctx.skip_module(module_name) {
            continue;
        }
        let Some(exports) = project.exports.get(&m.me) else { continue };
        let entries = export_entries(export_list);
        let entry_index: BTreeMap<(nr::Scope, ast::Ud), usize> =
            entries.iter().enumerate().map(|(i, e)| ((e.scope, e.ud), i)).collect();

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
            let Some(kind) = reportable_kind(ctx.opts, name.scope(), text) else { continue };

            if ctx.is_root(module_name, text)
                || referenced_elsewhere(project, m, name)
                || alias_ops
                    .get(&name)
                    .is_some_and(|ops| ops.iter().any(|op| referenced_elsewhere(project, m, *op)))
            {
                continue;
            }

            let entry = entry_index.get(&(name.scope(), name.name())).map(|&i| (i, &entries[i]));
            let span = entry
                .map(|(_, e)| e.span)
                .or_else(|| project.defines.get(&m.me)?.get(&name).map(|d| d.name))
                .unwrap_or(ast::Span::Known(m.fi, (0, 0), (0, 0)));
            // Drop the entry together with the separator that joins it to its neighbour. A sole
            // entry stays: an empty export list is a different decision.
            let fix = entry.and_then(|(i, e)| {
                if !e.fixable || entries.len() < 2 {
                    return None;
                }
                let (lo, hi) = if i > 0 {
                    (entries[i - 1].span.hi(), e.span.hi())
                } else {
                    (e.span.lo(), entries[i + 1].span.lo())
                };
                Some(vec![(ast::Span::Known(m.fi, lo, hi), String::new())])
            });
            findings.push(Finding {
                rule: NAME,
                span,
                message: format!("Exported {} `{}` is not used by any other module", kind, text),
                fix,
            });
        }
    }
    findings
}

/// Any `Ref` to `name` from a file other than `m`'s.
pub fn referenced_elsewhere(project: &ProjectData, m: &ParsedModule, name: nr::Name) -> bool {
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

struct Entry {
    scope: nr::Scope,
    ud: ast::Ud,
    span: ast::Span,
    /// The span covers the whole entry, so deleting it is safe. Not the case for `T(..)`, whose
    /// constructor list has no span of its own, nor for `module X`.
    fixable: bool,
}

/// The export list in source order.
fn export_entries(list: &[ast::Export]) -> Vec<Entry> {
    list.iter()
        .map(|e| {
            let (scope, s, fixable) = match e {
                ast::Export::Value(n) => (nr::Scope::Term, n.0, true),
                ast::Export::Symbol(s) => (nr::Scope::Term, s.0, true),
                ast::Export::Typ(p) => (nr::Scope::Type, p.0, true),
                ast::Export::TypDat(p, _) => (nr::Scope::Type, p.0, false),
                ast::Export::TypSymbol(s) => (nr::Scope::Type, s.0, true),
                ast::Export::Class(p) => (nr::Scope::Class, p.0, true),
                ast::Export::Module(m) => (nr::Scope::Module, m.0, false),
            };
            Entry { scope, ud: s.0, span: s.1, fixable }
        })
        .collect()
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

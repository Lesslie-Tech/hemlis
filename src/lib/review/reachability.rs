//! `no-unreachable-definitions` and `no-unused-modules`: what no entry point reaches.
//!
//! Every reference is attributed to the top-level definition whose span contains it, giving
//! definition -> name edges. References outside any definition (instance bodies, derive heads,
//! class member implementations) are roots, as are the configured roots, everything the BEAM
//! graph or the Elixir scan names, and every definition of a library module or of a module
//! without an export list. Liveness is the closure over the edges, following operator aliases to
//! their targets. Unlike `no-unused-exports`, a definition kept alive only by dead code is dead.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use super::unused_exports::{reportable_kind, Context};
use super::Finding;
use crate::project::ProjectData;
use crate::{ast, nr};

pub const UNREACHABLE: &str = "no-unreachable-definitions";
pub const UNUSED_MODULES: &str = "no-unused-modules";

pub struct Liveness {
    pub live: BTreeSet<nr::Name>,
}

struct Index {
    /// Top-level definition spans, sorted by start.
    spans: Vec<(ast::Pos, ast::Pos, nr::Name)>,
    /// The export list's extent, whose references are not uses.
    header: Option<(ast::Pos, ast::Pos)>,
}

impl Index {
    fn enclosing(&self, lo: ast::Pos, hi: ast::Pos) -> Option<nr::Name> {
        self.spans
            .iter()
            .find(|(slo, shi, _)| *slo <= lo && hi <= *shi)
            .map(|(_, _, name)| *name)
    }
}

pub fn compute(project: &ProjectData, ctx: &Context) -> Liveness {
    let mut index: BTreeMap<ast::Fi, Index> = BTreeMap::new();
    for m in project.modules.iter() {
        let mut spans = Vec::new();
        if let Some(defines) = project.defines.get(&m.me) {
            for (name, d) in defines.iter() {
                if name.3 != nr::Visibility::Public || name.module() != m.me {
                    continue;
                }
                let all = std::iter::once(d.name).chain(d.sig).chain(d.body.iter().copied());
                for span in all {
                    if let ast::Span::Known(_, lo, hi) = span {
                        spans.push((lo, hi, *name));
                    }
                }
            }
        }
        spans.sort();
        let header = m.module.0.as_ref().and_then(|h| match (h.5, h.6) {
            (ast::Span::Known(_, lo, _), ast::Span::Known(_, _, hi)) => Some((lo, hi)),
            _ => None,
        });
        index.insert(m.fi, Index { spans, header });
    }

    let mut edges: BTreeMap<nr::Name, Vec<nr::Name>> = BTreeMap::new();
    let mut roots: BTreeSet<nr::Name> = BTreeSet::new();
    for names in project.usages.values() {
        for (name, uses) in names.iter() {
            for (span, sort) in uses.iter() {
                if *sort != nr::Sort::Ref {
                    continue;
                }
                let Some(idx) = span.fi().and_then(|fi| index.get(&fi)) else { continue };
                let (lo, hi) = (span.lo(), span.hi());
                if idx.header.is_some_and(|(hlo, hhi)| hlo <= lo && hi <= hhi) {
                    continue;
                }
                match idx.enclosing(lo, hi) {
                    Some(definition) => edges.entry(definition).or_default().push(*name),
                    None => {
                        roots.insert(*name);
                    }
                }
            }
        }
    }
    for targets in edges.values_mut() {
        let via_alias: Vec<nr::Name> = targets
            .iter()
            .filter_map(|t| project.operator_aliases.get(t).copied())
            .collect();
        targets.extend(via_alias);
    }
    for op in roots.clone() {
        if let Some(target) = project.operator_aliases.get(&op) {
            roots.insert(*target);
        }
    }

    for m in project.modules.iter() {
        let module_name = project.name(m.me);
        let whole_module = ctx.skip_module(module_name)
            || m.module.0.as_ref().is_some_and(|h| h.1.is_none());
        if let Some(defines) = project.defines.get(&m.me) {
            for name in defines.keys() {
                if name.3 != nr::Visibility::Public || name.module() != m.me {
                    continue;
                }
                if whole_module || ctx.is_root(module_name, project.name(name.name())) {
                    roots.insert(*name);
                }
            }
        }
    }

    let mut live = roots.clone();
    let mut queue: VecDeque<nr::Name> = roots.into_iter().collect();
    while let Some(name) = queue.pop_front() {
        if let Some(targets) = edges.get(&name) {
            for t in targets.iter() {
                if live.insert(*t) {
                    queue.push_back(*t);
                }
            }
        }
    }
    Liveness { live }
}

pub fn check_unreachable(project: &ProjectData, ctx: &Context, liveness: &Liveness) -> Vec<Finding> {
    let mut findings = Vec::new();
    for m in project.modules.iter() {
        let Some(header) = m.module.0.as_ref() else { continue };
        let module_name = project.name(m.me);
        if ctx.skip_module(module_name) || header.1.is_none() {
            continue;
        }
        let Some(defines) = project.defines.get(&m.me) else { continue };
        let exported: BTreeSet<nr::Name> = project
            .exports
            .get(&m.me)
            .map(|exports| {
                exports
                    .iter()
                    .map(|e| match e {
                        nr::Export::Just(n) => *n,
                        nr::Export::ConstructorsAll(t, _, _) | nr::Export::ConstructorsSome(t, _, _) => *t,
                    })
                    .collect()
            })
            .unwrap_or_default();
        for (name, d) in defines.iter() {
            if name.3 != nr::Visibility::Public || name.module() != m.me || liveness.live.contains(name) {
                continue;
            }
            let text = project.name(name.name());
            let Some(kind) = reportable_kind(ctx.opts, name.scope(), text) else { continue };
            let note = if exported.contains(name) { ", nor is anything that uses it" } else { "" };
            findings.push(Finding {
                rule: UNREACHABLE,
                span: d.name,
                message: format!("{} `{}` is not reachable from any entry point{}", capitalise(kind), text, note),
                fix: None,
            });
        }
    }
    findings
}

pub fn check_unused_modules(project: &ProjectData, ctx: &Context, liveness: &Liveness) -> Vec<Finding> {
    let mut findings = Vec::new();
    for m in project.modules.iter() {
        let Some(header) = m.module.0.as_ref() else { continue };
        let module_name = project.name(m.me);
        if ctx.skip_module(module_name) || header.1.is_none() {
            continue;
        }
        let Some(defines) = project.defines.get(&m.me) else { continue };
        let mut any = false;
        let mut any_live = false;
        for name in defines.keys() {
            let counts = matches!(name.scope(), nr::Scope::Term | nr::Scope::Type | nr::Scope::Class);
            if name.3 != nr::Visibility::Public || name.module() != m.me || !counts {
                continue;
            }
            any = true;
            if liveness.live.contains(name) {
                any_live = true;
                break;
            }
        }
        if any && !any_live {
            findings.push(Finding {
                rule: UNUSED_MODULES,
                span: header.0 .0 .1,
                message: format!("Module `{}` has no definition reachable from any entry point", module_name),
                fix: None,
            });
        }
    }
    findings
}

fn capitalise(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
        None => String::new(),
    }
}

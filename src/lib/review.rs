//! `hemlis --review`: the review tool. Every finding carries a rule name, a JSON config turns
//! rules on and off, a per-file baseline keeps pre-existing findings from failing the run, and
//! output is text or JSON.

pub mod beam;
pub mod config;
pub mod reachability;
pub mod roots;
pub mod suppress;
pub mod unused_exports;

use std::collections::{BTreeMap, BTreeSet};
use std::io::IsTerminal;
use std::path::PathBuf;
use std::{env, fs, io};

use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use serde::Serialize;

use crate::project::{self, ProjectData};
use crate::style::rule_names as style_rules;
use crate::{ast, nr, source, style};

pub const EXIT_OK: i32 = 0;
pub const EXIT_FINDINGS: i32 = 1;
pub const EXIT_ERROR: i32 = 2;

pub const NO_UNUSED_IMPORTS: &str = "no-unused-imports";
pub const NO_UNUSED_LOCALS: &str = "no-unused-locals";
pub const NO_UNUSED_DEFINITIONS: &str = "no-unused-definitions";
pub const NO_UNUSED_CONSTRUCTORS: &str = "no-unused-constructors";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuleKind {
    /// Looks at one module at a time.
    Module,
    /// Needs the whole project resolved before it can conclude anything.
    Project,
}

pub struct RuleInfo {
    pub name: &'static str,
    pub kind: RuleKind,
    pub description: &'static str,
}

pub const RULES: &[RuleInfo] = &[
    RuleInfo {
        name: style_rules::FORBIDDEN_OPERATOR,
        kind: RuleKind::Module,
        description: "Operators that read backwards, e.g. `=<<` and `<<<`",
    },
    RuleInfo {
        name: style_rules::CONFUSING_MAP_OPERATOR,
        kind: RuleKind::Module,
        description: "Nested-map operators such as `<$$>` and `<##>`",
    },
    RuleInfo {
        name: style_rules::OPERATOR_SWAP,
        kind: RuleKind::Module,
        description: "Comparisons written with the constant on the left",
    },
    RuleInfo {
        name: style_rules::OP_TO_PARENS,
        kind: RuleKind::Module,
        description: "`f $ x` that should be `f (x)`",
    },
    RuleInfo {
        name: style_rules::UNNECESSARY_PARENS,
        kind: RuleKind::Module,
        description: "Parentheses around an expression that does not need them",
    },
    RuleInfo {
        name: style_rules::UNNECESSARY_TYPE_PARENS,
        kind: RuleKind::Module,
        description: "Parentheses around a type that does not need them",
    },
    RuleInfo {
        name: style_rules::IF_TO_CASE,
        kind: RuleKind::Module,
        description: "Multi-line `if` that should be a `case`",
    },
    RuleInfo {
        name: style_rules::UNQUALIFIED_DO,
        kind: RuleKind::Module,
        description: "`do`/`ado` without a monad qualifier",
    },
    RuleInfo {
        name: style_rules::UNQUALIFIED_PURE,
        kind: RuleKind::Module,
        description: "Bare `pure`",
    },
    RuleInfo {
        name: style_rules::QUALIFIED_CONSTRUCTOR,
        kind: RuleKind::Module,
        description: "Qualified `Just`/`Nothing`/`Left`/`Right`",
    },
    RuleInfo {
        name: style_rules::IMPORT_EXACT_NAME,
        kind: RuleKind::Module,
        description: "Import alias that is not the module's canonical name",
    },
    RuleInfo {
        name: style_rules::IMPORT_CTX_NAMING,
        kind: RuleKind::Module,
        description: "`Ctx.*` modules imported under a non-standard alias",
    },
    RuleInfo {
        name: style_rules::PREFER_LET,
        kind: RuleKind::Module,
        description: "`where` that should be `let`",
    },
    RuleInfo {
        name: style_rules::DOCSTRING_FORMAT,
        kind: RuleKind::Module,
        description: "Doc comments not written as `-- | `",
    },
    RuleInfo {
        name: style_rules::NO_MODULE_REEXPORT,
        kind: RuleKind::Module,
        description: "`module X` re-exports outside the designated barrel modules",
    },
    RuleInfo {
        name: style_rules::MISSING_EXPORT_LIST,
        kind: RuleKind::Module,
        description: "Module header without an export list",
    },
    RuleInfo {
        name: NO_UNUSED_IMPORTS,
        kind: RuleKind::Module,
        description: "Imports, import aliases and imported constructors that are never used",
    },
    RuleInfo {
        name: NO_UNUSED_LOCALS,
        kind: RuleKind::Module,
        description: "Local bindings that are never used",
    },
    RuleInfo {
        name: NO_UNUSED_DEFINITIONS,
        kind: RuleKind::Module,
        description: "Top-level definitions that are never used (modules with an export list only)",
    },
    RuleInfo {
        name: NO_UNUSED_CONSTRUCTORS,
        kind: RuleKind::Module,
        description: "Data constructors of an unused type",
    },
    RuleInfo {
        name: unused_exports::NAME,
        kind: RuleKind::Project,
        description: "Exports no other module references (source, BEAM call graph or roots)",
    },
    RuleInfo {
        name: reachability::UNREACHABLE,
        kind: RuleKind::Project,
        description: "Definitions no entry point reaches, even through other dead code",
    },
    RuleInfo {
        name: reachability::UNUSED_MODULES,
        kind: RuleKind::Project,
        description: "Modules none of whose definitions any entry point reaches",
    },
];

pub fn find_rule(name: &str) -> Option<&'static RuleInfo> {
    RULES.iter().find(|r| r.name == name)
}

#[derive(Debug, Default)]
pub struct ReviewOptions {
    /// Explicit config path; otherwise `hemlis-review.json` in the current directory if present.
    pub config: Option<String>,
    /// Only run these rules (all enabled rules when empty).
    pub rules: Vec<String>,
    pub module_rules_only: bool,
    pub json: bool,
    pub update_baseline: bool,
    /// Report everything, ignoring `review/suppressed/`.
    pub no_baseline: bool,
    /// Apply the fixes of reported findings and report only what could not be fixed.
    pub fix: bool,
    pub list_rules: bool,
    /// Path to an xref edge file; overrides the rule's `beam-edges` option.
    pub beam_edges: Option<String>,
}

/// A source edit: replace `span` with the text (empty text deletes).
pub type Edit = (ast::Span, String);

pub struct Finding {
    pub rule: &'static str,
    pub span: ast::Span,
    pub message: String,
    /// Edits that resolve the finding, when the rule has a safe one.
    pub fix: Option<Vec<Edit>>,
}

/// A finding with the file it belongs to: `path` as given on the command line, `rel` relative to
/// the config directory (stable across machines, used by the baseline and JSON output).
pub struct Located {
    pub path: String,
    pub rel: String,
    pub finding: Finding,
}

#[derive(Serialize)]
struct JsonFinding<'a> {
    rule: &'a str,
    path: &'a str,
    line: usize,
    col: usize,
    end_line: usize,
    end_col: usize,
    message: &'a str,
    fixable: bool,
}

#[derive(Serialize)]
struct JsonReport<'a> {
    findings: Vec<JsonFinding<'a>>,
    suppressed: usize,
    stale_baseline_entries: usize,
    fixed: usize,
}

fn nr_rule(e: &nr::NRerrors) -> Option<&'static str> {
    use nr::NRerrors::*;
    Some(match e {
        UnusedImport(..)
        | UnusedImportQualified(..)
        | UnusedImportUnqualified(..)
        | UnusedImportedConstructor(..)
        | UnusedImportTypeAndConstructor(..)
        | UnusedImportedConstructorsAll(..)
        | ImportDoesNothing(..) => NO_UNUSED_IMPORTS,
        UnusedDefinition(name, _) if name.scope() == nr::Scope::Namespace => NO_UNUSED_IMPORTS,
        // The resolver reports an unused `let` binding both as a local and as a definition;
        // `no-unused-locals` owns it.
        UnusedDefinition(name, _) if name.3 != nr::Visibility::Public => return None,
        UnusedLocal(..) => NO_UNUSED_LOCALS,
        UnusedDefinition(..) => NO_UNUSED_DEFINITIONS,
        UnusedConstructor(..) => NO_UNUSED_CONSTRUCTORS,
        _ => return None,
    })
}

/// Findings from the single-module rules: the resolver's unused-code warnings and the style rules.
/// Same two sources as `-W`, now tagged with a rule name.
pub fn module_findings(project: &ProjectData) -> Vec<Finding> {
    let mut out: Vec<Finding> = project
        .errors
        .iter()
        .filter_map(|e| {
            let rule = nr_rule(e)?;
            let (span, message) = crate::nrerror_as_warning(e, &project.names)?;
            Some(Finding { rule, span, message, fix: None })
        })
        .collect();

    let style_findings: Vec<Finding> = project
        .modules
        .par_iter()
        .flat_map(|m| {
            style::check_module(&m.module, &m.src, m.fi)
                .into_iter()
                .filter_map(|sd| {
                    crate::style_warning_message(&sd.action).map(|message| Finding {
                        rule: sd.rule,
                        span: sd.cursor_span,
                        message: message.to_string(),
                        fix: None,
                    })
                })
                .collect::<Vec<_>>()
        })
        .collect();
    out.extend(style_findings);
    out
}

/// Runs the review and returns the process exit code: 0 for no reported findings, 1 when
/// something was reported, 2 for a usage, config or read error.
pub fn run_cli(opts: ReviewOptions, files: Vec<String>) -> i32 {
    if opts.list_rules {
        for r in RULES {
            println!("{:<26} {:<8} {}", r.name, format!("{:?}", r.kind).to_lowercase(), r.description);
        }
        return EXIT_OK;
    }

    let (cfg, cfg_dir) = match config::load(opts.config.as_deref()) {
        Ok(x) => x,
        Err(e) => {
            eprintln!("ERR: {}", e);
            return EXIT_ERROR;
        }
    };
    for rule in cfg.rules.keys().chain(opts.rules.iter()) {
        if find_rule(rule).is_none() {
            eprintln!("ERR: unknown rule '{}' (see --list-rules)", rule);
            return EXIT_ERROR;
        }
    }

    let selected = |rule: &str| {
        cfg.enabled(rule) && (opts.rules.is_empty() || opts.rules.iter().any(|r| r == rule))
    };
    let want_exports = !opts.module_rules_only && selected(unused_exports::NAME);
    let want_reach = !opts.module_rules_only
        && (selected(reachability::UNREACHABLE) || selected(reachability::UNUSED_MODULES));
    let project_rules = want_exports || want_reach;

    // Project rules need the whole configured project even when the command line names a few
    // files; those files then only filter the report.
    let report_only: Option<BTreeSet<PathBuf>> =
        (!files.is_empty()).then(|| files.iter().map(|f| canonical(f)).collect());
    if report_only.is_some() && opts.update_baseline {
        eprintln!("ERR: --update-baseline covers the whole project; do not pass files");
        return EXIT_ERROR;
    }
    let analysis_files = if files.is_empty() || project_rules {
        match config::expand_files(&cfg, &cfg_dir) {
            Ok(mut configured) => {
                let known: BTreeSet<PathBuf> = configured.iter().map(|f| canonical(f)).collect();
                configured.extend(files.iter().filter(|f| !known.contains(&canonical(f))).cloned());
                configured
            }
            Err(e) => {
                eprintln!("ERR: {}", e);
                return EXIT_ERROR;
            }
        }
    } else {
        files.clone()
    };
    if analysis_files.is_empty() {
        eprintln!("ERR: no files to review");
        return EXIT_ERROR;
    }

    let project = project::resolve_project(&analysis_files);
    let mut failed = false;
    for (path, e) in project.read_errors.iter() {
        eprintln!("ERR: could not read '{}': {:?}", path, e);
        failed = true;
    }

    let mut findings = module_findings(&project);
    if project_rules {
        // The reachability rules take their own options when given, else `no-unused-exports`'s.
        let options_of = |rule: &str| -> Result<Option<unused_exports::Options>, String> {
            match cfg.options(rule) {
                Some(map) => serde_json::from_value(serde_json::Value::Object(map.clone()))
                    .map(Some)
                    .map_err(|e| format!("invalid options for {}: {}", rule, e)),
                None => Ok(None),
            }
        };
        let (export_opts, reach_opts) = match (options_of(unused_exports::NAME), options_of(reachability::UNREACHABLE)) {
            (Ok(e), Ok(r)) => {
                let e = e.unwrap_or_default();
                let r = r.unwrap_or_else(|| e.clone());
                (e, r)
            }
            (Err(e), _) | (_, Err(e)) => {
                eprintln!("ERR: {}", e);
                return EXIT_ERROR;
            }
        };
        let edges_path = |options: &unused_exports::Options| -> Option<PathBuf> {
            opts.beam_edges
                .as_ref()
                .map(PathBuf::from)
                .or_else(|| options.beam_edges.as_ref().map(|p| cfg_dir.join(p)))
        };
        if want_exports {
            let ctx = unused_exports::Context::load(&export_opts, &cfg_dir, edges_path(&export_opts).as_deref());
            for warning in ctx.warnings.iter() {
                eprintln!("WARN: {}", warning);
            }
            findings.extend(unused_exports::check(&project, &ctx));
        }
        if want_reach {
            let ctx = unused_exports::Context::load(&reach_opts, &cfg_dir, edges_path(&reach_opts).as_deref());
            if !want_exports {
                for warning in ctx.warnings.iter() {
                    eprintln!("WARN: {}", warning);
                }
            }
            let liveness = reachability::compute(&project, &ctx);
            if selected(reachability::UNREACHABLE) {
                findings.extend(reachability::check_unreachable(&project, &ctx, &liveness));
            }
            if selected(reachability::UNUSED_MODULES) {
                findings.extend(reachability::check_unused_modules(&project, &ctx, &liveness));
            }
        }
    }
    findings.retain(|f| selected(f.rule));
    if let Some(report_only) = &report_only {
        let reported_fis: BTreeSet<ast::Fi> = project
            .modules
            .iter()
            .filter(|m| report_only.contains(&canonical(&m.path)))
            .map(|m| m.fi)
            .collect();
        findings.retain(|f| f.span.fi().is_some_and(|fi| reported_fis.contains(&fi)));
    }

    let mut located: Vec<Located> = findings
        .into_iter()
        .filter_map(|finding| {
            let path = project.path_of(finding.span.fi()?)?;
            Some(Located {
                path: path.to_string(),
                rel: suppress::relative_path(path, &cfg_dir),
                finding,
            })
        })
        .collect();
    located.sort_by(|a, b| (&a.rel, a.finding.span.lo(), a.finding.rule).cmp(&(&b.rel, b.finding.span.lo(), b.finding.rule)));

    let baseline_dir = suppress::baseline_dir(&cfg_dir);
    let keys: Vec<(&str, &str)> = located.iter().map(|l| (l.finding.rule, l.rel.as_str())).collect();

    if opts.update_baseline {
        return match suppress::write(&baseline_dir, &keys) {
            Ok(files_written) => {
                eprintln!(
                    "baseline updated: {} findings, {} rule files in {}",
                    keys.len(),
                    files_written,
                    baseline_dir.display()
                );
                if failed { EXIT_ERROR } else { EXIT_OK }
            }
            Err(e) => {
                eprintln!("ERR: {}", e);
                EXIT_ERROR
            }
        };
    }

    let baseline = if opts.no_baseline {
        suppress::Baseline::default()
    } else {
        match suppress::Baseline::load(&baseline_dir) {
            Ok(b) => b,
            Err(e) => {
                eprintln!("ERR: {}", e);
                return EXIT_ERROR;
            }
        }
    };
    let applied = baseline.apply(&keys);
    let mut reported: Vec<&Located> = located
        .iter()
        .zip(applied.reported.iter())
        .filter_map(|(l, &r)| r.then_some(l))
        .collect();

    let mut fixed = 0;
    if opts.fix {
        let mut by_file: BTreeMap<&str, Vec<&Edit>> = BTreeMap::new();
        let mut unfixed = Vec::new();
        for l in reported {
            match &l.finding.fix {
                Some(edits) => {
                    by_file.entry(l.path.as_str()).or_default().extend(edits.iter());
                    fixed += 1;
                }
                None => unfixed.push(l),
            }
        }
        reported = unfixed;
        match apply_fixes(&project, by_file) {
            Ok(files_written) => eprintln!("applied {} fixes in {} files", fixed, files_written),
            Err(e) => {
                eprintln!("ERR: {}", e);
                return EXIT_ERROR;
            }
        }
    }

    if opts.json {
        let report = JsonReport {
            findings: reported
                .iter()
                .map(|l| JsonFinding {
                    rule: l.finding.rule,
                    path: &l.rel,
                    line: l.finding.span.lo().0 + 1,
                    col: l.finding.span.lo().1 + 1,
                    end_line: l.finding.span.hi().0 + 1,
                    end_col: l.finding.span.hi().1 + 1,
                    message: &l.finding.message,
                    fixable: l.finding.fix.is_some(),
                })
                .collect(),
            suppressed: applied.suppressed,
            stale_baseline_entries: applied.stale,
            fixed,
        };
        println!("{}", serde_json::to_string_pretty(&report).expect("report is serialisable"));
    } else {
        // Same colouring rules as -W: only on a terminal, and never under NO_COLOR.
        let use_color = io::stdout().is_terminal() && env::var_os("NO_COLOR").is_none();
        let (bold, yellow, dim, reset) = if use_color {
            ("\x1b[1m", "\x1b[33m", "\x1b[2m", "\x1b[0m")
        } else {
            ("", "", "", "")
        };
        for l in reported.iter() {
            let (line, col) = l.finding.span.lo();
            println!(
                "{bold}{}:{}:{}:{reset} {dim}[{}]{reset} {yellow}{}{reset}",
                l.path,
                line + 1,
                col + 1,
                l.finding.rule,
                l.finding.message
            );
        }
        if applied.suppressed > 0 || applied.stale > 0 {
            eprintln!(
                "{} findings reported, {} suppressed by the baseline{}",
                reported.len(),
                applied.suppressed,
                if applied.stale > 0 {
                    format!(" ({} baseline entries are stale, run --update-baseline)", applied.stale)
                } else {
                    String::new()
                }
            );
        }
    }

    if failed {
        EXIT_ERROR
    } else if reported.is_empty() {
        EXIT_OK
    } else {
        EXIT_FINDINGS
    }
}

fn canonical(path: &str) -> PathBuf {
    fs::canonicalize(path).unwrap_or_else(|_| PathBuf::from(path))
}

/// Applies edits per file, last-to-first so earlier offsets stay valid. An edit overlapping one
/// already applied is skipped; the next run picks it up.
fn apply_fixes(project: &ProjectData, by_file: BTreeMap<&str, Vec<&Edit>>) -> Result<usize, String> {
    let mut written = 0;
    for (path, edits) in by_file {
        let m = project
            .modules
            .iter()
            .find(|m| m.path == path)
            .ok_or_else(|| format!("no parsed source for '{}'", path))?;
        let mut ranges: Vec<(usize, usize, &str)> = edits
            .iter()
            .filter_map(|(span, text)| {
                source::span_to_byte_range(&m.src, span).map(|(lo, hi)| (lo, hi, text.as_str()))
            })
            .collect();
        ranges.sort_by(|a, b| b.0.cmp(&a.0));
        let mut out = m.src.clone();
        let mut last_lo = usize::MAX;
        for (lo, hi, text) in ranges {
            if hi > last_lo {
                continue;
            }
            out.replace_range(lo..hi, text);
            last_lo = lo;
        }
        fs::write(path, out).map_err(|e| format!("could not write '{}': {}", path, e))?;
        written += 1;
    }
    Ok(written)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fix_removes_unused_export_entries() {
        let dir = env::temp_dir().join(format!("hemlis-review-fix-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        fs::write(dir.join("hemlis-review.json"), r#"{ "files": ["*.purs"] }"#).unwrap();
        fs::write(
            dir.join("A.purs"),
            "module A (foo, bar, baz) where\n\nfoo :: Int\nfoo = 1\n\nbar :: Int\nbar = 2\n\nbaz :: Int\nbaz = 3\n",
        )
        .unwrap();
        fs::write(dir.join("B.purs"), "module B (main) where\n\nimport A as A\n\nmain :: Int\nmain = A.foo\n").unwrap();

        let code = run_cli(
            ReviewOptions {
                config: Some(dir.join("hemlis-review.json").to_string_lossy().into_owned()),
                rules: vec![unused_exports::NAME.to_string()],
                fix: true,
                no_baseline: true,
                ..Default::default()
            },
            Vec::new(),
        );

        let a = fs::read_to_string(dir.join("A.purs")).unwrap();
        assert!(a.starts_with("module A (foo) where\n"), "{}", a);
        // B's only export is `main`; a sole entry has no fix, so it is still reported.
        assert_eq!(code, EXIT_FINDINGS);
        let _ = fs::remove_dir_all(&dir);
    }
}

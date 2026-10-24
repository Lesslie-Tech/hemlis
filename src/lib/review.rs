//! `hemlis --review`: the review tool. Every finding carries a rule name, a JSON config turns
//! rules on and off, a per-file baseline keeps pre-existing findings from failing the run, and
//! output is text or JSON.

pub mod config;
pub mod suppress;

use std::collections::BTreeMap;
use std::io::IsTerminal;
use std::{env, io};

use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use serde::Serialize;

use crate::project::{self, ProjectData};
use crate::style::rule_names as style_rules;
use crate::{ast, nr, style};

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
    pub list_rules: bool,
}

pub struct Finding {
    pub rule: &'static str,
    pub span: ast::Span,
    pub message: String,
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
}

#[derive(Serialize)]
struct JsonReport<'a> {
    findings: Vec<JsonFinding<'a>>,
    suppressed: usize,
    stale_baseline_entries: usize,
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
            Some(Finding { rule, span, message })
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

    let files = if files.is_empty() {
        match config::expand_files(&cfg, &cfg_dir) {
            Ok(files) => files,
            Err(e) => {
                eprintln!("ERR: {}", e);
                return EXIT_ERROR;
            }
        }
    } else {
        files
    };
    if files.is_empty() {
        eprintln!("ERR: no files to review");
        return EXIT_ERROR;
    }

    let project = project::resolve_project(&files);
    let mut failed = false;
    for (path, e) in project.read_errors.iter() {
        eprintln!("ERR: could not read '{}': {:?}", path, e);
        failed = true;
    }

    let selected = |rule: &str| {
        cfg.enabled(rule) && (opts.rules.is_empty() || opts.rules.iter().any(|r| r == rule))
    };
    let mut findings = module_findings(&project);
    findings.retain(|f| selected(f.rule));

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

    let baseline = match suppress::Baseline::load(&baseline_dir) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("ERR: {}", e);
            return EXIT_ERROR;
        }
    };
    let applied = baseline.apply(&keys);
    let reported: Vec<&Located> = located
        .iter()
        .zip(applied.reported.iter())
        .filter_map(|(l, &r)| r.then_some(l))
        .collect();

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
                })
                .collect(),
            suppressed: applied.suppressed,
            stale_baseline_entries: applied.stale,
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

/// Findings grouped by rule, for callers that want to report per rule.
pub fn by_rule(findings: &[Located]) -> BTreeMap<&'static str, Vec<&Located>> {
    let mut out: BTreeMap<&'static str, Vec<&Located>> = BTreeMap::new();
    for f in findings {
        out.entry(f.finding.rule).or_default().push(f);
    }
    out
}

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

/// `--fix` re-runs until a pass changes nothing, since one fix uncovers the next (dropping an
/// export makes the definition unused, deleting it makes its imports unused).
const MAX_FIX_PASSES: usize = 10;

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
        description: "Unexported top-level definitions nothing in the module uses (fix: delete)",
    },
    RuleInfo {
        name: NO_UNUSED_CONSTRUCTORS,
        kind: RuleKind::Module,
        description: "Data constructors of an unused type",
    },
    RuleInfo {
        name: unused_exports::NAME,
        kind: RuleKind::Project,
        description: "Exports no other module references (fix: stop exporting)",
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
    /// Apply the fixes of reported findings, re-run until nothing changes, and report only what
    /// could not be fixed.
    pub fix: bool,
    pub list_rules: bool,
    /// Path to an xref edge file; overrides the rule's `beam-edges` option.
    pub beam_edges: Option<String>,
}

/// A source edit.
#[derive(Debug, Clone)]
pub enum Edit {
    /// Replace the span with the text (empty text deletes).
    Replace(ast::Span, String),
    /// Delete whole lines, inclusive, plus the `--` comment lines directly above and one of the
    /// blank lines left around the hole.
    DeleteLines { fi: ast::Fi, from: usize, to: usize },
}

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

/// The fix for an unused top-level definition: delete the whole declaration, signature included.
fn delete_definition(spans: &nr::DefineSpans) -> Option<Vec<Edit>> {
    let whole = spans.span();
    let fi = whole.fi()?;
    Some(vec![Edit::DeleteLines { fi, from: whole.lo().0, to: whole.hi().0 }])
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
            let fix = match e {
                nr::NRerrors::UnusedDefinition(_, spans) if rule == NO_UNUSED_DEFINITIONS => {
                    delete_definition(spans)
                }
                _ => None,
            };
            Some(Finding { rule, span, message, fix })
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

struct Setup {
    cfg: config::Config,
    cfg_dir: PathBuf,
    analysis_files: Vec<String>,
    report_only: Option<BTreeSet<PathBuf>>,
    want_exports: bool,
    want_reach: bool,
    export_opts: unused_exports::Options,
    reach_opts: unused_exports::Options,
}

impl Setup {
    fn selected(&self, opts: &ReviewOptions, rule: &str) -> bool {
        self.cfg.enabled(rule) && (opts.rules.is_empty() || opts.rules.iter().any(|r| r == rule))
    }

    fn edges_path(&self, opts: &ReviewOptions, options: &unused_exports::Options) -> Option<PathBuf> {
        opts.beam_edges
            .as_ref()
            .map(PathBuf::from)
            .or_else(|| options.beam_edges.as_ref().map(|p| self.cfg_dir.join(p)))
    }
}

/// Reads the config, validates the rule names and works out which files to analyse. Project
/// rules need the whole configured project even when the command line names a few files; those
/// files then only filter the report.
fn setup(opts: &ReviewOptions, files: &[String]) -> Result<Setup, String> {
    let (cfg, cfg_dir) = config::load(opts.config.as_deref())?;
    for rule in cfg.rules.keys().chain(opts.rules.iter()) {
        if find_rule(rule).is_none() {
            return Err(format!("unknown rule '{}' (see --list-rules)", rule));
        }
    }
    let selected = |rule: &str| {
        cfg.enabled(rule) && (opts.rules.is_empty() || opts.rules.iter().any(|r| r == rule))
    };
    let want_exports = !opts.module_rules_only && selected(unused_exports::NAME);
    let want_reach = !opts.module_rules_only
        && (selected(reachability::UNREACHABLE) || selected(reachability::UNUSED_MODULES));

    let report_only: Option<BTreeSet<PathBuf>> =
        (!files.is_empty()).then(|| files.iter().map(|f| canonical(f)).collect());
    if report_only.is_some() && opts.update_baseline {
        return Err("--update-baseline covers the whole project; do not pass files".into());
    }
    let analysis_files = if files.is_empty() || want_exports || want_reach {
        let mut configured = config::expand_files(&cfg, &cfg_dir)?;
        let known: BTreeSet<PathBuf> = configured.iter().map(|f| canonical(f)).collect();
        configured.extend(files.iter().filter(|f| !known.contains(&canonical(f))).cloned());
        configured
    } else {
        files.to_vec()
    };
    if analysis_files.is_empty() {
        return Err("no files to review".into());
    }

    // The reachability rules take their own options when given, else `no-unused-exports`'s.
    let options_of = |rule: &str| -> Result<Option<unused_exports::Options>, String> {
        match cfg.options(rule) {
            Some(map) => serde_json::from_value(serde_json::Value::Object(map.clone()))
                .map(Some)
                .map_err(|e| format!("invalid options for {}: {}", rule, e)),
            None => Ok(None),
        }
    };
    let export_opts = options_of(unused_exports::NAME)?.unwrap_or_default();
    let reach_opts = options_of(reachability::UNREACHABLE)?.unwrap_or_else(|| export_opts.clone());

    Ok(Setup { cfg, cfg_dir, analysis_files, report_only, want_exports, want_reach, export_opts, reach_opts })
}

struct Pass {
    located: Vec<Located>,
    applied: suppress::Applied,
    /// Indices into `located` that the baseline did not suppress.
    reported: Vec<usize>,
    read_errors: bool,
}

/// One analysis: resolve, run the rules, locate, sort and apply the baseline.
fn analyse(opts: &ReviewOptions, s: &Setup, baseline: &suppress::Baseline, warn: bool) -> Result<(ProjectData, Pass), String> {
    let project = project::resolve_project(&s.analysis_files);
    let mut read_errors = false;
    for (path, e) in project.read_errors.iter() {
        eprintln!("ERR: could not read '{}': {:?}", path, e);
        read_errors = true;
    }

    let mut findings = module_findings(&project);
    if s.want_exports {
        let ctx = unused_exports::Context::load(&s.export_opts, &s.cfg_dir, s.edges_path(opts, &s.export_opts).as_deref());
        if warn {
            for warning in ctx.warnings.iter() {
                eprintln!("WARN: {}", warning);
            }
        }
        findings.extend(unused_exports::check(&project, &ctx));
    }
    if s.want_reach {
        let ctx = unused_exports::Context::load(&s.reach_opts, &s.cfg_dir, s.edges_path(opts, &s.reach_opts).as_deref());
        if warn && !s.want_exports {
            for warning in ctx.warnings.iter() {
                eprintln!("WARN: {}", warning);
            }
        }
        let liveness = reachability::compute(&project, &ctx);
        if s.selected(opts, reachability::UNREACHABLE) {
            findings.extend(reachability::check_unreachable(&project, &ctx, &liveness));
        }
        if s.selected(opts, reachability::UNUSED_MODULES) {
            findings.extend(reachability::check_unused_modules(&project, &ctx, &liveness));
        }
    }
    findings.retain(|f| s.selected(opts, f.rule));
    if let Some(report_only) = &s.report_only {
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
                rel: suppress::relative_path(path, &s.cfg_dir),
                finding,
            })
        })
        .collect();
    located.sort_by(|a, b| {
        (&a.rel, a.finding.span.lo(), a.finding.rule).cmp(&(&b.rel, b.finding.span.lo(), b.finding.rule))
    });

    let keys: Vec<(&str, &str)> = located.iter().map(|l| (l.finding.rule, l.rel.as_str())).collect();
    let applied = baseline.apply(&keys);
    let reported = applied.reported.iter().enumerate().filter_map(|(i, &r)| r.then_some(i)).collect();
    Ok((project, Pass { located, applied, reported, read_errors }))
}

/// Runs the review and returns the process exit code: 0 for no reported findings, 1 when
/// something was reported, 2 for a usage, config or read error.
pub fn run_cli(opts: ReviewOptions, files: Vec<String>) -> i32 {
    if opts.list_rules {
        for r in RULES {
            println!("{:<28} {:<8} {}", r.name, format!("{:?}", r.kind).to_lowercase(), r.description);
        }
        return EXIT_OK;
    }

    let s = match setup(&opts, &files) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("ERR: {}", e);
            return EXIT_ERROR;
        }
    };
    let baseline_dir = suppress::baseline_dir(&s.cfg_dir);
    let baseline = if opts.no_baseline || opts.update_baseline {
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

    let mut fixed = 0;
    let mut passes = 0;
    let (pass, failed) = loop {
        passes += 1;
        let (project, mut pass) = match analyse(&opts, &s, &baseline, passes == 1) {
            Ok(x) => x,
            Err(e) => {
                eprintln!("ERR: {}", e);
                return EXIT_ERROR;
            }
        };
        let failed = pass.read_errors;
        if !opts.fix {
            break (pass, failed);
        }
        let mut by_file: BTreeMap<&str, Vec<&Edit>> = BTreeMap::new();
        let mut unfixed = Vec::new();
        for &i in pass.reported.iter() {
            let l = &pass.located[i];
            match &l.finding.fix {
                Some(edits) => by_file.entry(l.path.as_str()).or_default().extend(edits.iter()),
                None => unfixed.push(i),
            }
        }
        let fixed_now = pass.reported.len() - unfixed.len();
        if fixed_now == 0 || passes >= MAX_FIX_PASSES {
            break (pass, failed);
        }
        match apply_fixes(&project, by_file) {
            Ok(files_written) => eprintln!("pass {}: applied {} fixes in {} files", passes, fixed_now, files_written),
            Err(e) => {
                eprintln!("ERR: {}", e);
                return EXIT_ERROR;
            }
        }
        fixed += fixed_now;
        pass.reported = unfixed;
    };

    let keys: Vec<(&str, &str)> = pass.located.iter().map(|l| (l.finding.rule, l.rel.as_str())).collect();
    if opts.update_baseline {
        return match suppress::write(&baseline_dir, &keys) {
            Ok(files_written) => {
                eprintln!("baseline updated: {} findings, {} rule files in {}", keys.len(), files_written, baseline_dir.display());
                if failed { EXIT_ERROR } else { EXIT_OK }
            }
            Err(e) => {
                eprintln!("ERR: {}", e);
                EXIT_ERROR
            }
        };
    }

    let reported: Vec<&Located> = pass.reported.iter().map(|&i| &pass.located[i]).collect();
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
            suppressed: pass.applied.suppressed,
            stale_baseline_entries: pass.applied.stale,
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
        if fixed > 0 {
            eprintln!("applied {} fixes in {} passes", fixed, passes - 1);
        }
        if pass.applied.suppressed > 0 || pass.applied.stale > 0 {
            eprintln!(
                "{} findings reported, {} suppressed by the baseline{}",
                reported.len(),
                pass.applied.suppressed,
                if pass.applied.stale > 0 {
                    format!(" ({} baseline entries are stale, run --update-baseline)", pass.applied.stale)
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

/// `DeleteLines` as a byte range over `src`: the lines themselves, the `--` comment lines
/// directly above, and one of the blank lines around the hole so no double blank is left.
fn delete_lines_range(src: &str, from: usize, to: usize) -> Option<(usize, usize)> {
    let starts = source::line_starts(src);
    // `line_starts` ends with a start just past the final newline; that is not a line.
    let real_line = |l: usize| l < starts.len() && starts[l] < src.len();
    let blank = |l: usize| -> bool {
        let lo = starts[l];
        let hi = starts.get(l + 1).copied().unwrap_or(src.len());
        src[lo..hi].trim().is_empty()
    };
    let mut first = from;
    while first > 0 && src[starts[first - 1]..starts[first]].trim_start().starts_with("--") {
        first -= 1;
    }
    let mut end_line = to + 1;
    let blank_before = first > 0 && blank(first - 1);
    let blank_after = real_line(end_line) && blank(end_line);
    let at_eof = !real_line(end_line);
    if at_eof {
        if blank_before {
            first -= 1;
        }
    } else if blank_after && (blank_before || first == 0) {
        end_line += 1;
    }
    let lo = starts.get(first).copied()?;
    let hi = starts.get(end_line).copied().unwrap_or(src.len());
    Some((lo, hi))
}

/// Applies edits per file, last-to-first so earlier offsets stay valid. An edit overlapping one
/// already applied is skipped; the next pass picks it up.
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
            .filter_map(|edit| match edit {
                Edit::Replace(span, text) => {
                    source::span_to_byte_range(&m.src, span).map(|(lo, hi)| (lo, hi, text.as_str()))
                }
                Edit::DeleteLines { from, to, .. } => delete_lines_range(&m.src, *from, *to).map(|(lo, hi)| (lo, hi, "")),
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
    use std::path::Path;

    fn temp_project(name: &str) -> PathBuf {
        let dir = env::temp_dir().join(format!("hemlis-review-{}-{}", name, std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        fs::write(dir.join("hemlis-review.json"), r#"{ "files": ["*.purs"] }"#).unwrap();
        dir
    }

    fn fix_opts(dir: &Path, rules: &[&str]) -> ReviewOptions {
        ReviewOptions {
            config: Some(dir.join("hemlis-review.json").to_string_lossy().into_owned()),
            rules: rules.iter().map(|r| r.to_string()).collect(),
            fix: true,
            no_baseline: true,
            ..Default::default()
        }
    }

    #[test]
    fn fix_cascades_from_export_list_to_definition() {
        let dir = temp_project("cascade");
        fs::write(
            dir.join("A.purs"),
            "module A (foo, bar, baz) where\n\nfoo :: Int\nfoo = 1\n\n-- | Doc for bar.\nbar :: Int\nbar = 2\n\nbaz :: Int\nbaz = 3\n",
        )
        .unwrap();
        fs::write(dir.join("B.purs"), "module B (main) where\n\nimport A as A\n\nmain :: Int\nmain = A.foo\n").unwrap();

        let code = run_cli(fix_opts(&dir, &[unused_exports::NAME, NO_UNUSED_DEFINITIONS]), Vec::new());

        let a = fs::read_to_string(dir.join("A.purs")).unwrap();
        assert_eq!(a, "module A (foo) where\n\nfoo :: Int\nfoo = 1\n", "{}", a);
        // B's only export is `main`; a sole entry has no fix, so it is still reported.
        assert_eq!(code, EXIT_FINDINGS);
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn delete_lines_takes_comment_and_one_blank() {
        let src = "a = 1\n\n-- | doc\n-- more\nb :: Int\nb = 2\n\nc = 3\n";
        let (lo, hi) = delete_lines_range(src, 4, 5).unwrap();
        let mut out = src.to_string();
        out.replace_range(lo..hi, "");
        assert_eq!(out, "a = 1\n\nc = 3\n");

        let src = "b = 2\n\nc = 3\n";
        let (lo, hi) = delete_lines_range(src, 0, 0).unwrap();
        let mut out = src.to_string();
        out.replace_range(lo..hi, "");
        assert_eq!(out, "c = 3\n");

        // Last block in the file: the blank line before it goes instead.
        let src = "a = 1\n\nb = 2\n";
        let (lo, hi) = delete_lines_range(src, 2, 2).unwrap();
        let mut out = src.to_string();
        out.replace_range(lo..hi, "");
        assert_eq!(out, "a = 1\n");
    }
}

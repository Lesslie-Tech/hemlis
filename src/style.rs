use crate::ast::{self, Ast, Span, Ud};
use crate::parser::op_fixity;

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// What a style diagnostic does: warn, offer a fix, or both.
pub enum StyleAction {
    /// Emit a warning only; no code action (e.g. no safe auto-fix exists).
    Warn { message: String },
    /// Offer a code action only; no warning diagnostic.
    Fix { title: String, replacement: String },
    /// Emit a warning *and* offer a code action.
    WarnAndFix {
        message: String,
        title: String,
        replacement: String,
    },
}

/// A style diagnostic produced by the checker.
/// The LSP layer converts this into a Fixable + optional warning diagnostic.
pub struct StyleDiagnostic {
    /// Span used for cursor matching (e.g. the operator itself).
    pub cursor_span: Span,
    /// Span of the expression to replace / anchor the warning on.
    pub expr_span: Span,
    /// What the diagnostic offers: a warning, a fix, or both.
    pub action: StyleAction,
}

// ---------------------------------------------------------------------------
// Source text helpers
// ---------------------------------------------------------------------------

fn line_starts(source: &str) -> Vec<usize> {
    let mut starts = vec![0];
    for (i, b) in source.bytes().enumerate() {
        if b == b'\n' {
            starts.push(i + 1);
        }
    }
    starts
}

fn span_to_byte_range(source: &str, span: &Span) -> Option<(usize, usize)> {
    if let Span::Known(_, lo, hi) = span {
        let starts = line_starts(source);
        let lo_byte = starts.get(lo.0).map(|s| s + lo.1)?;
        let hi_byte = starts.get(hi.0).map(|s| s + hi.1)?;
        Some((lo_byte, hi_byte))
    } else {
        None
    }
}

fn source_text<'a>(source: &'a str, span: &Span) -> Option<&'a str> {
    let (lo, hi) = span_to_byte_range(source, span)?;
    source.get(lo..hi)
}

// ---------------------------------------------------------------------------
// Forbidden operators (PAY-3096)
// ---------------------------------------------------------------------------

struct ForbiddenOp {
    from: &'static str,
    to: &'static str,
    description: &'static str,
}

const FORBIDDEN_OPS: &[ForbiddenOp] = &[
    ForbiddenOp {
        from: "=<<",
        to: ">>=",
        description: "right-to-left bind",
    },
    ForbiddenOp {
        from: "<<<",
        to: ">>>",
        description: "right-to-left composition",
    },
];

fn needs_parens(expr: &ast::Expr, target_prec: usize) -> bool {
    match expr {
        ast::Expr::Op(_, qop, _) => {
            let inner_prec = op_fixity((qop.1).0 .0).prec();
            inner_prec <= target_prec
        }
        ast::Expr::Infix(..)
        | ast::Expr::Lambda(..)
        | ast::Expr::IfThenElse(..)
        | ast::Expr::Let(..)
        | ast::Expr::Case(..)
        | ast::Expr::Do(..)
        | ast::Expr::Ado(..)
        | ast::Expr::Typed(..) => true,
        _ => false,
    }
}

fn maybe_paren(text: &str, expr: &ast::Expr, target_prec: usize) -> String {
    if needs_parens(expr, target_prec) {
        format!("({})", text)
    } else {
        text.to_string()
    }
}

fn rule_forbidden_operator(expr: &ast::Expr, source: &str, out: &mut Vec<StyleDiagnostic>) {
    if let ast::Expr::Op(lhs, qop, rhs) = expr {
        let op_ud = (qop.1).0 .0;
        for forbidden in FORBIDDEN_OPS {
            if op_ud == Ud::new(forbidden.from) {
                let expr_span = expr.span();
                let lhs_text = source_text(source, &lhs.span()).unwrap_or("_");
                let rhs_text = source_text(source, &rhs.span()).unwrap_or("_");

                let target_prec = op_fixity(Ud::new(forbidden.to)).prec();
                let new_lhs = maybe_paren(rhs_text, rhs, target_prec);
                let new_rhs = maybe_paren(lhs_text, lhs, target_prec);

                out.push(StyleDiagnostic {
                    cursor_span: expr_span,
                    expr_span,
                    action: StyleAction::WarnAndFix {
                        title: format!("Replace `{}` with `{}`", forbidden.from, forbidden.to),
                        replacement: format!("{} {} {}", new_lhs, forbidden.to, new_rhs),
                        message: format!(
                            "Prefer `{}` over `{}` ({})",
                            forbidden.to, forbidden.from, forbidden.description
                        ),
                    },
                });
                break;
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Operator conversions (PAY-3098)
// ---------------------------------------------------------------------------

struct OpSwap {
    from: &'static str,
    to: &'static str,
    /// Wrap replacement in parens because the target op has lower precedence.
    wrap: bool,
}

const SWAP_OPS: &[OpSwap] = &[
    OpSwap {
        from: "$",
        to: "#",
        wrap: false,
    }, // prec 0 → prec 1 (higher is safe)
    OpSwap {
        from: "#",
        to: "$",
        wrap: true,
    }, // prec 1 → prec 0
    OpSwap {
        from: "<$>",
        to: "<#>",
        wrap: true,
    }, // prec 4 → prec 1
    OpSwap {
        from: "<#>",
        to: "<$>",
        wrap: false,
    }, // prec 1 → prec 4 (higher is safe)
];

fn rule_operator_swap(expr: &ast::Expr, source: &str, out: &mut Vec<StyleDiagnostic>) {
    if let ast::Expr::Op(lhs, qop, rhs) = expr {
        let op_ud = (qop.1).0 .0;
        for swap in SWAP_OPS {
            if op_ud == Ud::new(swap.from) {
                let op_span = (qop.1).0 .1;
                let expr_span = expr.span();
                let lhs_text = source_text(source, &lhs.span()).unwrap_or("_");
                let rhs_text = source_text(source, &rhs.span()).unwrap_or("_");

                let target_prec = op_fixity(Ud::new(swap.to)).prec();
                let new_lhs = maybe_paren(rhs_text, rhs, target_prec);
                let new_rhs = maybe_paren(lhs_text, lhs, target_prec);

                let replacement = if swap.wrap {
                    format!("({} {} {})", new_lhs, swap.to, new_rhs)
                } else {
                    format!("{} {} {}", new_lhs, swap.to, new_rhs)
                };

                out.push(StyleDiagnostic {
                    cursor_span: op_span,
                    expr_span,
                    action: StyleAction::Fix {
                        title: format!("Replace `{}` with `{}`", swap.from, swap.to),
                        replacement,
                    },
                });
                break;
            }
        }
    }
}

/// `f $ x` → `f (x)` and `x # f` → `f (x)`
fn rule_op_to_parens(expr: &ast::Expr, source: &str, out: &mut Vec<StyleDiagnostic>) {
    if let ast::Expr::Op(lhs, qop, rhs) = expr {
        let op_ud = (qop.1).0 .0;
        let (func, arg) = if op_ud == Ud::new("$") {
            (lhs, rhs) // f $ x → f is func, x is arg
        } else if op_ud == Ud::new("#") {
            (rhs, lhs) // x # f → f is func, x is arg
        } else {
            return;
        };
        let op_name = if op_ud == Ud::new("$") { "$" } else { "#" };
        let op_span = (qop.1).0 .1;

        let expr_span = expr.span();
        let func_text = source_text(source, &func.span()).unwrap_or("_");
        let arg_text = source_text(source, &arg.span()).unwrap_or("_");

        // If arg is already parenthesized, use it as-is; otherwise wrap in parens
        let parened_arg = if matches!(arg.as_ref(), ast::Expr::Paren(..)) {
            arg_text.to_string()
        } else {
            format!("({})", arg_text)
        };

        // Func needs parens if it's a case/lambda/do/etc that would swallow the arg
        let parened_func = if needs_parens(func, usize::MAX) {
            format!("({})", func_text)
        } else {
            func_text.to_string()
        };

        out.push(StyleDiagnostic {
            cursor_span: op_span,
            expr_span,
            action: StyleAction::Fix {
                title: format!("Replace `{}` with `()`", op_name),
                replacement: format!("{} {}", parened_func, parened_arg),
            },
        });
    }
}

// ---------------------------------------------------------------------------
// Unnecessary parenthesis (PAY-3104)
// ---------------------------------------------------------------------------

fn is_atom(expr: &ast::Expr) -> bool {
    matches!(
        expr,
        ast::Expr::Ident(_)
            | ast::Expr::Constructor(_)
            | ast::Expr::Symbol(_)
            | ast::Expr::Boolean(_)
            | ast::Expr::Char(_)
            | ast::Expr::Str(_)
            | ast::Expr::Number(_)
            | ast::Expr::HexInt(_)
            | ast::Expr::Array(..)
            | ast::Expr::Record(..)
            | ast::Expr::Section(_)
            | ast::Expr::Hole(_)
            | ast::Expr::Paren(..)
    )
}

/// An "open" expression extends as far to the right as it can when parsed. Wrapping one in parens
/// is therefore necessary whenever it sits in a non-tail position (i.e. some token follows it in
/// the enclosing construct), because without the parens it would swallow that trailing token.
/// Examples: a guard `(case ...) = body`, an `if (case ...) then ...`, a `case (case ...) of ...`.
/// (PAY-3322)
fn is_open_expr(expr: &ast::Expr) -> bool {
    matches!(
        expr,
        ast::Expr::Case(..)
            | ast::Expr::IfThenElse(..)
            | ast::Expr::Lambda(..)
            | ast::Expr::Let(..)
            | ast::Expr::Where(..)
            | ast::Expr::Do(..)
            | ast::Expr::Ado(..)
    )
}

#[allow(dead_code)]
enum ParenContext {
    AppFunc,
    AppArg,
    OpLeft(Ud),
    OpRight(Ud),
}

#[allow(dead_code)]
fn paren_is_unnecessary(inner: &ast::Expr, ctx: &ParenContext) -> bool {
    match ctx {
        ParenContext::AppFunc => is_atom(inner) || matches!(inner, ast::Expr::App(..)),
        ParenContext::AppArg => is_atom(inner),
        ParenContext::OpLeft(outer_ud) | ParenContext::OpRight(outer_ud) => {
            if is_atom(inner) || matches!(inner, ast::Expr::App(..)) {
                return true;
            }
            if let ast::Expr::Op(_, inner_qop, _) = inner {
                let outer_fix = op_fixity(*outer_ud);
                let inner_fix = op_fixity((inner_qop.1).0 .0);
                if inner_fix.prec() > outer_fix.prec() {
                    return true;
                }
                if inner_fix.prec() == outer_fix.prec() {
                    let on_left = matches!(ctx, ParenContext::OpLeft(_));
                    let left_assoc = inner_fix.is_left();
                    if (on_left && left_assoc) || (!on_left && !left_assoc) {
                        return true;
                    }
                }
            }
            false
        }
    }
}

fn emit_remove_parens(child: &ast::Expr, source: &str, out: &mut Vec<StyleDiagnostic>) {
    if let ast::Expr::Paren(_, inner, _) = child {
        let inner_text = source_text(source, &inner.span());
        if let Some(text) = inner_text {
            let paren_span = child.span();
            out.push(StyleDiagnostic {
                cursor_span: paren_span,
                expr_span: paren_span,
                action: StyleAction::WarnAndFix {
                    title: "Remove unnecessary parenthesis".into(),
                    replacement: text.to_string(),
                    message: "Unnecessary parenthesis".into(),
                },
            });
        }
    }
}

/// Simple heuristic for unnecessary parenthesis:
/// 1. Double parens: `((x))` → `(x)`
/// 2. Atom in parens: `(x)` → `x` (single ident/literal/array/record)
/// 3. Paren not inside App/Op: the parens are the whole expression in their
///    context (definition RHS, do-bind, let-bind, case scrutinee, etc.) — but only when in tail
///    position for "open" expressions (see `is_open_expr` / `tail_ok`).
/// 4. Same operator inside as outside, on the side that matches the operator's fixity:
///    a left-associative op only allows dropping parens on its left operand, a
///    right-associative op only on its right operand. E.g. for `+` (infixl),
///    `(a + b) + c` → `a + b + c`, but `a + (b + c)` keeps its parens; for `:` (infixr),
///    `x : (ys : zs)` → `x : ys : zs`, but `(x : ys) : zs` keeps its parens. (PAY-3202)
fn rule_unnecessary_parens(
    expr: &ast::Expr,
    source: &str,
    inside_app_or_op: bool,
    outer_op: Option<(Ud, bool)>,
    tail_ok: bool,
    out: &mut Vec<StyleDiagnostic>,
) {
    if let ast::Expr::Paren(_, inner, _) = expr {
        let same_op_removable = match (outer_op, inner.as_ref()) {
            (Some((outer, on_left)), ast::Expr::Op(_, inner_qop, _)) => {
                let inner_ud = (inner_qop.1).0 .0;
                // Same operator: the parens are only redundant on the associativity side.
                inner_ud == outer && (on_left == op_fixity(inner_ud).is_left())
            }
            _ => false,
        };
        // "Whole expression in its context" removal is unsafe for an open expression that isn't in
        // tail position: it would extend right and swallow the following token. (PAY-3322)
        let whole_expr_removable =
            !inside_app_or_op && (tail_ok || !is_open_expr(inner));
        let removable = matches!(inner.as_ref(), ast::Expr::Paren(..))
            || is_atom(inner)
            || whole_expr_removable
            || same_op_removable;
        if removable {
            emit_remove_parens(expr, source, out);
        }
    }
}

// ---------------------------------------------------------------------------
// Unnecessary type parenthesis (PAY-3104)
// ---------------------------------------------------------------------------

fn is_typ_atom(typ: &ast::Typ) -> bool {
    matches!(
        typ,
        ast::Typ::Wildcard(_)
            | ast::Typ::Var(_)
            | ast::Typ::Constructor(_)
            | ast::Typ::Symbol(_)
            | ast::Typ::Str(_)
            | ast::Typ::Int(..)
            | ast::Typ::Hole(_)
            | ast::Typ::Record(_)
            | ast::Typ::Row(_)
            | ast::Typ::Paren(..)
    )
}

fn emit_remove_typ_parens(typ: &ast::Typ, source: &str, out: &mut Vec<StyleDiagnostic>) {
    if let ast::Typ::Paren(_, inner, _) = typ {
        let inner_text = source_text(source, &inner.span());
        if let Some(text) = inner_text {
            let paren_span = typ.span();
            out.push(StyleDiagnostic {
                cursor_span: paren_span,
                expr_span: paren_span,
                action: StyleAction::WarnAndFix {
                    title: "Remove unnecessary parenthesis".into(),
                    replacement: text.to_string(),
                    message: "Unnecessary parenthesis".into(),
                },
            });
        }
    }
}

fn rule_unnecessary_typ_parens(
    typ: &ast::Typ,
    source: &str,
    inside_app_or_op: bool,
    outer_op: Option<Ud>,
    out: &mut Vec<StyleDiagnostic>,
) {
    if let ast::Typ::Paren(_, inner, _) = typ {
        let same_op =
            if let (Some(outer), ast::Typ::Op(_, inner_qop, _)) = (outer_op, inner.as_ref()) {
                (inner_qop.1).0 .0 == outer
            } else {
                false
            };
        // (Unit -> X) is a lazy-value pattern — keep parens for readability.
        let is_unit_thunk = matches!(inner.as_ref(), ast::Typ::Arr(a, _)
            if matches!(a.as_ref(), ast::Typ::Constructor(ast::QProperName(None, ast::ProperName(ast::S(ud, _)))) if *ud == Ud::new("Unit")));
        let removable = !is_unit_thunk
            && (matches!(inner.as_ref(), ast::Typ::Paren(..))
                || is_typ_atom(inner)
                || !inside_app_or_op
                || same_op);
        if removable {
            emit_remove_typ_parens(typ, source, out);
        }
    }
}

// ---------------------------------------------------------------------------
// PAY-3099: if → case conversion
// ---------------------------------------------------------------------------

fn rule_if_to_case(expr: &ast::Expr, source: &str, out: &mut Vec<StyleDiagnostic>) {
    let ast::Expr::IfThenElse(kw_span, cond, then_e, else_e) = expr else {
        return;
    };
    let Some(cond_text) = source_text(source, &cond.span()) else {
        return;
    };
    let Some(then_text) = source_text(source, &then_e.span()) else {
        return;
    };
    let Some(else_text) = source_text(source, &else_e.span()) else {
        return;
    };

    let case_col = kw_span.lo().1;
    let branch_indent = " ".repeat(case_col + 2);
    let cond_trimmed = cond_text.trim();
    let then_trimmed = then_text.trim_start();
    let else_trimmed = else_text.trim_start();

    let replacement = format!(
        "case {} of\n{}true -> {}\n{}false -> {}",
        cond_trimmed, branch_indent, then_trimmed, branch_indent, else_trimmed
    );

    let is_multiline = expr.span().lo().0 != expr.span().hi().0;
    let if_length = expr.span().hi().1.saturating_sub(expr.span().lo().1);
    let is_long_if = !is_multiline && if_length > 120;

    let (cursor_span, message) = if is_multiline {
        (expr.span(), Some("Prefer `case` over multiline `if`".to_string()))
    } else if is_long_if {
        (expr.span(), Some("Line exceeds 120 chars; prefer `case` over long `if`".to_string()))
    } else {
        (*kw_span, None)
    };

    let action = match message {
        Some(message) => StyleAction::WarnAndFix {
            message,
            title: "Convert to `case`".into(),
            replacement,
        },
        None => StyleAction::Fix {
            title: "Convert to `case`".into(),
            replacement,
        },
    };

    out.push(StyleDiagnostic {
        cursor_span,
        expr_span: expr.span(),
        action,
    });
}

// ---------------------------------------------------------------------------
// PAY-3687: warn on unqualified `do` / `ado`
// ---------------------------------------------------------------------------

/// Warn when a `do`/`ado` block is unqualified (bare `do` rather than
/// `Module.do`). Warn-only: hemlis can't know which qualified alias to use, so
/// there is no auto-fix. The diagnostic is anchored on the `do`/`ado` keyword.
fn rule_unqualified_do(expr: &ast::Expr, out: &mut Vec<StyleDiagnostic>) {
    let (qual, kw, keyword) = match expr {
        ast::Expr::Do(qual, kw, _) => (qual, kw, "do"),
        ast::Expr::Ado(qual, kw, _, _) => (qual, kw, "ado"),
        _ => return,
    };
    if qual.is_some() {
        return;
    }
    out.push(StyleDiagnostic {
        cursor_span: *kw,
        expr_span: *kw,
        action: StyleAction::Warn {
            message: format!(
                "Unqualified `{kw}` block; use a qualified `Module.{kw}`",
                kw = keyword
            ),
        },
    });
}

// ---------------------------------------------------------------------------
// PAY-3688: warn on unqualified `pure`
// ---------------------------------------------------------------------------

/// Warn when `pure` is used unqualified — prefer a qualified form such as
/// `Applicative.pure`. Warn-only. Qualified uses (`List.pure`, `Array.pure`,
/// …) carry a `Qual` and are naturally excluded. Imports/exports/type
/// signatures/definition LHSs are excluded because the checker only visits
/// expression positions. The whole-module allowance (when the module defines
/// its own top-level `pure`) is handled by the caller.
fn rule_unqualified_pure(expr: &ast::Expr, out: &mut Vec<StyleDiagnostic>) {
    if let ast::Expr::Ident(ast::QName(None, name)) = expr {
        if (name.0).0 == Ud::new("pure") {
            let span = expr.span();
            out.push(StyleDiagnostic {
                cursor_span: span,
                expr_span: span,
                action: StyleAction::Warn {
                    message: "Unqualified `pure`; use a qualified `Applicative.pure`".into(),
                },
            });
        }
    }
}

// ---------------------------------------------------------------------------
// PAY-3689: warn on qualified `Just` / `Left` / `Right`
// ---------------------------------------------------------------------------

/// Constructors that should be used unqualified, matched textually on the
/// qualifier alias as written. (qualifier, constructor)
const QUALIFIED_CONSTRUCTORS: &[(&str, &str)] = &[
    ("Maybe", "Just"),
    ("Either", "Left"),
    ("Either", "Right"),
];

/// Warn on qualified `Maybe.Just`, `Either.Left`, `Either.Right` — these are
/// idiomatically used unqualified. Offers a code action that strips the
/// qualifier; this is safe in practice because these constructors are almost
/// always already in scope (imported via `Maybe(..)` / `Either(..)`). The
/// match is textual on the qualifier alias, mirroring the `codestyle.py`
/// regexes.
fn rule_qualified_constructor(expr: &ast::Expr, out: &mut Vec<StyleDiagnostic>) {
    if let ast::Expr::Constructor(ast::QProperName(Some(qual), name)) = expr {
        let qual_ud = (qual.0).0;
        let name_ud = (name.0).0;
        for (q, n) in QUALIFIED_CONSTRUCTORS {
            if qual_ud == Ud::new(q) && name_ud == Ud::new(n) {
                let span = expr.span();
                out.push(StyleDiagnostic {
                    cursor_span: span,
                    expr_span: span,
                    action: StyleAction::WarnAndFix {
                        message: format!("Prefer unqualified `{n}` over `{q}.{n}`"),
                        title: format!("Replace `{q}.{n}` with `{n}`"),
                        replacement: n.to_string(),
                    },
                });
                break;
            }
        }
    }
}

// ---------------------------------------------------------------------------
// PAY-3691: import top-level modules with exact name
// ---------------------------------------------------------------------------

/// Warn when a single-segment (top-level) module is imported under a different
/// alias, e.g. `import Foo as Bar`. A single-character alias (`import Foo as F`)
/// is allowed, as is importing under the exact name (`import Foo as Foo`). An
/// alias that is itself re-exported via `module Alias` in the export list is
/// also allowed — that's the intentional module re-export pattern (e.g. Joe).
/// Warn-only: renaming the alias would require rewriting every `Bar.x`
/// reference, which the pure-AST style checker can't do. The comparison is
/// textual on the module name as written. (PAY-3691)
fn rule_import_exact_name(
    imp: &ast::ImportDecl,
    exported_modules: &[Ud],
    source: &str,
    out: &mut Vec<StyleDiagnostic>,
) {
    let Some(alias) = &imp.to else {
        return;
    };
    // The alias is re-exported (`module Alias`), so aliasing to it is intentional.
    if exported_modules.contains(&(alias.0).0) {
        return;
    }
    let from_span = imp.from.span();
    let alias_span = alias.span();
    let (Some(from_text), Some(alias_text)) = (
        source_text(source, &from_span),
        source_text(source, &alias_span),
    ) else {
        return;
    };

    // Only single-segment (top-level) modules; multi-segment names may
    // legitimately be aliased to their last segment (`Data.Maybe as Maybe`).
    if from_text.contains('.') {
        return;
    }
    // Importing under the exact name, or a single-character abbreviation, is ok.
    if alias_text == from_text || alias_text.chars().count() == 1 {
        return;
    }

    let first = from_text.chars().next().unwrap_or('?');
    out.push(StyleDiagnostic {
        cursor_span: alias_span,
        expr_span: alias_span,
        action: StyleAction::Warn {
            message: format!("Import `{from_text}` as `{from_text}` or `{first}`, not `{alias_text}`"),
        },
    });
}

// ---------------------------------------------------------------------------
// PAY-3692: Ctx module import naming convention
// ---------------------------------------------------------------------------

/// Enforce the `Ctx`-module aliasing convention: a Ctx-family module (its name
/// starts or ends with `Ctx`) should be aliased with `Ctx` *last* and no period
/// (e.g. `import Ctx.Time as TimeCtx`). Flag aliases that instead *start* with
/// `Ctx` (`CtxTime`, `Ctx.Time`). Warn-only. (PAY-3692)
fn rule_import_ctx_naming(imp: &ast::ImportDecl, source: &str, out: &mut Vec<StyleDiagnostic>) {
    let Some(alias) = &imp.to else {
        return;
    };
    let from_span = imp.from.span();
    let alias_span = alias.span();
    let (Some(from_text), Some(alias_text)) = (
        source_text(source, &from_span),
        source_text(source, &alias_span),
    ) else {
        return;
    };

    // The module must be Ctx-family: its name starts or ends with `Ctx`.
    let is_ctx_module =
        from_text.len() > 3 && (from_text.starts_with("Ctx") || from_text.ends_with("Ctx"));
    if !is_ctx_module {
        return;
    }
    // The alias only violates the convention if it *starts* with `Ctx`.
    if !(alias_text.starts_with("Ctx") && alias_text.len() > 3) {
        return;
    }

    // Suggest the convention-abiding alias: drop the leading `Ctx`/`Ctx.`, strip
    // any remaining periods, and append `Ctx`.
    let base = alias_text.strip_prefix("Ctx").unwrap_or(alias_text);
    let base = base.strip_prefix('.').unwrap_or(base);
    let suggestion = format!("{}Ctx", base.replace('.', ""));

    out.push(StyleDiagnostic {
        cursor_span: alias_span,
        expr_span: alias_span,
        action: StyleAction::Warn {
            message: format!(
                "Ctx module alias should end with `Ctx`: use `{suggestion}`, not `{alias_text}`"
            ),
        },
    });
}

// ---------------------------------------------------------------------------

struct StyleChecker<'a> {
    source: &'a str,
    diagnostics: Vec<StyleDiagnostic>,
    /// The module defines its own top-level `pure`, so the unqualified-`pure`
    /// rule is suppressed for the whole module. (PAY-3688)
    module_defines_pure: bool,
}

impl<'a> StyleChecker<'a> {
    fn new(source: &'a str, module_defines_pure: bool) -> Self {
        Self {
            source,
            diagnostics: Vec::new(),
            module_defines_pure,
        }
    }

    fn check_expr(&mut self, expr: &ast::Expr) {
        // Tail position: nothing follows the expression in its enclosing construct, so parens
        // around an open expression may be dropped.
        self.check_expr_ctx(expr, false, None, true);
    }

    fn check_expr_nontail(&mut self, expr: &ast::Expr) {
        // Non-tail position: a token follows the expression (a guard's `= body` / `-> body`, an
        // `if` condition's `then`, a scrutinee's `of`, a non-final list element's `,`), so parens
        // around an open expression must be kept. (PAY-3322)
        self.check_expr_ctx(expr, false, None, false);
    }

    fn check_expr_ctx(
        &mut self,
        expr: &ast::Expr,
        inside_app_or_op: bool,
        outer_op: Option<(Ud, bool)>,
        tail_ok: bool,
    ) {
        // ===== RULES (add new rules here) =====
        rule_forbidden_operator(expr, self.source, &mut self.diagnostics);
        rule_operator_swap(expr, self.source, &mut self.diagnostics);
        rule_op_to_parens(expr, self.source, &mut self.diagnostics);
        rule_unnecessary_parens(
            expr,
            self.source,
            inside_app_or_op,
            outer_op,
            tail_ok,
            &mut self.diagnostics,
        );
        rule_if_to_case(expr, self.source, &mut self.diagnostics);
        rule_unqualified_do(expr, &mut self.diagnostics);
        if !self.module_defines_pure {
            rule_unqualified_pure(expr, &mut self.diagnostics);
        }
        rule_qualified_constructor(expr, &mut self.diagnostics);
        // =======================================

        self.recurse_expr(expr);
    }

    fn recurse_expr(&mut self, expr: &ast::Expr) {
        match expr {
            ast::Expr::Typed(e, t) => {
                self.check_expr_ctx(e, true, None, true);
                self.check_typ(t);
            }
            ast::Expr::Op(a, qop, b) => {
                let op_ud = (qop.1).0 .0;
                self.check_expr_ctx(a, true, Some((op_ud, true)), true);
                self.check_expr_ctx(b, true, Some((op_ud, false)), true);
            }
            ast::Expr::Infix(a, o, b) => {
                self.check_expr_ctx(a, true, None, true);
                self.check_expr(o);
                self.check_expr_ctx(b, true, None, true);
            }
            ast::Expr::Negate(e) => self.check_expr(e),
            ast::Expr::App(a, b) => {
                self.check_expr_ctx(a, true, None, true);
                self.check_expr_ctx(b, true, None, true);
            }
            ast::Expr::Vta(e, t) => {
                self.check_expr(e);
                self.check_typ_ctx(t, true, None);
            }
            ast::Expr::IfThenElse(_, c, t, f) => {
                // `if <c> then <t> else <f>`: the condition is followed by `then` and the
                // then-branch by `else`, so both are non-tail; the else-branch is in tail position.
                self.check_expr_nontail(c);
                self.check_expr_nontail(t);
                self.check_expr(f);
            }
            ast::Expr::Do(_, _, stmts) | ast::Expr::Ado(_, _, stmts, _) => {
                for stmt in stmts {
                    self.check_do_stmt(stmt);
                }
                if let ast::Expr::Ado(_, _, _, e) = expr {
                    self.check_expr(e);
                }
            }
            ast::Expr::Lambda(_, _, e) => self.check_expr(e),
            ast::Expr::Let(_, bindings, e) => {
                self.check_let_bindings(bindings);
                self.check_expr(e);
            }
            ast::Expr::Where(_, e, bindings) => {
                // `<e> where ...`: `where` follows the expression, so it is non-tail.
                self.check_expr_nontail(e);
                self.check_let_bindings(bindings);
            }
            ast::Expr::Case(_, scrutinees, branches) => {
                for e in scrutinees {
                    // `case <e> of ...`: the scrutinee is followed by `of`, so it is non-tail.
                    self.check_expr_nontail(e);
                }
                for ast::CaseBranch(_, ge) in branches {
                    self.check_guarded_expr(ge);
                }
            }
            ast::Expr::Array(_, es, _) => {
                // Only the final element is in tail position (delimited by `]`); any earlier
                // element is followed by `,`.
                let last = es.len().saturating_sub(1);
                for (i, e) in es.iter().enumerate() {
                    if i == last {
                        self.check_expr(e);
                    } else {
                        self.check_expr_nontail(e);
                    }
                }
            }
            ast::Expr::Record(_, fields, _) => {
                // Only a field that nothing follows is in tail position (delimited by `}`).
                let last = fields.len().saturating_sub(1);
                for (i, field) in fields.iter().enumerate() {
                    if let ast::RecordLabelExpr::Field(_, e) = field {
                        if i == last {
                            self.check_expr(e);
                        } else {
                            self.check_expr_nontail(e);
                        }
                    }
                }
            }
            ast::Expr::Update(e, _, updates, _) => {
                self.check_expr_ctx(e, true, None, true);
                self.check_record_updates(updates);
            }
            ast::Expr::Access(e, _) => self.check_expr_ctx(e, true, None, true),
            ast::Expr::Paren(_, e, _) => self.check_expr(e),
            ast::Expr::Section(_)
            | ast::Expr::Hole(_)
            | ast::Expr::Ident(_)
            | ast::Expr::Constructor(_)
            | ast::Expr::Symbol(_)
            | ast::Expr::Boolean(_)
            | ast::Expr::Char(_)
            | ast::Expr::Str(_)
            | ast::Expr::Number(_)
            | ast::Expr::HexInt(_)
            | ast::Expr::Error(_) => {}
        }
    }

    fn check_do_stmt(&mut self, stmt: &ast::DoStmt) {
        match stmt {
            ast::DoStmt::Stmt(_, e) => self.check_expr(e),
            ast::DoStmt::Let(bindings) => self.check_let_bindings(bindings),
        }
    }

    fn check_let_bindings(&mut self, bindings: &[ast::LetBinding]) {
        for b in bindings {
            match b {
                ast::LetBinding::Name(_, _, ge) => self.check_guarded_expr(ge),
                ast::LetBinding::Pattern(_, e) => self.check_expr(e),
                ast::LetBinding::Sig(_, t) => self.check_typ(t),
            }
        }
    }

    fn check_guarded_expr(&mut self, ge: &ast::GuardedExpr) {
        match ge {
            ast::GuardedExpr::Unconditional(e) => self.check_expr(e),
            ast::GuardedExpr::Guarded(arms) => {
                for (guards, e) in arms {
                    for g in guards {
                        // A guard is followed by `= body` / `-> body`, so it is non-tail.
                        match g {
                            ast::Guard::Expr(e) => self.check_expr_nontail(e),
                            ast::Guard::Binder(_, e) => self.check_expr_nontail(e),
                        }
                    }
                    self.check_expr(e);
                }
            }
        }
    }

    fn check_record_updates(&mut self, updates: &[ast::RecordUpdate]) {
        for u in updates {
            match u {
                ast::RecordUpdate::Leaf(_, e) => self.check_expr(e),
                ast::RecordUpdate::Branch(_, us) => self.check_record_updates(us),
            }
        }
    }

    // --- Type traversal ---

    fn check_typ(&mut self, typ: &ast::Typ) {
        self.check_typ_ctx(typ, false, None);
    }

    fn check_typ_ctx(&mut self, typ: &ast::Typ, inside_app_or_op: bool, outer_op: Option<Ud>) {
        rule_unnecessary_typ_parens(
            typ,
            self.source,
            inside_app_or_op,
            outer_op,
            &mut self.diagnostics,
        );
        self.recurse_typ(typ);
    }

    fn recurse_typ(&mut self, typ: &ast::Typ) {
        match typ {
            ast::Typ::App(a, b) => {
                self.check_typ_ctx(a, true, None);
                self.check_typ_ctx(b, true, None);
            }
            ast::Typ::Op(a, qop, b) => {
                let op_ud = (qop.1).0 .0;
                self.check_typ_ctx(a, true, Some(op_ud));
                self.check_typ_ctx(b, true, Some(op_ud));
            }
            ast::Typ::Arr(a, b) => {
                self.check_typ_ctx(a, true, None);
                self.check_typ(b);
            }
            ast::Typ::Kinded(a, b) => {
                self.check_typ(a);
                self.check_typ(b);
            }
            ast::Typ::Forall(bindings, inner) => {
                for ast::TypVarBinding(_, k, _) in bindings {
                    if let Some(t) = k {
                        self.check_typ(t);
                    }
                }
                self.check_typ(inner);
            }
            ast::Typ::Constrained(ast::Constraint(_, args), inner) => {
                for a in args {
                    self.check_typ_ctx(a, true, None);
                }
                self.check_typ(inner);
            }
            ast::Typ::Paren(_, inner, _) => self.check_typ(inner),
            ast::Typ::Record(s) | ast::Typ::Row(s) => self.check_row(&s.0),
            ast::Typ::Wildcard(_)
            | ast::Typ::Var(_)
            | ast::Typ::Constructor(_)
            | ast::Typ::Symbol(_)
            | ast::Typ::Str(_)
            | ast::Typ::Int(..)
            | ast::Typ::Hole(_)
            | ast::Typ::Error(_) => {}
        }
    }

    fn check_row(&mut self, row: &ast::Row) {
        for (_, t) in &row.0 {
            self.check_typ(t);
        }
        if let Some(ext) = &row.1 {
            self.check_typ(ext);
        }
    }

    fn check_constraint(&mut self, c: &ast::Constraint) {
        for a in &c.1 {
            self.check_typ_ctx(a, true, None);
        }
    }

    fn check_decl(&mut self, decl: &ast::Decl) {
        match decl {
            ast::Decl::Def(_, _, ge) => self.check_guarded_expr(ge),
            ast::Decl::Sig(_, t) | ast::Decl::Foreign(_, t) | ast::Decl::ForeignData(_, t) => {
                self.check_typ(t);
            }
            ast::Decl::Instance(_, head, bindings) => {
                if let Some(constraints) = &head.0 {
                    for c in constraints {
                        self.check_constraint(c);
                    }
                }
                for t in &head.2 {
                    self.check_typ_ctx(t, true, None);
                }
                for b in bindings {
                    match b {
                        ast::InstBinding::Def(_, _, ge) => self.check_guarded_expr(ge),
                        ast::InstBinding::Sig(_, t) => self.check_typ(t),
                    }
                }
            }
            ast::Decl::Class(constraints, _, _, _, members) => {
                if let Some(constraints) = constraints {
                    for c in constraints {
                        self.check_constraint(c);
                    }
                }
                for ast::ClassMember(_, t) in members {
                    self.check_typ(t);
                }
            }
            ast::Decl::Data(_, _, ctors) => {
                for (_, args) in ctors {
                    for t in args {
                        self.check_typ_ctx(t, true, None);
                    }
                }
            }
            ast::Decl::Type(_, _, t)
            | ast::Decl::DataKind(_, t)
            | ast::Decl::TypeKind(_, t)
            | ast::Decl::NewTypeKind(_, t)
            | ast::Decl::ClassKind(_, t) => {
                self.check_typ(t);
            }
            ast::Decl::NewType(_, _, _, t) => {
                self.check_typ_ctx(t, true, None);
            }
            ast::Decl::FixityTyp(_, _, t, _) => self.check_typ(t),
            ast::Decl::Fixity(_, _, e, _) => self.check_expr(e),
            ast::Decl::Derive(_, _) | ast::Decl::Role(_, _) => {}
        }
    }
}

// ---------------------------------------------------------------------------
// PAY-3690: docstring comment spacing `-- | `
// ---------------------------------------------------------------------------

/// Map a byte offset in `source` to a 0-based `(line, column)`, where `column`
/// is a byte offset within the line. Matches the column convention the lexer
/// uses for AST spans.
fn byte_to_pos(line_starts: &[usize], byte: usize) -> (usize, usize) {
    let line = line_starts.partition_point(|&s| s <= byte) - 1;
    (line, byte - line_starts[line])
}

/// Given a line-comment slice (starting with `--`), decide whether it is a
/// docstring marker (`--`, optional spaces, `|`) that needs re-spacing: exactly
/// one space before `|` and at least one after (when it has content). Extra
/// spaces after `|` are preserved (multi-line docstring indentation). Returns
/// `(prefix_len, replacement)` for the `--…|…` prefix, or `None` for
/// non-docstring comments and already-correct ones.
fn docstring_prefix_fix(comment: &str) -> Option<(usize, String)> {
    let after_dashes = comment.strip_prefix("--")?;
    let spaces_before = after_dashes.len() - after_dashes.trim_start_matches(' ').len();
    let after_spaces = &after_dashes[spaces_before..];
    // Only a `|` immediately after the (optional) spaces marks a docstring.
    let after_pipe = after_spaces.strip_prefix('|')?;
    let spaces_after = after_pipe.len() - after_pipe.trim_start_matches(' ').len();
    let content = &after_pipe[spaces_after..];
    let has_content = !content.is_empty();

    // Require exactly one space before `|`, and — when there is content — *at
    // least* one space after. Extra spaces after `|` are intentional
    // indentation (common in multi-line docstrings), so they're preserved.
    let after_ok = if has_content {
        spaces_after >= 1
    } else {
        spaces_after == 0
    };
    if spaces_before == 1 && after_ok {
        return None;
    }

    let prefix_len = 2 + spaces_before + 1 + spaces_after;
    let kept_spaces_after = if has_content { spaces_after.max(1) } else { 0 };
    let replacement = format!("-- |{}", " ".repeat(kept_spaces_after));
    Some((prefix_len, replacement))
}

/// Scan line comments for mis-spaced docstring markers (`--|`, `-- |x`, …) and
/// emit a fixable warning that normalizes them to `-- | `. Comments are not in
/// the AST, so this is a lexer-level pass. String literals are lexed as
/// separate tokens, so `--|` inside a string is never seen here. (PAY-3690)
fn check_docstring_comments(source: &str, fi: ast::Fi, out: &mut Vec<StyleDiagnostic>) {
    use logos::Logos as _;
    let starts = line_starts(source);
    for (tok, byte_span) in crate::lexer::Token::lexer(source).spanned() {
        let Ok(crate::lexer::Token::LineComment(_)) = tok else {
            continue;
        };
        let text = &source[byte_span.start..byte_span.end];
        let Some((prefix_len, replacement)) = docstring_prefix_fix(text) else {
            continue;
        };
        let (line, col) = byte_to_pos(&starts, byte_span.start);
        let span = Span::Known(fi, (line, col), (line, col + prefix_len));
        out.push(StyleDiagnostic {
            cursor_span: span,
            expr_span: span,
            action: StyleAction::WarnAndFix {
                message: "Docstring comment should use `-- | ` (single space around `|`)".into(),
                title: "Fix docstring comment spacing".into(),
                replacement,
            },
        });
    }
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

pub fn check_module(module: &ast::Module, source: &str, fi: ast::Fi) -> Vec<StyleDiagnostic> {
    // Approximate the Python `ignore_files` set: if the module defines its own
    // `pure` — a top-level `Def`/`Sig` or a type-class member named `pure`
    // (e.g. `Control.Applicative`) — suppress the unqualified-`pure` rule for
    // the whole module. (PAY-3688)
    let module_defines_pure = module.1.iter().any(|decl| match decl {
        ast::Decl::Def(name, _, _) | ast::Decl::Sig(name, _) => (name.0).0 == Ud::new("pure"),
        ast::Decl::Class(_, _, _, _, members) => members
            .iter()
            .any(|ast::ClassMember(name, _)| (name.0).0 == Ud::new("pure")),
        _ => false,
    });
    let mut checker = StyleChecker::new(source, module_defines_pure);
    for decl in &module.1 {
        checker.check_decl(decl);
    }
    // Header imports (`import Foo as Bar`) are not decls; traverse them here.
    if let Some(header) = &module.0 {
        // Modules re-exported via `module X` in the export list — aliasing an
        // import to one of these is the intentional re-export pattern.
        let exported_modules: Vec<Ud> = header
            .1
            .iter()
            .flatten()
            .filter_map(|e| match e {
                ast::Export::Module(m) => Some((m.0).0),
                _ => None,
            })
            .collect();
        for imp in &header.2 {
            rule_import_exact_name(imp, &exported_modules, source, &mut checker.diagnostics);
            rule_import_ctx_naming(imp, source, &mut checker.diagnostics);
        }
    }
    check_docstring_comments(source, fi, &mut checker.diagnostics);
    checker.diagnostics
}

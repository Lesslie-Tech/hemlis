use crate::ast::{self, Ast, Span, Ud};

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// A style diagnostic produced by the checker.
/// The LSP layer converts this into a Fixable + optional warning diagnostic.
pub struct StyleDiagnostic {
    /// Span used for cursor matching (e.g. the operator itself).
    pub cursor_span: Span,
    /// Span of the expression to replace.
    pub expr_span: Span,
    /// Code action title shown in the editor.
    pub title: String,
    /// Replacement text for the expression.
    pub replacement: String,
    /// Warning message shown as a diagnostic. None = code action only.
    pub message: Option<String>,
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

fn byte_to_line_col(source: &str, byte_pos: usize) -> (usize, usize) {
    let starts = line_starts(source);
    for (i, &start) in starts.iter().enumerate().rev() {
        if start <= byte_pos {
            return (i, byte_pos - start);
        }
    }
    (0, byte_pos)
}

fn source_text<'a>(source: &'a str, span: &Span) -> Option<&'a str> {
    let (lo, hi) = span_to_byte_range(source, span)?;
    source.get(lo..hi)
}

/// Compute the full byte range of an expression, extending to cover
/// parenthesis delimiters that aren't captured by the derived span.
fn expr_byte_range(source: &str, expr: &ast::Expr) -> Option<(usize, usize)> {
    let (lo, hi) = span_to_byte_range(source, &expr.span())?;
    // Extend right if the expression (or its rightmost child) is a Paren
    let hi = if has_trailing_paren(expr) {
        match source[hi..].find(')') {
            Some(i) => hi + i + 1,
            None => hi,
        }
    } else {
        hi
    };
    Some((lo, hi))
}

/// Check if an expression has an uncovered trailing ')'.
fn has_trailing_paren(expr: &ast::Expr) -> bool {
    match expr {
        ast::Expr::Paren(_) => true,
        ast::Expr::Op(_, _, rhs) => has_trailing_paren(rhs),
        ast::Expr::App(_, arg) => has_trailing_paren(arg),
        _ => false,
    }
}

/// Extract source text for an expression, correctly including parentheses
/// for `Paren` nodes (whose derived span only covers the inner expression).
fn expr_text(source: &str, expr: &ast::Expr) -> Option<String> {
    if let ast::Expr::Paren(_) = expr {
        let (lo, hi) = span_to_byte_range(source, &expr.span())?;
        let open = source[..lo].rfind('(')?;
        let close = hi + source[hi..].find(')')?;
        Some(source[open..=close].to_string())
    } else {
        source_text(source, &expr.span()).map(|s| s.to_string())
    }
}

/// Compute the full Span for an expression, extending for trailing parens.
fn expr_full_span(source: &str, expr: &ast::Expr) -> Span {
    let base = expr.span();
    let fi = match base {
        Span::Known(fi, _, _) => fi,
        _ => return base,
    };
    match expr_byte_range(source, expr) {
        Some((lo, hi)) => {
            let lo_lc = byte_to_line_col(source, lo);
            let hi_lc = byte_to_line_col(source, hi);
            Span::Known(fi, lo_lc, hi_lc)
        }
        None => base,
    }
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

fn needs_parens(expr: &ast::Expr) -> bool {
    matches!(
        expr,
        ast::Expr::Op(..)
            | ast::Expr::Infix(..)
            | ast::Expr::Lambda(..)
            | ast::Expr::IfThenElse(..)
            | ast::Expr::Let(..)
            | ast::Expr::Case(..)
            | ast::Expr::Do(..)
            | ast::Expr::Ado(..)
            | ast::Expr::Typed(..)
    )
}

fn maybe_paren(text: &str, expr: &ast::Expr) -> String {
    if needs_parens(expr) {
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
                let expr_span = expr_full_span(source, expr);
                let lhs_text = expr_text(source, lhs).unwrap_or_else(|| "_".into());
                let rhs_text = expr_text(source, rhs).unwrap_or_else(|| "_".into());

                let new_lhs = maybe_paren(&rhs_text, rhs);
                let new_rhs = maybe_paren(&lhs_text, lhs);

                out.push(StyleDiagnostic {
                    cursor_span: expr_span,
                    expr_span,
                    title: format!("Replace `{}` with `{}`", forbidden.from, forbidden.to),
                    replacement: format!("{} {} {}", new_lhs, forbidden.to, new_rhs),
                    message: Some(format!(
                        "Prefer `{}` over `{}` ({})",
                        forbidden.to, forbidden.from, forbidden.description
                    )),
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
    OpSwap { from: "$", to: "#", wrap: false },    // prec 0 → prec 1 (higher is safe)
    OpSwap { from: "#", to: "$", wrap: true },     // prec 1 → prec 0
    OpSwap { from: "<$>", to: "<#>", wrap: true }, // prec 4 → prec 1
    OpSwap { from: "<#>", to: "<$>", wrap: false }, // prec 1 → prec 4 (higher is safe)
];

fn rule_operator_swap(expr: &ast::Expr, source: &str, out: &mut Vec<StyleDiagnostic>) {
    if let ast::Expr::Op(lhs, qop, rhs) = expr {
        let op_ud = (qop.1).0 .0;
        for swap in SWAP_OPS {
            if op_ud == Ud::new(swap.from) {
                let op_span = (qop.1).0 .1;
                let expr_span = expr_full_span(source, expr);
                let lhs_text = expr_text(source, lhs).unwrap_or_else(|| "_".into());
                let rhs_text = expr_text(source, rhs).unwrap_or_else(|| "_".into());

                let new_lhs = maybe_paren(&rhs_text, rhs);
                let new_rhs = maybe_paren(&lhs_text, lhs);

                let replacement = if swap.wrap {
                    format!("({} {} {})", new_lhs, swap.to, new_rhs)
                } else {
                    format!("{} {} {}", new_lhs, swap.to, new_rhs)
                };

                out.push(StyleDiagnostic {
                    cursor_span: op_span,
                    expr_span,
                    title: format!("Replace `{}` with `{}`", swap.from, swap.to),
                    replacement,
                    message: None,
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

        let expr_span = expr_full_span(source, expr);
        let func_text = expr_text(source, func).unwrap_or_else(|| "_".into());
        let arg_text = expr_text(source, arg).unwrap_or_else(|| "_".into());

        // If arg is already parenthesized, use it as-is; otherwise wrap in parens
        let parened_arg = if matches!(arg.as_ref(), ast::Expr::Paren(_)) {
            arg_text.clone()
        } else {
            format!("({})", arg_text)
        };

        // Func needs parens if it's a case/lambda/do/etc that would swallow the arg
        let parened_func = if needs_parens(func) {
            format!("({})", func_text)
        } else {
            func_text.clone()
        };

        out.push(StyleDiagnostic {
            cursor_span: op_span,
            expr_span,
            title: format!("Replace `{}` with `()`", op_name),
            replacement: format!("{} {}", parened_func, parened_arg),
            message: None,
        });
    }
}

// ---------------------------------------------------------------------------
// AST Traversal
// ---------------------------------------------------------------------------

struct StyleChecker<'a> {
    source: &'a str,
    diagnostics: Vec<StyleDiagnostic>,
}

impl<'a> StyleChecker<'a> {
    fn new(source: &'a str) -> Self {
        Self {
            source,
            diagnostics: Vec::new(),
        }
    }

    fn check_expr(&mut self, expr: &ast::Expr) {
        // ===== RULES (add new rules here) =====
        rule_forbidden_operator(expr, self.source, &mut self.diagnostics);
        rule_operator_swap(expr, self.source, &mut self.diagnostics);
        rule_op_to_parens(expr, self.source, &mut self.diagnostics);
        // =======================================

        self.recurse_expr(expr);
    }

    fn recurse_expr(&mut self, expr: &ast::Expr) {
        match expr {
            ast::Expr::Typed(e, _) => self.check_expr(e),
            ast::Expr::Op(a, _, b) => {
                self.check_expr(a);
                self.check_expr(b);
            }
            ast::Expr::Infix(a, o, b) => {
                self.check_expr(a);
                self.check_expr(o);
                self.check_expr(b);
            }
            ast::Expr::Negate(e) => self.check_expr(e),
            ast::Expr::App(a, b) => {
                self.check_expr(a);
                self.check_expr(b);
            }
            ast::Expr::Vta(e, _) => self.check_expr(e),
            ast::Expr::IfThenElse(_, c, t, f) => {
                self.check_expr(c);
                self.check_expr(t);
                self.check_expr(f);
            }
            ast::Expr::Do(_, stmts) | ast::Expr::Ado(_, stmts, _) => {
                for stmt in stmts {
                    self.check_do_stmt(stmt);
                }
                if let ast::Expr::Ado(_, _, e) = expr {
                    self.check_expr(e);
                }
            }
            ast::Expr::Lambda(_, _, e) => self.check_expr(e),
            ast::Expr::Let(_, bindings, e) => {
                self.check_let_bindings(bindings);
                self.check_expr(e);
            }
            ast::Expr::Where(_, e, bindings) => {
                self.check_expr(e);
                self.check_let_bindings(bindings);
            }
            ast::Expr::Case(_, scrutinees, branches) => {
                for e in scrutinees {
                    self.check_expr(e);
                }
                for ast::CaseBranch(_, ge) in branches {
                    self.check_guarded_expr(ge);
                }
            }
            ast::Expr::Array(_, es, _) => {
                for e in es {
                    self.check_expr(e);
                }
            }
            ast::Expr::Record(_, fields, _) => {
                for field in fields {
                    if let ast::RecordLabelExpr::Field(_, e) = field {
                        self.check_expr(e);
                    }
                }
            }
            ast::Expr::Update(e, updates) => {
                self.check_expr(e);
                self.check_record_updates(updates);
            }
            ast::Expr::Access(e, _) => self.check_expr(e),
            ast::Expr::Paren(e) => self.check_expr(e),
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
                ast::LetBinding::Sig(_, _) => {}
            }
        }
    }

    fn check_guarded_expr(&mut self, ge: &ast::GuardedExpr) {
        match ge {
            ast::GuardedExpr::Unconditional(e) => self.check_expr(e),
            ast::GuardedExpr::Guarded(arms) => {
                for (guards, e) in arms {
                    for g in guards {
                        match g {
                            ast::Guard::Expr(e) => self.check_expr(e),
                            ast::Guard::Binder(_, e) => self.check_expr(e),
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

    fn check_decl(&mut self, decl: &ast::Decl) {
        match decl {
            ast::Decl::Def(_, _, ge) => self.check_guarded_expr(ge),
            ast::Decl::Instance(_, _, bindings) => {
                for b in bindings {
                    match b {
                        ast::InstBinding::Def(_, _, ge) => self.check_guarded_expr(ge),
                        ast::InstBinding::Sig(_, _) => {}
                    }
                }
            }
            ast::Decl::Fixity(_, _, e, _) => self.check_expr(e),
            _ => {}
        }
    }
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

pub fn check_module(module: &ast::Module, source: &str) -> Vec<StyleDiagnostic> {
    let mut checker = StyleChecker::new(source);
    for decl in &module.1 {
        checker.check_decl(decl);
    }
    checker.diagnostics
}

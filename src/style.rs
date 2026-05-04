use crate::ast::{self, Ast, Span, Ud};
use crate::parser::op_fixity;

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
            title: format!("Replace `{}` with `()`", op_name),
            replacement: format!("{} {}", parened_func, parened_arg),
            message: None,
        });
    }
}

// ---------------------------------------------------------------------------
// Unnecessary parentheses (PAY-3104)
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
                title: "Remove unnecessary parentheses".into(),
                replacement: text.to_string(),
                message: Some("Unnecessary parentheses".into()),
            });
        }
    }
}

/// Simple heuristic for unnecessary parentheses:
/// 1. Double parens: `((x))` → `(x)`
/// 2. Atom in parens: `(x)` → `x` (single ident/literal/array/record)
/// 3. Paren not inside App/Op: the parens are the whole expression in their
///    context (definition RHS, do-bind, let-bind, case scrutinee, etc.)
/// 4. Same operator inside as outside: `(a + b) + c` → `a + b + c`
fn rule_unnecessary_parens(
    expr: &ast::Expr,
    source: &str,
    inside_app_or_op: bool,
    outer_op: Option<Ud>,
    out: &mut Vec<StyleDiagnostic>,
) {
    if let ast::Expr::Paren(_, inner, _) = expr {
        let same_op =
            if let (Some(outer), ast::Expr::Op(_, inner_qop, _)) = (outer_op, inner.as_ref()) {
                (inner_qop.1).0 .0 == outer
            } else {
                false
            };
        let removable = matches!(inner.as_ref(), ast::Expr::Paren(..))
            || is_atom(inner)
            || !inside_app_or_op
            || same_op;
        if removable {
            emit_remove_parens(expr, source, out);
        }
    }
}

// ---------------------------------------------------------------------------
// Unnecessary type parentheses (PAY-3104)
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
                title: "Remove unnecessary parentheses".into(),
                replacement: text.to_string(),
                message: Some("Unnecessary parentheses".into()),
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
        self.check_expr_ctx(expr, false, None);
    }

    fn check_expr_ctx(&mut self, expr: &ast::Expr, inside_app_or_op: bool, outer_op: Option<Ud>) {
        // ===== RULES (add new rules here) =====
        rule_forbidden_operator(expr, self.source, &mut self.diagnostics);
        rule_operator_swap(expr, self.source, &mut self.diagnostics);
        rule_op_to_parens(expr, self.source, &mut self.diagnostics);
        rule_unnecessary_parens(
            expr,
            self.source,
            inside_app_or_op,
            outer_op,
            &mut self.diagnostics,
        );
        // =======================================

        self.recurse_expr(expr);
    }

    fn recurse_expr(&mut self, expr: &ast::Expr) {
        match expr {
            ast::Expr::Typed(e, t) => {
                self.check_expr_ctx(e, true, None);
                self.check_typ(t);
            }
            ast::Expr::Op(a, qop, b) => {
                let op_ud = (qop.1).0 .0;
                self.check_expr_ctx(a, true, Some(op_ud));
                self.check_expr_ctx(b, true, Some(op_ud));
            }
            ast::Expr::Infix(a, o, b) => {
                self.check_expr_ctx(a, true, None);
                self.check_expr(o);
                self.check_expr_ctx(b, true, None);
            }
            ast::Expr::Negate(e) => self.check_expr(e),
            ast::Expr::App(a, b) => {
                self.check_expr_ctx(a, true, None);
                self.check_expr_ctx(b, true, None);
            }
            ast::Expr::Vta(e, t) => {
                self.check_expr(e);
                self.check_typ_ctx(t, true, None);
            }
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
            ast::Expr::Update(e, _, updates, _) => {
                self.check_expr_ctx(e, true, None);
                self.check_record_updates(updates);
            }
            ast::Expr::Access(e, _) => self.check_expr_ctx(e, true, None),
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
// Entry point
// ---------------------------------------------------------------------------

pub fn check_module(module: &ast::Module, source: &str) -> Vec<StyleDiagnostic> {
    let mut checker = StyleChecker::new(source);
    for decl in &module.1 {
        checker.check_decl(decl);
    }
    checker.diagnostics
}

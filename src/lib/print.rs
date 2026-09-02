//! A PureScript pretty-printer.
//!
//! This is a skeleton: it covers module headers, imports/exports, simple value
//! declarations, and the common expression/type/binder forms. Anything not yet
//! implemented falls back to slicing the original source text verbatim for that
//! node's span, so printing never panics or drops content - it just leaves
//! unsupported constructs unformatted until they're implemented.
//!
//! Layout decisions (whether a bracketed list prints on one line or one entry
//! per line) are made eagerly from the source spans already on every AST node:
//! if a list's first and last element don't start/end on the same source line,
//! it is printed expanded. No line-fitting/backtracking is involved.

use crate::ast::*;
use crate::lexer::{SourceToken, Token};
use crate::source::source_text;

const INDENT: usize = 2;

pub fn print_module(source: &str, module: &Module, comments: &[SourceToken<'_>]) -> String {
    let mut p = Printer::new(source, comments);
    p.print_module(module);
    p.flush_all_comments();
    if !p.out.ends_with('\n') {
        p.out.push('\n');
    }
    p.out
}

struct Printer<'s> {
    source: &'s str,
    comments: &'s [SourceToken<'s>],
    comment_idx: usize,
    out: String,
    indent: usize,
}

impl<'s> Printer<'s> {
    fn new(source: &'s str, comments: &'s [SourceToken<'s>]) -> Self {
        Printer {
            source,
            comments,
            comment_idx: 0,
            out: String::new(),
            indent: 0,
        }
    }

    // -- low level writer --------------------------------------------------

    fn raw(&mut self, s: &str) {
        self.out.push_str(s);
    }

    fn newline(&mut self) {
        while self.out.ends_with(' ') {
            self.out.pop();
        }
        self.out.push('\n');
        for _ in 0..self.indent * INDENT {
            self.out.push(' ');
        }
    }

    /// Break to a new line only if we're not already at the start of one -
    /// avoids piling up blank lines when a caller already ensured one.
    fn ensure_fresh_line(&mut self) {
        if !self.out.is_empty() && !self.out.ends_with('\n') {
            self.newline();
        }
    }

    fn indent_in(&mut self) {
        self.indent += 1;
    }

    fn indent_out(&mut self) {
        self.indent = self.indent.saturating_sub(1);
    }

    fn text(&self, span: Span) -> &'s str {
        source_text(self.source, &span).unwrap_or("")
    }

    /// Print a leaf AST node (identifier, literal, ...) by slicing its span out
    /// of the original source - this is always faithful since these nodes never
    /// carry sub-structure a formatter would want to reflow.
    fn lit<T: Ast>(&mut self, x: &T) {
        let t = self.text(x.span());
        self.raw(t);
    }

    /// Last-resort fallback for AST shapes not yet handled: print the original
    /// source text for this node verbatim.
    fn raw_fallback<T: Ast>(&mut self, x: &T) {
        self.lit(x);
    }

    // -- comments -------------------------------------------------------

    /// Emit every pending comment that starts strictly before `line`, each on
    /// its own line at the current indent.
    fn flush_comments_before(&mut self, line: usize) {
        while self.comment_idx < self.comments.len() {
            let (_, span) = &self.comments[self.comment_idx];
            if span.lo().0 >= line {
                break;
            }
            self.emit_pending_comment();
        }
    }

    fn flush_all_comments(&mut self) {
        while self.comment_idx < self.comments.len() {
            self.emit_pending_comment();
        }
    }

    fn emit_pending_comment(&mut self) {
        let (t, _) = &self.comments[self.comment_idx];
        if let Ok(Token::LineComment(s) | Token::BlockComment(s)) = t {
            let s = *s;
            self.ensure_fresh_line();
            self.raw(s);
            self.newline();
        }
        self.comment_idx += 1;
    }

    // -- lists ---------------------------------------------------------

    /// True if the span of the first and last item don't share a source line -
    /// i.e. the user originally wrote this list expanded across lines.
    fn is_multiline(first: Span, last: Span) -> bool {
        first.lo().0 != last.hi().0
    }

    /// True if `a` is a type signature immediately followed by its own
    /// definition - these stay adjacent, with no blank line between them.
    fn decls_are_glued(a: &Decl, b: &Decl) -> bool {
        matches!(a, Decl::Sig(..)) && a.ud() == b.ud()
    }

    /// Print `items` as `open item, item, item close` or, if the source had
    /// them expanded, one per line with leading commas:
    /// ```text
    /// open item
    /// , item
    /// close
    /// ```
    /// `pad` adds a space just inside the brackets on the flat (single-line) path,
    /// e.g. `{ a: 1, b: 2 }` vs `[1, 2, 3]`. The expanded path is always padded,
    /// since the leading-comma layout needs the space regardless.
    fn list<T>(
        &mut self,
        open: &str,
        close: &str,
        pad: bool,
        items: &[T],
        span_of: impl Fn(&T) -> Span,
        mut print_item: impl FnMut(&mut Self, &T),
    ) {
        if items.is_empty() {
            self.raw(open);
            self.raw(close);
            return;
        }

        let multiline =
            items.len() > 1 && Self::is_multiline(span_of(&items[0]), span_of(&items[items.len() - 1]));

        if !multiline {
            self.raw(open);
            if pad {
                self.raw(" ");
            }
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    self.raw(", ");
                }
                print_item(self, item);
            }
            if pad {
                self.raw(" ");
            }
            self.raw(close);
        } else {
            self.indent_in();
            self.newline();
            self.raw(open);
            self.raw(" ");
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    self.newline();
                    self.raw(", ");
                }
                print_item(self, item);
            }
            self.newline();
            self.raw(close);
            self.indent_out();
        }
    }

    // -- module ----------------------------------------------------------

    fn print_module(&mut self, m: &Module) {
        let mut first = true;
        if let Some(h) = &m.0 {
            self.print_header(h);
            first = false;
        }
        let mut prev: Option<&Decl> = None;
        for decl in &m.1 {
            let glued = prev.is_some_and(|p| Self::decls_are_glued(p, decl));
            if !first && !glued {
                self.raw("\n");
            }
            first = false;
            self.flush_comments_before(decl.span().lo().0);
            self.print_decl(decl);
            self.raw("\n");
            prev = Some(decl);
        }
    }

    fn print_header(&mut self, h: &Header) {
        let Header(name, exports, imports, ..) = h;
        self.raw("module ");
        self.lit(name);
        self.raw(" ");
        if let Some(exports) = exports {
            self.list(
                "(",
                ")",
                false,
                exports,
                |e| e.span(),
                |p, e| p.print_export(e),
            );
            self.raw(" ");
        }
        self.raw("where");
        self.newline();
        for imp in imports {
            self.flush_comments_before(imp.span().lo().0);
            self.print_import_decl(imp);
            self.newline();
        }
    }

    fn print_export(&mut self, e: &Export) {
        match e {
            Export::Value(n) => self.lit(n),
            Export::Symbol(s) => {
                self.raw("(");
                self.lit(s);
                self.raw(")");
            }
            Export::Typ(n) => self.lit(n),
            Export::TypSymbol(s) => {
                self.raw("type (");
                self.lit(s);
                self.raw(")");
            }
            Export::TypDat(n, dm) => {
                self.lit(n);
                self.print_data_member(dm);
            }
            Export::Class(n) => {
                self.raw("class ");
                self.lit(n);
            }
            Export::Module(n) => {
                self.raw("module ");
                self.lit(n);
            }
        }
    }

    fn print_data_member(&mut self, dm: &DataMember) {
        match dm {
            DataMember::All(_) => self.raw("(..)"),
            DataMember::Some(names) => {
                self.list("(", ")", false, names, |n| n.span(), |p, n| p.lit(n));
            }
        }
    }

    fn print_import_decl(&mut self, i: &ImportDecl) {
        self.raw("import ");
        self.lit(&i.from);
        if !i.hiding.is_empty() {
            self.raw(" hiding ");
            self.list(
                "(",
                ")",
                false,
                &i.hiding,
                |x| x.span(),
                |p, x| p.print_import(x),
            );
        } else if let Some(names) = &i.names {
            self.raw(" ");
            self.list(
                "(",
                ")",
                false,
                names,
                |x| x.span(),
                |p, x| p.print_import(x),
            );
        }
        if let Some(to) = &i.to {
            self.raw(" as ");
            self.lit(to);
        }
    }

    fn print_import(&mut self, i: &Import) {
        match i {
            Import::Value(_, n) => self.lit(n),
            Import::Symbol(_, s) => {
                self.raw("(");
                self.lit(s);
                self.raw(")");
            }
            Import::Typ(_, n) => self.lit(n),
            Import::TypDat(_, n, dm) => {
                self.lit(n);
                self.print_data_member(dm);
            }
            Import::TypSymbol(_, s) => {
                self.raw("type (");
                self.lit(s);
                self.raw(")");
            }
            Import::Class(_, n) => {
                self.raw("class ");
                self.lit(n);
            }
        }
    }

    // -- declarations ------------------------------------------------------

    fn print_decl(&mut self, d: &Decl) {
        match d {
            Decl::Sig(name, typ) => {
                self.lit(name);
                self.raw(" :: ");
                self.print_typ(typ);
            }
            Decl::Def(name, binders, ge) => {
                self.lit(name);
                for b in binders {
                    self.raw(" ");
                    self.print_binder(b);
                }
                match ge {
                    GuardedExpr::Unconditional(e) => {
                        self.raw(" = ");
                        self.print_expr(e);
                    }
                    GuardedExpr::Guarded(_) => self.raw_fallback(ge),
                }
            }
            _ => self.raw_fallback(d),
        }
    }

    // -- binders -------------------------------------------------------

    fn print_binder(&mut self, b: &Binder) {
        match b {
            Binder::Wildcard(_) => self.raw("_"),
            Binder::Var(n) => self.lit(n),
            Binder::Constructor(n) => self.lit(n),
            Binder::Boolean(x) => self.lit(x),
            Binder::Char(x) => self.lit(x),
            Binder::Str(x) => self.lit(x),
            Binder::Number(neg, x) => {
                if *neg {
                    self.raw("-");
                }
                self.lit(x);
            }
            Binder::Named(n, b) => {
                self.lit(n);
                self.raw("@");
                self.print_binder(b);
            }
            Binder::Typed(b, t) => {
                self.print_binder(b);
                self.raw(" :: ");
                self.print_typ(t);
            }
            Binder::App(f, a) => {
                self.print_binder(f);
                self.raw(" ");
                self.print_binder(a);
            }
            Binder::Paren(_, inner, _) => {
                self.raw("(");
                self.print_binder(inner);
                self.raw(")");
            }
            Binder::Array(items) => {
                self.list("[", "]", false, items, |x| x.span(), |p, x| p.print_binder(x));
            }
            _ => self.raw_fallback(b),
        }
    }

    // -- types -----------------------------------------------------------

    fn print_typ(&mut self, t: &Typ) {
        match t {
            Typ::Wildcard(_) => self.raw("_"),
            Typ::Var(n) => self.lit(n),
            Typ::Constructor(n) => self.lit(n),
            Typ::Symbol(s) => self.lit(s),
            Typ::Str(s) => self.lit(s),
            Typ::Int(neg, i) => {
                if *neg {
                    self.raw("-");
                }
                self.lit(i);
            }
            Typ::Hole(h) => self.lit(h),
            Typ::Paren(_, inner, _) => {
                self.raw("(");
                self.print_typ(inner);
                self.raw(")");
            }
            Typ::Arr(a, b) => {
                self.print_typ(a);
                self.raw(" -> ");
                self.print_typ(b);
            }
            Typ::App(f, a) => {
                self.print_typ(f);
                self.raw(" ");
                self.print_typ(a);
            }
            Typ::Op(l, op, r) => {
                self.print_typ(l);
                self.raw(" ");
                self.lit(op);
                self.raw(" ");
                self.print_typ(r);
            }
            Typ::Kinded(t, k) => {
                self.print_typ(t);
                self.raw(" :: ");
                self.print_typ(k);
            }
            Typ::Constrained(c, t) => {
                self.print_constraint(c);
                self.raw(" => ");
                self.print_typ(t);
            }
            Typ::Forall(vars, t) => {
                self.raw("forall");
                for v in vars {
                    self.raw(" ");
                    self.print_typ_var_binding(v);
                }
                self.raw(". ");
                self.print_typ(t);
            }
            Typ::Record(row) => {
                self.raw("{");
                self.print_row(&row.0, true);
                self.raw("}");
            }
            Typ::Row(row) => {
                self.raw("(");
                self.print_row(&row.0, false);
                self.raw(")");
            }
            Typ::Error(_) => self.raw_fallback(t),
        }
    }

    fn print_typ_var_binding(&mut self, v: &TypVarBinding) {
        let TypVarBinding(name, kind, paren) = v;
        if *paren {
            self.raw("(");
        }
        self.lit(name);
        if let Some(k) = kind {
            self.raw(" :: ");
            self.print_typ(k);
        }
        if *paren {
            self.raw(")");
        }
    }

    fn print_constraint(&mut self, c: &Constraint) {
        let Constraint(name, args) = c;
        self.lit(name);
        for a in args {
            self.raw(" ");
            self.print_typ(a);
        }
    }

    fn print_row(&mut self, row: &Row, spaced: bool) {
        let Row(fields, tail) = row;
        if fields.is_empty() && tail.is_none() {
            return;
        }
        if spaced {
            self.raw(" ");
        }
        for (i, (label, typ)) in fields.iter().enumerate() {
            if i > 0 {
                self.raw(", ");
            }
            self.lit(label);
            self.raw(" :: ");
            self.print_typ(typ);
        }
        if let Some(tail) = tail {
            if !fields.is_empty() {
                self.raw(" ");
            }
            self.raw("| ");
            self.print_typ(tail);
        }
        if spaced {
            self.raw(" ");
        }
    }

    // -- expressions -------------------------------------------------------

    fn print_expr(&mut self, e: &Expr) {
        match e {
            Expr::Ident(n) => self.lit(n),
            Expr::Constructor(n) => self.lit(n),
            Expr::Symbol(s) => self.lit(s),
            Expr::Boolean(x) => self.lit(x),
            Expr::Char(x) => self.lit(x),
            Expr::Str(x) => self.lit(x),
            Expr::Number(x) => self.lit(x),
            Expr::HexInt(x) => self.lit(x),
            Expr::Hole(x) => self.lit(x),
            Expr::Section(_) => self.raw("_"),
            Expr::Paren(_, inner, _) => {
                self.raw("(");
                self.print_expr(inner);
                self.raw(")");
            }
            Expr::Negate(inner) => {
                self.raw("-");
                self.print_expr(inner);
            }
            Expr::Typed(inner, t) => {
                self.print_expr(inner);
                self.raw(" :: ");
                self.print_typ(t);
            }
            Expr::App(f, a) => {
                self.print_expr(f);
                self.raw(" ");
                self.print_expr(a);
            }
            Expr::Vta(f, t) => {
                self.print_expr(f);
                self.raw(" @");
                self.print_typ(t);
            }
            Expr::Op(l, op, r) => {
                self.print_expr(l);
                self.raw(" ");
                self.lit(op);
                self.raw(" ");
                self.print_expr(r);
            }
            Expr::Access(inner, labels) => {
                self.print_expr(inner);
                for l in labels {
                    self.raw(".");
                    self.lit(l);
                }
            }
            Expr::Array(_, items, _) => {
                self.list(
                    "[",
                    "]",
                    false,
                    items,
                    |x| x.span(),
                    |p, x| p.print_expr(x),
                );
            }
            Expr::Record(_, fields, _) => {
                self.list(
                    "{",
                    "}",
                    true,
                    fields,
                    |x| x.span(),
                    |p, x| p.print_record_label_expr(x),
                );
            }
            Expr::Lambda(_, binders, body) => {
                self.raw("\\");
                for (i, b) in binders.iter().enumerate() {
                    if i > 0 {
                        self.raw(" ");
                    }
                    self.print_binder(b);
                }
                self.raw(" -> ");
                self.print_expr(body);
            }
            Expr::IfThenElse(_, cond, then_e, else_e) => {
                let multiline = cond.span().lo().0 != else_e.span().hi().0;
                self.raw("if ");
                self.print_expr(cond);
                if multiline {
                    self.indent_in();
                    self.newline();
                    self.raw("then ");
                    self.print_expr(then_e);
                    self.newline();
                    self.raw("else ");
                    self.print_expr(else_e);
                    self.indent_out();
                } else {
                    self.raw(" then ");
                    self.print_expr(then_e);
                    self.raw(" else ");
                    self.print_expr(else_e);
                }
            }
            _ => self.raw_fallback(e),
        }
    }

    fn print_record_label_expr(&mut self, f: &RecordLabelExpr) {
        match f {
            RecordLabelExpr::Pun(n) => self.lit(n),
            RecordLabelExpr::Field(l, e) => {
                self.lit(l);
                self.raw(": ");
                self.print_expr(e);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::Fi;
    use crate::lexer;
    use crate::parser;
    use dashmap::DashMap;

    fn fmt(src: &str) -> String {
        let (toks, comments) = lexer::lex(src, Fi(0));
        let names = DashMap::new();
        let mut p = parser::P::new(&toks, &names);
        let m = parser::module(&mut p).expect("module should parse");
        assert!(p.errors.is_empty(), "parse errors: {:?}", p.errors);
        super::print_module(src, &m, &comments)
    }

    fn assert_idempotent(src: &str) {
        let once = fmt(src);
        let twice = fmt(&once);
        assert_eq!(once, twice, "formatting is not idempotent");
    }

    #[test]
    fn simple_module() {
        let src = "module Foo (foo) where\n\nfoo = 1\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo (foo) where\n\nfoo = 1\n");
        assert_idempotent(src);
    }

    #[test]
    fn imports_and_multiple_decls() {
        let src = "module Foo where\n\nimport Prelude\nimport Data.Array (head, tail)\n\nfoo = 1\nbar = 2\n";
        let out = fmt(src);
        assert_eq!(
            out,
            "module Foo where\nimport Prelude\nimport Data.Array (head, tail)\n\nfoo = 1\n\nbar = 2\n"
        );
        assert_idempotent(src);
    }

    #[test]
    fn array_stays_flat_when_source_is_flat() {
        let src = "module Foo where\n\nfoo = [1, 2, 3]\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\nfoo = [1, 2, 3]\n");
        assert_idempotent(src);
    }

    #[test]
    fn array_expands_when_source_has_a_newline_inside() {
        let src = "module Foo where\n\nfoo = [1,\n  2, 3]\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\nfoo =\n  [ 1\n  , 2\n  , 3\n  ]\n");
        assert_idempotent(src);
    }

    #[test]
    fn record_expands_when_source_has_a_newline_inside() {
        let src = "module Foo where\n\nfoo = { a: 1,\n  b: 2 }\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\nfoo =\n  { a: 1\n  , b: 2\n  }\n");
        assert_idempotent(src);
    }

    #[test]
    fn sig_and_binders() {
        let src = "module Foo where\n\nfoo :: Int -> Int\nfoo x = x\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\nfoo :: Int -> Int\nfoo x = x\n");
        assert_idempotent(src);
    }

    #[test]
    fn record_flat_is_padded_array_flat_is_not() {
        let src = "module Foo where\n\nfoo = { a: 1, b: 2 }\nbar = [1, 2]\n";
        let out = fmt(src);
        assert_eq!(
            out,
            "module Foo where\n\nfoo = { a: 1, b: 2 }\n\nbar = [1, 2]\n"
        );
        assert_idempotent(src);
    }

    #[test]
    fn if_then_else_multiline_is_indented() {
        let src = "module Foo where\n\nfoo = if x\n  then 1\n  else 2\n";
        let out = fmt(src);
        assert_eq!(
            out,
            "module Foo where\n\nfoo = if x\n  then 1\n  else 2\n"
        );
        assert_idempotent(src);
    }

    #[test]
    fn leading_comment_before_decl_is_kept() {
        let src = "module Foo where\n\n-- a comment\nfoo = 1\n";
        let out = fmt(src);
        assert!(out.contains("-- a comment"), "comment lost: {:?}", out);
        assert_idempotent(src);
    }

    #[test]
    fn unimplemented_construct_falls_back_to_source_and_does_not_panic() {
        let src = "module Foo where\n\nfoo = case 1 of\n  x -> x\n";
        let out = fmt(src);
        assert!(out.contains("case 1 of"), "fallback dropped content: {:?}", out);
    }
}

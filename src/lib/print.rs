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

    /// A qualifier used on its own (not immediately followed by the name it
    /// qualifies, e.g. `A.` before `do`/`ado`). The parser's `Qual` span
    /// deliberately excludes the trailing `.` (so that merging it with a
    /// following name's span still yields the right text), so a bare `Qual`
    /// needs the dot added back explicitly.
    fn print_qual(&mut self, q: &Qual) {
        self.lit(q);
        self.raw(".");
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
                self.print_guarded_expr(ge, " = ");
            }

            Decl::DataKind(name, kind) => {
                self.raw("data ");
                self.lit(name);
                self.raw(" :: ");
                self.print_typ(kind);
            }
            Decl::Data(name, vars, ctors) => {
                self.raw("data ");
                self.lit(name);
                for v in vars {
                    self.raw(" ");
                    self.print_typ_var_binding(v);
                }
                if ctors.is_empty() {
                    return;
                }
                let multiline = ctors.len() > 1
                    && Self::is_multiline(ctors[0].span(), ctors[ctors.len() - 1].span());
                self.indent_in();
                for (i, (cname, cargs)) in ctors.iter().enumerate() {
                    if multiline {
                        self.newline();
                    } else {
                        self.raw(" ");
                    }
                    self.raw(if i == 0 { "= " } else { "| " });
                    self.lit(cname);
                    for a in cargs {
                        self.raw(" ");
                        self.print_typ(a);
                    }
                }
                self.indent_out();
            }

            Decl::TypeKind(name, kind) => {
                self.raw("type ");
                self.lit(name);
                self.raw(" :: ");
                self.print_typ(kind);
            }
            Decl::Type(name, vars, typ) => {
                self.raw("type ");
                self.lit(name);
                for v in vars {
                    self.raw(" ");
                    self.print_typ_var_binding(v);
                }
                self.raw(" = ");
                self.print_typ(typ);
            }

            Decl::NewTypeKind(name, kind) => {
                self.raw("newtype ");
                self.lit(name);
                self.raw(" :: ");
                self.print_typ(kind);
            }
            Decl::NewType(name, vars, ctor, typ) => {
                self.raw("newtype ");
                self.lit(name);
                for v in vars {
                    self.raw(" ");
                    self.print_typ_var_binding(v);
                }
                self.raw(" = ");
                self.lit(ctor);
                self.raw(" ");
                self.print_typ(typ);
            }

            Decl::ClassKind(name, kind) => {
                self.raw("class ");
                self.lit(name);
                self.raw(" :: ");
                self.print_typ(kind);
            }
            Decl::Class(constraints, name, vars, fundeps, members) => {
                self.raw("class ");
                if let Some(cs) = constraints {
                    self.print_constraint_list(cs);
                    self.raw(" <= ");
                }
                self.lit(name);
                for v in vars {
                    self.raw(" ");
                    self.print_typ_var_binding(v);
                }
                if let Some(fds) = fundeps {
                    self.raw(" | ");
                    for (i, fd) in fds.iter().enumerate() {
                        if i > 0 {
                            self.raw(", ");
                        }
                        self.print_fun_dep(fd);
                    }
                }
                if !members.is_empty() {
                    self.raw(" where");
                    self.indent_in();
                    for m in members {
                        self.newline();
                        self.print_class_member(m);
                    }
                    self.indent_out();
                }
            }

            Decl::Instance(is_else, head, bindings) => {
                if *is_else {
                    self.raw("else ");
                }
                self.raw("instance ");
                self.print_inst_head(head);
                if !bindings.is_empty() {
                    self.raw(" where");
                    self.indent_in();
                    for b in bindings {
                        self.newline();
                        self.print_inst_binding(b);
                    }
                    self.indent_out();
                }
            }
            Decl::Derive(is_newtype, head) => {
                self.raw("derive ");
                if *is_newtype {
                    self.raw("newtype ");
                }
                self.raw("instance ");
                self.print_inst_head(head);
            }

            Decl::Foreign(name, typ) => {
                self.raw("foreign import ");
                self.lit(name);
                self.raw(" :: ");
                self.print_typ(typ);
            }
            Decl::ForeignData(name, typ) => {
                self.raw("foreign import data ");
                self.lit(name);
                self.raw(" :: ");
                self.print_typ(typ);
            }

            Decl::Role(name, roles) => {
                self.raw("type role ");
                self.lit(name);
                for r in roles {
                    self.raw(" ");
                    self.raw(match r.0 {
                        Role::Nominal => "nominal",
                        Role::Representational => "representational",
                        Role::Phantom => "phantom",
                    });
                }
            }

            Decl::Fixity(side, num, e, op) => {
                self.print_fixity_side(side);
                self.raw(" ");
                self.lit(num);
                self.raw(" ");
                self.print_expr(e);
                self.raw(" as ");
                self.lit(op);
            }
            Decl::FixityTyp(side, num, t, op) => {
                self.print_fixity_side(side);
                self.raw(" ");
                self.lit(num);
                self.raw(" type ");
                self.print_typ(t);
                self.raw(" as ");
                self.lit(op);
            }
        }
    }

    fn print_fixity_side(&mut self, s: &S<FixitySide>) {
        self.raw(match s.0 {
            FixitySide::L => "infixl",
            FixitySide::R => "infixr",
            FixitySide::C => "infix",
        });
    }

    fn print_constraint_list(&mut self, cs: &[Constraint]) {
        if cs.len() == 1 {
            self.print_constraint(&cs[0]);
        } else {
            self.raw("(");
            for (i, c) in cs.iter().enumerate() {
                if i > 0 {
                    self.raw(", ");
                }
                self.print_constraint(c);
            }
            self.raw(")");
        }
    }

    fn print_fun_dep(&mut self, fd: &FunDep) {
        let FunDep(lhs, rhs) = fd;
        for (i, n) in lhs.iter().enumerate() {
            if i > 0 {
                self.raw(" ");
            }
            self.lit(n);
        }
        self.raw(" -> ");
        for (i, n) in rhs.iter().enumerate() {
            if i > 0 {
                self.raw(" ");
            }
            self.lit(n);
        }
    }

    fn print_class_member(&mut self, m: &ClassMember) {
        let ClassMember(name, typ) = m;
        self.lit(name);
        self.raw(" :: ");
        self.print_typ(typ);
    }

    fn print_inst_head(&mut self, h: &InstHead) {
        let InstHead(constraints, name, args) = h;
        if let Some(cs) = constraints {
            self.print_constraint_list(cs);
            self.raw(" => ");
        }
        self.lit(name);
        for a in args {
            self.raw(" ");
            self.print_typ(a);
        }
    }

    fn print_inst_binding(&mut self, b: &InstBinding) {
        match b {
            InstBinding::Sig(name, typ) => {
                self.lit(name);
                self.raw(" :: ");
                self.print_typ(typ);
            }
            InstBinding::Def(name, binders, ge) => {
                self.lit(name);
                for b in binders {
                    self.raw(" ");
                    self.print_binder(b);
                }
                self.print_guarded_expr(ge, " = ");
            }
        }
    }

    // -- guards --------------------------------------------------------

    fn print_guarded_expr(&mut self, ge: &GuardedExpr, arrow: &str) {
        match ge {
            GuardedExpr::Unconditional(e) => {
                self.raw(arrow);
                self.print_expr(e);
            }
            GuardedExpr::Guarded(clauses) => {
                self.indent_in();
                for (guards, e) in clauses {
                    self.newline();
                    self.raw("| ");
                    for (i, g) in guards.iter().enumerate() {
                        if i > 0 {
                            self.raw(", ");
                        }
                        self.print_guard(g);
                    }
                    self.raw(arrow);
                    self.print_expr(e);
                }
                self.indent_out();
            }
        }
    }

    fn print_guard(&mut self, g: &Guard) {
        match g {
            Guard::Expr(e) => self.print_expr(e),
            Guard::Binder(b, e) => {
                self.print_binder(b);
                self.raw(" <- ");
                self.print_expr(e);
            }
        }
    }

    // -- let bindings ----------------------------------------------------

    fn print_let_binding(&mut self, lb: &LetBinding) {
        match lb {
            LetBinding::Sig(name, typ) => {
                self.lit(name);
                self.raw(" :: ");
                self.print_typ(typ);
            }
            LetBinding::Name(name, binders, ge) => {
                self.lit(name);
                for b in binders {
                    self.raw(" ");
                    self.print_binder(b);
                }
                self.print_guarded_expr(ge, " = ");
            }
            LetBinding::Pattern(b, e) => {
                self.print_binder(b);
                self.raw(" = ");
                self.print_expr(e);
            }
        }
    }

    fn print_let_bindings(&mut self, bindings: &[LetBinding]) {
        self.indent_in();
        for b in bindings {
            self.newline();
            self.print_let_binding(b);
        }
        self.indent_out();
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
            Binder::Record(fields) => {
                self.list(
                    "{",
                    "}",
                    true,
                    fields,
                    |x| x.span(),
                    |p, x| p.print_record_label_binder(x),
                );
            }
            Binder::Op(l, op, r) => {
                self.print_binder(l);
                self.raw(" ");
                self.lit(op);
                self.raw(" ");
                self.print_binder(r);
            }
        }
    }

    fn print_record_label_binder(&mut self, f: &RecordLabelBinder) {
        match f {
            RecordLabelBinder::Pun(n) => self.lit(n),
            RecordLabelBinder::Field(l, b) => {
                self.lit(l);
                self.raw(": ");
                self.print_binder(b);
            }
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
                // Typ::Int stores a parsed i64 rather than interned source text (unlike most
                // literals), and the parser's span for the negative case covers only the `-`
                // token, not the digits - so print the value directly instead of slicing source.
                if *neg {
                    self.raw("-");
                }
                self.raw(&i.0 .0.to_string());
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
        // The third field is the `@` visible-type-application marker, not "wrap in
        // parens" - parens are only syntactically required when there's a kind
        // annotation (`forall (a :: Type).`), so that's what drives them here.
        let TypVarBinding(name, kind, is_at) = v;
        let needs_parens = kind.is_some();
        if needs_parens {
            self.raw("(");
        }
        if *is_at {
            self.raw("@");
        }
        self.lit(name);
        if let Some(k) = kind {
            self.raw(" :: ");
            self.print_typ(k);
        }
        if needs_parens {
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
            Expr::Infix(l, op, r) => {
                self.print_expr(l);
                self.raw(" `");
                self.print_expr(op);
                self.raw("` ");
                self.print_expr(r);
            }
            Expr::Update(target, _, updates, _) => {
                self.print_expr(target);
                self.raw(" ");
                self.list(
                    "{",
                    "}",
                    true,
                    updates,
                    |x| x.span(),
                    |p, x| p.print_record_update(x),
                );
            }
            Expr::Do(qual, _, stmts) => {
                if let Some(q) = qual {
                    self.print_qual(q);
                }
                self.raw("do");
                self.indent_in();
                for s in stmts {
                    self.newline();
                    self.print_do_stmt(s);
                }
                self.indent_out();
            }
            Expr::Ado(qual, _, stmts, result) => {
                if let Some(q) = qual {
                    self.print_qual(q);
                }
                self.raw("ado");
                self.indent_in();
                for s in stmts {
                    self.newline();
                    self.print_do_stmt(s);
                }
                self.newline();
                self.raw("in ");
                self.print_expr(result);
                self.indent_out();
            }
            Expr::Let(_, bindings, body) => {
                self.raw("let");
                self.print_let_bindings(bindings);
                self.newline();
                self.raw("in ");
                self.print_expr(body);
            }
            Expr::Where(_, body, bindings) => {
                self.print_expr(body);
                self.indent_in();
                self.newline();
                self.raw("where");
                self.print_let_bindings(bindings);
                self.indent_out();
            }
            Expr::Case(_, scrutinees, branches) => {
                self.raw("case ");
                for (i, s) in scrutinees.iter().enumerate() {
                    if i > 0 {
                        self.raw(", ");
                    }
                    self.print_expr(s);
                }
                self.raw(" of");
                self.indent_in();
                for b in branches {
                    self.newline();
                    self.print_case_branch(b);
                }
                self.indent_out();
            }

            Expr::Error(_) => self.raw_fallback(e),
        }
    }

    fn print_do_stmt(&mut self, s: &DoStmt) {
        match s {
            DoStmt::Stmt(None, e) => self.print_expr(e),
            DoStmt::Stmt(Some(b), e) => {
                self.print_binder(b);
                self.raw(" <- ");
                self.print_expr(e);
            }
            DoStmt::Let(bindings) => {
                self.raw("let");
                self.print_let_bindings(bindings);
            }
        }
    }

    fn print_case_branch(&mut self, b: &CaseBranch) {
        let CaseBranch(binders, ge) = b;
        for (i, bd) in binders.iter().enumerate() {
            if i > 0 {
                self.raw(", ");
            }
            self.print_binder(bd);
        }
        self.print_guarded_expr(ge, " -> ");
    }

    fn print_record_update(&mut self, u: &RecordUpdate) {
        match u {
            RecordUpdate::Leaf(l, e) => {
                self.lit(l);
                self.raw(" = ");
                self.print_expr(e);
            }
            RecordUpdate::Branch(l, updates) => {
                self.lit(l);
                self.raw(" ");
                self.list(
                    "{",
                    "}",
                    true,
                    updates,
                    |x| x.span(),
                    |p, x| p.print_record_update(x),
                );
            }
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
    fn case_of_with_multiple_branches() {
        let src = "module Foo where\n\nfoo = case 1 of\n  0 -> \"zero\"\n  x -> \"other\"\n";
        let out = fmt(src);
        assert_eq!(
            out,
            "module Foo where\n\nfoo = case 1 of\n  0 -> \"zero\"\n  x -> \"other\"\n"
        );
        assert_idempotent(src);
    }

    #[test]
    fn guarded_def() {
        let src = "module Foo where\n\nfoo x\n  | x > 0 = 1\n  | otherwise = 0\n";
        let out = fmt(src);
        assert_eq!(
            out,
            "module Foo where\n\nfoo x\n  | x > 0 = 1\n  | otherwise = 0\n"
        );
        assert_idempotent(src);
    }

    #[test]
    fn do_notation() {
        let src = "module Foo where\n\nfoo = do\n  x <- bar\n  pure x\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\nfoo = do\n  x <- bar\n  pure x\n");
        assert_idempotent(src);
    }

    #[test]
    fn let_in() {
        let src = "module Foo where\n\nfoo = let x = 1 in x\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\nfoo = let\n  x = 1\nin x\n");
        assert_idempotent(src);
    }

    #[test]
    fn where_clause() {
        let src = "module Foo where\n\nfoo = result where\n  result = 1\n";
        let out = fmt(src);
        assert_eq!(
            out,
            "module Foo where\n\nfoo = result\n  where\n    result = 1\n"
        );
        assert_idempotent(src);
    }

    #[test]
    fn record_update_and_infix() {
        let src = "module Foo where\n\nfoo = r { a = 1 }\nbar = 1 `add` 2\n";
        let out = fmt(src);
        assert_eq!(
            out,
            "module Foo where\n\nfoo = r { a = 1 }\n\nbar = 1 `add` 2\n"
        );
        assert_idempotent(src);
    }

    #[test]
    fn data_flat_and_multiline() {
        let src = "module Foo where\n\ndata Flat = A | B Int\n\ndata Tall\n  = C\n  | D String\n";
        let out = fmt(src);
        assert_eq!(
            out,
            "module Foo where\n\ndata Flat = A | B Int\n\ndata Tall\n  = C\n  | D String\n"
        );
        assert_idempotent(src);
    }

    #[test]
    fn type_newtype_class_instance() {
        let src = concat!(
            "module Foo where\n\n",
            "type Id a = a\n\n",
            "newtype Wrap = Wrap Int\n\n",
            "class Show a where\n  show :: a -> String\n\n",
            "instance Show Int where\n  show x = \"int\"\n\n",
            "derive instance Eq Wrap\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn foreign_and_fixity_and_role() {
        let src = concat!(
            "module Foo where\n\n",
            "foreign import unsafeCoerce :: forall a b. a -> b\n\n",
            "infixl 5 add as +++\n\n",
            "type role Foo nominal representational\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn qualified_do_and_ado_keep_the_dot() {
        let src = "module Foo where\n\na = A.do\n  x <- A.a\n  pure x\n";
        let out = fmt(src);
        assert!(out.contains("A.do"), "qualifier dot lost: {:?}", out);
        assert!(!out.contains("Ado") && !out.contains("Adodo"), "garbled qualifier: {:?}", out);
        assert_idempotent(src);
    }

    #[test]
    fn negative_typ_int_keeps_the_digits() {
        let src = "module Foo where\n\na :: -1\na = 1\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\na :: -1\na = 1\n");
        assert_idempotent(src);
    }

    #[test]
    fn visible_forall_binder_without_kind_has_no_parens() {
        let src = "module Foo where\n\nreadJSON :: forall @a. Array a\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\nreadJSON :: forall @a. Array a\n");
        assert_idempotent(src);
    }

    #[test]
    fn kinded_forall_binder_keeps_parens() {
        let src = "module Foo where\n\nfoo :: forall (a :: Type). a\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\nfoo :: forall (a :: Type). a\n");
        assert_idempotent(src);
    }

    fn purs_files_under(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                purs_files_under(&path, out);
            } else if path.extension().is_some_and(|e| e == "purs") {
                out.push(path);
            }
        }
    }

    /// Real-world-ish fixtures under tests/golden should format idempotently. Fixtures
    /// whose source doesn't already parse cleanly are skipped - some deliberately
    /// exercise parser error recovery rather than being formattable programs.
    #[test]
    fn golden_fixtures_format_idempotently() {
        let mut files = Vec::new();
        purs_files_under(std::path::Path::new("tests/golden"), &mut files);
        assert!(!files.is_empty(), "expected to find golden .purs fixtures");

        let mut checked = 0;
        for path in files {
            let src = std::fs::read_to_string(&path).unwrap();
            let (toks, comments) = lexer::lex(&src, Fi(0));
            let names = DashMap::new();
            let mut p = parser::P::new(&toks, &names);
            let Some(m) = parser::module(&mut p) else {
                continue;
            };
            if !p.errors.is_empty() {
                continue;
            }

            checked += 1;
            let once = super::print_module(&src, &m, &comments);
            let twice = fmt(&once);
            assert_eq!(once, twice, "not idempotent for {:?}", path);
        }
        assert!(
            checked > 10,
            "expected to actually check a good number of golden fixtures, only checked {checked}"
        );
    }
}

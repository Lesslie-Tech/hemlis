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
    /// Set while printing the type of a signature that's already been decided to
    /// print expanded (see `print_sig_typ`). A forall/constraint/arrow chain is
    /// typically nested several layers deep (`Forall(Constrained(Arr(Arr(...))))`) -
    /// without this, each layer would indent again on top of the last, producing a
    /// staircase instead of every `.`/`=>`/`->` breaking to the same indent level.
    in_broken_sig: bool,
}

/// One or more source `ImportDecl`s for the same (module, alias, hiding-ness),
/// merged together - see `Printer::print_imports`.
struct MergedImport {
    from: MName,
    to: Option<MName>,
    is_hiding: bool,
    hiding: Vec<Import>,
    names: Option<Vec<Import>>,
    is_bare: bool,
    /// True once a second source ImportDecl has been folded into this one - at
    /// that point "was this originally written expanded" no longer means anything
    /// (the merged items may come from lines that aren't even adjacent), so the
    /// merged name list is always printed flat rather than inheriting a stale
    /// multiline decision from whichever contributing decl happened to be first.
    merged: bool,
}

impl<'s> Printer<'s> {
    fn new(source: &'s str, comments: &'s [SourceToken<'s>]) -> Self {
        Printer {
            source,
            comments,
            comment_idx: 0,
            out: String::new(),
            indent: 0,
            in_broken_sig: false,
        }
    }

    // -- low level writer --------------------------------------------------

    fn raw(&mut self, s: &str) {
        self.out.push_str(s);
    }

    /// Break to a new line at the current indent. If we're already at the start
    /// of one (nothing but indent spaces written since the last '\n' - typically
    /// because an outer construct just broke here too, and what it's printing
    /// next is itself something that always opens with its own break), this
    /// reuses that line instead of leaving a blank one: two `newline()` calls in a
    /// row with no content between them never inserts a blank line by accident.
    /// A deliberate blank-line separator is always written directly as `raw("\n")`
    /// and is unaffected by this.
    fn newline(&mut self) {
        let trimmed_len = self.out.trim_end_matches(' ').len();
        if trimmed_len == 0 || self.out[..trimmed_len].ends_with('\n') {
            // Already at the start of a line (possibly with indent already
            // written by an earlier newline() call with nothing printed since -
            // typically because whatever we're about to print also always opens
            // with its own break). Leave it exactly as-is: re-indenting to
            // whatever level we're at *now* would let an inner construct's own
            // indent_in() retroactively re-indent a line an outer context already
            // started, which is wrong - the outer context owns this line's
            // margin, not whichever construct happens to share it.
            return;
        }
        self.out.truncate(trimmed_len);
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

    /// True if there's a source line break between the end of `a` and the start
    /// of `b` - i.e. the user's own line break sits right at this boundary.
    ///
    /// Deliberately a local, adjacent-boundary check rather than comparing an
    /// overall first-to-last span: an item that's internally forced to print
    /// across multiple lines regardless of source layout (e.g. a nested case/do
    /// block) would otherwise "infect" its neighbors into looking multiline on a
    /// later formatting pass even though nothing about *their* source layout
    /// changed - which breaks idempotence.
    fn breaks_before(a: Span, b: Span) -> bool {
        a.hi().0 != b.lo().0
    }

    /// True if any adjacent pair in `spans` has a line break between them (see
    /// `breaks_before`) - used to decide whether a whole chain/list should print
    /// expanded.
    fn any_breaks(spans: &[Span]) -> bool {
        spans.windows(2).any(|w| Self::breaks_before(w[0], w[1]))
    }

    /// True if `a` is a type signature immediately followed by its own
    /// definition - these stay adjacent, with no blank line between them.
    fn decls_are_glued(a: &Decl, b: &Decl) -> bool {
        matches!(a, Decl::Sig(..)) && a.ud() == b.ud()
    }

    /// Prints ` :: Typ`, breaking to an indented `\n:: Typ` when the signature
    /// originally spanned multiple lines - so a deliberately wrapped signature
    /// (forall/constraints/arrow chain sprawling across lines) doesn't collapse
    /// into one long line.
    fn print_sig_typ(&mut self, before: Span, typ: &Typ) {
        if Self::breaks_before(before, typ.span()) {
            self.indent_in();
            self.newline();
            self.raw(":: ");
            let outer = self.in_broken_sig;
            self.in_broken_sig = true;
            self.print_typ(typ);
            self.in_broken_sig = outer;
            self.indent_out();
        } else {
            self.raw(" :: ");
            self.print_typ(typ);
        }
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

        let spans: Vec<Span> = items.iter().map(&span_of).collect();
        let multiline = Self::any_breaks(&spans);

        if !multiline {
            self.raw(open);
            if pad {
                self.raw(" ");
            }
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    self.raw(", ");
                }
                self.flush_comments_before(span_of(item).lo().0);
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
                self.flush_comments_before(span_of(item).lo().0);
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
        self.flush_comments_before(h.span().lo().0);
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
        self.print_imports(imports);
    }

    /// Groups and sorts imports the way purs-tidy does: unqualified "bare" imports
    /// (`import Foo`, nothing else) form their own group first, separated by a blank
    /// line from the rest; everything else is sorted alphabetically by module name,
    /// with an unaliased import of a module sorting before its `as`-aliased form.
    /// Imports that only differ in their name list (same module, same alias, same
    /// hiding-ness) are merged into one, matching purs-tidy's import-merging.
    ///
    /// Comments inside the import block aren't reattached per-import after this
    /// reordering (that mapping stops being meaningful once imports move around) -
    /// they're flushed as one batch right before the block instead, so nothing is
    /// lost even though placement within the block may not be preserved exactly.
    fn print_imports(&mut self, imports: &[ImportDecl]) {
        if let Some(last_line) = imports.iter().map(|i| i.span().hi().0).max() {
            self.flush_comments_before(last_line + 1);
        }

        let mut merged: Vec<MergedImport> = Vec::new();
        for i in imports {
            let is_hiding = !i.hiding.is_empty();
            let existing = merged.iter_mut().find(|m| {
                self.text(m.from.span()) == self.text(i.from.span())
                    && m.to.map(|t| self.text(t.span())) == i.to.map(|t| self.text(t.span()))
                    && m.is_hiding == is_hiding
            });
            if let Some(existing) = existing {
                existing.merged = true;
                existing.hiding.extend(i.hiding.iter().cloned());
                match (&mut existing.names, &i.names) {
                    (Some(a), Some(b)) => a.extend(b.iter().cloned()),
                    (None, Some(b)) => existing.names = Some(b.clone()),
                    _ => {}
                }
            } else {
                merged.push(MergedImport {
                    from: i.from,
                    to: i.to,
                    is_hiding,
                    hiding: i.hiding.clone(),
                    names: i.names.clone(),
                    is_bare: i.hiding.is_empty() && i.names.is_none() && i.to.is_none(),
                    merged: false,
                });
            }
        }

        for m in &mut merged {
            self.dedup_sort_imports(&mut m.hiding);
            if let Some(names) = &mut m.names {
                self.dedup_sort_imports(names);
            }
        }

        merged.sort_by(|a, b| {
            (!a.is_bare, self.text(a.from.span()), a.to.is_some())
                .cmp(&(!b.is_bare, self.text(b.from.span()), b.to.is_some()))
        });

        for (idx, m) in merged.iter().enumerate() {
            if idx > 0 && merged[idx - 1].is_bare && !m.is_bare {
                self.raw("\n");
            }
            self.print_merged_import(m);
            self.newline();
        }
    }

    fn dedup_sort_imports(&self, items: &mut Vec<Import>) {
        items.sort_by_key(|a| self.import_display_text(a));
        items.dedup_by(|a, b| self.import_display_text(a) == self.import_display_text(b));
    }

    fn import_display_text(&self, i: &Import) -> String {
        match i {
            Import::Value(_, n) => self.text(n.span()).to_string(),
            Import::Symbol(_, s) => self.text(s.span()).to_string(),
            Import::Typ(_, n) => self.text(n.span()).to_string(),
            Import::TypDat(_, n, dm) => {
                format!("{}{}", self.text(n.span()), self.data_member_display_text(dm))
            }
            Import::TypSymbol(_, s) => format!("type {}", self.text(s.span())),
            Import::Class(_, n) => format!("class {}", self.text(n.span())),
        }
    }

    fn data_member_display_text(&self, dm: &DataMember) -> String {
        match dm {
            DataMember::All(_) => "(..)".to_string(),
            DataMember::Some(names) => format!(
                "({})",
                names
                    .iter()
                    .map(|n| self.text(n.span()))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }

    fn print_merged_import(&mut self, m: &MergedImport) {
        self.raw("import ");
        self.lit(&m.from);
        if !m.hiding.is_empty() {
            self.raw(" hiding ");
            self.print_import_names(&m.hiding, m.merged);
        } else if let Some(names) = &m.names {
            self.raw(" ");
            self.print_import_names(names, m.merged);
        }
        if let Some(to) = &m.to {
            self.raw(" as ");
            self.lit(to);
        }
    }

    fn print_import_names(&mut self, items: &[Import], force_flat: bool) {
        if force_flat {
            self.raw("(");
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    self.raw(", ");
                }
                self.print_import(item);
            }
            self.raw(")");
        } else {
            self.list("(", ")", false, items, |x| x.span(), |p, x| p.print_import(x));
        }
    }

    fn print_export(&mut self, e: &Export) {
        match e {
            Export::Value(n) => self.lit(n),
            // A Symbol's own span already covers its surrounding parens (the lexer
            // captures `(<*>)` as one token), so no parens are added here.
            Export::Symbol(s) => self.lit(s),
            Export::Typ(n) => self.lit(n),
            Export::TypSymbol(s) => {
                self.raw("type ");
                self.lit(s);
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

    fn print_import(&mut self, i: &Import) {
        match i {
            Import::Value(_, n) => self.lit(n),
            Import::Symbol(_, s) => self.lit(s),
            Import::Typ(_, n) => self.lit(n),
            Import::TypDat(_, n, dm) => {
                self.lit(n);
                self.print_data_member(dm);
            }
            Import::TypSymbol(_, s) => {
                self.raw("type ");
                self.lit(s);
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
                self.print_sig_typ(name.span(), typ);
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
                self.print_sig_typ(name.span(), kind);
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
                let ctor_spans: Vec<Span> = ctors.iter().map(|c| c.span()).collect();
                let multiline = Self::any_breaks(&ctor_spans);
                self.indent_in();
                for (i, (cname, cargs)) in ctors.iter().enumerate() {
                    if multiline {
                        self.newline();
                    } else {
                        self.raw(" ");
                    }
                    self.flush_comments_before(cname.span().lo().0);
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
                self.print_sig_typ(name.span(), kind);
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
                self.print_sig_typ(name.span(), kind);
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
                self.print_sig_typ(name.span(), kind);
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
                        self.flush_comments_before(m.span().lo().0);
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
                        self.flush_comments_before(b.span().lo().0);
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
                self.print_sig_typ(name.span(), typ);
            }
            Decl::ForeignData(name, typ) => {
                self.raw("foreign import data ");
                self.lit(name);
                self.print_sig_typ(name.span(), typ);
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
        self.print_sig_typ(name.span(), typ);
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
                self.print_sig_typ(name.span(), typ);
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
                self.print_sig_typ(name.span(), typ);
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
            self.flush_comments_before(b.span().lo().0);
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
            Typ::Arr(a, b) => self.print_typ_arrow_chain(a, b),
            Typ::App(f, a) => {
                self.print_typ(f);
                self.raw(" ");
                self.print_typ(a);
            }
            Typ::Op(l, op, r) => {
                self.print_typ(l);
                let multiline = self.in_broken_sig || Self::breaks_before(l.span(), r.span());
                let own_indent = multiline && !self.in_broken_sig;
                if own_indent {
                    self.indent_in();
                }
                if multiline {
                    self.newline();
                    self.lit(op);
                    self.raw(" ");
                    self.print_typ(r);
                } else {
                    self.raw(" ");
                    self.lit(op);
                    self.raw(" ");
                    self.print_typ(r);
                }
                if own_indent {
                    self.indent_out();
                }
            }
            Typ::Kinded(t, k) => {
                self.print_typ(t);
                self.raw(" :: ");
                self.print_typ(k);
            }
            Typ::Constrained(c, t) => self.print_typ_constrained_chain(c, t),
            Typ::Forall(vars, t) => {
                self.raw("forall");
                for v in vars {
                    self.raw(" ");
                    self.print_typ_var_binding(v);
                }
                if self.in_broken_sig {
                    self.newline();
                    self.raw(". ");
                    self.print_typ(t);
                } else {
                    let multiline =
                        vars.last().is_some_and(|v0| Self::breaks_before(v0.span(), t.span()));
                    if multiline {
                        self.indent_in();
                        self.newline();
                        self.raw(". ");
                        self.print_typ(t);
                        self.indent_out();
                    } else {
                        self.raw(". ");
                        self.print_typ(t);
                    }
                }
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

    /// `a -> b -> c -> ...` is parsed as a right-nested chain of `Typ::Arr`. Flatten
    /// it so that, when the chain was originally written across multiple lines, every
    /// `->` breaks to the same indent level (siblings) rather than nesting deeper
    /// with each arrow.
    fn print_typ_arrow_chain(&mut self, a: &Typ, b: &Typ) {
        let mut segments = vec![a];
        let mut rest = b;
        while let Typ::Arr(x, y) = rest {
            segments.push(x);
            rest = y;
        }
        segments.push(rest);

        let segment_spans: Vec<Span> = segments.iter().map(|s| s.span()).collect();
        let multiline = self.in_broken_sig || Self::any_breaks(&segment_spans);
        let own_indent = multiline && !self.in_broken_sig;
        self.print_typ(segments[0]);
        if own_indent {
            self.indent_in();
        }
        for seg in &segments[1..] {
            if multiline {
                self.newline();
                self.raw("-> ");
            } else {
                self.raw(" -> ");
            }
            self.print_typ(seg);
        }
        if own_indent {
            self.indent_out();
        }
    }

    /// `C1 => C2 => ... => Body` (including the desugared form of a parenthesized,
    /// comma-separated constraint list) is a right-nested chain of `Typ::Constrained`.
    /// Flattened the same way as `print_typ_arrow_chain`, for the same reason.
    fn print_typ_constrained_chain(&mut self, c0: &Constraint, body0: &Typ) {
        let mut constraints = vec![c0];
        let mut rest = body0;
        while let Typ::Constrained(c, b) = rest {
            constraints.push(c);
            rest = b;
        }
        let body = rest;

        let mut chain_spans: Vec<Span> = constraints.iter().map(|c| c.span()).collect();
        chain_spans.push(body.span());
        let multiline = self.in_broken_sig || Self::any_breaks(&chain_spans);
        let own_indent = multiline && !self.in_broken_sig;
        self.print_constraint(constraints[0]);
        if own_indent {
            self.indent_in();
        }
        for c in &constraints[1..] {
            if multiline {
                self.newline();
                self.raw("=> ");
            } else {
                self.raw(" => ");
            }
            self.print_constraint(c);
        }
        if multiline {
            self.newline();
            self.raw("=> ");
        } else {
            self.raw(" => ");
        }
        self.print_typ(body);
        if own_indent {
            self.indent_out();
        }
    }

    fn print_row(&mut self, row: &Row, spaced: bool) {
        let Row(fields, tail) = row;
        if fields.is_empty() && tail.is_none() {
            return;
        }
        // A record's braces are their own bracketed context, unrelated to whatever
        // signature this row happens to be nested inside - a field's own type (e.g.
        // a forall) shouldn't inherit an enclosing broken-signature's flattening.
        let outer_in_broken_sig = self.in_broken_sig;
        self.in_broken_sig = false;
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
        self.in_broken_sig = outer_in_broken_sig;
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
                if Self::breaks_before(l.span(), r.span()) {
                    self.indent_in();
                    self.newline();
                    self.lit(op);
                    self.raw(" ");
                    self.print_expr(r);
                    self.indent_out();
                } else {
                    self.raw(" ");
                    self.lit(op);
                    self.raw(" ");
                    self.print_expr(r);
                }
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
                let multiline = Self::any_breaks(&[cond.span(), then_e.span(), else_e.span()]);
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
                    self.flush_comments_before(s.span().lo().0);
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
                    self.flush_comments_before(s.span().lo().0);
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
                    self.flush_comments_before(b.span().lo().0);
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
            "module Foo where\nimport Prelude\n\nimport Data.Array (head, tail)\n\nfoo = 1\n\nbar = 2\n"
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

    #[test]
    fn symbol_export_import_are_not_double_parenthesized() {
        let src = "module Foo ((<*>), type (~>)) where\n\nimport Data.Functor ((<$>))\n\nfoo = (<*>)\n";
        let out = fmt(src);
        // An exact match is the real check here - `((<$>))` alone would look like a
        // double-paren bug, but is actually correct: the outer pair is the (single-
        // element) import list's own delimiters, the inner pair belongs to the
        // Symbol's own span (which already covers its parens).
        assert_eq!(
            out,
            "module Foo ((<*>), type (~>)) where\nimport Data.Functor ((<$>))\n\nfoo = (<*>)\n"
        );
        assert_idempotent(src);
    }

    #[test]
    fn comment_before_module_keyword_stays_before_it() {
        let src = "-- top comment\nmodule Foo where\n\nfoo = 1\n";
        let out = fmt(src);
        assert!(
            out.starts_with("-- top comment\nmodule Foo"),
            "comment should stay before the module keyword: {:?}",
            out
        );
        assert_idempotent(src);
    }

    #[test]
    fn comment_inside_export_list_is_not_relocated_past_the_header() {
        let src = "module Foo\n  ( a\n  -- mid comment\n  , b\n  ) where\n\na = 1\nb = 2\n";
        let out = fmt(src);
        let where_pos = out.find("where").unwrap();
        let comment_pos = out.find("-- mid comment").unwrap();
        assert!(
            comment_pos < where_pos,
            "comment should stay inside the export list, before `where`: {:?}",
            out
        );
        assert_idempotent(src);
    }

    #[test]
    fn bare_imports_are_grouped_first_and_separated() {
        let src = "module Foo where\n\nimport Data.Array (head)\nimport Prelude\nimport Data.Maybe\n\nfoo = 1\n";
        let out = fmt(src);
        assert_eq!(
            out,
            "module Foo where\nimport Data.Maybe\nimport Prelude\n\nimport Data.Array (head)\n\nfoo = 1\n"
        );
        assert_idempotent(src);
    }

    #[test]
    fn imports_are_sorted_and_duplicates_merged() {
        let src = concat!(
            "module Foo where\n\n",
            "import Data.Array (tail)\n",
            "import Control.Bind (class Bind)\n",
            "import Data.Array (head)\n\n",
            "foo = 1\n",
        );
        let out = fmt(src);
        assert_eq!(
            out,
            concat!(
                "module Foo where\n",
                "import Control.Bind (class Bind)\n",
                "import Data.Array (head, tail)\n\n",
                "foo = 1\n",
            )
        );
        assert_idempotent(src);
    }

    #[test]
    fn multiline_type_signature_stays_expanded() {
        let src = concat!(
            "module Foo where\n\n",
            "f\n",
            "  :: forall a\n",
            "  . Show a\n",
            "  => a\n",
            "  -> a\n",
            "  -> String\n",
            "f a b = show a\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn flat_type_signature_stays_flat() {
        let src = "module Foo where\n\nf :: forall a. Show a => a -> a -> String\nf a b = show a\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn multiline_operator_chain_stays_expanded() {
        let src = "module Foo where\n\nfoo =\n  a\n    >>> b\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\nfoo = a\n  >>> b\n");
        assert_idempotent(src);
    }

    #[test]
    fn comment_before_let_binding_is_not_relocated() {
        let src = concat!(
            "module Foo where\n\n",
            "foo = let\n",
            "  a = 1\n",
            "  -- a comment\n",
            "  b = 2\n",
            "in a { x: 1 }\n",
        );
        let out = fmt(src);
        let comment_pos = out.find("-- a comment").expect("comment lost");
        let record_pos = out.find("{ x: 1 }").expect("record missing");
        assert!(
            comment_pos < record_pos,
            "comment should stay near its let binding, not migrate into an unrelated record: {:?}",
            out
        );
        assert_idempotent(src);
    }

    #[test]
    fn comment_before_do_stmt_and_case_branch_is_not_relocated() {
        let src = concat!(
            "module Foo where\n\n",
            "foo = do\n",
            "  a\n",
            "  -- a comment\n",
            "  b\n",
        );
        let out = fmt(src);
        assert!(out.contains("-- a comment"), "comment lost: {:?}", out);
        assert_idempotent(src);

        let src2 = concat!(
            "module Foo where\n\n",
            "foo = case x of\n",
            "  A -> 1\n",
            "  -- a comment\n",
            "  B -> 2\n",
        );
        let out2 = fmt(src2);
        assert!(out2.contains("-- a comment"), "comment lost: {:?}", out2);
        assert_idempotent(src2);
    }
}

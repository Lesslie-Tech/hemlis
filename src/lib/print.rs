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
use crate::source::{line_starts, source_text_with_starts};

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
    /// Byte offset of the start of each source line, computed once up front -
    /// `text()`/`lit()` slice a span out of `source` for every leaf AST node
    /// printed, and recomputing this from scratch (an O(source_len) scan) on
    /// each of those calls turned printing into an O(source_len * leaf_count)
    /// pass over large files.
    line_starts: Vec<usize>,
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
    /// Byte offset into `out` marking a position some outer construct has
    /// already committed to as a glue point for whatever comes next - set
    /// right before printing that "whatever's next" (a `list()` item glued
    /// after `open `/`, `; an `Expr::Op` operand glued after `op ` once the
    /// chain's own `newline()` already put the operator on a fresh line of
    /// its own), consumed by a *nested* construct's own `own_indent`-style
    /// relocation check (`list()`'s own, `Expr::App`'s). Relocating there
    /// anyway would double up on a floor the outer construct already
    /// established - the same "floor" idea documented in FORMATTER.md,
    /// just for a value-side glue point rather than a type-side one. Valid
    /// only for as long as nothing has been printed since the mark was set;
    /// the moment `out.len()` no longer matches it, something (the current
    /// construct's own head token, an earlier sibling) has been glued in
    /// front of whatever's being decided now, and ordinary relocation
    /// resumes.
    glued_floor: Option<usize>,
}

/// One or more source `ImportDecl`s for the same (module, alias, hiding-ness),
/// merged together - see `Printer::print_imports`.
struct MergedImport {
    from: MName,
    to: Option<MName>,
    is_hiding: bool,
    hiding: Vec<Import>,
    names: Option<Vec<Import>>,
    /// True for an unqualified import with no explicit name list - a plain
    /// `import Foo` or a `import Foo hiding (...)` - which import names into
    /// scope openly (everything, or everything-except) rather than through an
    /// explicit closed list or a qualifier. These sort into their own group
    /// ahead of everything else, matching purs-tidy.
    is_open: bool,
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
            line_starts: line_starts(source),
            comments,
            comment_idx: 0,
            out: String::new(),
            indent: 0,
            in_broken_sig: false,
            glued_floor: None,
        }
    }

    // -- low level writer --------------------------------------------------

    fn raw(&mut self, s: &str) {
        self.out.push_str(s);
    }

    /// True if nothing but this line's indent (or nothing at all) has been
    /// written since the last real line break - i.e. we're sitting at the
    /// start of a line some outer construct already broke to.
    fn at_fresh_line(&self) -> bool {
        let trimmed_len = self.out.trim_end_matches(' ').len();
        trimmed_len == 0 || self.out[..trimmed_len].ends_with('\n')
    }

    /// The column (in characters, 0-based) of wherever printing continues
    /// right now on the current line - i.e. how much has already been
    /// written since the last line break. At a fresh line (see
    /// `at_fresh_line`) this is always exactly `self.indent`, since a fresh
    /// line consists of nothing but that many indent spaces; mid-line
    /// (something's been glued directly onto this line - `:: `, `-> `, a
    /// class name, ...) it's the real width of everything glued so far,
    /// which `self.indent` alone has no memory of. See `hang_at_column` and
    /// the "floor" model in FORMATTER.md.
    fn current_column(&self) -> usize {
        match self.out.rfind('\n') {
            Some(i) => self.out[i + 1..].chars().count(),
            // No newline anywhere in `self.out` - either this is truly the
            // start of the whole print (`self.indent` is 0 here too, so
            // returning it is the same as before), or `self.out` is a fresh
            // scratch buffer just swapped in by `render_indented`/
            // `render_at_column` (`with_indent_at` already set `self.indent`
            // to the intended starting column, but swapping the buffer never
            // physically writes those indent spaces the way a real
            // `newline()` would). Without this case, a fresh empty buffer
            // reads as column 0 regardless of `self.indent` - a nested
            // glued `Paren`'s own column capture would land at 0 instead of
            // its real column.
            None if self.out.is_empty() => self.indent,
            None => self.out.chars().count(),
        }
    }

    /// Runs `f` with the indent baseline set to `col` (an exact column, not
    /// necessarily a multiple of `INDENT`) instead of whatever it currently
    /// is, restoring the previous baseline afterward. `indent_in`/
    /// `indent_out` calls inside `f` still add/remove `INDENT` on top of
    /// `col` as usual - this only changes what they're relative to.
    fn with_indent_at<R>(&mut self, col: usize, f: impl FnOnce(&mut Self) -> R) -> R {
        let saved = self.indent;
        self.indent = col;
        let r = f(self);
        self.indent = saved;
        r
    }

    /// `with_indent_at(current_column(), f)` - runs `f` (printing something
    /// glued directly onto the current line: a nesting shape right after
    /// `:: `/`-> `/`=> `) with the indent baseline set to exactly the real
    /// column that glued prefix landed at, instead of leaving whatever
    /// *ambient* baseline was active before the prefix was printed. The
    /// ambient value has no memory of the prefix's own width - `:: `/`=> `
    /// are 3 characters, `INDENT` is a fixed 2 - so a plain `indent_in`
    /// bumping the stale ambient value lands one column short of lining up
    /// under the glued prefix's own text once something inside `f` (e.g.
    /// `print_spine_args`) does its own further `indent_in` when it breaks.
    /// Call this immediately before `f` would otherwise start printing -
    /// nothing may be written in between, or the captured column is wrong.
    /// See the "floor" model in FORMATTER.md.
    fn hang_glued<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        let col = self.current_column();
        self.with_indent_at(col, f)
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
        if self.at_fresh_line() {
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
        for _ in 0..self.indent {
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
        self.indent += INDENT;
    }

    fn indent_out(&mut self) {
        self.indent = self.indent.saturating_sub(INDENT);
        if self.at_fresh_line() {
            // The current line is nothing but indent spaces (or empty) at the
            // level we're now leaving - most commonly because a trailing
            // comment (`flush_trailing_comment`) ended its own line right
            // before this call, with nothing printed in between. `newline()`
            // trusts an already-fresh line's indent to be correct for
            // whatever prints next and won't touch it - which would leave
            // this now-stale, too-deep indent in place instead of the level
            // we just popped back out to. Re-write it here instead. Cascades
            // correctly through consecutive indent_out() calls (each one
            // re-checks freshness against its own new level).
            let trimmed = self.out.trim_end_matches(' ').len();
            self.out.truncate(trimmed);
            self.write_indent();
        }
    }

    fn write_indent(&mut self) {
        for _ in 0..self.indent {
            self.out.push(' ');
        }
    }

    /// Insert a genuinely blank line right before whatever prints next, given
    /// that `newline()` was just called (so the current line already carries
    /// this indent's leading spaces). Trims those back off first so the blank
    /// line itself has no trailing whitespace, then re-writes the indent for
    /// the line that follows.
    fn insert_blank_line(&mut self) {
        let trimmed = self.out.trim_end_matches(' ').len();
        self.out.truncate(trimmed);
        self.raw("\n");
        self.write_indent();
    }

    /// Prints `e` in isolation, `levels` indent levels deeper than wherever
    /// this is called from, and returns the resulting text without touching
    /// the real output. Used to render a subexpression "on paper" first -
    /// either to inspect what it would look like before committing to a
    /// layout choice (see `Expr::Paren`), or to get it indented at a level
    /// that depends on a choice made *after* it would otherwise have started
    /// printing (re-render at the right level rather than patching baked-in
    /// indent spaces after the fact).
    fn render_indented(&mut self, levels: usize, print_inner: impl FnOnce(&mut Self)) -> String {
        let saved = std::mem::take(&mut self.out);
        for _ in 0..levels {
            self.indent_in();
        }
        print_inner(self);
        for _ in 0..levels {
            self.indent_out();
        }
        std::mem::replace(&mut self.out, saved)
    }

    /// `render_indented`'s counterpart for an exact column rather than a
    /// level count - see `with_indent_at`. Used by `print_paren_block` so a
    /// glued `( `'s own content hangs under its real column (however much
    /// text it's glued after) instead of an approximate level bump.
    fn render_at_column(&mut self, col: usize, print_inner: impl FnOnce(&mut Self)) -> String {
        let saved = std::mem::take(&mut self.out);
        self.with_indent_at(col, print_inner);
        std::mem::replace(&mut self.out, saved)
    }

    /// True if `e` is a parenthesized expression that's going to print in the
    /// `( ` ... `)`-on-its-own-line block style (see `Expr::Paren`) at the
    /// current indent - checked by actually rendering it into a scratch
    /// buffer (discarded either way) and looking for a line break, not by
    /// comparing spans (see the long comment on `print_arrow_rhs` for why).
    /// Callers that glue something directly in front of `e` (an `arrow`, an
    /// `in`) use this to decide whether to break *before* `e` instead, so
    /// its closing `)` doesn't end up looking like it "moved back" past
    /// whatever precedes it once printed.
    fn paren_would_break(&mut self, e: &Expr) -> bool {
        matches!(e, Expr::Paren(..)) && self.expr_would_break(e)
    }

    /// True if `e` is an `ado` block with no statements (just `ado in
    /// result`) that isn't eligible to print glued flat on one line (see
    /// `Expr::Ado`'s own glue-vs-block decision) - used the same way
    /// `paren_would_break` is, to break the glued arrow/`=` onto its own
    /// line first instead of leaving `ado` glued with nothing but `in`
    /// dangling under it. Narrowed to the no-statements case: an `ado` with
    /// real statements already has visible content directly under `ado`
    /// itself (same as a `do` block), so it keeps `do`'s always-glued
    /// convention instead.
    fn ado_would_break(&mut self, e: &Expr) -> bool {
        matches!(e, Expr::Ado(_, _, stmts, _) if stmts.is_empty()) && self.expr_would_break(e)
    }

    /// `paren_would_break`'s unrestricted counterpart: true if printing `e`
    /// at the current indent produces any line break at all, whatever kind
    /// of node it is - a `Record`/`Array` with its own multiline items
    /// breaks just as well as a `Paren` does. Used where the *reason* a
    /// glued argument breaks doesn't matter, only whether it does (see
    /// `print_spine_args`'s `would_break` callback) - unlike
    /// `paren_would_break`'s two call sites, there's no "closing delimiter
    /// regresses to a shallower column" concern to narrow this to parens
    /// for.
    fn expr_would_break(&mut self, e: &Expr) -> bool {
        let comment_idx_before = self.comment_idx;
        let would_break = self.render_indented(0, |p| p.print_expr(e)).contains('\n');
        self.comment_idx = comment_idx_before;
        would_break
    }

    /// The `Binder` counterpart of `expr_would_break` - used by
    /// `print_spine_args` over a name/lambda's binders so a binder that's
    /// itself going to print multi-line (e.g. a record pattern with many
    /// fields) forces itself and every later binder onto its own line,
    /// instead of leaving a later binder glued after its closing bracket.
    fn binder_would_break(&mut self, b: &Binder) -> bool {
        let comment_idx_before = self.comment_idx;
        let would_break = self.render_indented(0, |p| p.print_binder(b)).contains('\n');
        self.comment_idx = comment_idx_before;
        would_break
    }

    /// The `Typ` counterpart of `paren_would_break`, for the same reason: a
    /// type glued directly after `::`/`->`/`=>` needs to know whether it's
    /// going to print in the block style before deciding whether to break
    /// onto a fresh line first, so its closing `)` doesn't end up looking
    /// like it moved back past whatever precedes it.
    fn typ_paren_would_break(&mut self, t: &Typ) -> bool {
        matches!(t, Typ::Paren(..)) && self.typ_would_break(t)
    }

    /// The `Typ` counterpart of `expr_would_break` - see its doc comment.
    fn typ_would_break(&mut self, t: &Typ) -> bool {
        let comment_idx_before = self.comment_idx;
        let would_break = self.render_indented(0, |p| p.print_typ(t)).contains('\n');
        self.comment_idx = comment_idx_before;
        would_break
    }

    /// Prints `(` `print_inner` `)`, using the `( ` ... `)`-on-its-own-line
    /// block style when `inner` would print across multiple lines - shared by
    /// `Expr::Paren` and `Typ::Paren` so a parenthesized type wraps exactly
    /// the same way a parenthesized value does.
    ///
    /// The block-vs-flat decision can't be made from source spans the way
    /// most other multiline decisions here are: `inner` might contain a
    /// `case`/`do`/`let`, which always prints across multiple lines
    /// regardless of its own source layout, so a span-based check would flip
    /// between formatting passes (flat on pass one, block-style on pass two
    /// once the close paren visibly lands on a later line than the open one).
    /// Instead, render `inner` into a scratch buffer and check whether the
    /// result actually contains a line break - a pure function of the AST,
    /// stable across repeated formatting.
    ///
    /// `(` is always glued in place here, never relocated onto its own fresh
    /// line even when that would leave `)` looking like it moved back past
    /// whatever precedes `(` - relocating based on "am I at a fresh line"
    /// can't distinguish "glued after `=`/`->`" from "one flat `Expr::App`
    /// argument", and relocating the latter would change this paren's own
    /// source position, flipping `Expr::App`'s own (span-based) multiline
    /// decision on the next pass. The "break the glued token instead"
    /// handling belongs at the call site that knows it's printing an arrow's
    /// RHS - see `print_arrow_rhs`.
    ///
    /// `is_typ` picks between two deliberately different hang strategies once
    /// `inner` is going to print as a block (see "Types are a floor" in
    /// FORMATTER.md):
    /// - `Typ::Paren` (`is_typ = true`): `inner` hangs under the *exact
    ///   column* right after `( `, however much text that's glued in front of
    ///   it (`:: `, `-> `, a class name, ...) - a type-level `::`/`=>`/`->`/`.`
    ///   never moves, so `inner`'s hang has to account for that prefix's real
    ///   width itself rather than approximating with a level bump.
    /// - `Expr::Paren` (`is_typ = false`): `inner` hangs one level below
    ///   wherever we already were, the same as always - a value's own glued
    ///   constructs already have an established "break the glued token
    ///   first instead" strategy (`paren_would_break` + `print_arrow_rhs`),
    ///   so by the time this runs, whatever `(` is glued after either isn't
    ///   going to move, or already broke onto its own fresh line.
    fn print_paren_block(&mut self, print_inner: impl FnOnce(&mut Self)) {
        // A paren is its own bracketed context, unrelated to whatever signature
        // it happens to be nested inside - a chain inside it that was written
        // flat shouldn't inherit an enclosing broken-signature's forced
        // expansion (see the same reset in `print_row`). Irrelevant to `Expr`,
        // which doesn't use `in_broken_sig`, so this is a no-op there.
        let outer_in_broken_sig = self.in_broken_sig;
        self.in_broken_sig = false;
        // Same "floor" model as `print_row`: hang the body, and the closing
        // paren, under this paren's own real column, not an `indent_in`-level
        // approximation of it - when `(` is glued mid-line after something of
        // its own width (an operator, a class name), the ambient indent
        // baseline has no memory of that width. Applies to `Expr::Paren` too,
        // not just `Typ::Paren`: an `Op` operand glued after `<#> ` with no
        // relocation decision of its own needs this the same way.
        let open_col = self.current_column();
        let inner_text = self.render_at_column(open_col + 2, print_inner);
        self.in_broken_sig = outer_in_broken_sig;
        self.raw("(");
        if inner_text.contains('\n') {
            self.raw(" ");
            self.raw(&inner_text);
            self.with_indent_at(open_col, Self::newline);
        } else {
            self.raw(&inner_text);
        }
        self.raw(")");
    }

    fn text(&self, span: Span) -> &'s str {
        source_text_with_starts(self.source, &self.line_starts, &span).unwrap_or("")
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
            let hi = span.hi().0;
            self.emit_pending_comment();
            // Preserve a source blank line between this comment and whatever
            // follows it - the next comment this same loop is about to flush
            // (only if it's actually still before `line`; otherwise it
            // belongs to some unrelated, much later comment group and its
            // position says nothing about a gap right here), or `line`
            // itself otherwise. Same "0 or 1, never more" leading-blank-line
            // preservation `print_module`'s decl loop and
            // `print_indented_siblings` already apply *before* a comment
            // group, just applied here *inside* one too (a standalone
            // section comment like `-- MODEL` followed by a deliberate blank
            // line before the declaration it precedes).
            let next_line = match self.comments.get(self.comment_idx) {
                Some((_, s)) if s.lo().0 < line => s.lo().0,
                _ => line,
            };
            if next_line > hi + 1 {
                self.insert_blank_line();
            }
        }
    }

    /// The line whatever prints next for `before_line` will actually start on:
    /// the first pending comment's line if one is attached ahead of it, else
    /// `before_line` itself. Used to measure "was there a source blank line
    /// here" against what visually comes first, since a comment block leading
    /// a decl/binding is what the blank line (if any) actually precedes, not
    /// the decl/binding's own span.
    fn next_visible_line(&self, before_line: usize) -> usize {
        match self.comments.get(self.comment_idx) {
            Some((_, span)) if span.lo().0 < before_line => span.lo().0,
            _ => before_line,
        }
    }

    /// If the very next pending comment starts on `hi_line` (the source line
    /// whatever was just printed ended on), it was written trailing that
    /// content on the same line (`foo = 1 -- like this`) rather than leading
    /// whatever comes next - glue it onto the current line instead of
    /// `flush_comments_before`'s always-its-own-leading-line treatment.
    /// A no-op, leaving the comment for the next `flush_comments_before` to
    /// pick up as a leading comment, if it starts on any other line. Returns
    /// whether a comment was actually flushed - callers that decide their own
    /// break state per-item (`Expr::Op`'s operand loop) need to know a
    /// trailing comment just ended the current line even when no source span
    /// gap says so, so the next item can't stay glued after it.
    fn flush_trailing_comment(&mut self, hi_line: usize) -> bool {
        let Some((Ok(Token::LineComment(s) | Token::BlockComment(s)), span)) =
            self.comments.get(self.comment_idx)
        else {
            return false;
        };
        if span.lo().0 != hi_line {
            return false;
        }
        self.raw(" ");
        self.raw(s);
        self.comment_idx += 1;
        // A `--` line comment swallows everything after it up to the next
        // real line break - whatever the caller goes on to print right after
        // this call (a closing `}`/`)`, the next sibling, ...) would silently
        // become part of the comment, corrupting the output, without this.
        // Safe/harmless for a block comment too, just not strictly required.
        self.newline();
        true
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

    /// True if there's a source line break between the end of `a` and the
    /// start of `b`.
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

    /// Flattens a curried `App(App(App(f, a1), a2), a3)` chain into
    /// `(f, [a1, a2, a3])` - lets `Expr::App` decide multiline-ness (and print
    /// one-arg-per-line) for the whole call at once, the same way `list()` does
    /// for bracketed items, instead of each binary `App` node deciding on its
    /// own in isolation. Without this, a block (`case`/`do`/...) buried inside
    /// one argument of a call whose *other* arguments span multiple lines in the
    /// source has no way to inherit the extra indent that implies - it prints at
    /// whatever indent level was already active before the call, which can land
    /// shallower than sibling lines the call goes on to print, i.e. its own
    /// contents appear to print "before" (at a shallower indent than) the block
    /// itself.
    fn app_spine(e: &Expr) -> (&Expr, Vec<&Expr>) {
        let mut args = Vec::new();
        let mut cur = e;
        while let Expr::App(f, a) = cur {
            args.push(a.as_ref());
            cur = f;
        }
        args.reverse();
        (cur, args)
    }

    /// An operator's precedence *number* (`op_fixity`'s `Prec::L(n)`/`R(n)`/
    /// `N(n)`, stripped of its associativity direction) - what `op_spine`
    /// uses to decide whether two adjacent operators bind at the same level.
    fn op_prec(op: &QOp) -> usize {
        crate::parser::op_fixity((op.1).0 .0).prec()
    }

    /// Flattens a *same-precedence* run of an `Op` tree - `Op(a, op1, Op(b,
    /// op2, c))`, `Op(Op(a, op1, b), op2, c)`, or any other nesting shape
    /// precedence climbing produces, provided `op1`/`op2`/... all share one
    /// precedence number - into the flat in-order sequence of operands and
    /// operators the source actually wrote: `(a, [(op1, b), (op2, c)])`. A
    /// child `Op` node whose operator binds at a *different* precedence than
    /// `e`'s own (a tighter or looser sub-chain, e.g. the `&&`s inside `a ||
    /// b && c || d && e`) is left un-flattened - it stays a single atomic
    /// operand here, printed later by recursing back into `Expr::Op`'s own
    /// printing, so it makes its own independent flat/multiline decision
    /// instead of being dragged into the outer chain's.
    ///
    /// Flattening a same-precedence run is needed for the same reason
    /// `app_spine` flattens `App`: printing each binary `Op` node's
    /// multiline decision independently nests one `indent_in` inside another
    /// whenever the tree leans the "wrong" way for its operator's
    /// associativity (e.g. right-associative `<>`, which nests on the right,
    /// puts each subsequent `Op` inside the previous one's own `indent_in`/
    /// `newline` block) - so a chain of N same-precedence operators drifts
    /// one indent level deeper per operator instead of lining up flush.
    /// Flattening first lets the whole run make one multiline decision and
    /// print every continuation at the same indent, regardless of how
    /// precedence happened to shape the tree.
    fn op_spine(e: &Expr) -> (&Expr, Vec<(&QOp, &Expr)>) {
        fn go<'e>(e: &'e Expr, target: usize, operands: &mut Vec<&'e Expr>, ops: &mut Vec<&'e QOp>) {
            match e {
                Expr::Op(l, op, r) if Printer::op_prec(op) == target => {
                    go(l, target, operands, ops);
                    ops.push(op);
                    go(r, target, operands, ops);
                }
                _ => operands.push(e),
            }
        }
        let target = match e {
            Expr::Op(_, op, _) => Self::op_prec(op),
            _ => return (e, Vec::new()),
        };
        let mut operands = Vec::new();
        let mut ops = Vec::new();
        go(e, target, &mut operands, &mut ops);
        let first = operands.remove(0);
        (first, ops.into_iter().zip(operands).collect())
    }

    /// The `Typ` counterpart of `app_spine`.
    fn typ_app_spine(t: &Typ) -> (&Typ, Vec<&Typ>) {
        let mut args = Vec::new();
        let mut cur = t;
        while let Typ::App(f, a) = cur {
            args.push(a.as_ref());
            cur = f;
        }
        args.reverse();
        (cur, args)
    }

    /// The `Typ` counterpart of `op_spine`. Unlike `Expr` operators, every
    /// type-level operator parses left-associative (see `typ_fop`), so a
    /// chain never nests the "wrong" way and never needs the stacked-indent
    /// fix `op_spine` exists for - but flattening it here still buys one
    /// multiline decision for the whole chain instead of one independent
    /// decision per adjacent pair, matching `print_typ_arrow_chain` and
    /// `print_typ_constrained_chain`.
    fn typ_op_spine(t: &Typ) -> (&Typ, Vec<(&QOp, &Typ)>) {
        fn go<'e>(t: &'e Typ, operands: &mut Vec<&'e Typ>, ops: &mut Vec<&'e QOp>) {
            match t {
                Typ::Op(l, op, r) => {
                    go(l, operands, ops);
                    ops.push(op);
                    go(r, operands, ops);
                }
                _ => operands.push(t),
            }
        }
        let mut operands = Vec::new();
        let mut ops = Vec::new();
        go(t, &mut operands, &mut ops);
        let first = operands.remove(0);
        (first, ops.into_iter().zip(operands).collect())
    }

    /// Prints `args` (already glued to some preceding `first_span`, e.g. a
    /// spine's head or a constraint's class name) one at a time: glue each
    /// with a leading space until one either has a real source break before
    /// it or would itself print multiline (`would_break`), then that
    /// argument and every one after it print one-per-line at a single shared
    /// indent level. Args before the first break stay glued, since nothing
    /// forces them apart.
    fn print_spine_args<T>(
        &mut self,
        first_span: Span,
        args: &[T],
        span_of: impl Fn(&T) -> Span,
        would_break: impl Fn(&mut Self, &T) -> bool,
        print: impl Fn(&mut Self, &T),
    ) {
        let mut prev_span = first_span;
        let mut broke = false;
        for a in args {
            let cur_span = span_of(a);
            if !broke && (Self::breaks_before(prev_span, cur_span) || would_break(self, a)) {
                self.indent_in();
                broke = true;
            }
            if broke {
                self.newline();
            } else {
                self.raw(" ");
            }
            print(self, a);
            prev_span = cur_span;
        }
        if broke {
            self.indent_out();
        }
    }

    /// `print_spine_args`'s counterpart for a data constructor's own
    /// argument types: same "glue until a break forces them apart, then one
    /// per line" policy, but *two* indent levels deep instead of one. `= `/
    /// `| ` are exactly `INDENT` wide, so one level alone would make the
    /// first argument look like it merely continues `cname`'s own column
    /// rather than nesting under it (same reasoning as
    /// `print_record_field_rhs`'s two-levels branch).
    fn print_ctor_args(&mut self, cname_span: Span, cargs: &[Typ]) {
        let mut prev_span = cname_span;
        let mut broke = false;
        for a in cargs {
            let cur_span = a.span();
            if !broke && (Self::breaks_before(prev_span, cur_span) || self.typ_would_break(a)) {
                self.indent_in();
                self.indent_in();
                broke = true;
            }
            if broke {
                self.newline();
            } else {
                self.raw(" ");
            }
            self.print_typ(a);
            prev_span = cur_span;
        }
        if broke {
            self.indent_out();
            self.indent_out();
        }
    }

    /// `Expr::App`'s own version of `print_spine_args`: glues each argument
    /// with a leading space until the first one that either has a real
    /// source break before it or doesn't fit flat, then moves that argument
    /// (and every one after it) onto its own line at one shared indent
    /// level. Whether an argument "doesn't fit flat" is decided by *trying*
    /// it directly in the real output (mark the position, print it, check
    /// afterward for a `'\n'`) and rolling back only that one attempt if it
    /// fails - not by rendering every argument into a scratch buffer up
    /// front the way `print_spine_args`'s `would_break` callback does
    /// elsewhere, which is `O(2^depth)` in AST nesting depth once an
    /// argument can itself be a call whose own arguments need the same
    /// decision (a real, deeply-nested file used to hang on this instead of
    /// finishing in a couple of seconds).
    fn print_app_args(&mut self, first_span: Span, args: &[&Expr]) {
        let mut prev_span = first_span;
        let mut broke = false;
        for a in args {
            let cur_span = a.span();
            if !broke && Self::breaks_before(prev_span, cur_span) {
                self.indent_in();
                broke = true;
            }
            if !broke {
                let mark = self.out.len();
                let comment_idx_before = self.comment_idx;
                self.raw(" ");
                self.print_expr(a);
                if !self.out[mark..].contains('\n') {
                    prev_span = cur_span;
                    continue;
                }
                self.out.truncate(mark);
                self.comment_idx = comment_idx_before;
                self.indent_in();
                broke = true;
            }
            self.newline();
            self.print_expr(a);
            prev_span = cur_span;
        }
        if broke {
            self.indent_out();
        }
    }

    /// True if `a` is a type signature immediately followed by its own
    /// definition, or both are pattern-matching clauses of the same function
    /// (`Decl::Def`) - these stay adjacent, with no blank line between them.
    fn decls_are_glued(a: &Decl, b: &Decl) -> bool {
        matches!(a, Decl::Sig(..) | Decl::Def(..)) && a.ud() == b.ud()
    }

    /// Prints ` :: Typ`, breaking to an indented `\n:: Typ` when the signature
    /// originally spanned multiple lines - so a deliberately wrapped signature
    /// (forall/constraints/arrow chain sprawling across lines) doesn't collapse
    /// into one long line.
    fn print_sig_typ(&mut self, before: Span, typ: &Typ) {
        // Both conditions must produce the *same* shape (`::` moves onto its
        // own line, glued to `typ`) - a `typ_paren_would_break`-only case
        // that printed a different shape would make `breaks_before` true on
        // the next parse, so it would never be a stable fixed point.
        if Self::breaks_before(before, typ.span()) || self.typ_paren_would_break(typ) {
            self.indent_in();
            self.newline();
            self.raw(":: ");
            let outer = self.in_broken_sig;
            self.in_broken_sig = true;
            // `typ` is glued directly after `:: ` here, a fixed-width raw
            // token the indent baseline has no memory of - so if `typ` is
            // itself a nesting shape (`App`/`Record`/`Row`) that breaks, it
            // needs to hang under `typ`'s own real column (`hang_glued`),
            // the same reasoning as `print_constraint`'s own hang. Not
            // applied to an operator-chain shape (`Arr`/`Op`/`Constrained`/
            // `Forall`): those must stay at the ambient level for their own
            // continuations (see `print_typ_arrow_chain`'s doc comment) -
            // hanging here would incorrectly push every `->`/`=>`
            // continuation deeper.
            let needs_hang = matches!(typ, Typ::App(..) | Typ::Record(..) | Typ::Row(..));
            if needs_hang {
                self.hang_glued(|p| p.print_typ(typ));
            } else {
                self.print_typ(typ);
            }
            self.in_broken_sig = outer;
            self.indent_out();
        } else {
            self.raw(" :: ");
            self.print_typ(typ);
        }
    }

    /// The `type X = Typ` counterpart of `print_sig_typ` - a type alias's `=`
    /// gets the same treatment a signature's `::` does (see `print_sig_typ`)
    /// so the two break consistently, and so a value's `=` (`print_arrow_rhs`)
    /// and a type alias's `=` behave the same way.
    fn print_typ_alias_rhs(&mut self, before: Span, typ: &Typ) {
        // Both conditions produce the same shape here already (`=` stays
        // glued to `before`, `typ` moves to a fresh indented line) - unlike
        // `print_sig_typ`, there's no second shape to collapse into on a
        // later pass, so this stays a stable fixed point either way.
        if Self::breaks_before(before, typ.span()) || self.typ_paren_would_break(typ) {
            self.raw(" =");
            self.indent_in();
            self.newline();
            let outer = self.in_broken_sig;
            self.in_broken_sig = true;
            self.print_typ(typ);
            self.in_broken_sig = outer;
            self.indent_out();
        } else {
            self.raw(" = ");
            self.print_typ(typ);
        }
    }

    /// A record/row field's own `label :: Typ` - like `print_typ_alias_rhs`,
    /// not `print_sig_typ`: a field's `::` stays glued to its label (unlike a
    /// top-level signature's `::`, which relocates to its own line), only
    /// `typ` itself moves to a fresh indented line when it would break. Real
    /// report: a field whose type was a multi-line application (`action ::
    /// VariantStorable (...)`) printed with `VariantStorable` glued right
    /// after `:: `, so its own parenthesized row just extended rightward
    /// from wherever that landed instead of relocating - `print_row`
    /// previously had no relocation logic here at all, unlike every other
    /// `name :: Typ`/`name = Typ` site in this printer.
    fn print_field_typ(&mut self, before: Span, typ: &Typ) {
        if Self::breaks_before(before, typ.span()) || self.typ_would_break(typ) {
            self.raw(" ::");
            // Two levels, not one - same reasoning as
            // `print_record_field_rhs`'s own two-levels branch: `label ::`/
            // `, ` is exactly `INDENT` wide, so a single `indent_in()` would
            // land the relocated type flush with the field's own label
            // column instead of visibly past it.
            self.indent_in();
            self.indent_in();
            self.newline();
            let outer = self.in_broken_sig;
            self.in_broken_sig = true;
            let needs_hang = matches!(typ, Typ::App(..) | Typ::Record(..) | Typ::Row(..));
            if needs_hang {
                self.hang_glued(|p| p.print_typ(typ));
            } else {
                self.print_typ(typ);
            }
            self.in_broken_sig = outer;
            self.indent_out();
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
    /// `open_span`/`close_span` are the brackets' own spans when the caller
    /// has them (pass `Span::zero()` otherwise, e.g. export/import lists,
    /// which never matches). `close_span` flushes a comment sitting after
    /// the last item but before the close - otherwise unreachable, since
    /// there's no next item to flush before and `flush_trailing_comment`
    /// only fires for a comment sharing the last item's own line. `open_span`
    /// detects a source break between the brackets when there are no items
    /// to otherwise carry one.
    /// `item_hang` gives each item, in the expanded path, one extra indent
    /// level while it's printed - needed when the item is itself a nesting
    /// shape (most commonly an operator chain glued right after `open `/`, `)
    /// that would otherwise look flush with its own head instead of nested
    /// under it. Pass `false` when the item printer already manages this
    /// itself (a record's fields do, via `print_record_field_rhs`).
    #[allow(clippy::too_many_arguments)]
    fn list<T>(
        &mut self,
        open: &str,
        close: &str,
        open_span: Span,
        close_span: Span,
        pad: bool,
        item_hang: bool,
        items: &[T],
        span_of: impl Fn(&T) -> Span,
        mut print_item: impl FnMut(&mut Self, &T),
    ) {
        // A source break can sit between `open` and the first item, or
        // between the last item and `close`, not just between two adjacent
        // items - the only way it can show up at all when there's one item
        // or none, since a plain `any_breaks` over item spans has no
        // adjacent pair to see it with then. Folding `open_span`/`close_span`
        // into the same boundary chain `any_breaks` walks handles all of
        // these uniformly, including the zero-item case.
        let mut boundary_spans: Vec<Span> = Vec::with_capacity(items.len() + 2);
        if open_span != Span::zero() {
            boundary_spans.push(open_span);
        }
        boundary_spans.extend(items.iter().map(&span_of));
        if close_span != Span::zero() {
            boundary_spans.push(close_span);
        }
        let multiline_from_source = Self::any_breaks(&boundary_spans);

        if !multiline_from_source {
            if items.is_empty() {
                self.raw(open);
                self.flush_comments_before(close_span.lo().0);
                self.raw(close);
                return;
            }
            // An item with no source break around it can still be going to
            // print across multiple lines on its own (an `App` whose own
            // spine breaks, an operator chain) - that should switch the
            // whole list to the expanded style too, not just leave the item
            // glued flat with its own internal break looking like a stray
            // mid-line indent.
            //
            // Decided by trying the flat style directly (write `open`/items/
            // `close` into the real output) and checking *after the fact*
            // for a `'\n'`, rather than probing every item into a scratch
            // buffer first: probing recurses into this same "render to
            // check" pattern for a nested `Array`/`Record`'s own items,
            // doubling work at every nesting level - `O(2^depth)` instead of
            // `O(depth)`, and a real pathological case (a deeply-nested but
            // entirely flat literal) never finished printing under it. If
            // nothing printed contains a break, this was the right call at
            // the cost of one traversal. If something did, roll back to
            // `mark` (rewinding `comment_idx` too, so the expanded path
            // below re-flushes what this attempt already flushed) and fall
            // through to the expanded style - a real but non-recursive 2x,
            // paid only by the ancestors of whatever forced the break.
            let mark = self.out.len();
            let comment_idx_before = self.comment_idx;
            // Deliberately no `flush_trailing_comment` call in this branch,
            // unlike the multiline one below: with several items sharing one
            // physical line, "a pending comment starts on this item's own hi()
            // line" doesn't mean *this* item is the last thing on that line -
            // any earlier item on the same flat line would wrongly claim a
            // comment that actually trails a *later* item, the closing
            // bracket, or (as found against real-world input) something
            // outside this list entirely. Safe in the multiline branch only
            // because each item there is genuinely alone on its own line.
            self.raw(open);
            if pad {
                self.raw(" ");
            }
            for (i, item) in items.iter().enumerate() {
                self.flush_comments_before(span_of(item).lo().0);
                if i > 0 {
                    self.raw(", ");
                }
                print_item(self, item);
            }
            self.flush_comments_before(close_span.lo().0);
            if pad {
                self.raw(" ");
            }
            self.raw(close);
            if !self.out[mark..].contains('\n') {
                return;
            }
            self.out.truncate(mark);
            self.comment_idx = comment_idx_before;
        }

        // Reached either because the source already forced this (checked
        // above), or because the flat attempt just rolled back.
        {
            // If some outer construct already broke to a fresh line right before
            // this call (e.g. a `=`/`->` that decided to break because *this*
            // list starts on its own source line), don't also bump our own
            // indent level - `newline()` below would be a no-op for the opening
            // bracket (we're already at the start of a line) but the level bump
            // would still stick around for every item after it, indenting them
            // one level deeper than the bracket itself. Only take our own level
            // when we're the one initiating the break.
            //
            // Unlike `print_row` (see its own version of this), a *value*-level
            // list glued after something (an outer `=`, a lambda's `->`, ...)
            // does relocate its opening bracket down a level here rather than
            // hanging in place - values and types are deliberately different
            // (see the "floor" model in FORMATTER.md): a value's own glued
            // constructs already have their own established "break the glued
            // token first instead" strategy (`paren_would_break` +
            // `print_arrow_rhs`), so by the time `list()` runs, whatever it's
            // glued after either isn't going to move, or already broke.
            //
            // Exception: if this whole list is itself sitting at exactly the
            // position an *outer* list() just glued it to (`glued_floor`) -
            // i.e. this list is a sole/first item like `[ { c: 1\n, d: 2\n} ]`
            // - the outer list already committed to gluing here. Relocating
            // anyway would double up on the outer list's own already-settled
            // layout.
            let own_indent =
                !self.at_fresh_line() && self.glued_floor != Some(self.out.len());
            if own_indent {
                self.indent_in();
                self.newline();
            }
            // Same "floor" fix as `print_paren_block`: hang every
            // continuation line (and the closing bracket) under `open`'s own
            // real column, not the ambient baseline - a no-op when
            // `own_indent` just relocated us, but needed when the list stays
            // glued mid-line (after an operator, most commonly), since
            // ambient has no memory of that glued prefix's width.
            let open_col = self.current_column();
            let saved_indent = self.indent;
            self.indent = open_col;
            self.raw(open);
            self.raw(" ");
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    self.newline();
                }
                // Flush before the leading comma, not after - a comment
                // belongs above the `, item` pair it precedes, not stranding
                // the comma alone on its own line ahead of it.
                self.flush_comments_before(span_of(item).lo().0);
                if i > 0 {
                    self.raw(", ");
                }
                // An item is glued directly after `open `/`, ` here, a
                // fixed-width raw token the indent baseline has no memory
                // of - so if the item is itself a nesting shape that breaks
                // further (most commonly an operator chain), that break
                // needs one more level than the item's own line, or it looks
                // flush with the item's own head instead of visibly nested
                // under it (easy to mistake for another sibling item at the
                // list's own comma column). Invisible when the item prints
                // flat. Same reasoning as `print_record_field_rhs`'s hang.
                // Only for callers whose items don't already manage their
                // own hang (`item_hang`) - a record's fields already get
                // this from `print_record_field_rhs`, and adding another
                // level here would double up on it.
                if item_hang {
                    self.indent_in();
                }
                let prev_glued_floor = self.glued_floor;
                self.glued_floor = Some(self.out.len());
                print_item(self, item);
                self.glued_floor = prev_glued_floor;
                if item_hang {
                    self.indent_out();
                }
                // Each item is always the last thing on its own line here (the
                // next one, or the closing bracket, starts its own fresh
                // `newline()`) - safe to check for a trailing comment. Without
                // this, a comment trailing the *last* item specifically had
                // nowhere to be flushed before the closing bracket, so it rode
                // straight past it to wherever the next flush point happened to
                // be - possibly relocating into unrelated code entirely, and
                // (since that also changes what row the bracket's own
                // surroundings appear to end on) risking a multiline decision
                // elsewhere flipping between formatting passes.
                self.flush_trailing_comment(span_of(item).hi().0);
            }
            // Catches a comment that's on its own separate line, still before
            // the close - `flush_trailing_comment` above only catches one
            // sharing the last item's own line.
            self.flush_comments_before(close_span.lo().0);
            self.newline();
            self.raw(close);
            self.indent = saved_indent;
            if own_indent {
                self.indent_out();
            }
        }
    }

    // -- module ----------------------------------------------------------

    fn print_module(&mut self, m: &Module) {
        let mut prev_hi_line: Option<usize> = None;
        if let Some(h) = &m.0 {
            self.print_header(h);
            // `print_header` already forced a blank line right after the export
            // list when there were no imports to absorb it instead - don't also
            // let the gap check below add a second one for the first decl based
            // on the (now-irrelevant) source line count.
            if !(h.1.is_some() && h.2.is_empty()) {
                prev_hi_line = Some(h.span().hi().0);
            }
        }
        let mut prev: Option<&Decl> = None;
        for decl in &m.1 {
            let glued = prev.is_some_and(|p| Self::decls_are_glued(p, decl));
            let content_line = self.next_visible_line(decl.span().lo().0);
            let had_blank = prev_hi_line.is_some_and(|hi| content_line > hi + 1);
            if !glued && had_blank {
                self.raw("\n");
            }
            self.flush_comments_before(decl.span().lo().0);
            self.print_decl(decl);
            // Redundant (a no-op) for a `Decl::Def`/`Decl::Instance`/etc. whose
            // own printing already checked this via `print_guarded_expr` or
            // `print_indented_siblings` - needed for the decl kinds that
            // don't route through either of those.
            self.flush_trailing_comment(decl.span().hi().0);
            // Not `raw("\n")` - a consumed trailing comment already ended
            // this line itself (`flush_trailing_comment` always calls
            // `newline()`), and unconditionally adding another would leave a
            // spurious blank line after every decl that has one.
            self.ensure_fresh_line();
            prev = Some(decl);
            prev_hi_line = Some(decl.span().hi().0);
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
                Span::zero(),
                Span::zero(),
                false,
                true,
                exports,
                |e| e.span(),
                |p, e| p.print_export(e),
            );
            self.raw(" ");
        }
        self.raw("where");
        self.newline();
        // purs-tidy always separates a real export list from whatever follows
        // (the first import, or the first decl if there are none) with a blank
        // line, regardless of whether the source had one there.
        if exports.is_some() {
            self.raw("\n");
        }
        self.print_imports(imports);
    }

    /// Groups and sorts imports the way purs-tidy does: unqualified "open" imports
    /// (`import Foo`, or `import Foo hiding (...)` - anything with no explicit name
    /// list and no alias) form their own group first, separated by a blank line
    /// from the rest; everything else is sorted alphabetically by module name,
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
                    is_open: i.names.is_none() && i.to.is_none(),
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
            (!a.is_open, self.text(a.from.span()), a.to.is_some())
                .cmp(&(!b.is_open, self.text(b.from.span()), b.to.is_some()))
        });

        for (idx, m) in merged.iter().enumerate() {
            if idx > 0 && merged[idx - 1].is_open && !m.is_open {
                self.raw("\n");
            }
            self.print_merged_import(m);
            self.newline();
        }
    }

    fn dedup_sort_imports(&self, items: &mut Vec<Import>) {
        items.sort_by_key(|a| self.import_sort_key(a));
        items.dedup_by(|a, b| self.import_display_text(a) == self.import_display_text(b));
    }

    /// Sorting key for an import item - a (tier, bare name) pair, not just
    /// rendered text. purs-tidy's real sort ranks by *kind* first - class
    /// imports, then type-operator imports (`type (~>)`), then plain type
    /// imports, then plain value imports, then value-operator imports last -
    /// and only alphabetically by name *within* each tier. That's why e.g.
    /// `type (..)` sorts before a plain type name even when its symbol text
    /// wouldn't win a flat compare, and why a value operator like `(>>=)`
    /// sorts after `bind`/`discard`/`join` (`(` is low ASCII, which a flat
    /// sort would put first). A flat sort on rendered or bare text can't
    /// reproduce this; the tier has to be its own key column.
    fn import_sort_key(&self, i: &Import) -> (u8, &str) {
        match i {
            Import::Class(_, n) => (0, self.text(n.span())),
            Import::TypSymbol(_, s) => (1, self.text(s.span())),
            Import::Typ(_, n) => (2, self.text(n.span())),
            Import::TypDat(_, n, _) => (2, self.text(n.span())),
            Import::Value(_, n) => (3, self.text(n.span())),
            Import::Symbol(_, s) => (4, self.text(s.span())),
        }
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
            self.list(
                "(",
                ")",
                Span::zero(),
                Span::zero(),
                false,
                true,
                items,
                |x| x.span(),
                |p, x| p.print_import(x),
            );
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
                self.list(
                    "(",
                    ")",
                    Span::zero(),
                    Span::zero(),
                    false,
                    true,
                    names,
                    |n| n.span(),
                    |p, n| p.lit(n),
                );
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
                self.print_spine_args(
                    name.span(),
                    binders,
                    |b| b.span(),
                    |p, b| p.binder_would_break(b),
                    |p, b| p.print_binder(b),
                );
                let before = binders.last().map_or(name.span(), |b| b.span());
                self.print_guarded_expr(before, ge, " = ");
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
                // `any_breaks` alone only catches breaking *between* two or
                // more constructors - a lone constructor has no adjacent pair
                // to compare, so it never fired even when that constructor's
                // own args would break (e.g. a record with enough fields),
                // leaving `= Ctor` glued flat while its args relocated out
                // from under it. Checking the sole constructor's own args
                // here closes that gap, matching the "= Ctor" line always
                // moving down together with its args, the same one true
                // shape the multi-constructor case already uses.
                let multiline = Self::any_breaks(&ctor_spans)
                    || (ctors.len() == 1 && ctors[0].1.iter().any(|a| self.typ_would_break(a)));
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
                    self.print_ctor_args(cname.span(), cargs);
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
                let before = vars.last().map_or(name.span(), |v| v.span());
                self.print_typ_alias_rhs(before, typ);
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
                // Unlike `Decl::Data`, a newtype constructor always wraps
                // exactly one `Typ` - never a space-separated arg list - so
                // this is its own direct relocation, not a borrowed call into
                // `print_ctor_args` (built for that plural case). The two
                // constructs are genuinely different (a newtype constructor
                // isn't a data constructor with one field), but land on the
                // same visual shape when the wrapped type would break: the
                // whole `= Ctor` line moves down together with it, rather
                // than leaving `= Ctor` glued flat while only `typ` relocates
                // out from under it.
                let multiline = self.typ_would_break(typ);
                self.indent_in();
                if multiline {
                    self.newline();
                } else {
                    self.raw(" ");
                }
                self.raw("= ");
                self.lit(ctor);
                if multiline {
                    // Two levels past the `= Ctor` line, matching
                    // `print_ctor_args`'s own double indent for a relocated
                    // data-constructor argument - same visual depth for the
                    // same kind of jump, even though this is separate code.
                    self.indent_in();
                    self.indent_in();
                    self.newline();
                    self.print_typ(typ);
                    self.indent_out();
                    self.indent_out();
                } else {
                    self.raw(" ");
                    self.print_typ(typ);
                }
                self.indent_out();
            }

            Decl::ClassKind(name, kind) => {
                self.raw("class ");
                self.lit(name);
                self.print_sig_typ(name.span(), kind);
            }
            Decl::Class(constraints, name, vars, fundeps, members) => {
                self.raw("class ");
                let multiline = self.print_constraint_ctx(constraints, name.span(), "<=");
                self.lit(name);
                for v in vars {
                    self.raw(" ");
                    self.print_typ_var_binding(v);
                }
                if multiline {
                    self.indent_out();
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
                    self.print_indented_siblings(
                        members,
                        |m| m.span(),
                        |p, m| p.print_class_member(m),
                    );
                }
            }

            Decl::Instance(is_else, head, bindings) => {
                if *is_else {
                    self.raw("else ");
                }
                self.raw("instance ");
                let mark = self.out.len();
                self.print_inst_head(head);
                if !bindings.is_empty() {
                    // `where` glues flat (` where`) unless the head - the
                    // constraint context, the class/args spine, or both -
                    // printed across more than one line, in which case it
                    // relocates onto its own line at the same indent level
                    // `=>` sits at (one `indent_in`, matching
                    // `print_constraint_ctx`'s own), rather than staying
                    // glued to whatever the head's last printed token
                    // happens to be (e.g. a spine arg like `to`). Checked by
                    // looking for a real `'\n'` in what was just printed
                    // (the same rendered-output check `paren_would_break`/
                    // `typ_would_break` use), not a span comparison - the
                    // head's own multiline-ness already accounts for every
                    // reason it could break, so this doesn't need its own
                    // parallel decision.
                    if self.out[mark..].contains('\n') {
                        self.indent_in();
                        self.newline();
                        self.raw("where");
                        self.indent_out();
                    } else {
                        self.raw(" where");
                    }
                    self.print_indented_siblings(
                        bindings,
                        |b| b.span(),
                        |p, b| p.print_inst_binding(b),
                    );
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

    /// Prints an `instance`/`class` head's optional constraint context -
    /// `(A, B) => `/`A => ` for an instance head, `(A, B) <= `/`A <= ` for a
    /// class - and decides, via `any_breaks` over the constraints' own spans
    /// plus the bracket spans (when parenthesized) plus `after` (the span of
    /// whatever comes right after the arrow, e.g. the instance/class name),
    /// whether the source had this expanded across multiple lines. Mirrors
    /// `print_typ_constrained_chain`'s decision, generalized from a single
    /// chained constraint to a comma-separated list - unlike that chain,
    /// there's no preceding name/`::` to check a "glued mid-line" boundary
    /// against (`instance`/`class` are fixed keywords, not spans), so on the
    /// multiline path everything - parens, arrow, and (per the caller, which
    /// must close the same `indent_in` this opens) whatever follows - is
    /// unconditionally relocated onto fresh indented lines: one canonical
    /// shape, always a fixed point on the next parse, the same reasoning as
    /// `print_sig_typ`'s "both branches produce the same shape" comment.
    /// Returns whether it took the multiline path, so the caller knows
    /// whether it must `indent_out` after printing what follows the arrow.
    fn print_constraint_ctx(
        &mut self,
        constraints: &Option<Constraints>,
        after: Span,
        arrow: &str,
    ) -> bool {
        let Some(Constraints(open, cs, close)) = constraints else {
            return false;
        };
        let mut spans: Vec<Span> = Vec::with_capacity(cs.len() + 3);
        if *open != Span::zero() {
            spans.push(*open);
        }
        spans.extend(cs.iter().map(|c| c.span()));
        if *close != Span::zero() {
            spans.push(*close);
        }
        spans.push(after);
        let multiline = Self::any_breaks(&spans);

        if multiline {
            self.indent_in();
            self.newline();
        }
        // Parens around a lone constraint are syntactically optional, but
        // whether the source actually wrote them is real information -
        // `constraints()` (parser.rs) only leaves `open`/`close` as
        // `Span::zero()` for the genuinely parenless form, never for an
        // explicit `(A) => `. Printing exactly what's there, rather than
        // unilaterally normalizing it away, matches how `Expr::Paren`/
        // `Typ::Paren` are handled everywhere else in this printer -
        // removing a truly redundant paren is a `style.rs` rule's job
        // (opt-in), not something the raw printer decides on its own.
        let has_parens = cs.len() > 1 || *open != Span::zero();
        if !has_parens {
            self.print_constraint(&cs[0]);
        } else if multiline {
            // Leading-comma style, matching `list()`'s convention for every
            // other bracketed multi-item construct.
            self.raw("( ");
            for (i, c) in cs.iter().enumerate() {
                if i > 0 {
                    self.newline();
                    self.raw(", ");
                }
                self.print_constraint(c);
            }
            self.newline();
            self.raw(")");
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
        if multiline {
            self.newline();
        } else {
            self.raw(" ");
        }
        self.raw(arrow);
        self.raw(" ");
        multiline
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
        let multiline = self.print_constraint_ctx(constraints, name.span(), "=>");
        // Same unconditional hang reasoning as `print_constraint`'s own args:
        // `name` is glued directly after `=> ` (or nothing at all), a
        // fixed-width raw token/absent-token the indent baseline has no
        // memory of - so a multiline arg needs to hang under `name`'s own
        // real column, not the ambient baseline.
        let name_col = self.current_column();
        self.lit(name);
        self.with_indent_at(name_col, |p| {
            // See `print_constraint`/`Typ::App` - a `Typ::Paren` arg that
            // would itself break relocates it and every arg after it, same
            // as `Expr::App`; `Record`/`Row` args keep hanging in place.
            p.print_spine_args(
                name.span(),
                args,
                |a| a.span(),
                |p, a| p.typ_paren_would_break(a),
                |p, a| p.print_typ(a),
            );
        });
        if multiline {
            self.indent_out();
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
                self.print_spine_args(
                    name.span(),
                    binders,
                    |b| b.span(),
                    |p, b| p.binder_would_break(b),
                    |p, b| p.print_binder(b),
                );
                let before = binders.last().map_or(name.span(), |b| b.span());
                self.print_guarded_expr(before, ge, " = ");
            }
        }
    }

    // -- guards --------------------------------------------------------

    /// `before` is the span of whatever immediately precedes `arrow` (the last
    /// binder, or the name/binder itself if there are none) - used to decide,
    /// via `breaks_before`, whether the RHS/guards should break onto their own
    /// indented line(s) or stay glued to `arrow` on the same line, the same
    /// source-fidelity pattern used throughout the printer (see `Expr::App`,
    /// `Expr::Lambda`, `Expr::Let`).
    /// `e`'s value is always the tail of a decl, guarded clause, let-binding,
    /// or case-branch - never a subexpression with more of the same source
    /// line still to come after it (contrast a bare `print_arrow_rhs` call,
    /// which is also how `Expr::Lambda`/`Guard::Binder` print, and can be
    /// nested arbitrarily deep - see the comment there) - so this is a safe,
    /// and the appropriate, place to check for a trailing comment after each
    /// clause's own RHS (or the one RHS, for `Unconditional`).
    fn print_guarded_expr(&mut self, before: Span, ge: &GuardedExpr, arrow: &str) {
        match ge {
            GuardedExpr::Unconditional(e) => {
                self.print_arrow_rhs(before, arrow, e);
                self.flush_trailing_comment(e.span().hi().0);
            }
            GuardedExpr::Guarded(clauses) => {
                let multiline = Self::breaks_before(before, clauses[0].0[0].span());
                if multiline {
                    self.indent_in();
                    for (guards, e) in clauses {
                        self.newline();
                        self.flush_comments_before(guards[0].span().lo().0);
                        self.raw("| ");
                        self.print_guard_clause(before, guards, e, arrow);
                        self.flush_trailing_comment(e.span().hi().0);
                    }
                    self.indent_out();
                } else {
                    for (guards, e) in clauses {
                        self.raw(" | ");
                        self.print_guard_clause(before, guards, e, arrow);
                        self.flush_trailing_comment(e.span().hi().0);
                    }
                }
            }
        }
    }

    /// Prints one guarded clause's `guard, guard ... arrow e` - `before` is the
    /// fallback anchor (see `print_guarded_expr`) used only when the clause has
    /// no guards; normally the clause's own last guard is what `e` is checked
    /// against for whether it should break onto its own indented line, the same
    /// way `Unconditional`'s RHS is.
    fn print_guard_clause(&mut self, before: Span, guards: &[Guard], e: &Expr, arrow: &str) {
        for (i, g) in guards.iter().enumerate() {
            if i > 0 {
                self.raw(", ");
            }
            self.print_guard(g);
        }
        let before = guards.last().map_or(before, |g| g.span());
        self.print_arrow_rhs(before, arrow, e);
    }

    /// The record-field counterpart of `print_arrow_rhs`: unlike a decl's
    /// `=` or a lambda's `->`, a record field's value always sits one level
    /// deeper than the field itself, whether or not it visibly moves onto
    /// its own line - so a nested multi-branch `case`/`do` value stays
    /// visually inside the field even when glued right after `label:`.
    ///
    /// The two branches need a *different* number of levels. When the value
    /// stays glued (`b: case x of`), its own head is still visually attached
    /// to the label, so one level is enough - it only has to keep the
    /// value's own further breaking from looking like a sibling field, and
    /// the value's own hang supplies the rest. When the value moves onto its
    /// own line entirely, that attachment is gone: `label:` and `{`/`, ` are
    /// exactly `INDENT` wide, so one level alone would place the value flush
    /// with `label`'s own column instead of visibly past it. Two levels are
    /// needed there.
    fn print_record_field_rhs(&mut self, before: Span, arrow: &str, e: &Expr) {
        if self.paren_would_break(e) || Self::breaks_before(before, e.span()) {
            self.raw(arrow.trim_end());
            self.indent_in();
            self.indent_in();
            self.newline();
            self.print_expr(e);
            self.indent_out();
            self.indent_out();
        } else {
            self.raw(arrow);
            self.indent_in();
            self.print_expr(e);
            self.indent_out();
        }
    }

    /// Prints `arrow e`, breaking `e` onto its own indented line when the
    /// source had it starting after a line break from `before` (the last
    /// token immediately preceding `arrow`) - the shared source-fidelity
    /// pattern behind a declaration's `=`, a lambda's `->`, a guarded
    /// clause's `->`/`=`, a do-statement's `<-`, and a let-pattern's `=`.
    /// Without this, a multiline construct (most commonly `let ... in`) that
    /// glues flat to `arrow` can end up printed at the same column as the
    /// statement it's embedded in, which is invalid PureScript layout - the
    /// parser reads it as that enclosing block ending early.
    ///
    /// One extra case forces a break even when the source didn't have one:
    /// `e` is a parenthesized expression that's going to print in the
    /// `( ` ... `)`-on-its-own-line block style (see `Expr::Paren`). Gluing
    /// `arrow` straight to `(` there would put the closing `)` back at
    /// `arrow`'s own (or an even shallower) column once printed - visually
    /// "moving back" past where this subexpression started, which a reader
    /// reasonably reads as the expression having ended early. Decided by
    /// actually rendering `e` at the current indent and checking for a line
    /// break, the same "don't trust a span here, trust what got printed"
    /// approach `Expr::Paren` itself uses and for the same reason (`e`'s
    /// paren can wrap a `case`/`do` that always breaks regardless of source
    /// layout, which would make a source-span check for this unstable across
    /// formatting passes). This check is deliberately narrow (only
    /// `Expr::Paren`, not e.g. `case`/`do`/`let`, which have no closing
    /// delimiter to regress to a shallower column) and deliberately lives
    /// here rather than as a general "am I at a fresh line" check inside
    /// `Expr::Paren` itself - `Expr::Paren` is also reached as one
    /// space-separated argument of a flat `Expr::App`, where relocating
    /// would rewrite that paren's own source position and flip `Expr::App`'s
    /// (span-based) multiline decision on the very next formatting pass.
    fn print_arrow_rhs(&mut self, before: Span, arrow: &str, e: &Expr) {
        if self.paren_would_break(e) || self.ado_would_break(e) || Self::breaks_before(before, e.span()) {
            self.raw(arrow.trim_end());
            self.indent_in();
            self.newline();
            self.print_expr(e);
            self.indent_out();
        } else {
            self.raw(arrow);
            self.print_expr(e);
        }
        // Deliberately no trailing-comment check here (contrast
        // `print_guarded_expr`, which does one): unlike a decl's `=` or a
        // guarded clause's `=`/`->`, this function is also how `Expr::Lambda`
        // prints its `->` and `Guard::Binder` prints its `<-` - and a lambda
        // can be nested anywhere inside a larger expression (with plenty
        // more of that same source line still to print after it returns),
        // and a guard can have more guards after it before the clause's own
        // arrow. Checking here would be exactly the "grabbed a comment
        // meant for something printed later on the same line" bug
        // `flush_trailing_comment` itself warns about - only call it from a
        // site that actually knows it's printing the last thing on a line.
    }

    fn print_guard(&mut self, g: &Guard) {
        match g {
            Guard::Expr(e) => self.print_expr(e),
            Guard::Binder(b, e) => {
                self.print_binder(b);
                self.print_arrow_rhs(b.span(), " <- ", e);
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
                self.print_spine_args(
                    name.span(),
                    binders,
                    |b| b.span(),
                    |p, b| p.binder_would_break(b),
                    |p, b| p.print_binder(b),
                );
                let before = binders.last().map_or(name.span(), |b| b.span());
                self.print_guarded_expr(before, ge, " = ");
            }
            LetBinding::Pattern(b, e) => {
                self.print_binder(b);
                self.print_arrow_rhs(b.span(), " = ", e);
            }
        }
    }

    fn print_let_bindings(&mut self, bindings: &[LetBinding]) {
        self.print_indented_siblings(bindings, |b| b.span(), |p, b| p.print_let_binding(b));
    }

    /// True if printing `b` at the current indent produces any line break at
    /// all - the `LetBinding` counterpart of `expr_would_break`, used by
    /// `print_let_kw_bindings` to decide whether a single binding can stay
    /// glued to `let` (its RHS might still be a `case`/`do`/`let` that always
    /// prints multiline regardless of source layout, which rules that out).
    fn let_binding_would_break(&mut self, b: &LetBinding) -> bool {
        let comment_idx_before = self.comment_idx;
        let would_break = self.render_indented(0, |p| p.print_let_binding(b)).contains('\n');
        self.comment_idx = comment_idx_before;
        would_break
    }

    /// The `DoStmt` counterpart of `let_binding_would_break`, used the same
    /// way by `Expr::Ado`'s own single-statement glue check.
    fn do_stmt_would_break(&mut self, s: &DoStmt) -> bool {
        let comment_idx_before = self.comment_idx;
        let would_break = self.render_indented(0, |p| p.print_do_stmt(s)).contains('\n');
        self.comment_idx = comment_idx_before;
        would_break
    }

    /// Prints a `let`-block's bindings right after the `let` keyword itself -
    /// used by `Expr::Let` and `DoStmt::Let`, where (unlike `where`, which
    /// always uses `print_let_bindings`' one-per-line indented block) the
    /// source commonly writes a single simple binding glued flat on the same
    /// line (`let a = 1`). Stays glued when there's exactly one binding, the
    /// source had it starting on `let`'s own line, and printing it doesn't
    /// itself force a line break (e.g. a nested `case`/`do`/`let` RHS always
    /// does, regardless of source layout); otherwise falls back to
    /// `print_let_bindings`'s indented block, same as `where`. Returns
    /// whether it glued - `Expr::Let` needs that to decide whether `in`
    /// itself can stay glued to the same line too (`let x = 1 in x`) or
    /// needs its own fresh line below the bindings block.
    fn print_let_kw_bindings(&mut self, let_span: Span, bindings: &[LetBinding]) -> bool {
        if let [only] = bindings
            && !Self::breaks_before(let_span, only.span())
            && !self.let_binding_would_break(only)
        {
            self.raw(" ");
            self.print_let_binding(only);
            return true;
        }
        self.print_let_bindings(bindings);
        false
    }

    /// The body of `print_indented_siblings`, without the indent_in()/
    /// indent_out() pair around it - for a caller (`Expr::Ado`) that needs to
    /// keep the same indent level active across the sibling list *and*
    /// something printed immediately after it.
    fn print_siblings_body<T>(
        &mut self,
        items: &[T],
        span_of: impl Fn(&T) -> Span,
        mut print_item: impl FnMut(&mut Self, &T),
    ) {
        let mut prev_hi_line: Option<usize> = None;
        for item in items {
            let content_line = self.next_visible_line(span_of(item).lo().0);
            let had_blank = prev_hi_line.is_some_and(|hi| content_line > hi + 1);
            self.newline();
            if had_blank {
                self.insert_blank_line();
            }
            self.flush_comments_before(span_of(item).lo().0);
            print_item(self, item);
            // Each item here is always the last thing on its own line (the
            // next one starts its own fresh `newline()`), so it's safe to
            // check for a trailing comment right after it.
            self.flush_trailing_comment(span_of(item).hi().0);
            prev_hi_line = Some(span_of(item).hi().0);
        }
    }

    /// Prints `items` one per line, one indent level deeper than the current
    /// one, preserving each item's own leading blank line from the source (0
    /// or 1, never more - the same idea as `print_module`'s decl loop, just
    /// at an indented sibling-list site instead of the top level) and
    /// flushing any comment attached before it. Shared by `let`-bindings,
    /// `do`-statements, and `case` branches - anywhere a block prints a
    /// vertical list of sibling items at one indent level.
    fn print_indented_siblings<T>(
        &mut self,
        items: &[T],
        span_of: impl Fn(&T) -> Span,
        print_item: impl FnMut(&mut Self, &T),
    ) {
        self.indent_in();
        self.print_siblings_body(items, span_of, print_item);
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
            Binder::Array(open, items, close) => {
                self.list(
                    "[",
                    "]",
                    *open,
                    *close,
                    true,
                    true,
                    items,
                    |x| x.span(),
                    |p, x| p.print_binder(x),
                );
            }
            Binder::Record(open, fields, close) => {
                self.list(
                    "{",
                    "}",
                    *open,
                    *close,
                    true,
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
                self.print_paren_block(|p| p.print_typ(inner));
            }
            Typ::Arr(a, b) => self.print_typ_arrow_chain(a, b),
            Typ::App(..) => {
                let (head, args) = Self::typ_app_spine(t);
                self.print_typ(head);
                // `Typ::Record`/`Typ::Row` arguments still use the "floor"
                // model unconditionally - they hang glued in place under
                // their own bracket rather than relocating. A `Typ::Paren`
                // arg is different: with no real source break before it but
                // internal breaks of its own, hanging it in place left every
                // sibling argument after it glued onto its closing line
                // instead of moving down with it. So a `Typ::Paren` arg gets
                // the same `would_break` treatment as `Expr::App`'s own
                // spine; `Record`/`Row` don't need it since they already
                // hang correctly on their own.
                self.print_spine_args(
                    head.span(),
                    &args,
                    |a| a.span(),
                    |p, a| p.typ_paren_would_break(a),
                    |p, a| p.print_typ(a),
                );
            }
            Typ::Op(..) => {
                let (first, rest) = Self::typ_op_spine(t);
                let mut spans = vec![first.span()];
                spans.extend(rest.iter().map(|(_, r)| r.span()));
                let multiline = self.in_broken_sig
                    || Self::any_breaks(&spans)
                    || rest.iter().any(|(_, r)| self.typ_paren_would_break(r));
                self.print_typ(first);
                // `in_broken_sig` means this chain is itself the flattened
                // continuation of a signature/alias's own `::`/`=` break (see
                // `print_typ_arrow_chain`/`print_typ_constrained_chain`), which
                // already established the right column - adding a level here
                // would push every operator deeper than the sibling `->`/`=>`
                // lines it lines up with. Anywhere else (e.g. glued right after
                // a `Typ::Paren`'s `( `, which resets `in_broken_sig` - see
                // `print_paren_block`), there's no such column already
                // accounted for, so the chain needs its own hang, the same way
                // a value's operator chain (`Expr::Op`) always does - otherwise
                // its continuation lands flush with the first operand instead
                // of one level past the bracket it's glued to.
                let own_hang = multiline && !self.in_broken_sig;
                if own_hang {
                    self.indent_in();
                }
                for (op, r) in &rest {
                    if multiline {
                        self.newline();
                        self.lit(*op);
                        self.raw(" ");
                    } else {
                        self.raw(" ");
                        self.lit(*op);
                        self.raw(" ");
                    }
                    self.print_typ(r);
                }
                if own_hang {
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
                    // The leading space aligns `.` (1 char) under `::`/`=>` (2 chars),
                    // matching purs-tidy's continuation-token alignment.
                    self.raw(" . ");
                    self.print_typ(t);
                } else {
                    let multiline =
                        vars.last().is_some_and(|v0| Self::breaks_before(v0.span(), t.span()));
                    if multiline {
                        self.indent_in();
                        self.newline();
                        self.raw(" . ");
                        self.print_typ(t);
                        self.indent_out();
                    } else {
                        self.raw(". ");
                        self.print_typ(t);
                    }
                }
            }
            Typ::Record(row) => {
                self.print_row("{", "}", row.1.hi().0, true, &row.0);
            }
            Typ::Row(row) => {
                self.print_row("(", ")", row.1.hi().0, false, &row.0);
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
        // Unconditional hang, same reasoning as `print_record_field_rhs`: a
        // constraint's args are glued directly after its name, which is in
        // turn glued after a fixed-width raw token (`. `, `=> `) whose own
        // width the indent baseline has no memory of - so if the args
        // break, they need to hang under `name`'s own real column (captured
        // here, before printing it, then handed to `print_spine_args` via
        // `with_indent_at` so *its* own break-handling adds one level on top
        // of that, not of the stale ambient), or the resulting block looks
        // shallower than the constraint's own name, not just less indented.
        let name_col = self.current_column();
        self.lit(name);
        self.with_indent_at(name_col, |p| {
            // See the matching note on `Typ::App` - a `Typ::Paren` arg that
            // would itself break relocates it and every arg after it, same
            // as `Expr::App`; `Record`/`Row` args keep hanging in place.
            p.print_spine_args(
                name.span(),
                args,
                |a| a.span(),
                |p, a| p.typ_paren_would_break(a),
                |p, a| p.print_typ(a),
            );
        });
    }

    /// Prints `t`, hung under its own real column first when `t` is a
    /// nesting shape (`App`/`Record`/`Row`) - mirrors `print_sig_typ`'s own
    /// `needs_hang` check, for the same reason: whatever glues directly in
    /// front of `t` here (an arrow chain's `-> `, a constrained chain's
    /// closing `=> `) is a fixed-width raw token the indent baseline has no
    /// memory of, so if `t` itself breaks, it needs to hang under `t`'s own
    /// column (`hang_glued`) or it lands shallower than that very token.
    /// Never applied to `Arr`/`Op`/`Constrained`/`Forall` - those decide
    /// their own indent independently, and hanging here would wrongly push
    /// every nested `->`/`=>`/operator continuation a level deeper.
    fn print_typ_glued(&mut self, t: &Typ) {
        let needs_hang = matches!(t, Typ::App(..) | Typ::Record(..) | Typ::Row(..));
        if needs_hang {
            self.hang_glued(|p| p.print_typ(t));
        } else {
            self.print_typ(t);
        }
    }

    /// `a -> b -> c -> ...` is parsed as a right-nested chain of `Typ::Arr`. Flatten
    /// it so the whole chain makes one multiline decision instead of one independent
    /// decision per `Arr` node. Unlike a value's operator chains (see `op_spine`), a
    /// broken type-operator chain never gets its own extra indent level - each `->`
    /// prints at whatever indent was already active (a bare `newline()`, no
    /// `indent_in`), the same way `Typ::Op` does; only a non-operator break (a
    /// `Typ::App` argument moving to its own line, a `Typ::Paren` block) increases
    /// indent - via `print_typ_glued`, since each segment is glued directly after
    /// `-> ` (or, for the first segment, `:: `/`= `).
    fn print_typ_arrow_chain(&mut self, a: &Typ, b: &Typ) {
        let mut segments = vec![a];
        let mut rest = b;
        while let Typ::Arr(x, y) = rest {
            segments.push(x);
            rest = y;
        }
        segments.push(rest);

        let segment_spans: Vec<Span> = segments.iter().map(|s| s.span()).collect();
        let multiline = self.in_broken_sig
            || Self::any_breaks(&segment_spans)
            || segments[1..].iter().any(|s| self.typ_paren_would_break(s));
        self.print_typ_glued(segments[0]);
        for seg in &segments[1..] {
            if multiline {
                self.newline();
                self.raw("-> ");
            } else {
                self.raw(" -> ");
            }
            self.print_typ_glued(seg);
        }
    }

    /// `C1 => C2 => ... => Body` (including the desugared form of a parenthesized,
    /// comma-separated constraint list) is a right-nested chain of `Typ::Constrained`.
    /// Flattened the same way as `print_typ_arrow_chain`, for the same reason - no
    /// extra indent for the `=>` breaks either.
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
        let multiline = self.in_broken_sig
            || Self::any_breaks(&chain_spans)
            || self.typ_paren_would_break(body);
        self.print_constraint(constraints[0]);
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
        self.print_typ_glued(body);
    }

    /// Prints a record/row type's `open field, field | tail close` (or the
    /// leading-comma multiline block style, when the source had one), mirroring
    /// `list()`'s architecture - a real multiline decision via `any_breaks`, own
    /// bracket placement (so it can relocate to a fresh line the same way
    /// `list()` does), and per-field `flush_comments_before`/
    /// `flush_trailing_comment` - rather than `list()` itself, since a row's
    /// optional `| tail` doesn't fit `list()`'s "comma-separated items only"
    /// shape. `close_line` is the closing bracket's own line (from the row's
    /// overall `S<Row>` span's `hi()` - reliable now that the `Typ::Row` parser
    /// arm captures it *before* consuming `)`, not after).
    fn print_row(&mut self, open: &str, close: &str, close_line: usize, pad: bool, row: &Row) {
        let Row(fields, tail) = row;
        if fields.is_empty() && tail.is_none() {
            self.raw(open);
            self.flush_comments_before(close_line);
            self.raw(close);
            return;
        }
        // A record's braces are their own bracketed context, unrelated to whatever
        // signature this row happens to be nested inside - a field's own type (e.g.
        // a forall) shouldn't inherit an enclosing broken-signature's flattening.
        let outer_in_broken_sig = self.in_broken_sig;
        self.in_broken_sig = false;

        let mut spans: Vec<Span> = fields.iter().map(|(l, t)| l.span().merge(t.span())).collect();
        if let Some(t) = tail {
            spans.push(t.span());
        }
        let multiline = Self::any_breaks(&spans);

        if !multiline {
            self.raw(open);
            if pad {
                self.raw(" ");
            }
            for (i, (label, typ)) in fields.iter().enumerate() {
                self.flush_comments_before(label.span().lo().0);
                if i > 0 {
                    self.raw(", ");
                }
                self.lit(label);
                self.print_field_typ(label.span(), typ);
            }
            if let Some(tail) = tail {
                if !fields.is_empty() {
                    self.raw(" ");
                }
                self.flush_comments_before(tail.span().lo().0);
                self.raw("| ");
                self.print_typ(tail);
            }
            self.flush_comments_before(close_line);
            if pad {
                self.raw(" ");
            }
            self.raw(close);
        } else {
            // See `list()`'s own version of this for why: hang every line
            // after `open` from the column it's about to print at, rather
            // than relocating `open` itself to a deeper line when something
            // (an arrow's `-> `, a class name, ...) is already glued onto
            // this line ahead of it.
            let saved_indent = self.indent;
            self.indent = self.current_column();
            self.raw(open);
            self.raw(" ");
            for (i, (label, typ)) in fields.iter().enumerate() {
                if i > 0 {
                    self.newline();
                }
                // Flush before the leading comma, not after - see `list()`.
                self.flush_comments_before(label.span().lo().0);
                if i > 0 {
                    self.raw(", ");
                }
                self.lit(label);
                self.print_field_typ(label.span(), typ);
                self.flush_trailing_comment(typ.span().hi().0);
            }
            if let Some(tail) = tail {
                self.newline();
                self.flush_comments_before(tail.span().lo().0);
                self.raw("| ");
                self.print_typ(tail);
                self.flush_trailing_comment(tail.span().hi().0);
            }
            // Catches a comment on its own separate line, still before the
            // close - see `list()`.
            self.flush_comments_before(close_line);
            self.newline();
            self.raw(close);
            self.indent = saved_indent;
        }

        self.in_broken_sig = outer_in_broken_sig;
    }

    // -- expressions -------------------------------------------------------

    fn print_expr(&mut self, e: &Expr) {
        // Every other place a comment can precede something in the source
        // flushes it explicitly before printing that thing (list items, case
        // branches, do-statements, let bindings, ...) - but there's no single
        // sibling-loop for "the expression that follows some keyword"
        // (`in` before a `let`'s body, `=`/`->` before a guarded clause's
        // RHS, ...), so each of those call sites would need its own flush
        // call, and it's easy to miss one (a `let`'s body was missing exactly
        // this - a comment right before it silently rode along to whatever
        // flush point came next, appearing somewhere unrelated). Flushing
        // here instead, unconditionally, covers every call site at once:
        // redundant (a no-op) wherever a comment before `e` was already
        // flushed by an outer loop, and otherwise catches what those loops
        // don't cover.
        self.flush_comments_before(e.span().lo().0);
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
                self.print_paren_block(|p| p.print_expr(inner));
            }
            Expr::Negate(inner) => {
                self.raw("-");
                self.print_expr(inner);
            }
            Expr::Typed(inner, t) => {
                // Same `name :: Typ` convention as every other signature site
                // (`print_sig_typ`'s 9 other call sites) - `::` relocates
                // onto its own line when there's a source break or `t` would
                // break, instead of always gluing `t` flat after `inner`.
                self.print_expr(inner);
                self.print_sig_typ(inner.span(), t);
            }
            Expr::App(..) => {
                let (head, args) = Self::app_spine(e);
                // Relocate the whole call - head included - onto its own
                // indented line whenever it's glued right after something
                // and is itself going to print across multiple lines, the
                // same concern `list()`'s own `own_indent` decides for a
                // glued `Array`/`Record`. Without this, only the argument
                // that actually breaks moves (via `print_app_args` below) -
                // the head, and any args before it, stay flush on the call's
                // original line.
                //
                // Decided by trying to print flat directly in the real
                // output first (head glued, `own_indent` never applied), and
                // rolling the whole attempt back to redo with the head
                // relocated only if it doesn't fit - same "try first, only
                // roll back on failure" trick as `list()`, and for the same
                // reason: probing every argument into a scratch buffer up
                // front is `O(2^depth)` once an argument can itself be a
                // call needing the same decision. Whether an individual
                // argument itself needs to break is decided the same way,
                // one level down, inside `print_app_args`.
                let could_relocate =
                    !self.at_fresh_line() && self.glued_floor != Some(self.out.len());
                let mut boundary_spans = vec![head.span()];
                boundary_spans.extend(args.iter().map(|a| a.span()));
                let breaks_from_source = Self::any_breaks(&boundary_spans);
                if !(could_relocate && breaks_from_source) {
                    let mark = self.out.len();
                    let comment_idx_before = self.comment_idx;
                    self.print_expr(head);
                    self.print_app_args(head.span(), &args);
                    if !self.out[mark..].contains('\n') || !could_relocate {
                        return;
                    }
                    self.out.truncate(mark);
                    self.comment_idx = comment_idx_before;
                }
                // Reached because the source already had a break somewhere
                // in this call, or because the flat attempt above didn't
                // fit and relocating the head could help.
                self.indent_in();
                self.newline();
                self.print_expr(head);
                self.print_app_args(head.span(), &args);
                self.indent_out();
            }
            Expr::Vta(f, t) => {
                self.print_expr(f);
                // Same shape as `print_sig_typ`/`print_typ_alias_rhs`: `@` is a
                // fixed-width raw token glued directly onto `f`'s own line, so if
                // `t` is going to break (a `Row`/`Record` visible type application
                // is the common case), hanging it under `@`'s own column instead
                // of relocating to a fresh indented line would inherit however
                // deep `f` already sits - e.g. as an `App` argument several
                // levels in - and blow the whole type out to the right instead of
                // a stable, shallow indent.
                if Self::breaks_before(f.span(), t.span()) || self.typ_would_break(t) {
                    self.indent_in();
                    self.newline();
                    self.raw("@");
                    self.print_typ_glued(t);
                    self.indent_out();
                } else {
                    self.raw(" @");
                    self.print_typ(t);
                }
            }
            Expr::Op(..) => {
                let (first, rest) = Self::op_spine(e);
                self.print_expr(first);
                // Same "glue until the first operand that actually needs to
                // break, then break from there onward" rule
                // `print_spine_args` already applies to `Expr::App`'s own
                // arguments - operators before the first forced break stay
                // glued flat on `first`'s own line; once one operand either
                // has a real source break before it or would print across
                // multiple lines on its own, that operand's operator (and
                // every operator after it) moves onto its own line at one
                // shared indent level, entered once on the first break, not
                // per operator - so a same-precedence run of operators lines
                // up flush instead of staircasing.
                //
                // "Would print across multiple lines on its own" is decided
                // by *trying* each operand glued flat directly in the real
                // output (mark the position, print it, check afterward for a
                // `'\n'`), not by rendering every operand into a throwaway
                // scratch buffer up front - the same "try first, roll back
                // only on failure" trick `list()` uses, for the same reason:
                // probing every operand separately and then re-printing all
                // of them for real the moment even one doesn't fit is
                // `O(2^depth)` in AST nesting depth instead of `O(depth)`.
                // Rolling back only the one operand whose attempt failed
                // means an operand that already committed flat is never
                // re-rendered.
                let mut prev_span = first.span();
                let mut broke = false;
                for (op, r) in &rest {
                    let cur_span = r.span();
                    // A comment can trail `prev_span`'s own line (`x # f --
                    // like this\n  <#> g`) - previously left pending for
                    // whatever printed next to pick up, and the next thing is
                    // always `print_expr(r)`, whose own unconditional
                    // `flush_comments_before` at entry has no way to tell
                    // "this comment trails the *previous* operand" from
                    // "this comment leads *this* operand", so it silently
                    // misattached as a leading comment on `r` instead,
                    // prying it away from the operator it trails. Only safe
                    // to claim it here, once `breaks_before` has confirmed
                    // `prev_span` really is the last thing on its own source
                    // line - checking any earlier (e.g. right after `first`,
                    // before even trying to glue `op r` after it) can't tell
                    // "trails `prev_span`" apart from "trails whatever *else*
                    // still shares this same physical line", the same
                    // ambiguity `trailing_comment_does_not_attach_to_an_earlier_token_on_the_same_line`
                    // already covers for a flat multi-token expression.
                    let mut just_flushed_comment = false;
                    if !broke && Self::breaks_before(prev_span, cur_span) {
                        self.indent_in();
                        broke = true;
                        just_flushed_comment = self.flush_trailing_comment(prev_span.hi().0);
                    }
                    if !broke {
                        let mark = self.out.len();
                        let comment_idx_before = self.comment_idx;
                        self.raw(" ");
                        self.lit(*op);
                        self.raw(" ");
                        // Glued directly after `op ` - suppress a nested
                        // `own_indent`-style relocation (most commonly
                        // `Expr::App`'s, when the operand is a call whose
                        // own argument breaks) the same way the broken path
                        // below does, so a self-relocating operand doesn't
                        // spuriously fail this flat attempt.
                        let prev_glued_floor = self.glued_floor;
                        self.glued_floor = Some(self.out.len());
                        // Hung under the operand's own real column (`op `'s
                        // width included), not a plain `indent_in()` off the
                        // chain's stale ambient level - `op ` is a
                        // fixed-width glued prefix the ambient baseline has
                        // no memory of, the same reasoning as
                        // `print_sig_typ`/`print_constraint`'s own
                        // `hang_glued` calls (see its doc comment). A plain
                        // ambient bump can land short of the operator's own
                        // column whenever `op `'s width isn't an exact
                        // multiple of `INDENT`, letting the operand's own
                        // break (an `App` call, a `case`) print "behind" the
                        // operator instead of past it - invisible when the
                        // operand prints flat.
                        self.hang_glued(|p| p.print_expr(r));
                        self.glued_floor = prev_glued_floor;
                        if !self.out[mark..].contains('\n') {
                            prev_span = cur_span;
                            continue;
                        }
                        self.out.truncate(mark);
                        self.comment_idx = comment_idx_before;
                        self.indent_in();
                        broke = true;
                        just_flushed_comment = self.flush_trailing_comment(prev_span.hi().0);
                    }
                    // A comment on its own line right before the operator
                    // (`x\n  -- comment\n  <#> y`) is a leading comment for
                    // this `op r` unit, not for `r` alone - claim it here,
                    // before `op` prints, so it lands above the operator
                    // instead of `print_expr(r)`'s own unconditional
                    // `flush_comments_before` claiming it as a leading
                    // comment on `r`, which would force `r` onto its own
                    // line under the comment even though nothing about `r`
                    // itself needed to break. A no-op when the comment was
                    // already claimed above as trailing `prev_span`'s line.
                    self.flush_comments_before(cur_span.lo().0);
                    // `flush_trailing_comment`/`flush_comments_before` above
                    // already ended the line itself (and, since `indent_in()`
                    // ran above, at the new broken indent) - an explicit
                    // `newline()` here too would leave a blank line behind it.
                    if !just_flushed_comment {
                        self.newline();
                    }
                    self.lit(*op);
                    self.raw(" ");
                    let prev_glued_floor = self.glued_floor;
                    self.glued_floor = Some(self.out.len());
                    self.hang_glued(|p| p.print_expr(r));
                    self.glued_floor = prev_glued_floor;
                    prev_span = cur_span;
                    // Only reachable once `prev_span` (now `r`) is confirmed
                    // the last thing on its own line - either the chain just
                    // broke onto its own line above, or it was already
                    // broken from an earlier iteration - so a comment
                    // pending on `cur_span`'s own line unambiguously trails
                    // it, not some later operand still to come on the same
                    // physical line the way `first`/a still-flat `r` could.
                    self.flush_trailing_comment(cur_span.hi().0);
                }
                if broke {
                    self.indent_out();
                }
            }
            Expr::Access(inner, labels) => {
                self.print_expr(inner);
                for l in labels {
                    self.raw(".");
                    self.lit(l);
                }
            }
            Expr::Array(open, items, close) => {
                self.list(
                    "[",
                    "]",
                    *open,
                    *close,
                    true,
                    true,
                    items,
                    |x| x.span(),
                    |p, x| p.print_expr(x),
                );
            }
            Expr::Record(open, fields, close) => {
                self.list(
                    "{",
                    "}",
                    *open,
                    *close,
                    true,
                    false,
                    fields,
                    |x| x.span(),
                    |p, x| p.print_record_label_expr(x),
                );
            }
            Expr::Lambda(lam, binders, body) => {
                self.raw("\\");
                // The first binder stays glued directly after `\` with no
                // space (unlike a name's binders, which always get a leading
                // space) - matches this printer's usual "a glued bracket
                // hangs in place, it never relocates" floor model, so only
                // binders *after* the first go through `print_spine_args`.
                if let Some((first, rest)) = binders.split_first() {
                    self.print_binder(first);
                    self.print_spine_args(
                        first.span(),
                        rest,
                        |b| b.span(),
                        |p, b| p.binder_would_break(b),
                        |p, b| p.print_binder(b),
                    );
                }
                let before_body = binders.last().map_or(*lam, |b| b.span());
                self.print_arrow_rhs(before_body, " -> ", body);
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
            Expr::Update(target, open, updates, close) => {
                self.print_expr(target);
                // Record update binds tighter than application - `target {
                // ... }` is one atom, so `App`'s own spine-arg breaking
                // (`print_app_args`) only ever sees this whole node's span,
                // never the gap between `target` and `{` inside it. A
                // source break there (`f x\n  { y = z }`) was silently
                // dropped, re-gluing onto `f x { y = z }` on every reformat
                // - this is the one place that gap can be represented at
                // all, so it has to be checked here, not left to the
                // caller.
                let broke = Self::breaks_before(target.span(), *open);
                if broke {
                    self.indent_in();
                    self.newline();
                } else {
                    self.raw(" ");
                }
                self.list(
                    "{",
                    "}",
                    *open,
                    *close,
                    true,
                    false,
                    updates,
                    |x| x.span(),
                    |p, x| p.print_record_update(x),
                );
                if broke {
                    self.indent_out();
                }
            }
            Expr::Do(qual, _, stmts) => {
                if let Some(q) = qual {
                    self.print_qual(q);
                }
                self.raw("do");
                self.print_indented_siblings(stmts, |s| s.span(), |p, s| p.print_do_stmt(s));
            }
            Expr::Ado(qual, kw, stmts, result) => {
                if let Some(q) = qual {
                    self.print_qual(q);
                }
                self.raw("ado");
                // A 0-or-1-statement `ado` glued flat on one source line in
                // the original (`ado in x`, `ado x <- pure 1 in x`) stays
                // flat here too, the same "single simple binding stays glued"
                // convention `print_let_kw_bindings` applies to `let`.
                // Stricter than that convention though (no tolerance for a
                // one-line gap): unlike `let ... in`, an `ado` with no
                // statements has nothing else to visually anchor `in` to, so
                // any real source break here instead falls through to the
                // block form below and lets `ado_would_break` relocate the
                // whole thing (see its own doc comment).
                let flat = match stmts.as_slice() {
                    [] => !Self::breaks_before(*kw, result.span()),
                    [only] => {
                        !Self::breaks_before(*kw, only.span())
                            && !self.do_stmt_would_break(only)
                            && !Self::breaks_before(only.span(), result.span())
                    }
                    _ => false,
                } && !self.expr_would_break(result);
                if flat {
                    self.raw(" ");
                    if let [only] = stmts.as_slice() {
                        self.print_do_stmt(only);
                        self.raw(" ");
                    }
                    self.raw("in ");
                    self.print_expr(result);
                } else {
                    self.indent_in();
                    self.print_siblings_body(stmts, |s| s.span(), |p, s| p.print_do_stmt(s));
                    self.newline();
                    self.raw("in ");
                    self.print_expr(result);
                    self.indent_out();
                }
            }
            Expr::Let(kw, bindings, body) => {
                self.raw("let");
                let glued = self.print_let_kw_bindings(*kw, bindings);
                // A glued single binding (`let x = 1`) stays on one line
                // with `in` too - only a bindings block that actually broke
                // onto its own indented lines needs `in` pushed onto a fresh
                // line below it.
                if glued {
                    self.raw(" ");
                } else {
                    self.newline();
                }
                self.raw("in");
                // There's no separate span for the `in` keyword itself (the parser
                // doesn't capture one), but it always sits on the line right after
                // the last binding's own last line - so a gap of exactly one line
                // means body shares `in`'s line (`in x`); a gap of two or more
                // means `in` had a line of its own and body breaks onto another.
                let multiline = self.paren_would_break(body)
                    || bindings.last().is_some_and(|b| body.span().lo().0 > b.span().hi().0 + 1);
                if multiline {
                    self.newline();
                } else {
                    self.raw(" ");
                }
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
            Expr::Case(kw, scrutinees, branches) => {
                self.raw("case");
                // Same "glued prefix in front of something that would break"
                // relocation every other fixed-width keyword/operator prefix
                // in this printer gets (see `print_arrow_rhs`, `print_sig_typ`) -
                // a source break before the first scrutinee, between two
                // scrutinees, or a scrutinee that's itself going to print
                // multi-line (an `Op` chain, say) all move the *whole*
                // scrutinee list onto its own indented line rather than
                // leaving `of` looking glued to wherever the last scrutinee's
                // own printing happened to end up.
                let mut spans = vec![*kw];
                spans.extend(scrutinees.iter().map(|s| s.span()));
                let multiline =
                    Self::any_breaks(&spans) || scrutinees.iter().any(|s| self.expr_would_break(s));
                if multiline {
                    self.indent_in();
                    for (i, s) in scrutinees.iter().enumerate() {
                        self.newline();
                        if i > 0 {
                            self.raw(", ");
                        }
                        self.print_expr(s);
                    }
                    self.newline();
                    self.raw("of");
                    self.indent_out();
                } else {
                    self.raw(" ");
                    for (i, s) in scrutinees.iter().enumerate() {
                        if i > 0 {
                            self.raw(", ");
                        }
                        self.print_expr(s);
                    }
                    self.raw(" of");
                }
                self.print_indented_siblings(branches, |b| b.span(), |p, b| p.print_case_branch(b));
            }

            Expr::Error(_) => self.raw_fallback(e),
        }
    }

    fn print_do_stmt(&mut self, s: &DoStmt) {
        match s {
            // No explicit trailing-comment check needed on either arm here -
            // `print_siblings_body` (the only caller, for both `do` and
            // `ado`) already checks after each statement using its own span.
            DoStmt::Stmt(None, e) => self.print_expr(e),
            DoStmt::Stmt(Some(b), e) => {
                self.print_binder(b);
                self.print_arrow_rhs(b.span(), " <- ", e);
            }
            DoStmt::Let(kw, bindings) => {
                self.raw("let");
                self.print_let_kw_bindings(*kw, bindings);
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
        let before = binders.last().unwrap().span();
        self.print_guarded_expr(before, ge, " -> ");
    }

    fn print_record_update(&mut self, u: &RecordUpdate) {
        match u {
            RecordUpdate::Leaf(l, e) => {
                self.lit(l);
                self.print_record_field_rhs(l.span(), " = ", e);
            }
            RecordUpdate::Branch(l, updates) => {
                self.lit(l);
                self.raw(" ");
                self.list(
                    "{",
                    "}",
                    Span::zero(),
                    Span::zero(),
                    true,
                    false,
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
                self.print_record_field_rhs(l.span(), ": ", e);
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
    fn paren_operand_of_an_op_chain_closes_under_its_own_open_paren() {
        // A `Paren` operand glued directly after an operator (`<#> ( ... )`)
        // that itself prints multi-line must close under its own `(`, not
        // one level short of it - `(` sits past the operator's own width,
        // which the ambient indent baseline has no memory of. See
        // `print_paren_block`.
        let src = "module M where\n\nx =\n  y\n    <#> ( \\cred ->\n            [ Foo.Bar cur cred ]\n        )\n";
        let out = fmt(src);
        assert_eq!(
            out,
            "module M where\n\nx =\n  y\n    <#> ( \\cred ->\n            [ Foo.Bar cur cred ]\n        )\n"
        );
        assert_idempotent(src);
    }

    #[test]
    fn array_operand_of_an_op_chain_closes_under_its_own_open_bracket() {
        // Same bug as the `Paren` case above, in `list()`'s glued (not
        // `own_indent`) branch: a bracketed operand glued after an operator
        // had its continuation `,`/closing `]` hang off the ambient indent
        // instead of `[`'s own real column.
        let src = "module M where\n\nx =\n  y\n    <#> [ credA\n        , credB\n        , credC\n        ]\n";
        let out = fmt(src);
        assert_eq!(
            out,
            "module M where\n\nx =\n  y\n    <#> [ credA\n        , credB\n        , credC\n        ]\n"
        );
        assert_idempotent(src);
    }

    #[test]
    fn nested_paren_inside_a_glued_paren_anchors_to_the_right_column() {
        // Root cause behind the two tests above: `current_column()` read a
        // freshly swapped-in scratch buffer (used to decide a `Paren`'s own
        // flat-vs-block layout) as column 0 regardless of `self.indent`,
        // since nothing had been physically written into it yet. A `Paren`
        // immediately inside another glued `Paren` then anchored its own
        // `open_col` at 0 instead of its real column, corrupting every line
        // under it into invalid layout.
        let src = "module M where\n\nx =\n  y\n    # f\n        ( ( case _ of\n              A -> 1\n              B -> 2\n          )\n            >>> g\n        )\n";
        let out = fmt(src);
        assert_idempotent(&out);
        let (toks, comments) = lexer::lex(&out, Fi(0));
        let names = DashMap::new();
        let mut p = parser::P::new(&toks, &names);
        let m = parser::module(&mut p).expect("formatted output should still parse");
        assert!(p.errors.is_empty(), "parse errors: {:?}", p.errors);
        let _ = (m, comments);
    }

    #[test]
    fn vta_row_type_breaks_to_a_fresh_line_instead_of_hanging_off_a_deep_column() {
        let src = "module M where\n\nx =\n    ( foo\n        @( aaa :: _\n        , bbb :: _\n        , ccc :: _\n        )\n    )\n";
        let out = fmt(src);
        assert_eq!(
            out,
            "module M where\n\nx =\n  ( foo\n      @( aaa :: _\n       , bbb :: _\n       , ccc :: _\n       )\n  )\n"
        );
        assert_idempotent(src);
    }

    #[test]
    fn simple_module() {
        let src = "module Foo (foo) where\n\nfoo = 1\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo (foo) where\n\nfoo = 1\n");
        assert_idempotent(src);
    }

    #[test]
    fn export_list_always_gets_a_blank_line_before_what_follows() {
        // No blank in the source at all before the import - one is still forced
        // in. The import-to-decl boundary is untouched by this fix and keeps
        // preserving 0-or-1 from the source (see `imports_and_multiple_decls`) -
        // no blank here since the source didn't have one.
        let src = "module Foo (foo) where\nimport Prelude\nfoo = 1\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo (foo) where\n\nimport Prelude\nfoo = 1\n");
        assert_idempotent(src);
    }

    #[test]
    fn export_list_forces_a_blank_line_before_a_decl_when_there_are_no_imports() {
        let src = "module Foo (foo) where\nfoo = 1\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo (foo) where\n\nfoo = 1\n");
        assert_idempotent(src);
    }

    #[test]
    fn no_export_list_does_not_force_a_blank_line() {
        // Unchanged behavior when there's no export list to begin with - this
        // boundary just preserves whatever the source had (see `next_visible_line`
        // based decl/let-binding blank-line preservation elsewhere).
        let src = "module Foo where\nfoo = 1\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\nfoo = 1\n");
        assert_idempotent(src);
    }

    #[test]
    fn paren_expands_when_source_has_a_newline_inside() {
        // `=` breaks too, even though the source had it glued - otherwise the
        // closing `)` would visually "move back" to `foo`'s own column, past
        // where `(` started (see `paren_would_break`/`print_arrow_rhs`).
        let src = "module Foo where\n\nfoo = (1 +\n  2)\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\nfoo =\n  ( 1\n      + 2\n  )\n");
        assert_idempotent(src);
    }

    #[test]
    fn paren_after_arrow_breaks_the_arrow_first_instead_of_moving_back() {
        // The same fix, but for `->` (a lambda body) instead of `=`.
        let src = "module Foo where\n\nfoo = map (\\x -> (x +\n  1)) xs\n";
        let out = fmt(src);
        assert_eq!(
            out,
            "module Foo where\n\nfoo =\n  map\n    ( \\x ->\n        ( x\n            + 1\n        )\n    )\n    xs\n"
        );
        assert_idempotent(src);
    }

    #[test]
    fn paren_stays_flat_when_source_is_flat() {
        let src = "module Foo where\n\nfoo = (1 + 2)\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\nfoo = (1 + 2)\n");
        assert_idempotent(src);
    }

    #[test]
    fn imports_and_multiple_decls() {
        let src = "module Foo where\n\nimport Prelude\nimport Data.Array (head, tail)\n\nfoo = 1\nbar = 2\n";
        let out = fmt(src);
        assert_eq!(
            out,
            "module Foo where\nimport Prelude\n\nimport Data.Array (head, tail)\n\nfoo = 1\nbar = 2\n"
        );
        assert_idempotent(src);
    }

    #[test]
    fn array_stays_flat_when_source_is_flat() {
        let src = "module Foo where\n\nfoo = [1, 2, 3]\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\nfoo = [ 1, 2, 3 ]\n");
        assert_idempotent(src);
    }

    #[test]
    fn array_expands_when_source_has_a_newline_inside() {
        let src = "module Foo where\n\nfoo = [1,\n  2, 3]\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\nfoo =\n  [ 1\n  , 2\n  , 3\n  ]\n");
        assert_idempotent(src);
    }

    /// Regression test: an empty array with a source newline between its
    /// brackets is a multiline array too, even with no items to carry the
    /// break - `list()`'s empty-items fast path used to ignore this
    /// entirely and always collapse to `[]`.
    #[test]
    fn empty_array_with_a_newline_between_the_brackets_stays_expanded() {
        let src = "module Foo where\n\nfoo = [\n]\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\nfoo =\n  [\n  ]\n");
        assert_idempotent(src);
    }

    /// Regression test: an item with no source break around it can still be
    /// going to print across multiple lines all on its own (here, `c d`'s
    /// own `App` spine breaks) - that alone should switch the whole array to
    /// the expanded style, the same as a source break between items would,
    /// instead of leaving the array looking flat with an item randomly
    /// breaking mid-line.
    #[test]
    fn array_item_that_would_break_on_its_own_expands_the_whole_array() {
        // `c` stays glued to the list's own leading comma (it's already
        // glued right after `, `, so `Expr::App`'s `own_indent` must not
        // double-relocate on top of that); only `d`, which genuinely breaks
        // from `c` in the source, drops to its own line.
        let src = "module Foo where\n\nfoo = [a b, c\n d]\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\nfoo =\n  [ a b\n  , c\n      d\n  ]\n");
        assert_idempotent(src);
    }

    #[test]
    fn app_stays_flat_when_source_is_flat() {
        let src = "module Foo where\n\nfoo = bar baz qux\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\nfoo = bar baz qux\n");
        assert_idempotent(src);
    }

    #[test]
    fn app_expands_one_arg_per_line_when_source_has_a_newline_between_args() {
        let src = "module Foo where\n\nfoo = bar\n  baz\n  qux\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\nfoo =\n  bar\n    baz\n    qux\n");
        assert_idempotent(src);
    }

    /// Regression test: a call glued right after `=` that ends up printing
    /// across multiple lines relocates entirely - head included - onto its
    /// own indented line, the same way `list()`'s `own_indent` already does
    /// for a glued `Array`/`Record` (`Expr::App` previously left its head
    /// flush glued to `=`/whatever precedes it, only pushing the arguments
    /// after the break onto their own line via `print_spine_args`'s
    /// existing "once broken, stay broken" rule).
    #[test]
    fn app_only_pushes_args_after_the_first_break_onto_their_own_line() {
        let src = "module Foo where\n\nfoo = a b\n  c d\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\nfoo =\n  a b\n    c\n    d\n");
        assert_idempotent(src);
    }

    /// Regression test: an argument that's itself going to print across
    /// multiple lines (here, a `Paren` wrapping a call that breaks) forces
    /// the same relocation as a real source break would, even with no
    /// source break of its own before it - `foo`'s own head/call was
    /// previously left glued flat in this case, only breaking *inside* the
    /// paren, which made the paren's closing `)` and the following argument
    /// look like they never left the call's own line.
    #[test]
    fn app_arg_that_would_break_pushes_itself_and_later_args_onto_their_own_line() {
        let src = "module Foo where\n\nfoo = a (b\nc) d\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\nfoo =\n  a\n    ( b\n        c\n    )\n    d\n");
        assert_idempotent(src);
    }

    /// Same fix as the previous test, but for a `Record` argument rather
    /// than a `Paren` one - `expr_would_break` (unlike `paren_would_break`)
    /// is deliberately not restricted to any one node shape, since any kind
    /// of glued argument can print across multiple lines on its own.
    #[test]
    fn app_record_arg_that_would_break_pushes_itself_and_later_args_onto_their_own_line() {
        let src = "module Foo where\n\nfoo = a { x: 1\n, y: 2 } d\n";
        let out = fmt(src);
        assert_eq!(
            out,
            "module Foo where\n\nfoo =\n  a\n    { x: 1\n    , y: 2\n    }\n    d\n"
        );
        assert_idempotent(src);
    }

    /// A call whose first argument stays glued (`x {}` - a single
    /// `Expr::Update` node with zero updates, not a separate `App` argument)
    /// followed by one that breaks (`[\na\n]`) needs the *whole* call to
    /// relocate, not just the argument that broke.
    #[test]
    fn app_relocates_when_a_later_glued_argument_would_break() {
        let src = "module Foo where\n\na = x {} [\na\n]\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\na =\n  x {}\n    [ a\n    ]\n");
        assert_idempotent(src);
    }

    /// A function definition's binders use `print_spine_args` too, so a
    /// binder that would itself break (a record pattern with several fields)
    /// pushes later binders onto their own line rather than leaving them
    /// glued onto the record's own closing `}` line. Same fix applies to
    /// `Decl::Def`, `InstBinding::Def`, `LetBinding::Name`, and
    /// `Expr::Lambda`.
    #[test]
    fn decl_def_binder_that_would_break_pushes_itself_and_later_binders_onto_their_own_line() {
        let src = "module M where\n\nf x@\n  { a\n  , b\n  }\n  y = 1\n";
        let out = fmt(src);
        assert_eq!(out, "module M where\n\nf\n  x@\n    { a\n    , b\n    }\n  y = 1\n");
        assert_idempotent(src);
    }

    #[test]
    fn inst_binding_def_binder_that_would_break_pushes_itself_and_later_binders_onto_their_own_line()
     {
        let src =
            "module M where\n\ninstance showFoo :: Show Foo where\n  f x@\n    { a\n    , b\n    }\n    y = 1\n";
        let out = fmt(src);
        assert_eq!(
            out,
            "module M where\n\ninstance Show Foo where\n  f\n    x@\n      { a\n      , b\n      }\n    y = 1\n"
        );
        assert_idempotent(src);
    }

    #[test]
    fn let_binding_name_binder_that_would_break_pushes_itself_and_later_binders_onto_their_own_line()
     {
        let src =
            "module M where\n\nfoo =\n  let\n    f x@\n      { a\n      , b\n      }\n      y = 1\n  in\n    f\n";
        let out = fmt(src);
        assert_eq!(
            out,
            "module M where\n\nfoo =\n  let\n    f\n      x@\n        { a\n        , b\n        }\n      y = 1\n  in\n  f\n"
        );
        assert_idempotent(src);
    }

    /// Same bug and fix as the tests above, but for `Expr::Lambda` - with one
    /// deliberate asymmetry: the *first* binder stays glued directly after
    /// `\` (no space, never relocating) both before and after the fix, since
    /// only binders after the first go through `print_spine_args` (see
    /// `Expr::Lambda`'s own doc comment).
    #[test]
    fn lambda_binder_that_would_break_pushes_later_binders_onto_their_own_line() {
        let src = "module M where\n\nfoo =\n  \\x@\n     { a\n     , b\n     }\n   y -> 1\n";
        let out = fmt(src);
        assert_eq!(
            out,
            "module M where\n\nfoo =\n  \\x@\n    { a\n    , b\n    }\n    y -> 1\n"
        );
        assert_idempotent(src);
    }

    /// Regression test for a bug where `case`/`do` nested inside one argument
    /// of a multiline call printed at whatever indent was active before the
    /// call, instead of inheriting the call's own extra indent - so its
    /// branches ended up no deeper than (or shallower than) sibling call
    /// arguments, looking like they printed "before" the block itself.
    #[test]
    fn case_nested_in_a_multiline_app_arg_indents_past_the_call() {
        let src =
            "module Foo where\n\nfoo = bar\n  (case x of\n    A -> 1\n    B -> 2)\n  qux\n";
        let out = fmt(src);
        assert_eq!(
            out,
            "module Foo where\n\nfoo =\n  bar\n    ( case x of\n        A -> 1\n        B -> 2\n    )\n    qux\n"
        );
        assert_idempotent(src);
    }

    #[test]
    fn case_branches_preserve_a_blank_line_between_groups() {
        let src = "module Foo where\n\nfoo x = case x of\n  A -> 1\n\n  B -> 2\n  C -> 3\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn guarded_clause_comments_stay_attached_to_their_own_clause() {
        // Regression test: `GuardedExpr::Guarded`'s multiline branch used to
        // never flush comments per clause, so every leading comment on every
        // clause silently rode along to whatever flush point came next -
        // dumping them all at the very end of the function instead.
        let src = concat!(
            "module Foo where\n\n",
            "f x\n",
            "  -- first\n",
            "  | a x = 1\n",
            "  -- second\n",
            "  | b x = 2\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn comment_before_a_field_does_not_strand_its_leading_comma() {
        // Regression test: `list()`'s multiline branch used to flush a
        // comment *after* writing the leading `, `, stranding the comma
        // alone on its own line ahead of the comment instead of above it.
        let src = concat!(
            "module Foo where\n\n",
            "foo =\n",
            "  { a: 1\n",
            "  -- comment\n",
            "  , b: 2\n",
            "  }\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn comment_before_a_lets_body_is_not_relocated_past_it() {
        // Regression test: `Expr::Let`'s body was printed via a plain
        // `print_expr` call with no `flush_comments_before` of its own, so a
        // comment right before the body rode along to whatever the body's
        // own printing flushed next - e.g. landing after a `case`'s own
        // first branch's own leading comment instead of before the `case`.
        let src = concat!(
            "module Foo where\n\n",
            "foo = do\n",
            "  let\n",
            "    y = 1\n",
            "  -- comment\n",
            "  case y of\n",
            "    _ -> pure y\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn trailing_comment_stays_on_its_own_line_glued_to_what_it_trails() {
        let src = "module Foo where\n\nfoo = 1 -- trailing\n\nbar = 2\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn trailing_comment_does_not_attach_to_an_earlier_token_on_the_same_line() {
        // Regression test: an earlier version checked "does a pending comment
        // start on this token's own line" for *every* subexpression, which a
        // multi-token flat expression can't distinguish from "trails
        // something later on the same line" - `Tuple a b -- c` would end up
        // as `Tuple -- c a b`, injecting the comment mid-expression.
        let src = "module Foo where\n\nfoo = Tuple a b -- trailing\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn op_chain_trailing_comment_stays_on_the_operand_it_trails() {
        // An `Op` chain must call `flush_trailing_comment` for its own
        // operands too, or a comment trailing one operand's line (`# f arg
        // -- comment`) falls through to the next operand's unconditional
        // `flush_comments_before` and misattaches as a *leading* comment on
        // that next operand, pushing it down onto its own separate line.
        let src = concat!(
            "module Foo where\n\n",
            "foo x =\n",
            "  x\n",
            "    # f arg -- comment\n",
            "    <#> (\\y -> y)\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn op_chain_trailing_comment_on_a_still_flat_operand_does_not_misattach_earlier() {
        // Regression test for a bug introduced while fixing the above: an
        // earlier version of the fix checked for a trailing comment right
        // after the chain's first operand unconditionally, before it was
        // known whether more of the chain still shared that same physical
        // source line - misattaching `a <> b -- comment` as `a -- comment\n
        // <> b` instead. Only safe to claim a trailing comment once a real
        // break confirms the preceding operand truly ends its own line.
        let src = "module Foo where\n\nfoo = a <> b -- comment\n  <> d\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn op_chain_leading_comment_before_an_operator_stays_above_it_instead_of_forcing_the_operand_down() {
        // A comment on its own line right before an operator (`x\n  --
        // comment\n  <#> y`) belongs to the `op y` unit as a whole, not to
        // `y` alone. `print_expr(y)`'s own unconditional
        // `flush_comments_before` would otherwise claim it as a leading
        // comment on `y`, forcing `y` onto its own line under the comment
        // even though `y` itself never needed to break.
        let src = concat!(
            "module Foo where\n\n",
            "foo =\n",
            "  a b c\n",
            "    -- comment\n",
            "    <#> List.map d\n",
            "    # e f\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
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
    fn record_and_array_flat_are_both_padded() {
        let src = "module Foo where\n\nfoo = { a: 1, b: 2 }\nbar = [1, 2]\n";
        let out = fmt(src);
        assert_eq!(
            out,
            "module Foo where\n\nfoo = { a: 1, b: 2 }\nbar = [ 1, 2 ]\n"
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

    /// `flush_comments_before` must also check for a source blank line
    /// *between* a leading comment and whatever it precedes (not just
    /// *before* the comment group itself) - otherwise a standalone section
    /// comment followed by a deliberate blank line collapses onto one line.
    #[test]
    fn blank_line_between_a_leading_comment_and_its_decl_is_kept() {
        let src = "module Foo where\n\n-- section\n\nfoo = 1\n";
        let out = fmt(src);
        assert_eq!(out, src);
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

    /// An empty-record binder `{}` had no `.span()` at all (the `Ast` derive
    /// merges only over its empty field list), reducing to `Span::Zero` -
    /// the same class of bug fixed for `Binder::Array`'s `[]`, just never
    /// applied to `Binder::Record`. `breaks_before` then compared the
    /// branch's real line against `Span::Zero`'s `(0, 0)`, always reading as
    /// a break, so `{} -> 0` relocated even when glued flat in the source -
    /// and since that shifted the branch's own end line, a second pass then
    /// saw a spurious gap before the next branch too. Fixed by giving
    /// `Binder::Record` real `{`/`}` brace spans, same as `Array`.
    #[test]
    fn empty_record_binder_case_branch_does_not_relocate_or_flip() {
        let src = "module Foo where\n\nfoo x = case x of\n  y | y > 0 -> y\n  {} -> 0\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// A `case` scrutinee that's itself going to print multi-line (an `Op`
    /// chain here) must push `case ... of` apart onto its own indented
    /// block, or `of` ends up glued right after wherever the scrutinee's
    /// last line happened to land.
    #[test]
    fn case_scrutinee_that_would_break_relocates_case_and_of_onto_their_own_lines() {
        let src = "module Foo where\n\nfoo = case\n  a\n    && b\n  of\n  true -> 1\n  false -> 2\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// Same fix, for multiple comma-separated scrutinees - each one lands on
    /// its own line, subsequent ones leading with `, ` (this printer's usual
    /// leading-comma list style), with `of` and the branches unaffected.
    #[test]
    fn case_multiple_scrutinees_that_would_break_print_one_per_line() {
        let src =
            "module Foo where\n\nfoo = case\n  a\n  , b\n  of\n  true, e -> 1\n  _, _ -> 2\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn record_field_with_case_value_hangs_one_level_deeper() {
        // A record field's value sits one level deeper than the field itself,
        // on top of whatever the value's own construct does - so `case`'s
        // branches (its own +1) land two levels below the field, not one.
        // Unlike top-level `=` (see `case_of_with_multiple_branches`), this
        // hang applies even though `case` stays glued to the field's `:`.
        let src =
            "module Foo where\n\nfoo =\n  { a: 1\n  , b: case x of\n      0 -> 1\n      _ -> 2\n  }\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn record_update_field_with_case_value_hangs_one_level_deeper() {
        let src = "module Foo where\n\nfoo =\n  r\n    { a = 1\n    , b = case x of\n        0 -> 1\n        _ -> 2\n    }\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn record_field_moves_to_its_own_line_when_its_value_already_broke_in_source() {
        // Unlike `case` (see `record_field_with_case_value_hangs_one_level_deeper`,
        // which stays glued to `:`), an `App` chain whose argument already
        // broke onto its own line in the source moves the whole value down
        // instead of gluing its head right after `label:`, two levels past
        // the field's own row rather than one (see
        // `print_record_field_rhs`'s doc comment).
        let src = "module Foo where\n\nf x =\n  update\n    { payload:\n        List.singleton\n          (Db.payload @\"type\" (selectedTypes # NonEmptyArray.map RowType.toStorageString))\n    , updatedColumns: List.singleton (Db.updatedColumn @\"status\")\n    }\n    tableRow\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn constraint_arg_moves_to_its_own_line_after_a_multiline_row_argument() {
        // `Union a (row) b`: `a` stays glued to `Union` (no source break),
        // but once `row` prints as its own multiline block, `b` - which sits
        // on the very next source line after the row's closing paren - must
        // not glue back onto that closing line; it needs its own line at the
        // same indent as the row block. The block hangs under `Union`'s own
        // real column (`print_constraint`'s hang, via `hang_glued`) - not an
        // approximate level bump - or it looks shallower than the very name
        // it's an argument of, since the ambient indent baseline has no
        // memory of `. `'s width.
        let src = "module Foo where\n\nempty\n  :: forall a b\n   . Union a\n       ( balance :: Maybe Money.Money\n       , currency :: Currency\n       )\n       b\n  => Record b\nempty = x\n";
        let out = fmt(src);
        assert_eq!(out, src);
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
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn ado_notation_with_statements_stays_glued_like_a_do_block() {
        let src = "module Foo where\n\nfoo = ado\n  x <- bar\n  in x\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn ado_with_no_statements_stays_flat_when_the_source_had_it_on_one_line() {
        let src = "module Foo where\n\nfoo = ado in 1\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn ado_with_one_statement_stays_flat_when_the_source_had_it_on_one_line() {
        let src = "module Foo where\n\nfoo = ado x <- pure 1 in x\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn ado_with_no_statements_and_a_source_break_relocates_the_whole_block() {
        // Unlike a populated `ado`/`do` block (which always stays glued to
        // `=`, real statements or not), an empty `ado` has nothing but `in`
        // to show under it - so once it can't stay flat on one line, the
        // whole `ado ... in ...` unit moves onto its own indented line
        // instead of leaving `ado` glued with just `in` dangling under it.
        let src = "module Foo where\n\nfoo = ado\n  in 1\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\nfoo =\n  ado\n    in 1\n");
        assert_idempotent(&out);
    }

    #[test]
    fn let_single_binding_stays_glued_in_do_block() {
        // Regression test: a single simple `let` binding that sat glued flat
        // on `let`'s own source line used to always break onto its own
        // indented line (`let\n  a = 1`) even though nothing about it needed
        // to - now it only breaks when the source did, or the binding's own
        // RHS forces a break (e.g. a nested `case`/`do`).
        let src = "module A where\n\na =\n  do\n    let a = 1\n    pure a\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn let_multiple_bindings_still_break() {
        let src = "module A where\n\na = do\n  let\n    x = 1\n    y = 2\n  pure (x + y)\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn let_binding_on_its_own_source_line_still_breaks() {
        let src = "module A where\n\na = do\n  let\n    x = 1\n  pure x\n";
        let out = fmt(src);
        assert_eq!(out, src);
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
            "module Foo where\n\nfoo = r { a = 1 }\nbar = 1 `add` 2\n"
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

    /// A single constructor's `any_breaks` check has no adjacent pair to
    /// compare (there's only one constructor, no `|` alternative), so it
    /// never caught a record-typed arg that would break on its own account
    /// while still glued flat after the constructor name in source - the
    /// constructor name stayed on the `=` line while only its args
    /// relocated out from under it. Now the whole `= Ctor` line relocates
    /// together with its args, matching the shape a multi-constructor
    /// break already used.
    #[test]
    fn data_single_ctor_arg_that_would_break_relocates_whole_line() {
        let src = concat!(
            "module Foo where\n\n",
            "data Store = Store { a :: Int\n",
            "  , b :: Int\n",
            "  }\n",
        );
        let out = fmt(src);
        assert_eq!(
            out,
            concat!(
                "module Foo where\n\n",
                "data Store\n",
                "  = Store\n",
                "      { a :: Int\n",
                "      , b :: Int\n",
                "      }\n",
            )
        );
        assert_idempotent(src);
    }

    /// A data constructor's own fields relocate when they break, same as a
    /// name's binders or a call's arguments. Also required a parser fix:
    /// `data_cnstr` parsed each field with the full `typ` parser rather than
    /// `typ_atom`, so two space-separated fields (`C A B`) mis-parsed as one
    /// field being `A` applied to `B` instead of two sibling fields (needs
    /// explicit parens for application, per PureScript's `atype*`
    /// constructor-field grammar).
    #[test]
    fn data_ctor_fields_that_would_break_relocate_two_levels_past_the_bullet() {
        let src = "module Foo where\n\ndata D\n  = C\n      A\n      B\n  | E\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// `newtype`'s single constructor argument relocates when it would
    /// break, even glued flat in the source - the common case for a record
    /// type with enough fields. A newtype constructor always wraps exactly
    /// one `Typ`, never a space-separated arg list like a data constructor
    /// can, so this has its own direct relocation logic rather than a
    /// borrowed call into `print_ctor_args` - but lands on the same visual
    /// shape as `Decl::Data`'s single-constructor case: the whole `= Ctor`
    /// line moves down together with the arg, two levels past the bullet.
    #[test]
    fn newtype_ctor_arg_that_would_break_relocates_even_when_source_glued_it_flat() {
        let src = concat!(
            "module Foo where\n\n",
            "newtype Store = Store { a :: Int\n",
            "  , b :: Int\n",
            "  }\n",
        );
        let out = fmt(src);
        assert_eq!(
            out,
            concat!(
                "module Foo where\n\n",
                "newtype Store\n",
                "  = Store\n",
                "      { a :: Int\n",
                "      , b :: Int\n",
                "      }\n",
            )
        );
        assert_idempotent(src);
    }

    /// A record/row field's own type relocates when it would break, the
    /// same as every other `name :: Typ`/`name = Typ` site. Unlike a
    /// top-level signature, a field's `::` stays glued to its label
    /// (`print_field_typ` mirrors `print_typ_alias_rhs`'s shape, not
    /// `print_sig_typ`'s) - only the type itself drops to a fresh line.
    #[test]
    fn record_field_typ_that_would_break_relocates_with_double_colon_staying_put() {
        let src = concat!(
            "module Foo where\n\n",
            "type T =\n",
            "  { a :: Int\n",
            "  , action :: Foo\n",
            "      Bar\n",
            "      Baz\n",
            "  }\n",
        );
        let out = fmt(src);
        assert_eq!(
            out,
            concat!(
                "module Foo where\n\n",
                "type T =\n",
                "  { a :: Int\n",
                "  , action ::\n",
                "      Foo\n",
                "        Bar\n",
                "        Baz\n",
                "  }\n",
            )
        );
        assert_idempotent(src);
    }

    #[test]
    fn record_field_typ_app_with_paren_row_arg_indents_two_levels_past_label() {
        // `label ::`/`, ` is exactly `INDENT` characters wide, so a single
        // `indent_in()` for the relocated type would land it flush with the
        // field's own label column - looking like it merely continued the
        // label instead of nesting under it.
        let src = concat!(
            "module Foo where\n\n",
            "type T =\n",
            "  { other :: Int\n",
            "  , action :: VariantStorable\n",
            "      ( conversion :: ProxyStorable \"conversion\"\n",
            "      , funding :: ProxyStorable \"funding\"\n",
            "      )\n",
            "  }\n",
        );
        let out = fmt(src);
        assert_eq!(
            out,
            concat!(
                "module Foo where\n\n",
                "type T =\n",
                "  { other :: Int\n",
                "  , action ::\n",
                "      VariantStorable\n",
                "        ( conversion :: ProxyStorable \"conversion\"\n",
                "        , funding :: ProxyStorable \"funding\"\n",
                "        )\n",
                "  }\n",
            )
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

    /// `print_inst_head`/`Decl::Class`'s constraint-context printing tracks
    /// multiline the same way `print_typ_constrained_chain` does for a
    /// signature's `=>` chain, instead of always gluing
    /// `(constraints) => head args... where` onto one line regardless of
    /// source breaks. `where` also relocates onto its own line here (see
    /// `Decl::Instance`) once anything between `instance` and `where` is
    /// multiline, regardless of where the source itself put it.
    #[test]
    fn instance_head_constraint_relocates_when_source_broke_it() {
        let src = concat!(
            "module Foo where\n\n",
            "instance\n",
            "  IsSymbol l\n",
            "  => Foldable.FoldWithIndex Foo (Proxy l) where\n",
            "  foldingWithIndex _ _ acc value = acc\n",
        );
        let out = fmt(src);
        assert_eq!(
            out,
            concat!(
                "module Foo where\n\n",
                "instance\n",
                "  IsSymbol l\n",
                "  => Foldable.FoldWithIndex Foo (Proxy l)\n",
                "  where\n",
                "  foldingWithIndex _ _ acc value = acc\n",
            )
        );
        assert_idempotent(out.as_str());
    }

    /// Same bug, the parenthesized multi-constraint shape - expands with
    /// leading commas, matching `list()`'s convention for every other
    /// bracketed multi-item construct.
    #[test]
    fn instance_head_multi_constraint_relocates_leading_comma_style() {
        let src = concat!(
            "module Foo where\n\n",
            "instance\n",
            "  ( IsSymbol l\n",
            "  , Foo l\n",
            "  )\n",
            "  => Foldable.FoldWithIndex Foo (Proxy l) where\n",
            "  foldingWithIndex _ _ acc value = acc\n",
        );
        let out = fmt(src);
        assert_eq!(
            out,
            concat!(
                "module Foo where\n\n",
                "instance\n",
                "  ( IsSymbol l\n",
                "  , Foo l\n",
                "  )\n",
                "  => Foldable.FoldWithIndex Foo (Proxy l)\n",
                "  where\n",
                "  foldingWithIndex _ _ acc value = acc\n",
            )
        );
        assert_idempotent(out.as_str());
    }

    /// `Decl::Class`'s superclass context (`<=`) shares the same fix.
    #[test]
    fn class_superclass_constraint_relocates_when_source_broke_it() {
        let src = concat!(
            "module Foo where\n\n",
            "class\n",
            "  Eq a\n",
            "  <= MyClass a where\n",
            "  bar :: a -> a\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// A singleton constraint's parens are optional syntax, but whether the
    /// source actually wrote them is real information the printer should
    /// preserve - same treatment as `Expr::Paren`/`Typ::Paren` everywhere
    /// else (removing a truly redundant paren is a `style.rs` rule's job,
    /// not something the raw printer silently decides). An earlier version
    /// of this fix unconditionally dropped these parens; that was wrong and
    /// got corrected in the same session.
    #[test]
    fn instance_head_single_constraint_paren_wrap_is_preserved_when_flat() {
        let src = "module Foo where\n\ninstance (IsSymbol l) => Foo (Proxy l) where\n  foo = 1\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// The parenless form stays parenless too - this isn't a "always add
    /// parens" normalization, just "print exactly what's there."
    #[test]
    fn instance_head_single_constraint_without_parens_stays_bare() {
        let src = "module Foo where\n\ninstance IsSymbol l => Foo (Proxy l) where\n  foo = 1\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// `where` must relocate onto its own line whenever the head's own
    /// class-args spine breaks onto several lines, not just when the
    /// constraint context itself relocates.
    #[test]
    fn instance_where_relocates_when_head_spine_args_break() {
        let src = concat!(
            "module Foo where\n\n",
            "instance\n",
            "  ( IsSymbol name\n",
            "  , WriteForeign ty\n",
            "  )\n",
            "  => WriteRowFields\n",
            "       ( Cons namea\n",
            "           (Maybe ty)\n",
            "           tail\n",
            "       )\n",
            "       row\n",
            "       from\n",
            "       to\n",
            "  where\n",
            "  writeRowFields _ _ = 1\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// `print_spine_args`'s `Typ` call sites (`Typ::App`, `print_constraint`,
    /// `print_inst_head`) treat a `Typ::Paren` argument that would itself
    /// break the same as `Expr::App`'s would-break args: it (and everything
    /// after it) relocates onto its own line, even glued right after the
    /// head with no source break before it.
    #[test]
    fn inst_head_paren_arg_with_no_source_break_before_it_still_relocates_when_it_would_break() {
        let src = concat!(
            "module Foo where\n\n",
            "instance\n",
            "  ( IsSymbol name\n",
            "  , ReadForeign ty\n",
            "  )\n",
            "  => ReadRowFields (Cons name\n",
            "                          ty\n",
            "                          tail\n",
            "                       )\n",
            "       from\n",
            "       to\n",
            "  where\n",
            "  readRowFields _ _ = 1\n",
        );
        let out = fmt(src);
        assert_eq!(
            out,
            concat!(
                "module Foo where\n\n",
                "instance\n",
                "  ( IsSymbol name\n",
                "  , ReadForeign ty\n",
                "  )\n",
                "  => ReadRowFields\n",
                "       ( Cons name\n",
                "           ty\n",
                "           tail\n",
                "       )\n",
                "       from\n",
                "       to\n",
                "  where\n",
                "  readRowFields _ _ = 1\n",
            )
        );
        assert_idempotent(out.as_str());
    }

    /// Same fix, `print_constraint`'s own spine - a constraint's `Typ::Paren`
    /// argument (not `Typ::Row`/`Typ::Record`, which keep hanging in place,
    /// see `row_type_expands_one_field_per_line_when_source_has_a_newline`)
    /// relocates the same way when it would break, even glued with no
    /// source break before it.
    #[test]
    fn constraint_paren_arg_with_no_source_break_before_it_still_relocates_when_it_would_break() {
        let src = concat!(
            "module Foo where\n\n",
            "empty\n",
            "  :: forall a b\n",
            "   . Union (Cons name\n",
            "              ty\n",
            "              tail\n",
            "           ) b\n",
            "  => Record b\n",
            "empty = x\n",
        );
        let out = fmt(src);
        assert_eq!(
            out,
            concat!(
                "module Foo where\n\n",
                "empty\n",
                "  :: forall a b\n",
                "   . Union\n",
                "       ( Cons name\n",
                "           ty\n",
                "           tail\n",
                "       )\n",
                "       b\n",
                "  => Record b\n",
                "empty = x\n",
            )
        );
        assert_idempotent(out.as_str());
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
            "module Foo ((<*>), type (~>)) where\n\nimport Data.Functor ((<$>))\n\nfoo = (<*>)\n"
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
    fn import_class_sorts_before_types_as_its_own_tier() {
        // Class imports are their own leading tier (purs-tidy's
        // `ImportClassCmp`), always ahead of plain type/value names -
        // not merely alphabetical among "class Eq"/"Foo"/"bar" as rendered
        // or bare text (both would put `Foo` before `class Eq` here).
        let src = "module Foo where\n\nimport Data.Foo (Foo, class Eq, bar)\n\nx = 1\n";
        let out = fmt(src);
        assert_eq!(
            out,
            "module Foo where\nimport Data.Foo (class Eq, Foo, bar)\n\nx = 1\n"
        );
        assert_idempotent(src);
    }

    #[test]
    fn import_sort_follows_purs_tidys_five_tier_kind_order() {
        // purs-tidy's `ordImportComparison` ranks import items by kind before
        // name: class, then type-operator (`type (~>)`), then plain type,
        // then plain value, then value-operator - each tier alphabetical
        // within itself. A flat alphabetical sort (on either the rendered
        // "class "/"type "-prefixed text or the bare name alone) would put
        // `(>>=)` first (low-ASCII `(`) instead of last, and wouldn't place
        // `type (..)` ahead of the plain type names.
        let src = concat!(
            "module Foo where\n\n",
            "import Db.Type (Name, class GetPk, type (..), toSqlValue, (>>=), class GetIndex, fromSqlValue)\n\n",
            "x = 1\n",
        );
        let out = fmt(src);
        assert_eq!(
            out,
            concat!(
                "module Foo where\n",
                "import Db.Type (class GetIndex, class GetPk, type (..), Name, fromSqlValue, toSqlValue, (>>=))\n\n",
                "x = 1\n",
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
            "   . Show a\n",
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

    /// `Typ::Paren`'s counterpart of `paren_expands_when_source_has_a_newline_inside` -
    /// a parenthesized type that breaks internally forces the same `( ` ... `)`
    /// block style (and the same "break `::` first rather than move the `)`
    /// back" fix) that a parenthesized value gets.
    #[test]
    fn typ_paren_expands_when_source_has_a_newline_inside() {
        // The paren's own hang lines up under its real column - right after
        // `( `, wherever that lands once glued after `:: ` - not an
        // approximate level bump; see the "floor" model in FORMATTER.md.
        let src = "module Foo where\n\nf :: (Int ->\n  String)\nf = undefined\n";
        let out = fmt(src);
        assert_eq!(
            out,
            "module Foo where\n\nf\n  :: ( Int\n       -> String\n     )\nf = undefined\n"
        );
        assert_idempotent(src);
    }

    /// `Typ::App`'s counterpart of `app_expands_one_arg_per_line_when_source_has_a_newline_between_args` -
    /// previously `Typ::App` had no multiline handling at all and always glued
    /// every argument flat with a single space.
    #[test]
    fn typ_app_expands_one_arg_per_line_when_source_has_a_newline_between_args() {
        let src = "module Foo where\n\nf :: Bar\n  Baz\n  Qux\nf = x\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn typ_app_directly_after_a_broken_sig_gets_an_extra_hang_level() {
        // `typ` is glued directly after `:: ` here (a fixed-width raw token
        // the ambient indent baseline has no memory of) - if `typ` is a
        // nesting shape (`Array { ... }`) that itself breaks, it needs to
        // hang under `Array`'s own real column (`hang_glued`), or the
        // resulting block looks shallower than `Array` itself.
        let src =
            "module Foo where\n\nf\n  :: Array\n       { from :: RowId\n       , to :: RowId\n       }\nf = x\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// Regression test: `print_typ_arrow_chain` printed every segment with a
    /// bare `print_typ`, unlike `print_sig_typ`'s own `needs_hang` check for
    /// a bare (non-arrow) signature type - so a nesting shape (`Array
    /// {...}`) that's the *first* segment of an arrow chain (glued directly
    /// after `:: `, same as `typ_app_directly_after_a_broken_sig_gets_an_extra_hang_level`
    /// above, just with a `-> ...` tail after it) never got its extra hang
    /// level, landing a whole level shallower than `Array` itself instead of
    /// past it.
    #[test]
    fn typ_arrow_chain_segment_gets_the_same_extra_hang_as_a_bare_sig() {
        let src = concat!(
            "module Foo where\n\n",
            "linkRows\n",
            "  :: Array\n",
            "       { source :: RowId\n",
            "       , target :: LinkId.LinkId\n",
            "       }\n",
            "  -> Ctx _ _ Unit\n",
            "linkRows = linkRowsSql >>> DbCtx.runSql\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// The same missing hang, reached through `print_sig_typ`'s own
    /// `needs_hang` branch directly (no arrow chain involved) rather than
    /// through `print_typ_arrow_chain` - a `Typ::App` whose own argument is a
    /// `Typ::Paren`-wrapped operator chain, glued after `:: `. `needs_hang`
    /// hangs under `Db.Table`'s own real column (`hang_glued`), not an
    /// approximate level bump off the ambient baseline.
    #[test]
    fn typ_app_paren_op_chain_directly_after_a_broken_sig_gets_an_extra_hang_level() {
        let src = concat!(
            "module Foo where\n\n",
            "tableLinkRow\n",
            "  :: Db.Table\n",
            "       ( Db.Pk (\"row_a\" .. \"row_b\")\n",
            "           .. Db.Index \"row_b\"\n",
            "           .. Db.Name \"row_link_v0\"\n",
            "       )\n",
            "       LinkRowR\n",
            "tableLinkRow = Db.table @\"row_link_v0\"\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// `print_typ_constrained_chain`'s counterpart of the same fix: the
    /// `body` after the last `=> ` is glued the same way a bare `:: `'s type
    /// or an arrow chain's segment is, so it needs the same `print_typ_glued`
    /// treatment when it's a nesting shape.
    #[test]
    fn typ_constrained_chain_body_gets_the_same_extra_hang_as_a_bare_sig() {
        let src = concat!(
            "module Foo where\n\n",
            "f\n",
            "  :: Eq a\n",
            "  => Array\n",
            "       { x :: Int\n",
            "       , y :: Int\n",
            "       }\n",
            "f = x\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// Regression test: a broken type-operator chain used to add its own
    /// indent level for the operator (like a value's operator chain does),
    /// drifting deeper than the non-operator break that introduced it. Type
    /// operators get no extra indent - `.. B`/`.. C` line up with `A`, one
    /// level in from `type T =`, not two.
    #[test]
    fn typ_operator_chain_does_not_add_its_own_indent() {
        let src = "module Foo where\n\ntype T =\n  A\n    .. B\n    .. C\nf = 1\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\ntype T =\n  A\n  .. B\n  .. C\nf = 1\n");
        assert_idempotent(src);
    }

    /// `Decl::Type`'s counterpart of `paren_expands_when_source_has_a_newline_inside` -
    /// previously a type alias's `=` had no "break me instead of letting the
    /// closing `)` move back" handling at all (unlike a value's `=` or a
    /// signature's `::`).
    #[test]
    fn type_alias_rhs_breaks_when_its_paren_would_break() {
        let src = "module Foo where\n\ntype T = (A\n  -> B)\nf = 1\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\ntype T =\n  ( A\n    -> B\n  )\nf = 1\n");
        assert_idempotent(src);
    }

    /// Regression test: `in_broken_sig` (which forces a signature's/alias's
    /// chains to stay fully expanded once the source deliberately wrapped
    /// them) used to leak into parenthesized sub-expressions, so a flat,
    /// single-line operator chain nested inside a paren got force-broken
    /// just because the *outer* declaration happened to be multiline. A
    /// paren is its own bracketed scope (like a row's braces already are;
    /// see `print_row`'s own reset) and must decide its own contents'
    /// multiline-ness independently. The outer chain's own operator
    /// continuation (`.. Db.Index`) gets its own hang level past the `( `
    /// it's glued to - see `typ_op_chain_gets_its_own_hang_when_not_in_a_broken_sig`
    /// - while the flat, nested `("region_id" .. "type")` stays untouched.
    #[test]
    fn broken_type_alias_does_not_force_a_flat_nested_paren_to_expand() {
        let src = concat!(
            "module Foo where\n\n",
            "type Table =\n",
            "  Db.Table\n",
            "    ( Db.Pk \"id\"\n",
            "        .. Db.Index (\"region_id\" .. \"type\")\n",
            "    )\n",
            "    Row\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// Regression test: a `Typ::Op` chain glued directly after a `Typ::Paren`'s
    /// `( ` (which resets `in_broken_sig` - see `print_paren_block`) needs its
    /// own hang level for its operator continuations, the same way `Expr::Op`
    /// always does - without it, `.. Db.Index`/`.. Db.Name` land flush
    /// with `Db.Pk`, one level shallower than they should (only as deep as
    /// the paren's own content baseline, not past it). This is distinct from
    /// `typ_operator_chain_does_not_add_its_own_indent`, where the chain *is*
    /// the flattened continuation of a signature/alias's own break
    /// (`in_broken_sig` true) and must stay flush with that break's column
    /// instead.
    #[test]
    fn typ_op_chain_gets_its_own_hang_when_not_in_a_broken_sig() {
        let src = concat!(
            "module Foo where\n\n",
            "type Route =\n",
            "  Schema\n",
            "    ( Db.Pk \"key\"\n",
            "        .. Db.Index \"row_b\"\n",
            "        .. Db.Name \"row_idem_v0\"\n",
            "    )\n",
            "    IdemRowR\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// Parser regression test: `Db.Pk ("key")` used to lose `"key"`
    /// entirely, printing `Db.Pk ()`. Root cause was in `row_label`, not
    /// the printer - `row`'s stop condition treats a `String`/`RawString` as
    /// a possible row-label start (quoted labels like `("my-label" ::
    /// Int)`), so parsing `("key")` first tried it as an empty row type: the
    /// old `row_label` committed to consuming `"key"` as a label via
    /// `label(p)?` *before* checking for the `::` that would confirm it
    /// really was one, and that consumption didn't roll back when the `::`
    /// check then failed. `sep_until` saw the (spuriously) failed field
    /// attempt, stopped with zero fields, and by then `"key"` was already
    /// gone - so the very next token looked like the closing `)` the
    /// row-alternative wanted, and `typ_atom`'s `alt!` never got to try the
    /// `Typ::Paren` alternative that should have parsed `"key"` as an
    /// ordinary type. Fixed by checking for `::` with lookahead before
    /// committing to a label at all (`row_label`, matching the existing
    /// `record_label`/`record_binder` style) instead of consume-then-fail.
    #[test]
    fn paren_wrapped_string_typ_is_not_mistaken_for_an_empty_row() {
        let src = concat!(
            "module Foo where\n\n",
            "tableIdemRow\n",
            "  :: Db.Table\n",
            "       ( Db.Pk (\"key\")\n",
            "           .. Db.Index \"row_b\"\n",
            "           .. Db.Name \"row_idem_v0\"\n",
            "       )\n",
            "       IdemRowR\n",
            "tableIdemRow = x\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// A quoted row label immediately followed by `::` must still parse as
    /// a label, not get rejected by the same lookahead that now bails out on
    /// a bare string used as an ordinary type (see the test above).
    #[test]
    fn quoted_row_label_still_parses() {
        let src = "module Foo where\n\ntype Foo = (\"my-label\" :: Int, normal :: String)\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// The formatter must never break a type that was written on a single
    /// line into multiple lines, no matter how many nested parens/operators/
    /// applications it contains - it only ever preserves breaks the source
    /// already had.
    #[test]
    fn single_line_type_alias_with_nested_parens_and_operators_stays_flat() {
        let src = "module Foo where\n\ntype Table = Db.Table (Db.Pk \"id\" .. Db.Index (\"region_id\" .. \"type\")) Row\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn row_type_expands_one_field_per_line_when_source_has_a_newline() {
        // The row's own `(` glues flat right after `Record ` (its argument
        // never broke from the head in the source, so `print_spine_args`
        // never moves it) - its own fields then hang under its real column,
        // not a level bump. See the "floor" model in FORMATTER.md.
        let src = "module Foo where\n\nf :: forall r. Record (a :: Int,\n  b :: String)\nf r = r\n";
        let out = fmt(src);
        assert_eq!(
            out,
            "module Foo where\n\nf :: forall r. Record ( a :: Int\n                      , b :: String\n                      )\nf r = r\n"
        );
        assert_idempotent(src);
    }

    #[test]
    fn comment_inside_a_multiline_row_stays_attached_to_its_own_field() {
        // Regression test: `print_row` used to have no comment handling at
        // all (always flat, no per-field flush) - a comment here would
        // silently ride past the whole row to wherever the next flush point
        // happened to be.
        let src = concat!(
            "module Foo where\n\n",
            "f :: forall r. Record (a :: Int\n",
            "  -- comment\n",
            "  , b :: String)\n",
            "f r = r\n",
        );
        let out = fmt(src);
        assert_eq!(
            out,
            "module Foo where\n\nf :: forall r. Record ( a :: Int\n                      -- comment\n                      , b :: String\n                      )\nf r = r\n"
        );
        assert_idempotent(src);
    }

    /// Regression test for the "floor" model (see FORMATTER.md): a type-level
    /// `::`/`=>`/`->`/`.` is only ever a floor that whatever follows it glues
    /// onto - it never moves, no matter how much the glued thing itself goes
    /// on to break. A record glued right after `=> `/`-> ` must stay glued,
    /// with its own fields hanging under its real column, rather than
    /// relocating `{` onto a deeper line with `=>`/`->` left alone above it.
    #[test]
    fn typ_record_glued_after_a_broken_sig_hangs_in_place_instead_of_moving_down() {
        let src = concat!(
            "module Foo where\n\n",
            "unpack\n",
            "  :: forall unpacked packed\n",
            "   . Lacks \"type_index\" packed\n",
            "  => Db.Pack\n",
            "       { balance :: Maybe Money.Money\n",
            "       | unpacked\n",
            "       }\n",
            "       { date_created :: Maybe ExDate\n",
            "       , type :: RowType\n",
            "       | packed\n",
            "       }\n",
            "  => { date_created :: Maybe ExDate\n",
            "     , type :: RowType\n",
            "     , type_index :: Int\n",
            "     | packed\n",
            "     }\n",
            "  -> { balance :: Maybe Money.Money\n",
            "     | unpacked\n",
            "     }\n",
            "unpack = x\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// `Typ::Paren`'s counterpart of the same fix, for `print_paren_block`:
    /// `(` glued directly after an arrow's `-> ` hangs its own nested arrow
    /// chain under its own first token (`c`, not an approximate level bump),
    /// and its closing `)` lines up under its own `(` - not the outer `->`'s
    /// floor, which can be a completely different column once `(` is glued
    /// mid-line.
    #[test]
    fn typ_paren_glued_after_arrow_hangs_under_its_own_first_token() {
        let src = concat!(
            "module Foo where\n\n",
            "a\n",
            "  :: forall b c d\n",
            "   . b\n",
            "  -> (c\n",
            "      -> Int\n",
            "      -> String)\n",
            "  -> d\n",
            "a x y = z\n",
        );
        let out = fmt(src);
        assert_eq!(
            out,
            concat!(
                "module Foo where\n\n",
                "a\n",
                "  :: forall b c d\n",
                "   . b\n",
                "  -> ( c\n",
                "       -> Int\n",
                "       -> String\n",
                "     )\n",
                "  -> d\n",
                "a x y = z\n",
            )
        );
        assert_idempotent(src);
    }

    #[test]
    fn multiline_operator_chain_stays_expanded() {
        let src = "module Foo where\n\nfoo =\n  a\n    >>> b\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// Regression test: an array item glued directly after `[ `/`, ` (a
    /// fixed-width raw token) that's itself an operator chain used to hang
    /// its own continuation one level too shallow - the operator landed
    /// flush with the item's own head column instead of visibly past it,
    /// since `[ `/`, ` are exactly `INDENT` wide (see `list()`'s `item_hang`).
    /// Unlike `multiline_operator_chain_stays_expanded` above (glued after a
    /// declaration's own `=`, a genuine "floor"), a list item needs the extra
    /// level so it isn't mistaken for a sibling item at the list's own comma
    /// column.
    #[test]
    fn array_item_operator_chain_hangs_past_its_own_head() {
        let src = concat!(
            "module Foo where\n\n",
            "buttons =\n",
            "  [ Widget.create { onclick: ClickedClose false, children: [ Html.text \"Cancel\" ] }\n",
            "      # Widget.isWide true\n",
            "      # Widget.render\n",
            "  , Widget.create { onclick: confirmMsg, children: [ Html.text \"Done\" ] }\n",
            "      # Widget.isPrimary\n",
            "      # Widget.isWide true\n",
            "      # Widget.render\n",
            "  ]\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// Regression test: a `list()` item that's itself a *nested* `list()`-
    /// based value (a record, here) glued directly after `[ ` used to
    /// relocate its own opening brace onto a fresh, deeper line - doubling
    /// up on `item_hang`'s own extra level instead of just hanging its
    /// fields off the column it's already glued to (see `glued_floor`).
    /// The record here has nothing forcing this array to be anything but a
    /// single item, so the only thing making it expand at all is the
    /// record's own internal break - exactly the shape that exposed the bug.
    #[test]
    fn array_sole_item_record_stays_glued_after_open_bracket() {
        let src = concat!(
            "module Foo where\n\n",
            "a =\n",
            "  [ { c: 1\n",
            "    , d: 2\n",
            "    }\n",
            "  ]\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// Regression test: the same `glued_floor` bug as
    /// `array_sole_item_record_stays_glued_after_open_bracket`, but with the
    /// record as the head of an operator chain (`{...} # f # g`) rather than
    /// the whole item on its own - confirms the fix composes with
    /// `item_hang`'s own extra level for the chain's continuations instead
    /// of stacking a second, spurious level on top of the record's own
    /// brace.
    #[test]
    fn array_sole_item_operator_chain_head_record_stays_glued() {
        let src = concat!(
            "module Foo where\n\n",
            "a =\n",
            "  x y\n",
            "    [ { c: 1\n",
            "      , d: 2\n",
            "      }\n",
            "        # f\n",
            "        # g\n",
            "    ]\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// Same `glued_floor` bug as the two `array_sole_item_*` tests above,
    /// but for `Expr::App`'s own `own_indent` instead of a nested `list()`
    /// call: a single-item array whose item is a call with an argument that
    /// itself breaks (a record) must not relocate the whole call onto its
    /// own line below an empty `[`, doubling up on `item_hang`'s own level.
    #[test]
    fn array_sole_item_call_head_stays_glued_after_open_bracket() {
        let src = concat!(
            "module Foo where\n\n",
            "a =\n",
            "  [ g\n",
            "      { b: 1\n",
            "      , c: 2\n",
            "      }\n",
            "      h\n",
            "  ]\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn multiline_operator_chain_flat_after_equals_stays_flat() {
        let src = "module Foo where\n\nfoo = a\n  >>> b\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// Regression test: an operand glued flat after an operator (no source
    /// break before it) can still relocate itself onto its own line
    /// (`Expr::App`'s own `own_indent`, when the operand is a call whose own
    /// argument breaks) - which used to make the *first* formatting pass
    /// stay flat (correctly, matching the source) while the *second* pass,
    /// reparsing that output, saw a break between `first` and the operand
    /// that wasn't really there in the original source and switched the
    /// whole chain to the one-operator-per-line style: not idempotent. Now
    /// decided by rendering (`expr_would_break`, like `list()`/`Expr::App`'s
    /// own equivalent generalizations), so the *first* pass already produces
    /// the stable, multiline-chain shape directly.
    #[test]
    fn operator_chain_operand_that_would_break_on_its_own_expands_the_whole_chain() {
        // `b` stays glued right after `$` - see `glued_floor`.
        let src = "module Foo where\n\nfoo = a $ b\n  { x: 1\n  , y: 2\n  }\n";
        let out = fmt(src);
        assert_eq!(
            out,
            "module Foo where\n\nfoo = a\n  $ b\n      { x: 1\n      , y: 2\n      }\n"
        );
        assert_idempotent(src);
    }

    /// Regression test: a right-associative operator (`<>` is `R(6)`, see
    /// `op_fixity`) parses `a <> b <> c <> d` as a right-nested tree, so each
    /// subsequent `Op` node used to print *inside* the previous one's own
    /// `indent_in`/`newline` block - drifting one indent level deeper per
    /// operator instead of lining up flush (see `op_spine`).
    #[test]
    fn multiline_operator_chain_of_three_or_more_stays_at_one_indent_level() {
        let src = "module Foo where\n\nfoo =\n  a\n    <> b\n    <> c\n    <> d\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn operator_chain_operand_that_is_itself_a_broken_call_hangs_one_level_deeper() {
        // An operand is glued directly after its operator, so if the operand
        // itself breaks (an `App` call whose argument is on its own line),
        // that break needs to land one level deeper than the chain's own
        // continuation - not at the same level, which would look like the
        // call's argument is just another step of the chain. The call
        // itself (`List.map (...)`) stays glued right after `#` - `op ` is
        // its own floor (`glued_floor`), the same way `open `/`, ` already
        // is for a `list()` item, so the call's own `own_indent` doesn't
        // relocate it a second time on top of that.
        let src = "module Foo where\n\nf rs =\n  rs\n    # List.map\n        ( \\r ->\n            r\n              # empty\n        )\n    # List.toArray\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// An operand must hang under its own real column (`op `'s width
    /// included), not a plain `indent_in()` off the chain's ambient level -
    /// invisible for a one-char operator like `#` (`"# "` happens to be
    /// exactly one `INDENT` wide), but for a wider operator (`<#>`) the
    /// operand's own further break would otherwise land level with the
    /// operand itself instead of past it.
    #[test]
    fn operator_chain_lambda_operand_case_body_hangs_under_the_lambda_not_the_chain() {
        let src = "module Foo where\n\nfoo =\n  a\n    <#> \\x ->\n          case y of\n            true -> 1\n            false -> 2\n";
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// Same bug, for a call operand whose own argument relocates (see
    /// `operator_chain_operand_that_is_itself_a_broken_call_hangs_one_level_deeper`
    /// above) - `f`'s paren argument needs to hang under `f`'s own column,
    /// not the chain's ambient level.
    #[test]
    fn operator_chain_call_operand_paren_arg_hangs_under_the_call_not_the_chain() {
        let src = "module Foo where\n\nfoo =\n  a\n    <#> f\n          ( b\n              >>> c\n          )\n          d\n";
        let out = fmt(src);
        assert_eq!(out, src);
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

    #[test]
    fn deeply_nested_flat_literal_formats_without_exponential_blowup() {
        // Regression test: `list()`'s multiline check used to render every
        // item into a scratch buffer to check for a `'\n'`, then print it
        // again for real - a call whose args (or an array's/record's items)
        // never break still paid for two full renders of each, and since an
        // item can itself be a nested `Array`/`Record`, that doubling
        // recursed: `O(2^depth)` instead of `O(depth)`. A real
        // deeply-nested-but-entirely-flat record literal (an XML-shaped
        // test fixture on one line) hit this and never finished printing.
        // This depth (30) would take unreasonably long (or overflow a
        // `-release` binary's stack) if the exponential behavior ever comes
        // back - the real value of this test is that it completes at all.
        let depth = 30;
        let mut inner = "1".to_string();
        for _ in 0..depth {
            inner = format!("[ {} ]", inner);
        }
        let src = format!("module Foo where\n\nx = {}\n", inner);
        let out = fmt(&src);
        assert_eq!(out, src);
        assert_idempotent(&src);
    }

    #[test]
    fn record_update_target_relocates_away_from_its_braces_on_a_source_break() {
        // A record update (`RecordStore store { store = ... }`) whose source
        // already broke between `store` and `{` must keep that break, not
        // re-glue onto one line on reformat. Record update binds tighter
        // than application (`store { ... }` is one `Expr::Update` atom,
        // applied as `App`'s single argument), so `App`'s own spine-arg
        // breaking only ever sees this whole node's span - the internal
        // break between the target and its own `{` needed its own check.
        // Once `Expr::Update` reports that internal break, the existing "an
        // argument that would break relocates the whole call" rule takes
        // over, same as it already does for a plain `Record` argument.
        let src = concat!(
            "module Foo where\n\n",
            "reInsert event =\n",
            "  RecordStore store\n",
            "    { store = Map.insert (recordId event) (Pending event) store.store }\n",
        );
        let out = fmt(src);
        assert_eq!(
            out,
            concat!(
                "module Foo where\n\n",
                "reInsert event =\n",
                "  RecordStore\n",
                "    store\n",
                "      { store = Map.insert (recordId event) (Pending event) store.store }\n",
            )
        );
        assert_idempotent(src);
    }

    #[test]
    fn record_update_target_stays_glued_when_source_had_no_break() {
        let src = concat!(
            "module Foo where\n\n",
            "reInsert event =\n",
            "  RecordStore store { store = Map.insert (recordId event) (Pending event) store.store }\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn expr_typed_relocates_the_double_colon_like_a_signature_when_the_type_would_break() {
        // `Expr::Typed`'s `:: Typ` relocates the same way every other
        // `name :: Typ` site does (`print_sig_typ`), instead of always
        // gluing flat and letting a multi-line arrow type extend rightward.
        let src = concat!(
            "module Foo where\n\n",
            "foo =\n",
            "  bar\n",
            "    # ( fromSerializable\n",
            "          :: VariantStorable (pending :: ProxyStorable \"pending\")\n",
            "          -> Variant (pending :: Proxy \"pending\")\n",
            "      )\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }
}

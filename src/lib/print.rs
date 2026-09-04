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
        let last_nl = self.out.rfind('\n').map_or(0, |i| i + 1);
        self.out[last_nl..].chars().count()
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
    /// Whether this should use that block style can't be decided from the
    /// source span of `inner` (or of the open/close parens) the way most
    /// other multiline decisions in this printer are: `inner` might contain a
    /// `case`/`do`/`let` that *always* prints across multiple lines
    /// regardless of its own source layout (that's their own established,
    /// deliberate behavior), which would make a span-based decision here flip
    /// between formatting passes - flat on the first pass (matching
    /// originally-flat source), block-style on the second (now that the
    /// previous pass's own output put the close paren on a later line than
    /// the open one). Instead, print `inner` into a scratch buffer and look
    /// at what actually came out: multiline exactly when printing it produced
    /// any line break at all. That's a pure function of the AST - stable no
    /// matter how many times it's reformatted.
    ///
    /// This only ever glues `(` in place (never relocates it onto its own
    /// fresh line, even when that would leave the closing `)` looking like it
    /// "moved back" past whatever precedes the `(`) - deliberately:
    /// relocating here based on "am I at a fresh line" doesn't distinguish
    /// "glued right after `=`/`->`" from "glued as one space-separated
    /// argument in a flat `Expr::App`", and relocating in the latter case
    /// changes *this* paren's own source position, which is exactly the kind
    /// of self-inflicted instability the "no `at_fresh_line` here" choice
    /// avoids: `Expr::App`'s multiline decision is itself span-based, and a
    /// self-relocated paren would flip that decision on the next formatting
    /// pass. The "don't move back" fix belongs at the call site that
    /// actually knows it's printing an arrow's RHS - see `print_arrow_rhs`.
    ///
    /// `is_typ` picks which of two, deliberately different, hang strategies
    /// `inner` gets once it's decided to print as a block (see the "floor"
    /// model in FORMATTER.md - types and values are not the same here):
    /// - `Typ::Paren` (`is_typ = true`): `inner` hangs under the *exact
    ///   column* right after `( `, however much text that's glued after
    ///   (`:: `, `-> `, a class name, ...) - a type-level `::`/`=>`/`->`/`.`
    ///   is only ever a "floor" that the very next thing glues onto; it never
    ///   moves, so `inner`'s own hang has to account for its real width
    ///   itself instead of approximating with a level bump.
    /// - `Expr::Paren` (`is_typ = false`): `inner` hangs one level below
    ///   wherever we already were, the same as always - a value's own glued
    ///   constructs already have an established "break the glued token
    ///   first instead" strategy (`paren_would_break` + `print_arrow_rhs`),
    ///   so by the time this runs, whatever `(` is glued after either isn't
    ///   going to move, or already broke onto its own fresh line.
    fn print_paren_block(&mut self, is_typ: bool, print_inner: impl FnOnce(&mut Self)) {
        // A paren is its own bracketed context, unrelated to whatever signature
        // it happens to be nested inside - a chain inside it that was written
        // flat shouldn't inherit an enclosing broken-signature's forced
        // expansion (see the same reset in `print_row`). Irrelevant to `Expr`,
        // which doesn't use `in_broken_sig`, so this is a no-op there.
        let outer_in_broken_sig = self.in_broken_sig;
        self.in_broken_sig = false;
        let open_col = self.current_column();
        let inner_text = if is_typ {
            self.render_at_column(open_col + 2, print_inner)
        } else {
            self.render_indented(1, print_inner)
        };
        self.in_broken_sig = outer_in_broken_sig;
        self.raw("(");
        if inner_text.contains('\n') {
            self.raw(" ");
            self.raw(&inner_text);
            if is_typ {
                // The closing paren lines up under the opening one, not
                // wherever this whole block happened to start - which can be
                // a different column entirely when `(` itself was glued
                // mid-line.
                self.with_indent_at(open_col, Self::newline);
            } else {
                self.newline();
            }
        } else {
            self.raw(&inner_text);
        }
        self.raw(")");
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
    /// pick up as a leading comment, if it starts on any other line.
    fn flush_trailing_comment(&mut self, hi_line: usize) {
        let Some((Ok(Token::LineComment(s) | Token::BlockComment(s)), span)) =
            self.comments.get(self.comment_idx)
        else {
            return;
        };
        if span.lo().0 != hi_line {
            return;
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

    /// Flattens an `Op` tree - `Op(a, op1, Op(b, op2, c))`,
    /// `Op(Op(a, op1, b), op2, c)`, or any other nesting shape precedence
    /// climbing produces - into the flat in-order sequence of operands and
    /// operators the source actually wrote: `(a, [(op1, b), (op2, c)])`.
    ///
    /// Needed for the same reason `app_spine` flattens `App`: printing each
    /// binary `Op` node's multiline decision independently nests one
    /// `indent_in` inside another whenever the tree leans the "wrong" way for
    /// its operator's associativity (e.g. right-associative `<>`, which nests
    /// on the right, puts each subsequent `Op` inside the previous one's own
    /// `indent_in`/`newline` block) - so a chain of N same-precedence
    /// operators drifts one indent level deeper per operator instead of
    /// lining up flush. Flattening first lets the whole chain make one
    /// multiline decision and print every continuation at the same indent,
    /// regardless of how precedence happened to shape the tree.
    fn op_spine(e: &Expr) -> (&Expr, Vec<(&QOp, &Expr)>) {
        fn go<'e>(e: &'e Expr, operands: &mut Vec<&'e Expr>, ops: &mut Vec<&'e QOp>) {
            match e {
                Expr::Op(l, op, r) => {
                    go(l, operands, ops);
                    ops.push(op);
                    go(r, operands, ops);
                }
                _ => operands.push(e),
            }
        }
        let mut operands = Vec::new();
        let mut ops = Vec::new();
        go(e, &mut operands, &mut ops);
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
    /// spine's head or a constraint's class name) one at a time, deciding
    /// per-argument whether to glue it with a leading space or move it onto
    /// a fresh, shared indent level: once one argument either has a source
    /// break before it, or is itself going to print across multiple lines
    /// (`would_break`, e.g. a paren/record/array argument with multiline
    /// content of its own), that argument and every one after it print
    /// one-per-line at a single indent level entered on the first break -
    /// so an argument gets glued right after some *other* argument that
    /// printed as a multiline block (e.g. `Union a (row) b`, where `row`
    /// prints as its own multi-line block but `b` still followed it on the
    /// very next source line) doesn't end up looking like it moved back
    /// onto that block's own closing line, and a call whose only multiline
    /// argument breaks with no source line break before it (`f (a\nb) c`)
    /// still gets `c` pushed onto its own line rather than left glued flat
    /// after a block that visually spans several lines. Args before the
    /// first break stay glued to whatever precedes them, since nothing
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
        // Both conditions must produce the *same* shape (`::` moves down onto
        // its own line, glued to `typ`) - not one shape per condition. A
        // `typ_paren_would_break`-only case prints with `typ` starting on a
        // fresh line same as the `breaks_before` case does, which makes
        // `breaks_before(before, typ.span())` true on the next parse of that
        // very output - so a second shape here would never be a fixed point,
        // it would always collapse into this one on the next formatting pass.
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
    /// `open_span`/`close_span` are the brackets' own spans, when the caller
    /// has them available (pass `Span::zero()` otherwise, e.g. export/import
    /// lists - `Span::zero().lo()` is `(0, 0)`, so the flush below simply
    /// never finds anything to do). `close_span` is used to flush a comment
    /// that sits after the last item but before the close, which nothing
    /// else here would ever reach otherwise - not `flush_comments_before(next
    /// item's line)` (there's no next item) and not `flush_trailing_comment`
    /// (only fires for a comment sharing the *last item's own* line, not one
    /// on its own separate line still before the close). Left unflushed,
    /// such a comment rides past this whole list to wherever the next flush
    /// point happens to be - relocating into unrelated code, and (since that
    /// also changes what row this list's own surroundings appear to end on)
    /// risking a multiline decision elsewhere flipping between formatting
    /// passes. `open_span` is used only to detect a source break between the
    /// brackets when there are *no* items to otherwise carry one (see below).
    /// Like `close_span`, pass `Span::zero()` there too when unavailable,
    /// which simply never matches.
    /// `item_hang` gives each item, in the expanded path, one extra level
    /// while it's being printed - for a nesting shape that itself breaks
    /// further (most commonly an operator chain glued right after `open `/
    /// `, `), or it looks flush with the item's own head instead of visibly
    /// nested under it (see the loop body's own comment). Pass `false` when
    /// the item printer already manages this itself - a record's own fields
    /// do, via `print_record_field_rhs` - to avoid doubling up.
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
        // A source break between adjacent items isn't the only place this
        // list can be told to expand: a break can just as well sit between
        // `open` and the first item, or between the last item and `close`
        // (most visibly - and the only way it can show up at all - when
        // there's only one item, or none: a plain `any_breaks` over item
        // spans has no adjacent pair to see it with then). Real report:
        // `[\na\n]` (one item, broken away from both brackets) stayed flat
        // as `[ a ]`. Folding `open_span`/`close_span` into the same
        // boundary-span chain `any_breaks` already walks handles every one
        // of these uniformly, including the zero-item case (`[\n]`, wrongly
        // collapsing to `[]`) - a real report in its own right, fixed the
        // same way.
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
            // A source break isn't the only thing that should switch this
            // list to the expanded, one-per-line style: an item can have no
            // break around it at all and still be going to print across
            // multiple lines all on its own (an `App` whose own spine
            // breaks, an operator chain, ...) - real report: `[a b, c\n d]`
            // (no break around the second item's own span, which itself
            // starts on the same line as the first item's comma) stayed
            // glued flat with the second item's own internal break looking
            // like it randomly indented mid-line, instead of switching the
            // whole list to the expanded style the way a source break
            // would.
            //
            // This used to be decided upfront: render every item into a
            // scratch buffer just to check for a `'\n'`, then - once that
            // confirmed nothing broke - print every item a *second* time for
            // real. Cheap in isolation, but catastrophic once an item is
            // itself a nested `Array`/`Record`: printing it (for the
            // scratch check, or for real) recurses into this exact same
            // "render twice" pattern for *its own* items, doubling the
            // redundant work at every level of nesting - `O(2^depth)`
            // instead of `O(depth)`. A real deeply-nested-but-entirely-flat
            // record literal (an XML-shaped test fixture on one line, ~10+
            // levels deep) hit this and never finished printing.
            //
            // Fixed by trying the flat style directly instead of probing
            // first: write `open`/items/`close` straight into the real
            // output, then check *after the fact* whether anything just
            // printed contains a `'\n'` (a nested `case`/`do`/`let` value
            // always does, regardless of source layout). If nothing did,
            // this was exactly the right call, at the cost of one traversal
            // - not two. If something did, roll back to `mark` (rewinding
            // `comment_idx` too - whatever this attempt flushed needs to be
            // re-flushed by the expanded path below, not skipped) and fall
            // through to the expanded style instead: a real but
            // non-recursive 2x, paid only by the ancestors of whatever
            // actually forced the break, not by every level of nesting
            // regardless of whether anything under it ever breaks.
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
            let own_indent = !self.at_fresh_line();
            if own_indent {
                self.indent_in();
                self.newline();
            }
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
                // of - so if the item itself is a nesting shape that breaks
                // further (most commonly an operator chain: `Button.create
                // {...}\n  # Button.isFullwidth true`), that break needs one
                // more level than the item's own line, or it looks flush
                // with the item's own head - or worse, easy to mistake for
                // another sibling item at the list's own comma column -
                // instead of visibly nested under it. Invisible when the
                // item prints flat (no `newline()` calls inside it to see
                // the difference). Same reasoning as
                // `print_record_field_rhs`'s doc comment, which found the
                // identical bug for a record field's value moving to its
                // own line - `{ `/`, ` are exactly `INDENT` (2) characters
                // wide too, which is exactly why the missing level here
                // went unnoticed for plain items but not for one that itself
                // breaks. Only for callers whose items don't already manage
                // their own hang (`item_hang`) - a record's own fields
                // already get exactly this treatment, branch-by-branch, from
                // `print_record_field_rhs`, and adding another level on top
                // here would double up on it.
                if item_hang {
                    self.indent_in();
                }
                print_item(self, item);
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
                for b in binders {
                    self.raw(" ");
                    self.print_binder(b);
                }
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
                self.print_inst_head(head);
                if !bindings.is_empty() {
                    self.raw(" where");
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
    /// visually inside the field even when glued right after `label:`/
    /// `label =`.
    ///
    /// The two branches need a *different* number of levels, though - one is
    /// not just the other with a forced newline. When the value stays glued
    /// (the `else` branch: `b: case x of`), one level is enough, because the
    /// value's own head (`case`) is still visually attached to the label on
    /// the same line - the one level only has to keep the value's own
    /// further breaking (`case`'s branches) from looking like a sibling
    /// field rather than nested content, and `case`'s own
    /// `print_indented_siblings` hang supplies the rest. When the value
    /// moves onto its own line entirely (the `if` branch), that visual
    /// attachment is gone, so one level isn't enough on its own: `label:`
    /// and `{`/`, ` are always exactly `INDENT` characters wide, so one
    /// level places the value flush with `label`'s own column - looking
    /// like it merely continues the label rather than nesting under it, not
    /// visibly "one level deeper than the field" the way the doc comment
    /// above promises. Two levels are needed there - real report:
    /// `columnIn:\n  List.singleton\n    (...)` needs `List.singleton` a
    /// full level past `columnIn`'s own column, with `App`'s own further
    /// break (its own `indent_in`, for the argument that itself broke) on
    /// top of that.
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
        if self.paren_would_break(e) || Self::breaks_before(before, e.span()) {
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
                for b in binders {
                    self.raw(" ");
                    self.print_binder(b);
                }
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
        if let [only] = bindings {
            if !Self::breaks_before(let_span, only.span()) && !self.let_binding_would_break(only) {
                self.raw(" ");
                self.print_let_binding(only);
                return true;
            }
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
            Binder::Record(fields) => {
                self.list(
                    "{",
                    "}",
                    Span::zero(),
                    Span::zero(),
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
                self.print_paren_block(true, |p| p.print_typ(inner));
            }
            Typ::Arr(a, b) => self.print_typ_arrow_chain(a, b),
            Typ::App(..) => {
                let (head, args) = Self::typ_app_spine(t);
                self.print_typ(head);
                // No `would_break` check here (unlike `Expr::App`'s spine,
                // see `expr_would_break`'s doc comment): the "floor" model
                // (FORMATTER.md) means a glued type-level bracket that
                // breaks hangs in place at its own column instead of
                // relocating (see `print_row`/`print_paren_block`), so a
                // `Typ` argument that would break is never itself a reason
                // to move it, or its successors, onto a fresh line - only a
                // real source break is.
                self.print_spine_args(
                    head.span(),
                    &args,
                    |a| a.span(),
                    |_, _| false,
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
            // See the matching note on `Typ::App` - the floor model means a
            // `Typ` arg that would break is never itself a reason to
            // relocate it or its successors.
            p.print_spine_args(
                name.span(),
                args,
                |a| a.span(),
                |_, _| false,
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
                self.raw(" :: ");
                self.print_typ(typ);
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
                self.raw(" :: ");
                self.print_typ(typ);
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
                self.print_paren_block(false, |p| p.print_expr(inner));
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
            Expr::App(..) => {
                let (head, args) = Self::app_spine(e);
                // Relocate the whole call - head included - onto its own
                // indented line whenever it's glued right after something
                // (an outer `=`, a lambda's `->`, an operator, ...) and is
                // itself going to print across multiple lines - the same
                // "would this end up looking flat-glued while what follows
                // it drops down" concern `list()`'s own `own_indent` already
                // decides for a glued `Array`/`Record`. Real report: `x {}
                // [\na\n]` printed as `x {}\n  [ a\n  ]`, the head (`x {}`,
                // itself a single `Expr::Update` node - not two separate
                // `App` arguments) never moving down even though the array
                // it heads spans several lines. Without this, only the
                // argument that actually breaks moved (via
                // `print_spine_args`, below) - the head, and any args
                // before whatever breaks, stayed flush on the call's
                // original line.
                let mut spans = vec![head.span()];
                spans.extend(args.iter().map(|a| a.span()));
                // Check each argument's own `expr_would_break` at most once,
                // caching its already-rendered flat text when it doesn't
                // break so it can be reused directly below instead of being
                // printed a second time. This used to be two separate full
                // renders per argument (this check, then `print_spine_args`
                // re-checking - and, either way, re-printing - each one
                // again) - cheap in isolation, but since an argument can
                // itself be a call with its own arguments, that doubling
                // recurses: `O(2^depth)` instead of `O(depth)` for a chain
                // of calls each wrapping the next (`Ctor { field: [ Ctor
                // { ... } ] }`, ~15 levels, no forced breaks anywhere - a
                // real report that never finished printing). Same fix as
                // `list()`'s own version of this (see its comment).
                let arg_texts: Vec<Option<String>> = args
                    .iter()
                    .map(|a| {
                        let comment_idx_before = self.comment_idx;
                        let text = self.render_indented(0, |p| p.print_expr(a));
                        if text.contains('\n') {
                            self.comment_idx = comment_idx_before;
                            None
                        } else {
                            Some(text)
                        }
                    })
                    .collect();
                let multiline = Self::any_breaks(&spans) || arg_texts.iter().any(Option::is_none);
                let own_indent = multiline && !self.at_fresh_line();
                if own_indent {
                    self.indent_in();
                    self.newline();
                }
                self.print_expr(head);
                let mut prev_span = head.span();
                let mut broke = false;
                for (a, cached) in args.iter().zip(arg_texts) {
                    let cur_span = a.span();
                    if !broke {
                        if Self::breaks_before(prev_span, cur_span) {
                            self.indent_in();
                            broke = true;
                        } else if let Some(text) = cached {
                            self.raw(" ");
                            self.raw(&text);
                            prev_span = cur_span;
                            continue;
                        } else {
                            self.indent_in();
                            broke = true;
                        }
                    }
                    if broke {
                        self.newline();
                    } else {
                        self.raw(" ");
                    }
                    self.print_expr(a);
                    prev_span = cur_span;
                }
                if broke {
                    self.indent_out();
                }
                if own_indent {
                    self.indent_out();
                }
            }
            Expr::Vta(f, t) => {
                self.print_expr(f);
                self.raw(" @");
                self.print_typ(t);
            }
            Expr::Op(..) => {
                let (first, rest) = Self::op_spine(e);
                let mut spans = vec![first.span()];
                spans.extend(rest.iter().map(|(_, r)| r.span()));
                let multiline = Self::any_breaks(&spans);
                self.print_expr(first);
                if multiline {
                    self.indent_in();
                    for (op, r) in &rest {
                        self.newline();
                        self.lit(*op);
                        self.raw(" ");
                        // Unconditional hang, same reasoning as
                        // `print_record_field_rhs`: an operand is glued
                        // directly after its operator, so if the operand
                        // itself breaks (an `App` call, a `case`), that
                        // break needs to land one level deeper than the
                        // chain's own continuation, not at the same level -
                        // invisible when the operand prints flat.
                        self.indent_in();
                        self.print_expr(r);
                        self.indent_out();
                    }
                    self.indent_out();
                } else {
                    for (op, r) in &rest {
                        self.raw(" ");
                        self.lit(*op);
                        self.raw(" ");
                        self.indent_in();
                        self.print_expr(r);
                        self.indent_out();
                    }
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
                for (i, b) in binders.iter().enumerate() {
                    if i > 0 {
                        self.raw(" ");
                    }
                    self.print_binder(b);
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
                self.raw(" ");
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
            }
            Expr::Do(qual, _, stmts) => {
                if let Some(q) = qual {
                    self.print_qual(q);
                }
                self.raw("do");
                self.print_indented_siblings(stmts, |s| s.span(), |p, s| p.print_do_stmt(s));
            }
            Expr::Ado(qual, _, stmts, result) => {
                if let Some(q) = qual {
                    self.print_qual(q);
                }
                self.raw("ado");
                self.indent_in();
                self.print_siblings_body(stmts, |s| s.span(), |p, s| p.print_do_stmt(s));
                self.newline();
                self.raw("in ");
                self.print_expr(result);
                self.indent_out();
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
            Expr::Case(_, scrutinees, branches) => {
                self.raw("case ");
                for (i, s) in scrutinees.iter().enumerate() {
                    if i > 0 {
                        self.raw(", ");
                    }
                    self.print_expr(s);
                }
                self.raw(" of");
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
        let src = "module Foo where\n\nfoo = [a b, c\n d]\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\nfoo =\n  [ a b\n  ,\n      c\n        d\n  ]\n");
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

    /// Real report: a call whose first argument stays glued (`x {}` - a
    /// single `Expr::Update` node with zero updates, not a separate `App`
    /// argument) followed by one that breaks (`[\na\n]`) needs the *whole*
    /// call to relocate, not just the argument that broke - `own_indent`'s
    /// job at every level, `App` included.
    #[test]
    fn app_relocates_when_a_later_glued_argument_would_break() {
        let src = "module Foo where\n\na = x {} [\na\n]\n";
        let out = fmt(src);
        assert_eq!(out, "module Foo where\n\na =\n  x {}\n    [ a\n    ]\n");
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
        // instead of gluing its head right after `label:` - and needs two
        // levels past `columnIn`'s own row, not one (see
        // `print_record_field_rhs`'s doc comment): one level alone puts
        // `List.singleton` flush with `columnIn`'s own column instead of
        // visibly nested under it, since `{ `/`columnIn:` are each exactly
        // `INDENT` wide.
        let src = "module Foo where\n\nf x =\n  update\n    { columnIn:\n        List.singleton\n          (Kanon.columnIn @\"type\" (relevantTypes # NonEmptyArray.map TransactionType.toStorageString))\n    , changedColumns: List.singleton (Kanon.changedColumn @\"status\")\n    }\n    tableTransaction\n";
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
        let src = "module Foo where\n\nempty\n  :: forall a b\n   . Union a\n       ( balance :: Maybe StarBuck.StarBuck\n       , currency :: Currency\n       )\n       b\n  => Record b\nempty = x\n";
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
            "module Foo where\n\nf\n  :: Array\n       { from :: TransactionId\n       , to :: TransactionId\n       }\nf = x\n";
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
            "linkBraids\n",
            "  :: Array\n",
            "       { transaction :: TransactionId\n",
            "       , braid :: BraidId.BraidId\n",
            "       }\n",
            "  -> Ctx _ _ Unit\n",
            "linkBraids = linkBraidsSql >>> KanonCtx.runSql\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// The same missing hang, reached through `print_sig_typ`'s own
    /// `needs_hang` branch directly (no arrow chain involved) rather than
    /// through `print_typ_arrow_chain` - a `Typ::App` whose own argument is a
    /// `Typ::Paren`-wrapped operator chain, glued after `:: `. `needs_hang`
    /// hangs under `Kanon.Table`'s own real column (`hang_glued`) rather
    /// than approximating with a level bump off the ambient baseline - see
    /// "Session: the 'floor' model" in FORMATTER.md for why the earlier,
    /// level-based version of this landed one column short.
    #[test]
    fn typ_app_paren_op_chain_directly_after_a_broken_sig_gets_an_extra_hang_level() {
        let src = concat!(
            "module Foo where\n\n",
            "tableTransactionLinkBraid\n",
            "  :: Kanon.Table\n",
            "       ( Kanon.Pk (\"transaction\" .. \"braid\")\n",
            "           .. Kanon.Index \"braid\"\n",
            "           .. Kanon.Name \"transaction_link_braid_v0\"\n",
            "       )\n",
            "       TransactionLinkBraidR\n",
            "tableTransactionLinkBraid = Kanon.table @\"transaction_link_braid_v0\"\n",
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
    /// continuation (`.. Kanon.Index`) gets its own hang level past the `( `
    /// it's glued to - see `typ_op_chain_gets_its_own_hang_when_not_in_a_broken_sig`
    /// - while the flat, nested `("company_id" .. "type")` stays untouched.
    #[test]
    fn broken_type_alias_does_not_force_a_flat_nested_paren_to_expand() {
        let src = concat!(
            "module Foo where\n\n",
            "type Table =\n",
            "  Kanon.Table\n",
            "    ( Kanon.Pk \"id\"\n",
            "        .. Kanon.Index (\"company_id\" .. \"type\")\n",
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
    /// always does - without it, `.. Kanon.Index`/`.. Kanon.Name` land flush
    /// with `Kanon.Pk`, one level shallower than they should (only as deep as
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
            "  Endpoint\n",
            "    ( Kanon.Pk \"key\"\n",
            "        .. Kanon.Index \"transaction\"\n",
            "        .. Kanon.Name \"transaction_link_idempotency_v0\"\n",
            "    )\n",
            "    TransactionLinkIdempotencyR\n",
        );
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// Parser regression test: `Kanon.Pk ("key")` used to lose `"key"`
    /// entirely, printing `Kanon.Pk ()`. Root cause was in `row_label`, not
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
            "tableTransactionLinkIdempotency\n",
            "  :: Kanon.Table\n",
            "       ( Kanon.Pk (\"key\")\n",
            "           .. Kanon.Index \"transaction\"\n",
            "           .. Kanon.Name \"transaction_link_idempotency_v0\"\n",
            "       )\n",
            "       TransactionLinkIdempotencyR\n",
            "tableTransactionLinkIdempotency = x\n",
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
        let src = "module Foo where\n\ntype Table = Kanon.Table (Kanon.Pk \"id\" .. Kanon.Index (\"company_id\" .. \"type\")) Row\n";
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
    /// on to break. `print_row` used to treat "not at a fresh line" (glued
    /// right after `=> `/`-> `) as a reason to relocate its own `{` onto a
    /// deeper line (`indent_in` + `newline` before printing `open`) - so
    /// `=>`/`->` ended up alone on their own line with the record moved two
    /// levels below them, instead of staying glued with the record's own
    /// fields hanging under its real column. Real report: a `Kanon.Pack`
    /// constraint whose own two args correctly move to their own lines (an
    /// `App`-argument break, unrelated and unaffected by this fix, though
    /// also since made column-exact rather than a level approximation - see
    /// `typ_app_directly_after_a_broken_sig_gets_an_extra_hang_level`), but
    /// whose *constrained-chain body* (`=> { ... }`, then `-> { ... }`) kept
    /// getting relocated.
    #[test]
    fn typ_record_glued_after_a_broken_sig_hangs_in_place_instead_of_moving_down() {
        let src = concat!(
            "module Foo where\n\n",
            "unpack\n",
            "  :: forall unpacked packed\n",
            "   . Lacks \"type_index\" packed\n",
            "  => Kanon.Pack\n",
            "       { balance :: Maybe StarBuck.StarBuck\n",
            "       | unpacked\n",
            "       }\n",
            "       { date_transaction :: Maybe ExDate\n",
            "       , type :: TransactionType\n",
            "       | packed\n",
            "       }\n",
            "  => { date_transaction :: Maybe ExDate\n",
            "     , type :: TransactionType\n",
            "     , type_index :: Int\n",
            "     | packed\n",
            "     }\n",
            "  -> { balance :: Maybe StarBuck.StarBuck\n",
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
    /// its own continuation one level too shallow - `# Button.isFullwidth`
    /// landed flush with `Button.create`'s own column instead of visibly
    /// past it, since `[ `/`, ` are exactly `INDENT` wide (see `list()`'s
    /// `item_hang` and its doc comment). Unlike `multiline_operator_chain_stays_expanded`
    /// above (glued after a declaration's own `=`, which is a genuine
    /// "floor" - nothing else competes with it at that column), a list item
    /// needs the extra level so it isn't mistaken for a sibling item at the
    /// list's own comma column.
    #[test]
    fn array_item_operator_chain_hangs_past_its_own_head() {
        let src = concat!(
            "module Foo where\n\n",
            "buttons =\n",
            "  [ Button.create { onclick: ClickedHideModal false, children: [ Html.text \"Avbryt\" ] }\n",
            "      # Button.isFullwidth true\n",
            "      # Button.toHtml\n",
            "  , Button.create { onclick: initiatedMsg, children: [ Html.text \"Klar\" ] }\n",
            "      # Button.isPrimary\n",
            "      # Button.isFullwidth true\n",
            "      # Button.toHtml\n",
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
        // itself (`List.map (...)`) also relocates off `#` onto its own
        // line first, same as it would off `=` - it's glued right after an
        // operator and ends up printing across multiple lines.
        let src = "module Foo where\n\nf rs =\n  rs\n    #\n        List.map\n          ( \\r ->\n              r\n                # empty\n          )\n    # List.toArray\n";
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
}

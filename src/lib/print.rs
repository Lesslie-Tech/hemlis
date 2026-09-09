//! A PureScript pretty-printer.
//!
//! Skeleton: unimplemented constructs fall back to slicing the original
//! source text for that node's span, so printing never panics or drops
//! content. Layout (one-line vs. expanded) is decided eagerly from source
//! spans - if a list's first/last element don't start/end on the same
//! source line, it prints expanded. No line-fitting/backtracking.

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
    /// Byte offset of the start of each source line, precomputed - avoids an
    /// O(source_len) rescan on every leaf node's `text()`/`lit()` call.
    line_starts: Vec<usize>,
    comments: &'s [SourceToken<'s>],
    comment_idx: usize,
    out: String,
    indent: usize,
    /// Set while printing an already-expanded signature type (see
    /// `print_sig_typ`), so a nested forall/constraint/arrow chain breaks
    /// all its `.`/`=>`/`->` to one indent level instead of staircasing.
    in_broken_sig: bool,
    /// Byte offset in `out` marking a glue point an outer construct already
    /// committed to (e.g. after `open `/`, `, or after an Op chain's own
    /// operator newline) - a nested construct's relocation check
    /// (`own_indent`-style) reads this to avoid double-indenting on top of
    /// a floor the outer construct already established (see FORMATTER.md).
    /// Only valid while `out.len()` still matches the recorded offset;
    /// once something else has been glued in front, ordinary relocation
    /// resumes.
    glued_floor: Option<usize>,
    /// True screen column corresponding to `out`'s own position 0, for as
    /// long as `out` holds no `\n` yet - `current_column()`'s char count
    /// alone is only the real column for the top-level buffer (which starts
    /// at column 0); a scratch buffer swapped in by `render_at_column`/
    /// `render_indented` starts empty but virtually continues from wherever
    /// printing had reached before the swap, which this remembers. Once a
    /// real `\n` lands in `out`, its own written indent makes this moot.
    out_floor: usize,
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
            out_floor: 0,
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

    /// Column of wherever printing continues on the current line. At a
    /// fresh line this is `out_floor` (usually 0, or a scratch buffer's
    /// virtual starting column); mid-line (something glued after
    /// `:: `/`-> `/etc.) it's that plus the real width printed since.
    fn current_column(&self) -> usize {
        match self.out.rfind('\n') {
            Some(i) => self.out[i + 1..].chars().count(),
            None => self.out_floor + self.out.chars().count(),
        }
    }

    /// Runs `f` with the indent baseline set to `col` (not necessarily a
    /// multiple of `INDENT`), restoring the previous baseline after.
    fn with_indent_at<R>(&mut self, col: usize, f: impl FnOnce(&mut Self) -> R) -> R {
        let saved = self.indent;
        self.indent = col;
        let r = f(self);
        self.indent = saved;
        r
    }

    /// `with_indent_at(current_column(), f)` for printing something glued
    /// right after a prefix like `:: `/`-> `/`=> `, so a later `indent_in`
    /// inside `f` lines up under the glued text instead of the stale
    /// ambient indent. Call immediately before `f` prints anything.
    fn hang_glued<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        let col = self.current_column();
        self.with_indent_at(col, f)
    }

    /// Break to a new line at the current indent. Reuses an already-fresh
    /// line instead of adding a blank one, so back-to-back `newline()`
    /// calls never insert a blank line by accident (a deliberate blank
    /// line is written directly via `raw("\n")`).
    fn newline(&mut self) {
        let trimmed_len = self.out.trim_end_matches(' ').len();
        if self.at_fresh_line() {
            return;
        }
        self.out.truncate(trimmed_len);
        self.out.push('\n');
        for _ in 0..self.indent {
            self.out.push(' ');
        }
    }

    /// Like `newline()`, but forces the line to have exactly `col` spaces of
    /// indent even if we're already at a fresh line - `newline()`'s no-op
    /// short-circuit trusts an existing fresh line's width, which is wrong
    /// right after something (e.g. `flush_comments_before`) left one at a
    /// different indent than `col`.
    fn realign_to(&mut self, col: usize) {
        let trimmed = self.out.trim_end_matches(' ').len();
        self.out.truncate(trimmed);
        if !self.out.is_empty() && !self.out.ends_with('\n') {
            self.out.push('\n');
        }
        for _ in 0..col {
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

    /// Insert a blank line before whatever prints next (call right after
    /// `newline()`); trims the just-written indent so the blank line has no
    /// trailing whitespace, then re-writes it for the following line.
    fn insert_blank_line(&mut self) {
        let trimmed = self.out.trim_end_matches(' ').len();
        self.out.truncate(trimmed);
        self.raw("\n");
        self.write_indent();
    }

    /// Renders `print_inner` in isolation (into a scratch buffer, `levels`
    /// indents deeper) without touching the real output - lets a layout
    /// decision inspect what a subexpression would look like first.
    fn render_indented(&mut self, levels: usize, print_inner: impl FnOnce(&mut Self)) -> String {
        let saved = std::mem::take(&mut self.out);
        for _ in 0..levels {
            self.indent_in();
        }
        let saved_floor = std::mem::replace(&mut self.out_floor, self.indent);
        print_inner(self);
        self.out_floor = saved_floor;
        for _ in 0..levels {
            self.indent_out();
        }
        std::mem::replace(&mut self.out, saved)
    }

    /// `render_indented`'s counterpart for an exact column (see
    /// `with_indent_at`), used by `print_paren_block` for a glued `(`.
    fn render_at_column(&mut self, col: usize, print_inner: impl FnOnce(&mut Self)) -> String {
        let saved = std::mem::take(&mut self.out);
        let saved_floor = std::mem::replace(&mut self.out_floor, col);
        self.with_indent_at(col, print_inner);
        self.out_floor = saved_floor;
        std::mem::replace(&mut self.out, saved)
    }

    /// True if `e` is an `Expr::Paren` that would print in the `( ` ...
    /// `)`-on-its-own-line block style at the current indent - rendered
    /// into a scratch buffer rather than checked via spans (see
    /// `print_arrow_rhs`). Callers glue something in front of `e` (an
    /// arrow, an `in`) and use this to break before `e` instead, so its
    /// closing `)` doesn't look like it "moved back" past what precedes it.
    fn paren_would_break(&mut self, e: &Expr) -> bool {
        matches!(e, Expr::Paren(..)) && self.expr_would_break(e)
    }

    /// True if `e` is a `case`/`do`/`ado`/`let` block that would print
    /// multi-line - used like `paren_would_break` (see `print_arrow_rhs`).
    /// `let`/`ado` can still print flat when trivial enough, which
    /// `expr_would_break` already accounts for.
    fn keyword_block_would_break(&mut self, e: &Expr) -> bool {
        matches!(e, Expr::Case(..) | Expr::Do(..) | Expr::Ado(..) | Expr::Let(..))
            && self.expr_would_break(e)
    }

    /// True if `e` is an `Expr::Op` chain that would print multi-line -
    /// relocates it off a glued arrow/`=`, same as `paren_would_break`/
    /// `keyword_block_would_break` (see `print_arrow_rhs`). The chain still
    /// decides *where within itself* to break (`glued_floor`); this only
    /// stops its first operand from staying glued to the arrow.
    fn op_chain_would_break(&mut self, e: &Expr) -> bool {
        matches!(e, Expr::Op(..)) && self.expr_would_break(e)
    }

    /// True if printing `e` at the current indent produces any line break,
    /// regardless of node kind - used where only whether it breaks matters,
    /// not why (see `print_spine_args`'s `would_break` callback).
    fn expr_would_break(&mut self, e: &Expr) -> bool {
        let comment_idx_before = self.comment_idx;
        let would_break = self.render_indented(0, |p| p.print_expr(e)).contains('\n');
        self.comment_idx = comment_idx_before;
        would_break
    }

    /// `expr_would_break` for `Binder`s - used by `print_spine_args` so a
    /// binder that would print multi-line forces itself and later binders
    /// onto their own lines.
    fn binder_would_break(&mut self, b: &Binder) -> bool {
        let comment_idx_before = self.comment_idx;
        let would_break = self.render_indented(0, |p| p.print_binder(b)).contains('\n');
        self.comment_idx = comment_idx_before;
        would_break
    }

    /// `paren_would_break` for `Typ::Paren`.
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
    /// block style when `inner` would print multi-line, or `force_block`
    /// says the source had a break right after `(`/before `)`. Shared by
    /// `Expr::Paren` and `Typ::Paren`.
    ///
    /// - Block-style is decided by rendering `inner` into a scratch buffer
    ///   and checking for a line break, not by comparing spans - `inner`
    ///   can contain a `case`/`do`/`let` that always breaks regardless of
    ///   source layout, which would make a span check flip between passes.
    /// - `force_block` (`Expr::Paren` only; `Typ::Paren` always passes
    ///   `false`) preserves a source break the content alone wouldn't ask
    ///   for. Safe to OR in without reintroducing pass-to-pass
    ///   instability: once block style is chosen, `)` always lands on its
    ///   own line, so the same source gap stays true on later passes.
    /// - `(` is always glued in place, never relocated - that would change
    ///   its own source position and flip `Expr::App`'s span-based
    ///   multiline decision on the next pass. Breaking the glued token
    ///   instead is the caller's job (see `print_arrow_rhs`).
    /// - `is_typ` picks the hang once `inner` prints as a block: a type
    ///   hangs under the exact column after `( ` (a type-level arrow/`::`
    ///   never relocates, so this must account for the glued prefix's real
    ///   width); an expr just hangs one level deeper as usual.
    fn print_paren_block(&mut self, force_block: bool, close: Span, print_inner: impl FnOnce(&mut Self)) {
        // A paren is its own bracketed context - reset so it doesn't inherit
        // an enclosing broken-signature's forced expansion (see `print_row`).
        let outer_in_broken_sig = self.in_broken_sig;
        self.in_broken_sig = false;
        // Same "floor" model as `print_row`: hang the body/closing paren
        // under this paren's own real column, not an indent-level approximation.
        let open_col = self.current_column();
        let inner_text = self.render_at_column(open_col + 2, print_inner);
        self.in_broken_sig = outer_in_broken_sig;
        let has_comment_before_close =
            self.comments.get(self.comment_idx).is_some_and(|(_, s)| s.lo().0 < close.lo().0);
        self.raw("(");
        if inner_text.contains('\n') || force_block || has_comment_before_close {
            self.raw(" ");
            self.raw(&inner_text);
            if has_comment_before_close {
                let hang_col = inner_text
                    .rsplit('\n')
                    .next()
                    .map(|l| l.len() - l.trim_start().len())
                    .unwrap_or(open_col);
                self.with_indent_at(hang_col, |p| p.flush_comments_before(close.lo().0));
            }
            self.realign_to(open_col);
        } else {
            self.raw(&inner_text);
        }
        self.raw(")");
    }

    fn text(&self, span: Span) -> &'s str {
        source_text_with_starts(self.source, &self.line_starts, &span).unwrap_or("")
    }

    /// Print a leaf AST node by slicing its span out of the source verbatim.
    fn lit<T: Ast>(&mut self, x: &T) {
        let t = self.text(x.span());
        self.raw(t);
    }

    /// Last-resort fallback: print the original source text verbatim.
    fn raw_fallback<T: Ast>(&mut self, x: &T) {
        self.lit(x);
    }

    /// A qualifier used standalone (e.g. `A.` before `do`/`ado`). `Qual`'s
    /// span excludes the trailing `.`, so it's added back explicitly.
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
            // itself otherwise.
            let next_line = match self.comments.get(self.comment_idx) {
                Some((_, s)) if s.lo().0 < line => s.lo().0,
                _ => line,
            };
            if next_line > hi + 1 {
                self.insert_blank_line();
            }
        }
    }

    /// `flush_comments_before`, for a boundary keyword with no span of its
    /// own (`in`, after a `let`/`ado` bindings block) - `line` is only an
    /// upper bound (the following expression's line), not the keyword's
    /// actual line, so unlike `flush_comments_before` this never inserts a
    /// blank line after the last flushed comment (still preserved between
    /// two comments, where both positions are real).
    fn flush_comments_before_keyword(&mut self, line: usize) {
        while self.comment_idx < self.comments.len() {
            let (_, span) = &self.comments[self.comment_idx];
            if span.lo().0 >= line {
                break;
            }
            let hi = span.hi().0;
            self.emit_pending_comment();
            if let Some((_, s)) = self.comments.get(self.comment_idx)
                && s.lo().0 < line
                && s.lo().0 > hi + 1
            {
                self.insert_blank_line();
            }
        }
    }

    /// The source line a boundary keyword with no span of its own (`in`,
    /// after a `let`/`do`/`ado` bindings block) actually sits on - needed to
    /// split `flush_comments_before_keyword`'s callers so a comment
    /// *trailing* the keyword (a leading comment on the body) isn't also
    /// swept up and printed before it. The grammar guarantees the gap
    /// between `after_line` (the last binding's own end) and `before_line`
    /// (the body's first line) holds only whitespace, comments (already
    /// known via `self.comments`), and exactly one `in` token - so the
    /// first line in that gap which is neither blank nor a pending
    /// comment's own line must be it.
    fn keyword_line(&self, after_line: usize, before_line: usize) -> usize {
        let mut line = after_line + 1;
        let mut idx = self.comment_idx;
        while line < before_line {
            if idx < self.comments.len() && self.comments[idx].1.lo().0 == line {
                line = self.comments[idx].1.hi().0 + 1;
                idx += 1;
                continue;
            }
            let start = match self.line_starts.get(line) {
                Some(s) => *s,
                None => break,
            };
            let end = self.line_starts.get(line + 1).copied().unwrap_or(self.source.len());
            if !self.source[start..end].trim().is_empty() {
                return line;
            }
            line += 1;
        }
        before_line
    }

    /// The line whatever prints next for `before_line` actually starts on:
    /// a leading pending comment's line if any, else `before_line` itself.
    fn next_visible_line(&self, before_line: usize) -> usize {
        match self.comments.get(self.comment_idx) {
            Some((_, span)) if span.lo().0 < before_line => span.lo().0,
            _ => before_line,
        }
    }

    /// If the next pending comment starts on `hi_line` (where whatever was
    /// just printed ended), it's trailing (`foo = 1 -- like this`) - glue it
    /// onto the current line instead of leaving it for
    /// `flush_comments_before`. No-op otherwise. Returns whether a comment
    /// was flushed, since that ends the current line even with no source
    /// span gap - callers like `Expr::Op`'s operand loop need to know their
    /// next item can't stay glued after it.
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
        // A `--` comment swallows everything up to the next line break;
        // without this, whatever prints next would silently join it.
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
    /// start of `b`. Deliberately a local adjacent-boundary check, not an
    /// overall first-to-last span comparison - a neighbor forced multiline
    /// by its own content (e.g. a nested `case`/`do`) would otherwise
    /// "infect" this pair on a later pass, breaking idempotence.
    fn breaks_before(a: Span, b: Span) -> bool {
        a.hi().0 != b.lo().0
    }

    /// True if any adjacent pair in `spans` has a line break between them
    /// (see `breaks_before`) - decides whether a chain/list prints expanded.
    fn any_breaks(spans: &[Span]) -> bool {
        spans.windows(2).any(|w| Self::breaks_before(w[0], w[1]))
    }

    /// Flattens a curried `App(App(App(f, a1), a2), a3)` chain into
    /// `(f, [a1, a2, a3])` so `Expr::App` decides multiline-ness for the
    /// whole call at once (like `list()` does for bracketed items) instead
    /// of each binary `App` node deciding in isolation.
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

    /// Flattens a same-precedence run of an `Op` tree (whatever nesting
    /// shape precedence climbing produced) into the flat in-order sequence
    /// `(a, [(op1, b), (op2, c)])`. A child `Op` at a *different* precedence
    /// is left as a single atomic operand, printed later via its own
    /// recursive `Expr::Op` call so it makes its own multiline decision.
    /// Needed like `app_spine`: printing each binary node independently
    /// would nest one `indent_in` per operator whenever the tree leans the
    /// "wrong" way for its associativity (e.g. right-associative `<>`),
    /// drifting one level deeper per operator instead of lining up flush.
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

    /// The `Typ` counterpart of `op_spine`. Type operators always parse
    /// left-associative, so this doesn't need the stacked-indent fix
    /// `op_spine` exists for, but still flattens for one shared multiline
    /// decision across the chain.
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

    /// Prints `args` glued after `first_span` with a leading space each,
    /// until one has a real source break before it or would itself print
    /// multiline (`would_break`) - that argument and every later one then
    /// print one-per-line at a shared indent level.
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
                let just_flushed_comment = self.flush_trailing_comment(prev_span.hi().0);
                if !just_flushed_comment {
                    self.newline();
                }
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

    /// Whether `print_ctor_args` would break `cargs` onto their own lines -
    /// same condition as its loop, without the printing side effects, so a
    /// caller (`Decl::Data`'s single-ctor `multiline` check) can decide
    /// whether to relocate `= Ctor` itself before any printing happens.
    fn ctor_args_would_break(&mut self, cname_span: Span, cargs: &[Typ]) -> bool {
        let mut prev_span = cname_span;
        for a in cargs {
            let cur_span = a.span();
            if Self::breaks_before(prev_span, cur_span) || self.typ_would_break(a) {
                return true;
            }
            prev_span = cur_span;
        }
        false
    }

    /// `print_spine_args` for a data constructor's argument types, but two
    /// indent levels deep - `= `/`| ` are exactly `INDENT` wide, so one
    /// level alone would look like a continuation of `cname`'s own column
    /// rather than nesting under it.
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
                let just_flushed_comment = self.flush_trailing_comment(prev_span.hi().0);
                if !just_flushed_comment {
                    self.newline();
                }
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

    /// `print_spine_args` for `Expr::App`, but decides "doesn't fit flat" by
    /// trying each argument directly in the real output and rolling back if
    /// it breaks, instead of pre-rendering into a scratch buffer - the
    /// scratch-buffer approach is O(2^depth) once an argument can itself be
    /// a call needing the same decision (a real deeply-nested file used to
    /// hang on this).
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
            let just_flushed_comment = self.flush_trailing_comment(prev_span.hi().0);
            if !just_flushed_comment {
                self.newline();
            }
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
        // Both branches must produce the same shape (`::` glued to `typ` on
        // its own line) or this wouldn't be a stable fixed point on reformat.
        if Self::breaks_before(before, typ.span()) || self.typ_paren_would_break(typ) {
            self.indent_in();
            self.newline();
            self.raw(":: ");
            let outer = self.in_broken_sig;
            self.in_broken_sig = true;
            // Hang App/Record/Row under `typ`'s own column after the glued
            // `:: ` (see print_constraint); an operator-chain shape must
            // stay at the ambient level instead (print_typ_arrow_chain).
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

    /// The `type X = Typ` counterpart of `print_sig_typ` - a type alias's
    /// `=` breaks the same way a signature's `::` does.
    fn print_typ_alias_rhs(&mut self, before: Span, typ: &Typ) {
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

    /// A record/row field's `label :: Typ` - unlike `print_sig_typ`, the
    /// `::` stays glued to the label; only `typ` relocates when it would
    /// break.
    fn print_field_typ(&mut self, before: Span, typ: &Typ) {
        if Self::breaks_before(before, typ.span()) || self.typ_would_break(typ) {
            self.raw(" ::");
            // Two levels, not one: `label ::`/`, ` is exactly `INDENT` wide,
            // so one level would land flush with the label instead of past it.
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

    /// Print `items` as `open item, item, item close`, or one per line with
    /// leading commas if the source had them expanded:
    /// ```text
    /// open item
    /// , item
    /// close
    /// ```
    /// `pad` adds a space inside the brackets on the flat path (`{ a: 1 }`
    /// vs `[1, 2]`); the expanded path is always padded. `open_span`/
    /// `close_span` are the brackets' spans, or `Span::zero()` if the
    /// caller has none (e.g. export/import lists) - used to catch a source
    /// break with zero/one items, and to flush a trailing comment before
    /// `close`. `item_hang` adds one indent level per item in the expanded
    /// path, for an item that's itself a nesting shape (e.g. an operator
    /// chain glued after `open `/`, `) that would otherwise look flush
    /// instead of nested; pass `false` when the item printer already
    /// handles this itself.
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
        // A source break can also sit between `open`/first item or last
        // item/`close`, the only way to see one at all with 0-1 items -
        // fold open_span/close_span into the same boundary chain.
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
            // An item with no source break can still print multiline on its
            // own (a breaking App/operator chain), which should expand the
            // whole list too. Decided by writing the flat attempt directly
            // into the real output and checking after the fact for a '\n',
            // then rolling back to `mark` on failure - pre-rendering every
            // item into a scratch buffer instead would recurse into nested
            // Array/Record items and go O(2^depth) (a real deeply-nested
            // flat literal used to hang on that).
            let mark = self.out.len();
            let comment_idx_before = self.comment_idx;
            // No `flush_trailing_comment` here (unlike the multiline branch):
            // with several items sharing a line, an earlier item could
            // wrongly claim a comment trailing a later item or the bracket.
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

        // Reached either because the source already forced this, or because
        // the flat attempt just rolled back.
        {
            // A comment fully preceding `open` (its own line above, not
            // sharing `open`'s line at all) must print before `open` at the
            // ambient indent - see `print_row`'s identical fix. Flushing it
            // only once the first item's own `flush_comments_before` ran
            // (further down) would leave `open` stranded alone on a line
            // with nothing hung under it, since `self.indent` isn't raised
            // to `open`'s column until after this.
            if open_span != Span::zero() {
                self.flush_comments_before(open_span.lo().0);
            }
            // If an outer construct already broke to a fresh line before this
            // call, don't also bump our own indent level - only take a level
            // when we're the one initiating the break, else items end up one
            // level too deep. Unlike print_row, a glued value-level list does
            // relocate its opening bracket down a level (see FORMATTER.md's
            // "floor" model) - except when this list sits exactly at a floor
            // an outer list() already committed to (`glued_floor`), e.g. a
            // sole/first item like `[ { c: 1\n, d: 2\n} ]`, where relocating
            // would double up on the outer list's own settled layout.
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
            // A comment can trail `open` itself (`[ -- size` before the first
            // item, with nothing else sharing that line) - glue it right
            // there instead of letting the first item's own
            // `flush_comments_before` strand it unindented on its own line
            // with no memory of `open`'s column. Guarded to only the item's
            // own line matching a lone `open`, since a comment on a line
            // `open` shares with the first item's own content (a flat-glued
            // attempt) belongs to that item instead.
            let open_alone_on_its_line = open_span != Span::zero()
                && items.first().is_some_and(|it| span_of(it).lo().0 > open_span.hi().0);
            let comment_after_open =
                open_alone_on_its_line && self.flush_trailing_comment(open_span.hi().0);
            if !comment_after_open {
                self.raw(" ");
            }
            for (i, item) in items.iter().enumerate() {
                let extra_hang = i == 0 && comment_after_open;
                if i > 0 {
                    self.newline();
                } else if extra_hang {
                    self.indent_in();
                    self.realign_to(self.indent);
                }
                // Flush before the leading comma, not after - a comment
                // belongs above the `, item` pair, not stranding the comma
                // alone ahead of it.
                self.flush_comments_before(span_of(item).lo().0);
                if i > 0 {
                    self.raw(", ");
                }
                // An item glued after `open `/`, ` needs one extra indent
                // level if it breaks further (e.g. an operator chain), or it
                // looks flush with its own head instead of nested under it.
                // Skipped when the item printer already manages this itself.
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
                // Each item is always the last thing on its own line here, so
                // it's safe to check for a trailing comment - without this, a
                // comment trailing the last item had nowhere to flush before
                // the closing bracket and could relocate into unrelated code.
                self.flush_trailing_comment(span_of(item).hi().0);
                if extra_hang {
                    self.indent_out();
                }
            }
            // Catches a comment on its own line before the close, which
            // flush_trailing_comment above doesn't (it only catches one
            // sharing the last item's line).
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
            // print_header already forced a blank line after the export list
            // when there were no imports to absorb it - don't add a second one.
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
            // No-op for decl kinds already covered via print_guarded_expr/
            // print_indented_siblings; needed for the rest.
            self.flush_trailing_comment(decl.span().hi().0);
            self.ensure_fresh_line();
            prev = Some(decl);
            prev_hi_line = Some(decl.span().hi().0);
        }
    }

    fn print_header(&mut self, h: &Header) {
        self.flush_comments_before(h.span().lo().0);
        let Header(name, exports, imports, _, _, exports_open, exports_close) = h;
        self.raw("module ");
        self.lit(name);
        self.raw(" ");
        if let Some(exports) = exports {
            self.list(
                "(",
                ")",
                *exports_open,
                *exports_close,
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

    /// Groups and sorts imports like purs-tidy: unqualified "open" imports
    /// form their own group first; everything else sorts alphabetically by
    /// module name (unaliased before `as`-aliased). Imports differing only
    /// in name list (same module/alias/hiding-ness) get merged.
    ///
    /// Comments inside the import block aren't reattached per-import after
    /// reordering - flushed as one batch before the block instead.
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
        let mut deduped: Vec<Import> = Vec::with_capacity(items.len());
        for item in items.drain(..) {
            match deduped.last_mut() {
                Some(last) if self.import_sort_key(last) == self.import_sort_key(&item) => {
                    match self.merge_dup_import(last, &item) {
                        Some(merged) => *last = merged,
                        None => deduped.push(item),
                    }
                }
                _ => deduped.push(item),
            }
        }
        *items = deduped;
    }

    /// Merges two imports that share a sort key (same tier and bare name), if
    /// one subsumes the other: a bare `Typ` is subsumed by any `TypDat` of the
    /// same name, and `DataMember::All` (`(..)`) subsumes an explicit
    /// constructor list. Returns `None` (keep both) for two `TypDat`s with
    /// different, non-overlapping constructor lists - merging those would
    /// attribute a made-up span to constructors from another import.
    fn merge_dup_import(&self, a: &Import, b: &Import) -> Option<Import> {
        match (a, b) {
            (Import::Typ(_, _), Import::TypDat(..)) => Some(b.clone()),
            (Import::TypDat(..), Import::Typ(_, _)) => Some(a.clone()),
            (Import::TypDat(span, name, DataMember::All(_)), Import::TypDat(..))
            | (Import::TypDat(span, name, DataMember::Some(_)), Import::TypDat(_, _, DataMember::All(_))) =>
            {
                Some(Import::TypDat(*span, *name, DataMember::All(*span)))
            }
            (Import::TypDat(span, name, DataMember::Some(a_names)), Import::TypDat(_, _, DataMember::Some(b_names))) => {
                let same_set = a_names.len() == b_names.len()
                    && a_names
                        .iter()
                        .all(|x| b_names.iter().any(|y| self.text(x.span()) == self.text(y.span())));
                same_set.then(|| Import::TypDat(*span, *name, DataMember::Some(a_names.clone())))
            }
            _ if self.text(a.span()) == self.text(b.span()) => Some(a.clone()),
            _ => None,
        }
    }

    /// Sort key: (kind tier, bare name), not just rendered text. purs-tidy
    /// ranks class < type-operator < type < value < value-operator, then
    /// alphabetically within a tier - a flat text sort can't reproduce this
    /// (e.g. `(>>=)` would sort before `bind` on raw ASCII).
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
                // `any_breaks` alone misses a lone constructor (no adjacent
                // pair to compare), so also check its own args directly -
                // otherwise `= Ctor` stays flat while its args relocate away.
                let multiline = Self::any_breaks(&ctor_spans)
                    || (ctors.len() == 1 && self.ctor_args_would_break(ctors[0].0.span(), &ctors[0].1));
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
                    self.flush_trailing_comment(ctor_spans[i].hi().0);
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
                // A newtype constructor wraps exactly one Typ (never a
                // space-separated list), so this relocates directly rather
                // than reusing print_ctor_args, but matches its visual shape.
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
                    // Two levels, matching print_ctor_args's own double
                    // indent for a relocated data-constructor argument.
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
                    // `where` glues flat unless the head printed multi-line,
                    // in which case it relocates to its own line at the same
                    // indent `=>` sits at. Checked via a rendered-output '\n'
                    // scan (like paren_would_break), not a span comparison.
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
    /// `(A, B) => `/`A => ` (or `<= ` for a class) - deciding via
    /// `any_breaks` over the constraints/brackets/`after` (whatever follows
    /// the arrow) whether to expand across multiple lines. On the multiline
    /// path everything relocates onto fresh indented lines unconditionally,
    /// for one canonical shape that's a fixed point on reformat. Returns
    /// whether it took the multiline path, so the caller knows to
    /// `indent_out` after printing what follows the arrow.
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
        // Parens around a lone constraint are optional but real source
        // information (`open`/`close` are Span::zero() only for the
        // genuinely parenless form) - print exactly what's there; removing
        // a redundant paren is style.rs's job, not the raw printer's.
        let has_parens = cs.len() > 1 || *open != Span::zero();
        if !has_parens {
            self.print_constraint(&cs[0]);
        } else if multiline {
            // Leading-comma style, matching list()'s convention.
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
        // `name` is glued after `=> `, so a multiline arg hangs under its
        // real column, not the ambient baseline (see print_constraint).
        let name_col = self.current_column();
        self.lit(name);
        self.with_indent_at(name_col, |p| {
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

    /// `before` is whatever immediately precedes `arrow`, used via
    /// `breaks_before` to decide if the RHS/guards break onto their own
    /// line. `e` is always a decl/clause/let-binding/case-branch tail
    /// (never a nested subexpression with more of the line to come, unlike
    /// a bare `print_arrow_rhs` call), so checking for a trailing comment
    /// here is safe.
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

    /// Prints one guarded clause's `guard, guard ... arrow e`. `before` is
    /// only the fallback anchor for a clause with no guards; normally the
    /// last guard is checked instead (see `print_guarded_expr`).
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

    /// The record-field counterpart of `print_arrow_rhs`: a field's value
    /// always sits at least one level deeper than the field, even when glued
    /// right after `label:`, so a nested multi-branch value stays visually
    /// inside the field. When the value relocates onto its own line, it
    /// needs two levels instead of one - `label:`/`{`/`, ` are exactly
    /// `INDENT` wide, so one level alone would land it flush with `label`.
    fn print_record_field_rhs(&mut self, before: Span, arrow: &str, e: &Expr) {
        if self.paren_would_break(e)
            || self.keyword_block_would_break(e)
            || self.op_chain_would_break(e)
            || Self::breaks_before(before, e.span())
        {
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
    /// source had a break before it - the shared pattern behind a decl's
    /// `=`, a lambda's `->`, a guarded clause's `->`/`=`, a do-statement's
    /// `<-`, and a let-pattern's `=`. Without this a multiline construct
    /// (e.g. `let ... in`) glued flat to `arrow` can land at the same
    /// column as its enclosing statement, which is invalid layout.
    ///
    /// Three cases also force a break even without a source one, when
    /// gluing `arrow` to a multi-line `e` would look wrong:
    /// - `e` is a `Paren` printing in block style (`paren_would_break`) -
    ///   gluing would put `)` back at/above `arrow`'s column, reading as
    ///   the expression having ended early.
    /// - `e` is a `case`/`do`/`ado`/`let` block that prints multi-line
    ///   (`keyword_block_would_break`) - no closing delimiter to regress,
    ///   but a glued keyword with content hanging underneath reads just as odd.
    /// - `e` is an `Op` chain that would print multi-line
    ///   (`op_chain_would_break`) - relocates even for a single break.
    ///
    /// All three render `e` and check for an actual line break rather than
    /// comparing spans, since `e` can contain a `case`/`do` that always
    /// breaks regardless of source layout. `Expr::App` and `Array`/`Record`
    /// are excluded - they already relocate internally.
    fn print_arrow_rhs(&mut self, before: Span, arrow: &str, e: &Expr) {
        if self.paren_would_break(e)
            || self.keyword_block_would_break(e)
            || self.op_chain_would_break(e)
            || Self::breaks_before(before, e.span())
        {
            self.raw(arrow.trim_end());
            self.indent_in();
            self.newline();
            self.print_expr(e);
            self.indent_out();
        } else {
            self.raw(arrow);
            self.print_expr(e);
        }
        // No trailing-comment check here (contrast print_guarded_expr):
        // this also prints Expr::Lambda's `->` and Guard::Binder's `<-`,
        // which can have more of the same line still to print afterward.
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

    /// `expr_would_break` for `LetBinding` - used by `print_let_kw_bindings`
    /// to decide if a single binding can stay glued to `let`.
    fn let_binding_would_break(&mut self, b: &LetBinding) -> bool {
        let comment_idx_before = self.comment_idx;
        let would_break = self.render_indented(0, |p| p.print_let_binding(b)).contains('\n');
        self.comment_idx = comment_idx_before;
        would_break
    }

    /// `let_binding_would_break` for `DoStmt`, used by `Expr::Ado`.
    fn do_stmt_would_break(&mut self, s: &DoStmt) -> bool {
        let comment_idx_before = self.comment_idx;
        let would_break = self.render_indented(0, |p| p.print_do_stmt(s)).contains('\n');
        self.comment_idx = comment_idx_before;
        would_break
    }

    /// Prints a `let`-block's bindings right after `let` - unlike `where`
    /// (always an indented block), a single simple binding can stay glued
    /// flat (`let a = 1`) when the source had it on `let`'s line and it
    /// wouldn't itself force a break. Returns whether it glued, so
    /// `Expr::Let` knows whether `in` can share that line too.
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

    /// `print_indented_siblings`'s body without the indent_in/indent_out
    /// pair, for a caller (`Expr::Ado`) that keeps the same indent level
    /// active across the list and something printed right after it.
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
            self.flush_trailing_comment(span_of(item).hi().0);
            prev_hi_line = Some(span_of(item).hi().0);
        }
    }

    /// Prints `items` one per line, one indent level deeper, preserving each
    /// item's own leading blank line (0 or 1) and flushing comments before
    /// it. Shared by `let`-bindings, `do`-statements, and `case` branches.
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
            Binder::Paren(open, inner, close) => {
                let force_block =
                    Self::breaks_before(*open, inner.span()) || Self::breaks_before(inner.span(), *close);
                self.print_paren_block(force_block, *close, |p| p.print_binder(inner));
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
                // Stores a parsed i64, not source text, and the negative
                // case's span covers only `-`, not the digits.
                if *neg {
                    self.raw("-");
                }
                self.raw(&i.0 .0.to_string());
            }
            Typ::Hole(h) => self.lit(h),
            Typ::Paren(_, inner, close) => {
                self.print_paren_block(false, *close, |p| p.print_typ(inner));
            }
            Typ::Arr(a, b) => self.print_typ_arrow_chain(a, b),
            Typ::App(..) => {
                let (head, args) = Self::typ_app_spine(t);
                self.print_typ(head);
                // Record/Row args hang glued under their own bracket (the
                // "floor" model); a Paren arg with internal breaks but no
                // source break before it needs the would_break treatment
                // instead, or later siblings stay glued to its closing line.
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
                // `in_broken_sig` means the enclosing signature/alias already
                // established the right column, so no extra hang is needed;
                // elsewhere (e.g. glued after a Typ::Paren's `( `) it does,
                // like Expr::Op's chain, or the continuation lands flush.
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
                self.print_row("{", "}", row.1.lo().0, row.1.hi().0, true, &row.0);
            }
            Typ::Row(row) => {
                self.print_row("(", ")", row.1.lo().0, row.1.hi().0, false, &row.0);
            }
            Typ::Error(_) => self.raw_fallback(t),
        }
    }

    fn print_typ_var_binding(&mut self, v: &TypVarBinding) {
        // The `@` marks visible-type-application; parens are driven by the
        // kind annotation instead, only syntactically required there.
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
        // Args are glued after `name`, itself glued after a fixed-width
        // token (`. `, `=> `) - hang under name's own column so a breaking
        // arg doesn't land shallower than the constraint name itself.
        let name_col = self.current_column();
        self.lit(name);
        self.with_indent_at(name_col, |p| {
            p.print_spine_args(
                name.span(),
                args,
                |a| a.span(),
                |p, a| p.typ_paren_would_break(a),
                |p, a| p.print_typ(a),
            );
        });
    }

    /// Prints `t`, hung under its own real column when `t` is a nesting
    /// shape (`App`/`Record`/`Row`) glued after a fixed-width token (`-> `,
    /// `=> `) - mirrors `print_sig_typ`'s `needs_hang` check. Not applied to
    /// `Arr`/`Op`/`Constrained`/`Forall`, which decide their own indent.
    fn print_typ_glued(&mut self, t: &Typ) {
        let needs_hang = matches!(t, Typ::App(..) | Typ::Record(..) | Typ::Row(..));
        if needs_hang {
            self.hang_glued(|p| p.print_typ(t));
        } else {
            self.print_typ(t);
        }
    }

    /// `a -> b -> c -> ...` parses as a right-nested `Typ::Arr` chain -
    /// flattened for one shared multiline decision. Unlike a value's
    /// operator chains, a broken type chain never gets its own indent level
    /// per `->`; only a non-operator break (an App arg, a Paren block)
    /// increases indent, via `print_typ_glued`.
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
        let mut prev_span = segment_spans[0];
        for (seg, &cur_span) in segments[1..].iter().zip(&segment_spans[1..]) {
            if multiline {
                let just_flushed_comment = self.flush_trailing_comment(prev_span.hi().0);
                if !just_flushed_comment {
                    self.newline();
                }
                self.flush_comments_before(cur_span.lo().0);
                self.raw("-> ");
            } else {
                self.raw(" -> ");
            }
            self.print_typ_glued(seg);
            prev_span = cur_span;
        }
    }

    /// `C1 => C2 => ... => Body` is a right-nested `Typ::Constrained` chain,
    /// flattened like `print_typ_arrow_chain` - no extra indent per `=>`.
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
        let mut prev_span = chain_spans[0];
        for (c, &cur_span) in constraints[1..].iter().zip(&chain_spans[1..]) {
            if multiline {
                let just_flushed_comment = self.flush_trailing_comment(prev_span.hi().0);
                if !just_flushed_comment {
                    self.newline();
                }
                self.flush_comments_before(cur_span.lo().0);
                self.raw("=> ");
            } else {
                self.raw(" => ");
            }
            self.print_constraint(c);
            prev_span = cur_span;
        }
        if multiline {
            let just_flushed_comment = self.flush_trailing_comment(prev_span.hi().0);
            if !just_flushed_comment {
                self.newline();
            }
            self.flush_comments_before(body.span().lo().0);
            self.raw("=> ");
        } else {
            self.raw(" => ");
        }
        self.print_typ_glued(body);
    }

    /// Prints a record/row type's `open field, field | tail close` (or the
    /// leading-comma multiline block style), mirroring `list()`'s
    /// architecture but not reusing it - a row's optional `| tail` doesn't
    /// fit `list()`'s comma-only shape. `close_line` is the closing
    /// bracket's own line.
    fn print_row(&mut self, open: &str, close: &str, open_line: usize, close_line: usize, pad: bool, row: &Row) {
        let Row(fields, tail) = row;
        if fields.is_empty() && tail.is_none() {
            self.raw(open);
            self.flush_comments_before(close_line);
            self.raw(close);
            return;
        }
        // A record's braces are their own bracketed context - a field's type
        // shouldn't inherit an enclosing broken-signature's flattening.
        let outer_in_broken_sig = self.in_broken_sig;
        self.in_broken_sig = false;

        let mut spans: Vec<Span> = fields.iter().map(|(l, t)| l.span().merge(t.span())).collect();
        if let Some(t) = tail {
            spans.push(t.span());
        }
        // `any_breaks` can't see a break before `close` with only one field
        // (no adjacent pair to compare) - force block style same as
        // `Expr::Paren`'s `force_block`. Not checked on the `open` side: that
        // would flip across passes as the first field's printed line shifts,
        // breaking idempotence.
        let force_block = spans.last().is_some_and(|l| l.hi().0 != close_line);
        let multiline = force_block || Self::any_breaks(&spans);

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
            // A comment fully preceding `open` (its own line above `{`, not
            // sharing `open`'s line at all) must print before `{` at the
            // ambient ("outer") ident - flushing it after `open` (like any
            // other pending comment would, via the first field's own
            // `flush_comments_before`) would instead strand `{` alone with
            // nothing hung under it, since `self.indent` isn't raised to
            // `open`'s column until after this.
            self.flush_comments_before(open_line);
            // Hang every line from the column `open` prints at, like `list()`.
            let saved_indent = self.indent;
            self.indent = self.current_column();
            self.raw(open);
            // A comment can trail `open` itself, with nothing else sharing
            // that line - see `list()`'s identical `comment_after_open`.
            let open_alone_on_its_line =
                fields.first().is_some_and(|(l, _)| l.span().lo().0 > open_line);
            let comment_after_open =
                open_alone_on_its_line && self.flush_trailing_comment(open_line);
            if !comment_after_open {
                self.raw(" ");
            }
            for (i, (label, typ)) in fields.iter().enumerate() {
                let extra_hang = i == 0 && comment_after_open;
                if i > 0 {
                    self.newline();
                } else if extra_hang {
                    self.indent_in();
                    self.realign_to(self.indent);
                }
                // Flush before the leading comma, not after - see `list()`.
                self.flush_comments_before(label.span().lo().0);
                if i > 0 {
                    self.raw(", ");
                }
                self.lit(label);
                self.print_field_typ(label.span(), typ);
                self.flush_trailing_comment(typ.span().hi().0);
                if extra_hang {
                    self.indent_out();
                }
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
        // Unconditional flush here covers call sites with no sibling-loop of
        // their own (a let's body, a guarded clause's RHS, ...) - redundant
        // where an outer loop already flushed, but a `let` body once missed
        // its comment entirely without this.
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
            Expr::Paren(open, inner, close) => {
                let force_block =
                    Self::breaks_before(*open, inner.span()) || Self::breaks_before(inner.span(), *close);
                self.print_paren_block(force_block, *close, |p| p.print_expr(inner));
            }
            Expr::Negate(inner) => {
                self.raw("-");
                self.print_expr(inner);
            }
            Expr::Typed(inner, t) => {
                // Same `name :: Typ` convention as every other signature site.
                self.print_expr(inner);
                self.print_sig_typ(inner.span(), t);
            }
            Expr::App(..) => {
                let (head, args) = Self::app_spine(e);
                // Relocate the whole call onto its own indented line when
                // glued after something and going to break multiline - same
                // concern as `list()`'s `own_indent` for a glued
                // `Array`/`Record`. Otherwise only the breaking argument
                // moves, via `print_app_args`.
                //
                // Decided by trying flat directly in the real output first,
                // rolling back to relocate the head only if it doesn't fit -
                // same "try first, roll back on failure" trick as `list()`,
                // for the same reason (scratch-buffer probing is
                // `O(2^depth)`).
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
                // Relocate `t` to a fresh indented line rather than hanging
                // under `@`'s column - `f` may sit deep (e.g. as an App
                // argument), and hanging would inherit that depth.
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
                // Same "glue until the first forced break, then break from
                // there on at one shared indent" rule as `print_spine_args`.
                // Whether an operand would break on its own is decided by
                // trying it glued flat in the real output and rolling back on
                // failure (same reason as `list()`: a scratch-buffer probe is
                // `O(2^depth)`).
                let mut prev_span = first.span();
                let mut broke = false;
                for (op, r) in &rest {
                    let cur_span = r.span();
                    // A comment trailing `prev_span`'s line must be claimed
                    // here, once `breaks_before` confirms `prev_span` really
                    // is last on its line - otherwise `print_expr(r)`'s own
                    // unconditional flush misattaches it as leading `r`.
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
                        // Suppress a nested `own_indent`-style relocation so a
                        // self-relocating operand doesn't spuriously fail
                        // this flat attempt.
                        let prev_glued_floor = self.glued_floor;
                        self.glued_floor = Some(self.out.len());
                        // Hang under the operand's own column, not the
                        // chain's stale ambient indent (see `hang_glued`).
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
                    // A comment on its own line before the operator belongs
                    // to `op r`, not `r` alone - claim it here so it lands
                    // above the operator. No-op if already claimed above.
                    self.flush_comments_before(cur_span.lo().0);
                    // The flushes above already ended the line at the new
                    // broken indent; an extra newline() would leave a gap.
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
                    // `r` is confirmed last on its own line here (chain
                    // already broke), so a pending comment unambiguously
                    // trails it.
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
                // `target { ... }` is one atom to `App`'s spine-arg breaking,
                // which never sees the gap between `target` and `{` - so a
                // source break there has to be checked here, not the caller.
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
                // A 0-or-1-statement `ado` glued flat in the source stays
                // flat here too, like `print_let_kw_bindings` does for
                // `let` - but stricter, with no tolerance for any gap, since
                // an empty `ado` has nothing else to anchor `in` to.
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
                    let after = stmts.last().map_or(kw.hi().0, |s| s.span().hi().0);
                    let in_line = self.keyword_line(after, result.span().lo().0);
                    self.flush_comments_before_keyword(in_line);
                    self.newline();
                    self.raw("in ");
                    // A comment can also trail `in` itself, before `result` -
                    // `print_expr`'s own leading-comment flush picks it up.
                    self.print_expr(result);
                    self.indent_out();
                }
            }
            Expr::Let(kw, bindings, body) => {
                self.raw("let");
                let base_indent = self.indent;
                let glued = self.print_let_kw_bindings(*kw, bindings);
                // Only a bindings block that broke onto its own lines needs
                // `in` pushed onto a fresh line below it.
                if glued {
                    self.raw(" ");
                } else {
                    let after = bindings.last().map_or(kw.hi().0, |b| b.span().hi().0);
                    let in_line = self.keyword_line(after, body.span().lo().0);
                    self.with_indent_at(base_indent + INDENT, |p| p.flush_comments_before_keyword(in_line));
                    self.realign_to(base_indent);
                }
                self.raw("in");
                // A comment can also trail `in` itself, before `body` -
                // `print_expr`'s own leading-comment flush picks it up.
                // The parser captures no span for `in` itself: a gap of
                // exactly one line after a glued binding means body shares
                // `in`'s line; two or more means it breaks onto another.
                let multiline = !glued
                    || self.paren_would_break(body)
                    || self.keyword_block_would_break(body)
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
                // Same glued-prefix relocation as `print_arrow_rhs`/
                // `print_sig_typ`: any break among the scrutinees moves the
                // whole list onto its own indented line rather than leaving
                // `of` glued wherever the last one ends up.
                let mut spans = vec![*kw];
                spans.extend(scrutinees.iter().map(|s| s.span()));
                let multiline =
                    Self::any_breaks(&spans) || scrutinees.iter().any(|s| self.expr_would_break(s));
                // A single-branch case with no source break anywhere between
                // `case` and the branch's own body can stay flat, same as
                // everything else that only explodes because the source
                // already broke it - PureScript's layout rule requires every
                // OTHER branch to start its own line, so this can never
                // trigger for more than one branch anyway.
                if !multiline
                    && branches.len() == 1
                    && !Self::breaks_before(*spans.last().unwrap(), branches[0].span())
                {
                    let mark = self.out.len();
                    let comment_idx_before = self.comment_idx;
                    self.raw(" ");
                    for (i, s) in scrutinees.iter().enumerate() {
                        if i > 0 {
                            self.raw(", ");
                        }
                        self.print_expr(s);
                    }
                    self.raw(" of ");
                    self.print_case_branch(&branches[0]);
                    if !self.out[mark..].contains('\n') {
                        return;
                    }
                    self.out.truncate(mark);
                    self.comment_idx = comment_idx_before;
                }
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
            // No trailing-comment check needed here - `print_siblings_body`
            // (the only caller) already does it per statement.
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
    use indoc::indoc;

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

    /// A comment fully preceding `{` (its own line above, not sharing `{`'s
    /// line at all) used to only get flushed once the first field's own
    /// `flush_comments_before` ran - by then `self.indent` had already been
    /// raised to `{`'s column, so `{` was left stranded alone on a line with
    /// nothing hung under it instead of staying glued to the first field.
    #[test]
    fn typ_record_comment_fully_before_open_brace_stays_above_it() {
        let src = indoc! {"
            module Foo where

            type Response =
              -- explanation comment
              { \"DocumentType\" :: Int -- inline
              , count :: Int
              }
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// `list()`'s counterpart to
    /// `typ_record_comment_fully_before_open_brace_stays_above_it` - a
    /// comment fully preceding `[` (its own line above, not sharing `[`'s
    /// line) used to only get flushed once the first item's own
    /// `flush_comments_before` ran, by which point `self.indent` had already
    /// moved to `[`'s column, stranding `[` alone with nothing hung under it.
    #[test]
    fn list_comment_fully_before_open_bracket_stays_above_it() {
        let src = indoc! {"
            module Foo where

            xs =
              -- explanation comment
              [ a -- inline
              , b
              ]
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// The `in` keyword has no span of its own in the AST, so a comment
    /// *trailing* it (a leading comment on the body) used to get swept up by
    /// the same flush that handles a comment before `in`
    /// (see `let_binding_trailing_comment_before_in_stays_before_in`) and
    /// print above `in` instead of below it.
    #[test]
    fn let_in_body_leading_comment_stays_after_in() {
        let src = indoc! {"
            module Foo where

            f x =
              let
                y = 1
              in
              -- NOTE: explanation of the following case
              case x of
                _ -> y
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// `do`/`ado`'s own `in` (see `Expr::Ado`) has the identical gap.
    #[test]
    fn ado_in_result_leading_comment_stays_after_in() {
        let src = indoc! {"
            module Foo where

            f x =
              ado
                y <- Just x
                in
                -- NOTE: explanation
                y
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn paren_operand_of_an_op_chain_closes_under_its_own_open_paren() {
        // Regression: a Paren operand glued after an operator must close
        // under its own `(`, not the chain's ambient indent.
        let src = indoc! {"
            module M where

            x =
              y
                <#> ( \\cred ->
                        [ Foo.Bar cur cred ]
                    )
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module M where

                x =
                  y
                    <#> ( \\cred ->
                            [ Foo.Bar cur cred ]
                        )
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn array_operand_of_an_op_chain_closes_under_its_own_open_bracket() {
        // Same bug as the Paren case above, for list()'s glued branch.
        let src = indoc! {"
            module M where

            x =
              y
                <#> [ credA
                    , credB
                    , credC
                    ]
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module M where

                x =
                  y
                    <#> [ credA
                        , credB
                        , credC
                        ]
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn nested_paren_inside_a_glued_paren_anchors_to_the_right_column() {
        // Regression: `current_column()` read a freshly swapped-in scratch
        // buffer as column 0 regardless of `self.indent`, so a nested glued
        // `Paren` anchored its `open_col` at 0 instead of its real column.
        let src = indoc! {"
            module M where

            x =
              y
                # f
                    ( ( case _ of
                          A -> 1
                          B -> 2
                      )
                        >>> g
                    )
        "};
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
        let src = indoc! {"
            module M where

            x =
                ( foo
                    @( aaa :: _
                    , bbb :: _
                    , ccc :: _
                    )
                )
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module M where

                x =
                  ( foo
                      @( aaa :: _
                       , bbb :: _
                       , ccc :: _
                       )
                  )
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn simple_module() {
        let src = indoc! {"
            module Foo (foo) where

            foo = 1
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo (foo) where

                foo = 1
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn export_list_always_gets_a_blank_line_before_what_follows() {
        // Forced even with no blank in the source; the import-to-decl
        // boundary below is untouched and keeps preserving 0-or-1.
        let src = indoc! {"
            module Foo (foo) where
            import Prelude
            foo = 1
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo (foo) where

                import Prelude
                foo = 1
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn export_list_forces_a_blank_line_before_a_decl_when_there_are_no_imports() {
        let src = indoc! {"
            module Foo (foo) where
            foo = 1
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo (foo) where

                foo = 1
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn no_export_list_does_not_force_a_blank_line() {
        let src = indoc! {"
            module Foo where
            foo = 1
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where
                foo = 1
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn paren_expands_when_source_has_a_newline_inside() {
        // `=` breaks too, else the closing `)` would move back past `(`.
        let src = indoc! {"
            module Foo where

            foo = (1 +
              2)
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo =
                  ( 1
                      + 2
                  )
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn paren_after_arrow_breaks_the_arrow_first_instead_of_moving_back() {
        let src = indoc! {"
            module Foo where

            foo = map (\\x -> (x +
              1)) xs
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo =
                  map
                    ( \\x ->
                        ( x
                            + 1
                        )
                    )
                    xs
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn paren_stays_flat_when_source_is_flat() {
        let src = indoc! {"
            module Foo where

            foo = (1 + 2)
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo = (1 + 2)
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn imports_and_multiple_decls() {
        let src = indoc! {"
            module Foo where

            import Prelude
            import Data.Array (head, tail)

            foo = 1
            bar = 2
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where
                import Prelude

                import Data.Array (head, tail)

                foo = 1
                bar = 2
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn array_stays_flat_when_source_is_flat() {
        let src = indoc! {"
            module Foo where

            foo = [1, 2, 3]
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo = [ 1, 2, 3 ]
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn array_expands_when_source_has_a_newline_inside() {
        let src = indoc! {"
            module Foo where

            foo = [1,
              2, 3]
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo =
                  [ 1
                  , 2
                  , 3
                  ]
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn empty_array_with_a_newline_between_the_brackets_stays_expanded() {
        // Regression: `list()`'s empty-items fast path used to always
        // collapse to `[]`, ignoring a source break between the brackets.
        let src = indoc! {"
            module Foo where

            foo = [
            ]
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo =
                  [
                  ]
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn array_item_that_would_break_on_its_own_expands_the_whole_array() {
        // `c` stays glued to its leading comma; `App`'s own_indent must not
        // double-relocate on top of that.
        let src = indoc! {"
            module Foo where

            foo = [a b, c
             d]
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo =
                  [ a b
                  , c
                      d
                  ]
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn app_stays_flat_when_source_is_flat() {
        let src = indoc! {"
            module Foo where

            foo = bar baz qux
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo = bar baz qux
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn app_expands_one_arg_per_line_when_source_has_a_newline_between_args() {
        let src = indoc! {"
            module Foo where

            foo = bar
              baz
              qux
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo =
                  bar
                    baz
                    qux
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn app_only_pushes_args_after_the_first_break_onto_their_own_line() {
        let src = indoc! {"
            module Foo where

            foo = a b
              c d
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo =
                  a b
                    c
                    d
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn app_arg_that_would_break_pushes_itself_and_later_args_onto_their_own_line() {
        let src = indoc! {"
            module Foo where

            foo = a (b
            c) d
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo =
                  a
                    ( b
                        c
                    )
                    d
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn app_record_arg_that_would_break_pushes_itself_and_later_args_onto_their_own_line() {
        let src = indoc! {"
            module Foo where

            foo = a { x: 1
            , y: 2 } d
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo =
                  a
                    { x: 1
                    , y: 2
                    }
                    d
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn app_relocates_when_a_later_glued_argument_would_break() {
        // `x {}` is one `Expr::Update` node with zero updates, not a
        // separate `App` argument.
        let src = indoc! {"
            module Foo where

            a = x {} [
            a
            ]
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                a =
                  x {}
                    [ a
                    ]
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn decl_def_binder_that_would_break_pushes_itself_and_later_binders_onto_their_own_line() {
        // Same fix applies to InstBinding::Def, LetBinding::Name, and Lambda.
        let src = indoc! {"
            module M where

            f x@
              { a
              , b
              }
              y = 1
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module M where

                f
                  x@
                    { a
                    , b
                    }
                  y = 1
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn inst_binding_def_binder_that_would_break_pushes_itself_and_later_binders_onto_their_own_line()
     {
        let src = indoc! {"
            module M where

            instance showFoo :: Show Foo where
              f x@
                { a
                , b
                }
                y = 1
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module M where

                instance Show Foo where
                  f
                    x@
                      { a
                      , b
                      }
                    y = 1
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn let_binding_name_binder_that_would_break_pushes_itself_and_later_binders_onto_their_own_line()
     {
        let src = indoc! {"
            module M where

            foo =
              let
                f x@
                  { a
                  , b
                  }
                  y = 1
              in
                f
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module M where

                foo =
                  let
                    f
                      x@
                        { a
                        , b
                        }
                      y = 1
                  in
                  f
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn lambda_binder_that_would_break_pushes_later_binders_onto_their_own_line() {
        // Deliberate asymmetry: the first binder always stays glued after
        // `\`; only binders after it go through print_spine_args.
        let src = indoc! {"
            module M where

            foo =
              \\x@
                 { a
                 , b
                 }
               y -> 1
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module M where

                foo =
                  \\x@
                    { a
                    , b
                    }
                    y -> 1
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn case_nested_in_a_multiline_app_arg_indents_past_the_call() {
        let src = indoc! {"
            module Foo where

            foo = bar
              (case x of
                A -> 1
                B -> 2)
              qux
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo =
                  bar
                    ( case x of
                        A -> 1
                        B -> 2
                    )
                    qux
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn case_branches_preserve_a_blank_line_between_groups() {
        let src = indoc! {"
            module Foo where

            foo x = case x of
              A -> 1

              B -> 2
              C -> 3
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo x =
                  case x of
                    A -> 1

                    B -> 2
                    C -> 3
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn guarded_clause_comments_stay_attached_to_their_own_clause() {
        let src = indoc! {"
            module Foo where

            f x
              -- first
              | a x = 1
              -- second
              | b x = 2
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn comment_before_a_field_does_not_strand_its_leading_comma() {
        // Regression: `list()` used to write the leading `, ` before
        // flushing the comment, stranding the comma on its own line.
        let src = indoc! {"
            module Foo where

            foo =
              { a: 1
              -- comment
              , b: 2
              }
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn comment_before_a_lets_body_is_not_relocated_past_it() {
        // Regression: `Expr::Let`'s body printed via plain `print_expr` with
        // no `flush_comments_before`, so the comment rode along to whatever
        // the body flushed next (e.g. past a case branch's own comment).
        let src = indoc! {"
            module Foo where

            foo = do
              let
                y = 1
              -- comment
              case y of
                _ -> pure y
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo =
                  do
                    let
                      y = 1
                    -- comment
                    case y of
                      _ -> pure y
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn trailing_comment_stays_on_its_own_line_glued_to_what_it_trails() {
        let src = indoc! {"
            module Foo where

            foo = 1 -- trailing

            bar = 2
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn trailing_comment_does_not_attach_to_an_earlier_token_on_the_same_line() {
        // Regression: checking "does a comment start on this token's line"
        // per-subexpression made `Tuple a b -- c` print as `Tuple -- c a b`.
        let src = indoc! {"
            module Foo where

            foo = Tuple a b -- trailing
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn op_chain_trailing_comment_stays_on_the_operand_it_trails() {
        // Without flush_trailing_comment per operand, the comment falls
        // through and misattaches as a leading comment on the next operand.
        let src = indoc! {"
            module Foo where

            foo x =
              x
                # f arg -- comment
                <#> (\\y -> y)
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn op_chain_trailing_comment_on_a_still_flat_operand_does_not_misattach_earlier() {
        let src = indoc! {"
            module Foo where

            foo = a <> b -- comment
              <> d
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo =
                  a <> b -- comment
                    <> d
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn op_chain_leading_comment_before_an_operator_stays_above_it_instead_of_forcing_the_operand_down() {
        // The comment belongs to the `op y` unit, not to `y` alone -
        // print_expr(y)'s own flush_comments_before would otherwise claim it.
        let src = indoc! {"
            module Foo where

            foo =
              a b c
                -- comment
                <#> List.map d
                # e f
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn record_expands_when_source_has_a_newline_inside() {
        let src = indoc! {"
            module Foo where

            foo = { a: 1,
              b: 2 }
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo =
                  { a: 1
                  , b: 2
                  }
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn sig_and_binders() {
        let src = indoc! {"
            module Foo where

            foo :: Int -> Int
            foo x = x
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo :: Int -> Int
                foo x = x
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn record_and_array_flat_are_both_padded() {
        let src = indoc! {"
            module Foo where

            foo = { a: 1, b: 2 }
            bar = [1, 2]
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo = { a: 1, b: 2 }
                bar = [ 1, 2 ]
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn if_then_else_multiline_is_indented() {
        let src = indoc! {"
            module Foo where

            foo = if x
              then 1
              else 2
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo = if x
                  then 1
                  else 2
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn leading_comment_before_decl_is_kept() {
        let src = indoc! {"
            module Foo where

            -- a comment
            foo = 1
        "};
        let out = fmt(src);
        assert!(out.contains("-- a comment"), "comment lost: {:?}", out);
        assert_idempotent(src);
    }

    #[test]
    fn blank_line_between_a_leading_comment_and_its_decl_is_kept() {
        // flush_comments_before must check for a blank line between the
        // comment and what follows, not just before the comment group.
        let src = indoc! {"
            module Foo where

            -- section

            foo = 1
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn case_of_with_multiple_branches() {
        // `case` always relocates off a glued `=` (see `keyword_block_would_break`).
        let src = indoc! {"
            module Foo where

            foo = case 1 of
              0 -> \"zero\"
              x -> \"other\"
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo =
                  case 1 of
                    0 -> \"zero\"
                    x -> \"other\"
            "}
        );
        assert_idempotent(src);
    }

    /// `{}` binder had no span, reading as `Span::Zero` - a false "break" that
    /// relocated the branch and shifted later branches too.
    #[test]
    fn empty_record_binder_case_branch_does_not_relocate_or_flip() {
        let src = indoc! {"
            module Foo where

            foo x = case x of
              y | y > 0 -> y
              {} -> 0
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo x =
                  case x of
                    y | y > 0 -> y
                    {} -> 0
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn case_scrutinee_that_would_break_relocates_case_and_of_onto_their_own_lines() {
        let src = indoc! {"
            module Foo where

            foo = case
              a
                && b
              of
              true -> 1
              false -> 2
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo =
                  case
                    a
                      && b
                    of
                    true -> 1
                    false -> 2
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn case_multiple_scrutinees_that_would_break_print_one_per_line() {
        let src = indoc! {"
            module Foo where

            foo = case
              a
              , b
              of
              true, e -> 1
              _, _ -> 2
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo =
                  case
                    a
                    , b
                    of
                    true, e -> 1
                    _, _ -> 2
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn record_field_with_case_value_hangs_one_level_deeper() {
        // `print_record_field_rhs` uses two `indent_in`s here, not one.
        let src = indoc! {"
            module Foo where

            foo =
              { a: 1
              , b: case x of
                  0 -> 1
                  _ -> 2
              }
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo =
                  { a: 1
                  , b:
                      case x of
                        0 -> 1
                        _ -> 2
                  }
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn record_update_field_with_case_value_hangs_one_level_deeper() {
        let src = indoc! {"
            module Foo where

            foo =
              r
                { a = 1
                , b = case x of
                    0 -> 1
                    _ -> 2
                }
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo =
                  r
                    { a = 1
                    , b =
                        case x of
                          0 -> 1
                          _ -> 2
                    }
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn record_field_moves_to_its_own_line_when_its_value_already_broke_in_source() {
        // Unlike a `case` value (stays glued to `:`), an already-broken value
        // moves down whole, two levels past the field's own row.
        let src = indoc! {"
            module Foo where

            f x =
              update
                { payload:
                    List.singleton
                      (Db.payload @\"type\" (selectedTypes # NonEmptyArray.map RowType.toStorageString))
                , updatedColumns: List.singleton (Db.updatedColumn @\"status\")
                }
                tableRow
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn constraint_arg_moves_to_its_own_line_after_a_multiline_row_argument() {
        // The row block hangs under `Union`'s real column (`hang_glued`), not
        // an approximate level bump, since the ambient indent has no memory
        // of `. `'s width.
        let src = indoc! {"
            module Foo where

            empty
              :: forall a b
               . Union a
                   ( balance :: Maybe Money.Money
                   , currency :: Currency
                   )
                   b
              => Record b
            empty = x
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn guarded_def() {
        let src = indoc! {"
            module Foo where

            foo x
              | x > 0 = 1
              | otherwise = 0
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo x
                  | x > 0 = 1
                  | otherwise = 0
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn do_notation() {
        // `do` always relocates off a glued `=` (see `keyword_block_would_break`).
        let src = indoc! {"
            module Foo where

            foo = do
              x <- bar
              pure x
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo =
                  do
                    x <- bar
                    pure x
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn let_in() {
        let src = indoc! {"
            module Foo where

            foo = let x = 1 in x
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn let_in_relocates_and_separates_in_from_body_when_bindings_block() {
        let src = indoc! {"
            module A where

            a = let
              b = 2
              in b
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module A where

                a =
                  let
                    b = 2
                  in
                  b
            "}
        );
        assert_idempotent(src);
    }

    /// A single-branch `case` written flat in the source with no break
    /// anywhere between `case` and the branch's own body used to explode
    /// unconditionally - `print_indented_siblings` always put branches on
    /// their own lines regardless of source layout, unlike every other
    /// construct (App args, Op operands, record fields) which only breaks
    /// when the source already did. That forced explosion then cascaded
    /// outward through the surrounding App/Op "would this break" checks,
    /// blowing up an otherwise-flat call chain that only contained the case
    /// as a lambda body deep inside one operand.
    #[test]
    fn case_single_branch_with_no_source_break_stays_flat() {
        let src = indoc! {"
            module Foo where

            run k m =
              Wrap (m >>= veither (\\a -> case k a of Wrapped b -> b) (Applicative.pure >>> Applicative.pure))
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// A single-branch `case` still relocates/explodes like normal when the
    /// source itself already broke somewhere before the branch - only a
    /// fully flat source case is eligible to stay flat.
    #[test]
    fn case_relocates_off_a_glued_arrow_even_for_a_single_trivial_branch() {
        let src = indoc! {"
            module A where

            a = case 1 of
              _ -> 1
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module A where

                a =
                  case 1 of
                    _ -> 1
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn nested_case_branch_body_also_relocates_off_its_glued_arrow() {
        let src = indoc! {"
            module A where

            a =
              case 1 of
                _ -> case 1 of
                  _ -> 1
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module A where

                a =
                  case 1 of
                    _ ->
                      case 1 of
                        _ -> 1
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn paren_preserves_a_source_break_around_trivial_content() {
        // A source break right after `(` or before `)` forces block style
        // even when the content would otherwise print flat.
        let src = indoc! {"
            module A where

            a = (
             1)
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module A where

                a =
                  ( 1
                  )
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn ado_notation_with_statements_relocates_off_a_glued_arrow_like_do_does() {
        let src = indoc! {"
            module Foo where

            foo = ado
              x <- bar
              in x
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo =
                  ado
                    x <- bar
                    in x
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn ado_with_no_statements_stays_flat_when_the_source_had_it_on_one_line() {
        let src = indoc! {"
            module Foo where

            foo = ado in 1
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn ado_with_one_statement_stays_flat_when_the_source_had_it_on_one_line() {
        let src = indoc! {"
            module Foo where

            foo = ado x <- pure 1 in x
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn ado_with_no_statements_and_a_source_break_relocates_the_whole_block() {
        // Unlike a populated `ado`/`do` (always glued to `=`), an empty `ado`
        // relocates the whole `ado ... in ...` unit instead of leaving `ado`
        // glued with just `in` dangling under it.
        let src = indoc! {"
            module Foo where

            foo = ado
              in 1
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo =
                  ado
                    in 1
            "}
        );
        assert_idempotent(&out);
    }

    #[test]
    fn let_single_binding_stays_glued_in_do_block() {
        let src = indoc! {"
            module A where

            a =
              do
                let a = 1
                pure a
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn let_multiple_bindings_still_break() {
        let src = indoc! {"
            module A where

            a = do
              let
                x = 1
                y = 2
              pure (x + y)
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module A where

                a =
                  do
                    let
                      x = 1
                      y = 2
                    pure (x + y)
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn let_binding_on_its_own_source_line_still_breaks() {
        let src = indoc! {"
            module A where

            a = do
              let
                x = 1
              pure x
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module A where

                a =
                  do
                    let
                      x = 1
                    pure x
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn where_clause() {
        let src = indoc! {"
            module Foo where

            foo = result where
              result = 1
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo = result
                  where
                    result = 1
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn record_update_and_infix() {
        let src = indoc! {"
            module Foo where

            foo = r { a = 1 }
            bar = 1 `add` 2
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo = r { a = 1 }
                bar = 1 `add` 2
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn data_flat_and_multiline() {
        let src = indoc! {"
            module Foo where

            data Flat = A | B Int

            data Tall
              = C
              | D String
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                data Flat = A | B Int

                data Tall
                  = C
                  | D String
            "}
        );
        assert_idempotent(src);
    }

    /// A single constructor has no adjacent `|` alternative for `any_breaks`
    /// to compare against, so a would-break arg alone must still relocate
    /// the whole `= Ctor` line, not just the arg.
    #[test]
    fn data_single_ctor_arg_that_would_break_relocates_whole_line() {
        let src = indoc! {"
            module Foo where

            data Store = Store { a :: Int
              , b :: Int
              }
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                data Store
                  = Store
                      { a :: Int
                      , b :: Int
                      }
            "}
        );
        assert_idempotent(src);
    }

    /// Also fixes `data_cnstr` parsing fields with `typ` instead of `typ_atom`
    /// (which mis-parsed `C A B` as one field `A` applied to `B`).
    #[test]
    fn data_ctor_fields_that_would_break_relocate_two_levels_past_the_bullet() {
        let src = indoc! {"
            module Foo where

            data D
              = C
                  A
                  B
              | E
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// Without `flush_trailing_comment` per constructor, the comment falls
    /// through `flush_comments_before` and misattaches as a leading comment
    /// on the next constructor's own line.
    #[test]
    fn data_ctor_trailing_comment_stays_on_the_ctor_it_trails() {
        let src = indoc! {"
            module Foo where

            data Product
              = A
              | B -- DEPRECATED
              | C -- DEPRECATED
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// `newtype` wraps exactly one `Typ` (no arg list like `data`), so this
    /// has its own relocation logic, landing on the same shape as `Decl::Data`.
    #[test]
    fn newtype_ctor_arg_that_would_break_relocates_even_when_source_glued_it_flat() {
        let src = indoc! {"
            module Foo where

            newtype Store = Store { a :: Int
              , b :: Int
              }
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                newtype Store
                  = Store
                      { a :: Int
                      , b :: Int
                      }
            "}
        );
        assert_idempotent(src);
    }

    /// Unlike a top-level signature, a field's `::` stays glued to its label
    /// (`print_field_typ` mirrors `print_typ_alias_rhs`, not `print_sig_typ`).
    #[test]
    fn record_field_typ_that_would_break_relocates_with_double_colon_staying_put() {
        let src = indoc! {"
            module Foo where

            type T =
              { a :: Int
              , action :: Foo
                  Bar
                  Baz
              }
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                type T =
                  { a :: Int
                  , action ::
                      Foo
                        Bar
                        Baz
                  }
            "}
        );
        assert_idempotent(src);
    }

    /// A leading comment shifts the field onto a different output line than
    /// `{`; the block-style check must not mistake that for a real source
    /// break on a later pass, or it never stabilizes.
    #[test]
    fn comment_before_ctor_record_arg_does_not_flip_flat_row_to_block_on_reformat() {
        let src = indoc! {"
            module Foo where

            data D
              = C
                  -- TODO comment
                  { a :: Int, b :: Int }
        "};
        assert_idempotent(src);
    }

    /// A single-field record has no adjacent pair for `any_breaks` to
    /// compare, so the break before `}` alone must force block style.
    #[test]
    fn single_field_record_with_a_break_before_close_brace_stays_block_style() {
        let src = indoc! {"
            module Foo where

            type Model =
              { page :: PageModel
              }
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// `Header` didn't carry the export list's paren spans, so a source break
    /// there had no way to force block style; once it does, `module Name`
    /// relocates too, not just the list.
    #[test]
    fn module_header_export_list_relocates_on_a_source_break_after_open_paren() {
        let src = indoc! {"
            module A (
            a) where
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module A
                  ( a
                  ) where

            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn record_field_typ_app_with_paren_row_arg_indents_two_levels_past_label() {
        // `label ::`/`, ` is exactly `INDENT` wide, so a single `indent_in()`
        // would land the type flush with the label column, not nested under it.
        let src = indoc! {"
            module Foo where

            type T =
              { other :: Int
              , action :: VariantStorable
                  ( conversion :: ProxyStorable \"conversion\"
                  , funding :: ProxyStorable \"funding\"
                  )
              }
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                type T =
                  { other :: Int
                  , action ::
                      VariantStorable
                        ( conversion :: ProxyStorable \"conversion\"
                        , funding :: ProxyStorable \"funding\"
                        )
                  }
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn type_newtype_class_instance() {
        let src = indoc! {"
            module Foo where

            type Id a = a

            newtype Wrap = Wrap Int

            class Show a where
              show :: a -> String

            instance Show Int where
              show x = \"int\"

            derive instance Eq Wrap
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// `where` also relocates onto its own line once anything between
    /// `instance` and `where` is multiline.
    #[test]
    fn instance_head_constraint_relocates_when_source_broke_it() {
        let src = indoc! {"
            module Foo where

            instance
              IsSymbol l
              => Foldable.FoldWithIndex Foo (Proxy l) where
              foldingWithIndex _ _ acc value = acc
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                instance
                  IsSymbol l
                  => Foldable.FoldWithIndex Foo (Proxy l)
                  where
                  foldingWithIndex _ _ acc value = acc
            "}
        );
        assert_idempotent(out.as_str());
    }

    #[test]
    fn instance_head_multi_constraint_relocates_leading_comma_style() {
        let src = indoc! {"
            module Foo where

            instance
              ( IsSymbol l
              , Foo l
              )
              => Foldable.FoldWithIndex Foo (Proxy l) where
              foldingWithIndex _ _ acc value = acc
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                instance
                  ( IsSymbol l
                  , Foo l
                  )
                  => Foldable.FoldWithIndex Foo (Proxy l)
                  where
                  foldingWithIndex _ _ acc value = acc
            "}
        );
        assert_idempotent(out.as_str());
    }

    /// `Decl::Class`'s superclass context (`<=`) shares the same fix.
    #[test]
    fn class_superclass_constraint_relocates_when_source_broke_it() {
        let src = indoc! {"
            module Foo where

            class
              Eq a
              <= MyClass a where
              bar :: a -> a
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// A singleton constraint's optional parens are preserved, not stripped -
    /// removing a redundant paren is `style.rs`'s job, not the raw printer's.
    #[test]
    fn instance_head_single_constraint_paren_wrap_is_preserved_when_flat() {
        let src = indoc! {"
            module Foo where

            instance (IsSymbol l) => Foo (Proxy l) where
              foo = 1
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn instance_head_single_constraint_without_parens_stays_bare() {
        let src = indoc! {"
            module Foo where

            instance IsSymbol l => Foo (Proxy l) where
              foo = 1
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// `where` relocates when the head's class-args spine breaks, not just
    /// when the constraint context does.
    #[test]
    fn instance_where_relocates_when_head_spine_args_break() {
        let src = indoc! {"
            module Foo where

            instance
              ( IsSymbol name
              , WriteForeign ty
              )
              => WriteRowFields
                   ( Cons namea
                       (Maybe ty)
                       tail
                   )
                   row
                   from
                   to
              where
              writeRowFields _ _ = 1
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// `print_spine_args` treats a would-break `Typ::Paren` arg the same as
    /// `Expr::App`'s would-break args, even glued with no source break before it.
    #[test]
    fn inst_head_paren_arg_with_no_source_break_before_it_still_relocates_when_it_would_break() {
        let src = indoc! {"
            module Foo where

            instance
              ( IsSymbol name
              , ReadForeign ty
              )
              => ReadRowFields (Cons name
                                      ty
                                      tail
                                   )
                   from
                   to
              where
              readRowFields _ _ = 1
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                instance
                  ( IsSymbol name
                  , ReadForeign ty
                  )
                  => ReadRowFields
                       ( Cons name
                           ty
                           tail
                       )
                       from
                       to
                  where
                  readRowFields _ _ = 1
            "}
        );
        assert_idempotent(out.as_str());
    }

    /// Same fix in `print_constraint`'s spine - unlike `Typ::Row`/`Typ::Record`,
    /// which keep hanging in place, a `Typ::Paren` arg relocates.
    #[test]
    fn constraint_paren_arg_with_no_source_break_before_it_still_relocates_when_it_would_break() {
        let src = indoc! {"
            module Foo where

            empty
              :: forall a b
               . Union (Cons name
                          ty
                          tail
                       ) b
              => Record b
            empty = x
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                empty
                  :: forall a b
                   . Union
                       ( Cons name
                           ty
                           tail
                       )
                       b
                  => Record b
                empty = x
            "}
        );
        assert_idempotent(out.as_str());
    }

    #[test]
    fn foreign_and_fixity_and_role() {
        let src = indoc! {"
            module Foo where

            foreign import unsafeCoerce :: forall a b. a -> b

            infixl 5 add as +++

            type role Foo nominal representational
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn qualified_do_and_ado_keep_the_dot() {
        let src = indoc! {"
            module Foo where

            a = A.do
              x <- A.a
              pure x
        "};
        let out = fmt(src);
        assert!(out.contains("A.do"), "qualifier dot lost: {:?}", out);
        assert!(!out.contains("Ado") && !out.contains("Adodo"), "garbled qualifier: {:?}", out);
        assert_idempotent(src);
    }

    #[test]
    fn negative_typ_int_keeps_the_digits() {
        let src = indoc! {"
            module Foo where

            a :: -1
            a = 1
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                a :: -1
                a = 1
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn visible_forall_binder_without_kind_has_no_parens() {
        let src = indoc! {"
            module Foo where

            readJSON :: forall @a. Array a
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                readJSON :: forall @a. Array a
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn kinded_forall_binder_keeps_parens() {
        let src = indoc! {"
            module Foo where

            foo :: forall (a :: Type). a
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo :: forall (a :: Type). a
            "}
        );
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

    // Fixtures that fail to parse cleanly are skipped (parser-error-recovery fixtures).
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
        let src = indoc! {"
            module Foo ((<*>), type (~>)) where

            import Data.Functor ((<$>))

            foo = (<*>)
        "};
        let out = fmt(src);
        // `((<$>))` isn't doubled - outer paren is the import list's, inner is the Symbol's own.
        assert_eq!(
            out,
            indoc! {"
                module Foo ((<*>), type (~>)) where

                import Data.Functor ((<$>))

                foo = (<*>)
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn comment_before_module_keyword_stays_before_it() {
        let src = indoc! {"
            -- top comment
            module Foo where

            foo = 1
        "};
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
        let src = indoc! {"
            module Foo
              ( a
              -- mid comment
              , b
              ) where

            a = 1
            b = 2
        "};
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
        let src = indoc! {"
            module Foo where

            import Data.Array (head)
            import Prelude
            import Data.Maybe

            foo = 1
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where
                import Data.Maybe
                import Prelude

                import Data.Array (head)

                foo = 1
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn imports_are_sorted_and_duplicates_merged() {
        let src = indoc! {"
            module Foo where

            import Data.Array (tail)
            import Control.Bind (class Bind)
            import Data.Array (head)

            foo = 1
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where
                import Control.Bind (class Bind)
                import Data.Array (head, tail)

                foo = 1
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn merging_a_bare_type_import_with_its_data_ctors_keeps_only_the_data_ctors() {
        // A bare `AccessRight` import is subsumed by `AccessRight(..)` for the
        // same type - keep only the more complete one, not both.
        let src = indoc! {"
            module Foo where

            import Storage.AccessRight (AccessRight)
            import Storage.AccessRight (AccessRight(..), userHasAccess)

            foo = 1
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where
                import Storage.AccessRight (AccessRight(..), userHasAccess)

                foo = 1
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn merging_identical_data_ctor_imports_keeps_one_copy() {
        let src = indoc! {"
            module Foo where

            import Data.Foo (Foo(A, B))
            import Data.Foo (Foo(A, B))

            foo = 1
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where
                import Data.Foo (Foo(A, B))

                foo = 1
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn merging_data_ctor_imports_with_different_ctor_lists_keeps_both() {
        // `Foo(A, B)` and `Foo(B, C)` aren't the same set, so merging them
        // would have to invent a span for constructors pulled from another
        // import - keep both entries rather than guessing.
        let src = indoc! {"
            module Foo where

            import Data.Foo (Foo(A, B))
            import Data.Foo (Foo(B, C))

            foo = 1
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where
                import Data.Foo (Foo(A, B), Foo(B, C))

                foo = 1
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn import_class_sorts_before_types_as_its_own_tier() {
        // Class imports are their own leading tier (purs-tidy's `ImportClassCmp`), not alphabetical.
        let src = indoc! {"
            module Foo where

            import Data.Foo (Foo, class Eq, bar)

            x = 1
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where
                import Data.Foo (class Eq, Foo, bar)

                x = 1
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn import_sort_follows_purs_tidys_five_tier_kind_order() {
        // Kind order is class, type-op, type, value, value-op (purs-tidy's `ordImportComparison`), not flat alphabetical.
        let src = indoc! {"
            module Foo where

            import Db.Type (Name, class GetPk, type (..), toSqlValue, (>>=), class GetIndex, fromSqlValue)

            x = 1
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where
                import Db.Type (class GetIndex, class GetPk, type (..), Name, fromSqlValue, toSqlValue, (>>=))

                x = 1
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn multiline_type_signature_stays_expanded() {
        let src = indoc! {"
            module Foo where

            f
              :: forall a
               . Show a
              => a
              -> a
              -> String
            f a b = show a
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn flat_type_signature_stays_flat() {
        let src = indoc! {"
            module Foo where

            f :: forall a. Show a => a -> a -> String
            f a b = show a
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn typ_paren_expands_when_source_has_a_newline_inside() {
        // Hangs under its own real column (after glued `( `), not an approximate level bump.
        let src = indoc! {"
            module Foo where

            f :: (Int ->
              String)
            f = undefined
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                f
                  :: ( Int
                       -> String
                     )
                f = undefined
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn typ_app_expands_one_arg_per_line_when_source_has_a_newline_between_args() {
        let src = indoc! {"
            module Foo where

            f :: Bar
              Baz
              Qux
            f = x
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn typ_app_directly_after_a_broken_sig_gets_an_extra_hang_level() {
        // Glued after `:: ` (a fixed-width token), so it must hang_glued under its own real column.
        let src = indoc! {"
            module Foo where

            f
              :: Array
                   { from :: RowId
                   , to :: RowId
                   }
            f = x
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    // An arrow chain's first segment needs the same needs_hang check as a bare signature type.
    #[test]
    fn typ_arrow_chain_segment_gets_the_same_extra_hang_as_a_bare_sig() {
        let src = indoc! {"
            module Foo where

            linkRows
              :: Array
                   { source :: RowId
                   , target :: LinkId.LinkId
                   }
              -> Ctx _ _ Unit
            linkRows = linkRowsSql >>> DbCtx.runSql
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn typ_arrow_chain_segment_keeps_its_trailing_comment() {
        let src = indoc! {"
            module Foo where

            cancelThing
              :: { a :: A, b :: B, c :: C } -- TODO: may not need this field
              -> ThingId
              -> ResultT
                   _
                   Effect
                   Status
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// Same as `typ_arrow_chain_segment_keeps_its_trailing_comment`, for a
    /// comment on its own line right before a `->` segment instead of
    /// trailing after the previous one.
    #[test]
    fn typ_arrow_chain_leading_comment_before_a_segment_stays_before_it() {
        let src = indoc! {"
            module Foo where

            cancelThing
              :: AccessToken
              -- comment before ThingId
              -> ThingId
              -> ResultT
                   _
                   Effect
                   Status
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    // Same needs_hang gotcha, reached via print_sig_typ directly (no arrow chain involved).
    #[test]
    fn typ_app_paren_op_chain_directly_after_a_broken_sig_gets_an_extra_hang_level() {
        let src = indoc! {"
            module Foo where

            tableLinkRow
              :: Db.Table
                   ( Db.Pk (\"row_a\" .. \"row_b\")
                       .. Db.Index \"row_b\"
                       .. Db.Name \"row_link_v0\"
                   )
                   LinkRowR
            tableLinkRow = Db.table @\"row_link_v0\"
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// A comment on its own line after a `Typ::Op` chain's last operand, but
    /// still before the enclosing paren's `)`, must stay right there - not
    /// escape all the way out to wherever the next comment flush happens to
    /// be (previously the end of the whole declaration).
    #[test]
    fn typ_op_chain_comment_before_the_closing_paren_stays_inside_it() {
        let src = indoc! {"
            module Foo where

            tableLinkRow
              :: Db.Table
                   ( Db.Pk (\"row_a\" .. \"row_b\")
                       .. Db.Index \"row_b\"
                       .. Db.Name \"row_link_v0\"
                       -- NOTE: extra note
                   )
                   LinkRowR
            tableLinkRow = Db.table @\"row_link_v0\"
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// A `Binder::Paren` around a constructor pattern whose own arg (a
    /// record binder) breaks must relocate like `Expr::Paren`/`Typ::Paren`
    /// do - `( ` glued to a fresh line, the closing `)` back at the paren's
    /// own column - not just glue `(`/`)` directly onto the inner content.
    #[test]
    fn binder_paren_around_a_breaking_record_pattern_relocates_like_expr_paren() {
        let src = indoc! {"
            module Foo where

            viewFundingItem
              isCreated
              ( BankfileFundingItem
                  { additionalInformation
                  , amount
                  , valueDate
                  }
              ) = valueDate
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// A comment on its own line after a `let` block's last binding, but
    /// still before `in`, must stay right there - not get deferred to
    /// `print_expr(body)`'s own leading-comment flush and print after `in`.
    #[test]
    fn let_binding_trailing_comment_before_in_stays_before_in() {
        let src = indoc! {"
            module Foo where

            f =
              let
                x = 1
                -- y = someDebugExpr x
              in
              x
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// A comment trailing `open` itself (`[ -- size`, before any item) used
    /// to strand the first item unindented on its own line, with `[` left
    /// alone above it - the item now hangs one level deeper instead.
    #[test]
    fn list_leading_comment_after_open_bracket_hangs_the_first_item() {
        let src = indoc! {"
            module Foo where

            h1Styles :: Array String
            h1Styles =
              [ -- size
                \"text-2xl\"
              ]
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// Same `comment_after_open` gap as `list()`'s (see
    /// `list_leading_comment_after_open_bracket_hangs_the_first_item`), for
    /// `print_row`'s independent copy of the same "hang from `open`'s own
    /// column" logic (used by `Typ::Record`/`Typ::Row`, not `Expr`s).
    #[test]
    fn typ_record_leading_comment_after_open_brace_hangs_the_first_field() {
        let src = indoc! {"
            module Foo where

            type Response =
              { -- explanation
                id :: String -- an id
              }
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// `current_column()` used to fall back to a raw char count once a
    /// scratch buffer (from `render_at_column`/`render_indented`) held any
    /// text without a `\n`, forgetting the virtual column that buffer
    /// started at - collapsing a doubly-nested glued literal's own indent
    /// decisions (here, a record glued inside an array glued inside a
    /// paren) down near column 0 instead of hanging under their real column.
    #[test]
    fn doubly_nested_glued_literal_keeps_its_real_hang_column() {
        let src = indoc! {"
            module Foo where

            x =
              ( [ { id: TransactionId \"a\"
                  , amount: MoneyString.moneyString SEK \"10.10\" # unreachableEither [ TO ]
                  } # Storage.Transaction
                ] # Veither.pure # Just
              )
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// `= Ctor` must relocate whole when its arg breaks only because the
    /// source put it on its own line (not because the arg is inherently
    /// multi-line) - the single-ctor `multiline` check used to only ask
    /// `typ_would_break`, missing this `breaks_before`-only case that
    /// `print_ctor_args`'s own loop already reacts to.
    #[test]
    fn data_single_ctor_arg_on_its_own_source_line_relocates_whole_line() {
        let src = indoc! {"
            module Foo where

            data Memory
              = Memory
                  (Map CompanyId CompanyMem)
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// An App arg's trailing comment (here, the record arg trailing before
    /// the array arg breaks onto its own line) used to fall through
    /// unflushed into the outer list's `flush_comments_before` for the next
    /// item, landing on its own line instead of staying glued.
    #[test]
    fn app_arg_trailing_comment_stays_glued_to_the_arg_it_trails() {
        let src = indoc! {"
            module Foo where

            x =
              [ Html.div { class: \"flex flex-col\" } --responsive layout
                  [ a
                  , b
                  ]
              , c
              ]
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// Same as `let_binding_trailing_comment_before_in_stays_before_in`, for
    /// `ado`'s own `in` - unlike `let`'s, `ado`'s `in` hangs at the
    /// statements' own (deeper) indent, not the block's base indent.
    #[test]
    fn ado_statement_trailing_comment_before_in_stays_before_in() {
        let src = indoc! {"
            module Foo where

            foo =
              ado
                x <- bar
                -- y <- someDebugM x
                in x
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    // Same needs_hang gotcha, for the body after a constrained chain's last `=> `.
    #[test]
    fn typ_constrained_chain_body_gets_the_same_extra_hang_as_a_bare_sig() {
        let src = indoc! {"
            module Foo where

            f
              :: Eq a
              => Array
                   { x :: Int
                   , y :: Int
                   }
            f = x
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn typ_constrained_chain_constraint_keeps_its_trailing_comment() {
        let src = indoc! {"
            module Foo where

            f
              :: Eq a -- comment
              => Show a
              => a
              -> String
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn typ_constrained_chain_last_constraint_keeps_its_trailing_comment() {
        let src = indoc! {"
            module Foo where

            f
              :: Eq a -- comment
              => a
              -> String
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    /// A comment on its own line right before a `=>` segment (a leading
    /// comment for the constraint/body that follows) must stay right there -
    /// not escape past the rest of the chain to the end of the declaration.
    #[test]
    fn typ_constrained_chain_leading_comment_before_a_segment_stays_before_it() {
        let src = indoc! {"
            module Foo where

            f
              :: Eq a
              -- comment before Show
              => Show a
              -- comment before body
              => a
              -> String
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    // Unlike a value operator chain, type operators get no extra indent level.
    #[test]
    fn typ_operator_chain_does_not_add_its_own_indent() {
        let src = indoc! {"
            module Foo where

            type T =
              A
                .. B
                .. C
            f = 1
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                type T =
                  A
                  .. B
                  .. C
                f = 1
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn type_alias_rhs_breaks_when_its_paren_would_break() {
        let src = indoc! {"
            module Foo where

            type T = (A
              -> B)
            f = 1
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                type T =
                  ( A
                    -> B
                  )
                f = 1
            "}
        );
        assert_idempotent(src);
    }

    // A paren is its own scope for multiline-ness; in_broken_sig must not leak into it.
    #[test]
    fn broken_type_alias_does_not_force_a_flat_nested_paren_to_expand() {
        let src = indoc! {"
            module Foo where

            type Table =
              Db.Table
                ( Db.Pk \"id\"
                    .. Db.Index (\"region_id\" .. \"type\")
                )
                Row
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    // Glued after a paren's `( ` (in_broken_sig reset), the chain hangs like Expr::Op does.
    #[test]
    fn typ_op_chain_gets_its_own_hang_when_not_in_a_broken_sig() {
        let src = indoc! {"
            module Foo where

            type Route =
              Schema
                ( Db.Pk \"key\"
                    .. Db.Index \"row_b\"
                    .. Db.Name \"row_idem_v0\"
                )
                IdemRowR
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    // Parser regression: row_label consumed a quoted label before checking for `::`, losing it when there wasn't one.
    #[test]
    fn paren_wrapped_string_typ_is_not_mistaken_for_an_empty_row() {
        let src = indoc! {"
            module Foo where

            tableIdemRow
              :: Db.Table
                   ( Db.Pk (\"key\")
                       .. Db.Index \"row_b\"
                       .. Db.Name \"row_idem_v0\"
                   )
                   IdemRowR
            tableIdemRow = x
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    // Companion to the test above: a quoted label immediately followed by `::` must still parse.
    #[test]
    fn quoted_row_label_still_parses() {
        let src = indoc! {"
            module Foo where

            type Foo = (\"my-label\" :: Int, normal :: String)
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn single_line_type_alias_with_nested_parens_and_operators_stays_flat() {
        let src = indoc! {"
            module Foo where

            type Table = Db.Table (Db.Pk \"id\" .. Db.Index (\"region_id\" .. \"type\")) Row
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn row_type_expands_one_field_per_line_when_source_has_a_newline() {
        // Fields hang under the row's own real column after glued `(`, not a level bump.
        let src = indoc! {"
            module Foo where

            f :: forall r. Record (a :: Int,
              b :: String)
            f r = r
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                f :: forall r. Record ( a :: Int
                                      , b :: String
                                      )
                f r = r
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn comment_inside_a_multiline_row_stays_attached_to_its_own_field() {
        // print_row previously had no per-field comment flush at all.
        let src = indoc! {"
            module Foo where

            f :: forall r. Record (a :: Int
              -- comment
              , b :: String)
            f r = r
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                f :: forall r. Record ( a :: Int
                                      -- comment
                                      , b :: String
                                      )
                f r = r
            "}
        );
        assert_idempotent(src);
    }

    // A record glued after `=>`/`->` stays glued (the "floor" model); see FORMATTER.md.
    #[test]
    fn typ_record_glued_after_a_broken_sig_hangs_in_place_instead_of_moving_down() {
        let src = indoc! {"
            module Foo where

            unpack
              :: forall unpacked packed
               . Lacks \"type_index\" packed
              => Db.Pack
                   { balance :: Maybe Money.Money
                   | unpacked
                   }
                   { date_created :: Maybe ExDate
                   , type :: RowType
                   | packed
                   }
              => { date_created :: Maybe ExDate
                 , type :: RowType
                 , type_index :: Int
                 | packed
                 }
              -> { balance :: Maybe Money.Money
                 | unpacked
                 }
            unpack = x
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    // The closing `)` lines up under its own `(`, not the outer `->`'s floor column.
    #[test]
    fn typ_paren_glued_after_arrow_hangs_under_its_own_first_token() {
        let src = indoc! {"
            module Foo where

            a
              :: forall b c d
               . b
              -> (c
                  -> Int
                  -> String)
              -> d
            a x y = z
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                a
                  :: forall b c d
                   . b
                  -> ( c
                       -> Int
                       -> String
                     )
                  -> d
                a x y = z
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn multiline_operator_chain_stays_expanded() {
        let src = indoc! {"
            module Foo where

            foo =
              a
                >>> b
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    // `[ `/`, ` are exactly INDENT wide, so a naive hang would land flush with a sibling item.
    #[test]
    fn array_item_operator_chain_hangs_past_its_own_head() {
        let src = indoc! {"
            module Foo where

            buttons =
              [ Widget.create { onclick: ClickedClose false, children: [ Html.text \"Cancel\" ] }
                  # Widget.isWide true
                  # Widget.render
              , Widget.create { onclick: confirmMsg, children: [ Html.text \"Done\" ] }
                  # Widget.isPrimary
                  # Widget.isWide true
                  # Widget.render
              ]
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    // Previously doubled up on item_hang's level instead of gluing to the `[` column (glued_floor).
    #[test]
    fn array_sole_item_record_stays_glued_after_open_bracket() {
        let src = indoc! {"
            module Foo where

            a =
              [ { c: 1
                , d: 2
                }
              ]
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    // Same glued_floor fix as the test above, composed with an operator chain head.
    #[test]
    fn array_sole_item_operator_chain_head_record_stays_glued() {
        let src = indoc! {"
            module Foo where

            a =
              x y
                [ { c: 1
                  , d: 2
                  }
                    # f
                    # g
                ]
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    // Same glued_floor fix, for Expr::App's own_indent rather than a nested list().
    #[test]
    fn array_sole_item_call_head_stays_glued_after_open_bracket() {
        let src = indoc! {"
            module Foo where

            a =
              [ g
                  { b: 1
                  , c: 2
                  }
                  h
              ]
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn multiline_operator_chain_relocates_off_a_glued_equals() {
        let src = indoc! {"
            module Foo where

            foo = a
              >>> b
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo =
                  a
                    >>> b
            "}
        );
        assert_idempotent(src);
    }

    // Used to format flat on the first pass but reflow to one-per-line on the second (not idempotent).
    #[test]
    fn operator_chain_operand_that_would_break_on_its_own_expands_the_whole_chain() {
        let src = indoc! {"
            module Foo where

            foo = a $ b
              { x: 1
              , y: 2
              }
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                foo =
                  a
                    $ b
                        { x: 1
                        , y: 2
                        }
            "}
        );
        assert_idempotent(src);
    }

    // Right-associative chains parse as a right-nested tree; op_spine keeps segments flush, not drifting deeper.
    #[test]
    fn multiline_operator_chain_of_three_or_more_stays_at_one_indent_level() {
        let src = indoc! {"
            module Foo where

            foo =
              a
                <> b
                <> c
                <> d
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn operator_chain_operand_that_is_itself_a_broken_call_hangs_one_level_deeper() {
        // Must land one level deeper than the chain's continuation, else it reads as another chain step.
        let src = indoc! {"
            module Foo where

            f rs =
              rs
                # List.map
                    ( \\r ->
                        r
                          # empty
                    )
                # List.toArray
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    // A wide operator like `<#>` exposes a gap invisible with `#` (exactly INDENT wide).
    #[test]
    fn operator_chain_lambda_operand_case_body_hangs_under_the_lambda_not_the_chain() {
        let src = indoc! {"
            module Foo where

            foo =
              a
                <#> \\x ->
                      case y of
                        true -> 1
                        false -> 2
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    // Same gotcha as the test above, for a call operand's own relocating argument.
    #[test]
    fn operator_chain_call_operand_paren_arg_hangs_under_the_call_not_the_chain() {
        let src = indoc! {"
            module Foo where

            foo =
              a
                <#> f
                      ( b
                          >>> c
                      )
                      d
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn comment_before_let_binding_is_not_relocated() {
        let src = indoc! {"
            module Foo where

            foo = let
              a = 1
              -- a comment
              b = 2
            in a { x: 1 }
        "};
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
        let src = indoc! {"
            module Foo where

            foo = do
              a
              -- a comment
              b
        "};
        let out = fmt(src);
        assert!(out.contains("-- a comment"), "comment lost: {:?}", out);
        assert_idempotent(src);

        let src2 = indoc! {"
            module Foo where

            foo = case x of
              A -> 1
              -- a comment
              B -> 2
        "};
        let out2 = fmt(src2);
        assert!(out2.contains("-- a comment"), "comment lost: {:?}", out2);
        assert_idempotent(src2);
    }

    #[test]
    fn deeply_nested_flat_literal_formats_without_exponential_blowup() {
        // Regression: double-rendering to check for multiline used to recurse O(2^depth).
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
        // Expr::Update's internal target/`{` break needed its own check (App only sees the whole atom).
        let src = indoc! {"
            module Foo where

            reInsert event =
              RecordStore store
                { store = Map.insert (recordId event) (Pending event) store.store }
        "};
        let out = fmt(src);
        assert_eq!(
            out,
            indoc! {"
                module Foo where

                reInsert event =
                  RecordStore
                    store
                      { store = Map.insert (recordId event) (Pending event) store.store }
            "}
        );
        assert_idempotent(src);
    }

    #[test]
    fn record_update_target_stays_glued_when_source_had_no_break() {
        let src = indoc! {"
            module Foo where

            reInsert event =
              RecordStore store { store = Map.insert (recordId event) (Pending event) store.store }
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }

    #[test]
    fn expr_typed_relocates_the_double_colon_like_a_signature_when_the_type_would_break() {
        let src = indoc! {"
            module Foo where

            foo =
              bar
                # ( fromSerializable
                      :: VariantStorable (pending :: ProxyStorable \"pending\")
                      -> Variant (pending :: Proxy \"pending\")
                  )
        "};
        let out = fmt(src);
        assert_eq!(out, src);
        assert_idempotent(src);
    }
}

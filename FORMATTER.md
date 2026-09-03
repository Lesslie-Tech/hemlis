# Formatter work — status and notes

Working notes for the PureScript formatter being built on top of this repo's
parser. Written so a new session can get oriented fast. Branch: `formatter`
(8 commits on top of `main`, not yet merged).

## Status

Functionally complete first version. Covers the entire `Decl`/`Expr`/`Binder`/
`Typ` AST surface (only genuine `Error` parser-recovery nodes fall back to a
verbatim source-text slice — nothing else does). Verified against all 1423
real-world `.purs` files in a sibling repo, `../pay-backend/lib` (external,
read-only reference — never modified): every file formats and reparses
cleanly and idempotently. 64 unit tests in `src/lib/print.rs`, all passing;
full suite (166 lib + 123 style + golden) and clippy clean.

A diff of our output against `../pay-backend/lib/Array.purs` (formatted by
`purs-tidy`, the tool this is meant to replace) shrank from 511 diff lines to
a single 2-line hunk over several sessions' fixes - see "Session: closing the
purs-tidy gap" and "Session: paren blocks + the export-list blank line"
below for the full list. `Expr::Paren` now gets its own `( ` ... `)`-on-
its-own-line indented block when its contents don't fit on one line
(matching purs-tidy), and a real export list always gets a blank line before
whatever follows it. The one hunk still remaining
(`Tuple (Just b)` staying on one line for purs-tidy vs. us splitting it to
`Tuple\n  (Just b)`) is the same already-documented, deliberate gap from the
no-line-fitting-engine design (see "Layout philosophy") - not new.

Usage: `hemlis -f file.purs` prints formatted output to stdout; `hemlis -f -w
file.purs` writes in place (skips the write if already formatted, reports
which files it touched). This is the debug `hemlis` binary, not
`hemlis-language-server`.

## Architecture

- `src/lib/lexer.rs` — `lex()` returns `(tokens, comments)`. Comments are
  collected in a fully separate pass (`lex_comments`) that never touches the
  layout/offside-rule state machine, so the parser/layout algorithm is
  provably unaffected (see `lexer.rs` tests `comments_are_captured_separately`
  / `comments_do_not_affect_layout`).
- `src/lib/source.rs` — `line_starts`/`span_to_byte_range`/`source_text`,
  extracted from `style.rs` (which used to have its own private copies) so
  the printer and the style checker share one implementation.
- `src/lib/print.rs` — the printer. Everything lives in a `Printer<'s>`
  struct with an eager indent-tracking `String` writer (no `Doc`/combinator
  IR, no line-fitting pass — see "Layout philosophy" below). Entry point:
  `print_module(source, module, comments) -> String`.
- CLI wiring: `Flag::Format`/`Flag::Write` in `src/lib/lib.rs`
  (`parse_modules`), `-f`/`-w` flags in `src/lib/main.rs`.

## Layout philosophy (why there's no Wadler/prettyplease-style engine)

The user's explicit ask: track whether the source had a construct expanded
across lines, and preserve that — not a general line-width-fitting algorithm.
Since every AST node already carries a `Span` with `(line, col)`, "was this
expanded in the source" is answered directly from spans, no trivia-preserving
CST needed.

Two helpers do all of it (`print.rs`, near the top of `impl Printer`):

- `breaks_before(a: Span, b: Span) -> bool` — is there a source line break
  between the end of `a` and the start of `b`. Local, adjacent-boundary only.
- `any_breaks(spans: &[Span]) -> bool` — true if any *adjacent* pair in the
  list has a break between them.

**Important gotcha, already hit once:** do not compare a whole construct's
*first-to-last* span (e.g. `first.lo() != last.hi()`) to decide multiline.
Early versions did this and it broke idempotence: if the last item in a list
is something that always prints across multiple lines regardless of its own
source layout (a nested `case`/`do` block, for instance), the *whole outer
construct* looks "multiline" on the second formatting pass even though
nothing about its own source layout changed. `any_breaks`/`breaks_before`
only ever look at the immediate boundary between two adjacent pieces, which
doesn't have this problem. If you add a new construct that decides
flat-vs-expanded, use these two helpers, not a first/last span comparison.

`list()` is the shared helper for bracketed comma-lists (arrays, records,
export/import lists, data constructors via a hand-rolled variant). Flat:
`open item, item close`. Expanded: leading-comma style,
`open item\n, item\n close`, matching common PureScript formatter
convention. `pad: bool` controls the flat-path inner spacing (`{ a, b }` /
`[ a, b ]` vs `(a, b)` — records/arrays pad, export/import lists don't).

`Expr::App` is a curried binary node (`App(App(App(f, a1), a2), a3)`), but is
printed by first flattening the whole spine (`Printer::app_spine`) into
`(head, [a1, a2, a3])` and deciding multiline-ness for the *whole* call at
once via `any_breaks`, the same way `list()` does — not by letting each
binary `App` layer decide independently. `Expr::Lambda` similarly checks
`breaks_before` between its last binder and its body to decide whether to
break after `->`. Without these, a `case`/`do` block buried inside one
argument of a call whose *other* arguments span multiple lines in the source
had no way to inherit the extra indent that implies: it printed at whatever
indent level was already active before the call started, which is often
shallower than sibling lines the call goes on to print — i.e. the block's own
contents appeared to print "before" (at a lower indent than) the block
itself. `Expr::Paren` gets its own `( ` ... `)`-on-its-own-line indented
block, but *not* via a span-based multiline decision the way everything else
here is - see "Session: paren blocks + the export-list blank line" below for
why (span comparisons for this one are provably unstable across formatting
passes) and how it's decided instead.

Multi-line `forall`/constraint/arrow chains (`Typ::Forall` →
`Typ::Constrained` → `Typ::Arr`, arbitrarily nested) are flattened so every
`.`/`=>`/`->` breaks to the *same* indent level rather than staircasing one
level deeper per nesting layer. This needed a printer-state flag,
`Printer::in_broken_sig`, set by `print_sig_typ` (the shared "name :: Typ"
helper used by every signature-shaped decl — `Decl::Sig`, `DataKind`,
`Foreign`, `ClassMember`, `InstBinding::Sig`, `LetBinding::Sig`, etc.) and
checked/propagated by `print_typ_arrow_chain` / `print_typ_constrained_chain`
/ the `Typ::Forall` and `Typ::Op` arms, so a nested chain doesn't re-indent
on top of the outer one. It's explicitly reset to `false` while printing a
record row's fields (`print_row`), since a record's braces are their own
bracketed context unrelated to whatever signature it's nested inside.

### `newline()` semantics — read this before touching it

`newline()` (write a line break at the current indent) is **idempotent by
design**: calling it twice in a row with nothing printed in between does
*not* produce a blank line — it reuses the existing line, and critically,
**does not re-indent it** to whatever the current level is now. This matters
because an inner construct's own `indent_in()` + `newline()` (e.g. a record
literal that decides to print expanded) can run immediately after an outer
context's `newline()` (e.g. a `do`-statement) with zero content between them;
without idempotent-newline, you get either a spurious blank line or (worse,
and it silently broke real-world parsing) the shared line gets re-indented to
the *inner* construct's deeper level, desyncing it from its sibling
statements and failing to reparse.

A **deliberate** blank line (between top-level decls, between the bare-import
group and the rest) is always written as `self.raw("\n")` directly, never via
`newline()` — that's the one call that bypasses the collapsing behavior. If
you add a new blank-line separator anywhere, use `raw("\n")`, not
`newline()`, or it'll get silently eaten.

### Comment placement

Comments live in a side-channel (`Printer::comments`, a cursor into the
sorted list `lex_comments` produced), not in the AST. `flush_comments_before(line)`
walks the cursor and emits (each on its own leading line — no
leading/trailing-on-same-line distinction yet, see Known gaps) every pending
comment before that line. **Every loop that prints a sequence of sibling
items must call this before each item**, or a comment sitting between two of
those items gets silently carried forward to whatever the next flush point
happens to be — this was a real bug (comment ended up relocated into an
unrelated record literal two declarations later). Current call sites: module
decls, imports, `list()` items (covers export/import lists, arrays, records),
data constructors, class members, instance bindings, let bindings,
do-statements, case branches, and once right before the `module` keyword
itself (in `print_header`, via `h.span().lo().0`).

### Two "already-parenthesized span" gotchas (parser quirks, not printer bugs)

- `Symbol`'s own span already includes its surrounding parens (the lexer
  captures `(<*>)` as one token via `lex_symbol`). `Expr::Symbol`/`Typ::Symbol`
  print it bare (`self.lit(s)`); do **not** add `raw("(")`/`raw(")")` around
  it (that was a real double-paren bug, now fixed — grep `print_qual` and the
  `Export::Symbol`/`Import::Symbol` arms for the pattern to copy).
- A bare `Qual` (e.g. the `A` in `A.do`/`A.ado`) has its span trimmed to
  *exclude* the trailing `.` (so that merging its span with a following
  name's span still yields correct text elsewhere in the codebase). Printing
  a `Qual` standalone needs the dot added back explicitly — that's what
  `Printer::print_qual` is for. Don't call `self.lit()` directly on a bare
  `Qual`.

### `Typ::Int` and `TypVarBinding` — two more parser-adjacent quirks

- `Typ::Int`'s span for a *negative* literal (`a :: -1`) covers only the `-`
  token, not the digits (a real pre-existing parser bug in `typ_atom` —
  `let span = p.span()` is captured before `kw_minus` runs). Worked around
  in the printer by using the already-parsed `i64` value directly
  (`i.0 .0.to_string()`) instead of slicing source text for this one node.
- `TypVarBinding`'s third field is the `@`-visible-type-application marker
  (`is_at`), not "wrap in parens" — parens are only syntactically required
  when there's a kind annotation (`forall (a :: Type).`), so that's what
  drives them in `print_typ_var_binding`.

## Session: closing the purs-tidy gap

A follow-up session diffed our output against `Array.purs` (real purs-tidy
output) and fixed everything the diff turned up:

- **Arrays/binder-arrays are now padded like records** (`[ a ]`, not `[a]`) —
  `Expr::Array`/`Binder::Array` now pass `pad: true` to `list()`, matching
  purs-tidy (was previously the one asymmetry between arrays and records).

- **`=`/`->`/`<-` now break onto a fresh indented line when the source had
  the RHS starting on its own line** — `Printer::print_arrow_rhs(before,
  arrow, e)` is the one shared implementation, used by every "keyword then
  expression" site: `Decl::Def`/`InstBinding::Def`/`LetBinding::Name`'s `=`
  (via `print_guarded_expr`'s `Unconditional` arm), a guarded clause's
  `=`/`->` (`print_guard_clause`, anchored to that clause's own last guard,
  not the outer `before`), `Expr::Lambda`'s `->`, `DoStmt::Stmt`'s `<-`,
  `Guard::Binder`'s `<-`, and `LetBinding::Pattern`'s `=`. Before this, all of
  these always glued flat (`f x = expr`), so a `case`/`do`/`let` starting a
  new source line right after one of these always collapsed back onto the
  same line, and any nested multiline construct only had one level less
  indent available than the source actually gave it.
  **This one is load-bearing, not just cosmetic**: for `DoStmt::Stmt`/
  `Guard::Binder` specifically, gluing a multiline RHS (typically `let ...
  in`) flat to `<-` can print it at the *same column* as the enclosing
  do-block's own statement column, which is invalid PureScript layout — the
  parser reads that as the enclosing block closing early and mis-parses the
  rest as a new statement (this was a real `REPARSE FAIL` found by the
  1422-file sweep, not just a style nit).

- **`let`/`in` layout**: `Expr::Let` now breaks `in`'s body onto its own
  line when the source had it there. There's no dedicated span for the `in`
  keyword itself (the parser doesn't capture one), so this can't use
  `breaks_before` directly against it — instead it compares the last
  binding's line to the body's line with a `> hi + 1` threshold (the same
  "was there a real gap" idiom used for blank-line detection elsewhere):
  a gap of exactly one line means the body shares `in`'s own line (`in x`),
  a gap of two or more means `in` had its own line and the body breaks onto
  another. Comparing directly against the last binding's line (gap `> 0`)
  is *not* the right check here and was a real bug hit while building this —
  `in` itself always occupies the line right after the bindings, so that
  naive comparison is true unconditionally the moment there's ≥1 binding.

- **Guard clauses stay flat when the source had them flat.**
  `GuardedExpr::Guarded` previously always broke every clause onto its own
  indented `| ...` line unconditionally. Now, if the source had a single
  clause glued to the declaration head (`deleteBy _ _ ys | isEmpty ys = []`),
  it stays that way; multiple clauses, or a clause that started on its own
  source line, still get the one-per-line indented style.

- **Multi-clause function definitions no longer get a blank line inserted
  between clauses.** `decls_are_glued` used to only recognize a `Sig`
  immediately followed by its own `Def`; it now also glues two `Decl::Def`s
  that share a name (pattern-matching clauses of one function), matching
  purs-tidy.

- **`forall`'s `.` now aligns under `::`/`=>`** when a signature is printed
  broken across lines — one extra leading space (`" . "` instead of `". "`),
  since `::`/`=>` are two characters wide and `.` is one.

- **Import grouping now includes `hiding` imports in the "open" group.**
  purs-tidy's real rule (confirmed against `import Prelude hiding (map)`
  sorting to the very front of the block, ahead of alphabetically-earlier
  modules) is "unqualified, no explicit name list" — i.e. any import that
  pulls names into scope openly, whether that's a bare `import Foo` or a
  `import Foo hiding (...)`. The `MergedImport` field driving this was
  renamed `is_bare` → `is_open` and its condition dropped the
  `hiding.is_empty()` requirement that used to exclude `hiding` imports from
  the group entirely.

- **Blank lines between declarations, and between `let` bindings, are now
  preserved as present-or-absent (0 or 1), never collapsed to "always
  exactly one" and never allowed to exceed one.** `print_module`'s decl loop
  and `print_let_bindings` both now compare the previous item's end line to
  the next item's *visible* start line (`Printer::next_visible_line` - the
  line of a leading comment if one is attached, else the item's own line;
  blank-line-ness is about what visually comes first) via a `> hi + 1`
  check, and only emit a separator when that's true. For `let`-bindings,
  where the separator needs to land *inside* an already-indented block
  rather than at column 0, `Printer::insert_blank_line()` + `write_indent()`
  produce a clean blank line (no trailing whitespace) followed by a
  correctly-reindented next line — plain `raw("\n")` alone would leave the
  *current* line's already-written indent spaces trailing on the blank line.
  Glued decls (`decls_are_glued`) still never get a blank line regardless.

- **`list()`'s multiline branch no longer double-indents when it's already
  sitting at a fresh line an outer construct just broke to.** This was the
  root cause of a nasty idempotence bug uncovered while building the `=`/`->`
  break above: `list()` (used by `Expr::Array`/`Expr::Record`) always did its
  own `indent_in()` + `newline()` before printing its opening bracket,
  unconditionally. When some *other* construct (e.g. the new `=`-break) had
  *already* broken to a fresh indented line right before calling into
  `list()`, `list()`'s own `newline()` became a silent no-op (per its
  documented idempotent-collapse behavior) - but its `indent_in()` still
  happened and stuck around for the rest of that list's items, so the
  opening bracket stayed at the outer level while every following item
  jumped one level deeper than it. Fixed by adding `Printer::at_fresh_line()`
  and having `list()` skip its own `indent_in()`/`indent_out()` pair
  entirely when it's already at a fresh line - the outer context's indent is
  reused directly instead of stacking another level on top of it.

- **Parser bug fix, not just a printer workaround**: `P::prev()` (used by
  `import_decl` to capture the closing-paren span of a `hiding (...)`/`(...)`
  import list) paired the *previous* token with `self.span()` — the *current*
  (next-to-parse) token's span — instead of that previous token's own span.
  In practice this made the last import in a file's `end` span reach into
  whatever came right after it (sometimes the next declaration's own name).
  Fixed at the root (`self.tokens.get(self.i - 1)` for both halves of the
  pair) since it's used in exactly two places, both for this one field.
  Required re-recording two `insta` parser snapshots and one golden fixture's
  embedded "expected stdout" span dump - all three diffs were exactly this
  fix (garbage span → correct closing-paren span), not new breakage.

## Session: paren blocks + the export-list blank line

A direct follow-up, closing the two gaps the previous session had explicitly
left open.

- **`Expr::Paren` now gets a `( ` ... `)`-on-its-own-line indented block**
  when its contents don't fit on one line, matching purs-tidy - e.g.
  `unsafePartial (fromJust (insertAt ...))` becomes
  `unsafePartial\n  ( fromJust\n      ( insertAt ...\n      )\n  )`.

  The first attempt at this used the same pattern as everywhere else in the
  printer: compare the open and close paren's source spans
  (`breaks_before(open, close)`) to decide flat-vs-block. That's wrong, and
  it's wrong in a way the corpus sweep actually caught (a fresh `NOT
  IDEMPOTENT` batch, ~47 files): a paren can wrap something that *always*
  prints across multiple lines regardless of its own source layout - most
  commonly a `case`/`do` with more than one branch/statement, which (by
  their own long-established, deliberate design) always break. When that
  happens, the *decision* to stay flat (correct, matching originally-flat
  source) still produces *output* where the close paren lands on a later
  line than the open one purely because of what's inside - and reparsing
  that output makes the same span comparison come out `true` on the next
  pass. Flat on pass 1, block-style on pass 2: not idempotent. This is
  exactly the class of bug the "Important gotcha" note under "Layout
  philosophy" above already warns about (don't decide multiline-ness from a
  span that a `case`/`do` child can silently stretch), just showing up
  through a different comparison (a wrapper's own open/close spans) than the
  original warning anticipated (a list's first-to-last span).

  The fix: decide by *rendering*, not by comparing spans. `Expr::Paren`
  prints `inner` into a scratch buffer (`Printer::render_indented`, backed by
  `std::mem::take`/`replace` on `Printer::out`, with `indent_in()` applied
  first so any nested breaks land at the right level), then checks whether
  that buffer contains a `'\n'` at all - block style if so, flat if not -
  before splicing it back into the real output with the appropriate
  wrapping. This is a pure function of the AST (does printing this exact
  subtree, with this exact indent, ever need a line break), so it's stable no
  matter how many times the result is reformatted. `Expr::Paren` always just
  glues `(` wherever it's called from and never relocates it - see "Session:
  don't let a subexpression 'move back' in indentation" below for why an
  earlier version of this fix that *did* relocate was itself a regression.

- **A real export list always gets a blank line before whatever follows
  it** (the first import, or the first decl if there are none) -
  `print_header` now unconditionally emits one right after `where` when
  `exports.is_some()`, regardless of what the source had there. This is a
  hard "always", not a "preserve 0-or-1" - deliberately different from the
  declaration/let-binding blank-line handling elsewhere (see "Known gaps"
  for why that boundary isn't just folded into the general mechanism). To
  avoid a *second* blank line getting added on top when there happen to be
  no imports to absorb the first one, `print_module` skips seeding
  `prev_hi_line` from the header's own span in exactly that case
  (`exports.is_some() && imports.is_empty()`) - otherwise the decl loop's
  own independent gap check (see the previous session's "0 or 1" blank-line
  work) would also see a gap and add a second `raw("\n")`.

## Session: don't let a subexpression "move back" in indentation

A direct follow-up to the paren-block session above, fixing an awkward case
it left behind: `a = (1\n  + 1)` in a `let` binding printed as
```
a = ( 1
    + 1
)
```
- the closing `)` visually dedents back past `a`'s own line, since `(` was
glued right after `= ` (mid-line, at whatever column that happened to be)
while the closing `)` prints at the *ambient* logical indent level (which
tracks levels, not columns - see "Layout philosophy"). The general principle
this violates: a subexpression should never look like it "moved back" to a
shallower indent than where it started. Wanted instead:
```
a =
  ( 1
      + 1
  )
```
i.e. break `=` (or `->`, or `in` - anywhere something glues directly in
front of a paren) *first*, so the whole block - including its closing `)` -
stays at or past the binding's own indent.

The first implementation put this fix inside `Expr::Paren` itself: check
`at_fresh_line()` (the same helper `list()` uses), and if not fresh, relocate
the whole `(` onto its own deeper line before printing. This is *wrong* -
`Expr::Paren` is also reached as one space-separated argument inside a flat
`Expr::App` (`map (\x -> ...) xs`), and relocating there rewrites that
paren's own source position. `Expr::App`'s multiline decision is itself
span-based (`any_breaks` over the call's head/args), so a self-relocated
paren flips that decision on the very next formatting pass - a fresh
`NOT IDEMPOTENT` regression the sweep caught immediately (~9 files). The
mistake was putting a "don't move back" fix inside `Expr::Paren`, which has
no way to distinguish "I'm glued after `arrow`" (needs the fix) from "I'm
glued as one flat `Expr::App` argument" (doesn't, and actively breaks if it
gets it).

The fix instead: `Expr::Paren` reverted to always just gluing `(` in place
(deciding its own flat-vs-block purely by rendering, as before - no
relocation, ever), and the "don't move back" logic moved to exactly the call
sites that know they're printing something glued directly in front of a
paren: `Printer::paren_would_break(e)` - `false` immediately unless `e` is
literally an `Expr::Paren`, otherwise renders it at the current indent into
a scratch buffer (discarded either way, comment cursor rewound after) and
checks for a line break, the same rendering-based decision `Expr::Paren`
itself uses. `print_arrow_rhs` (already the one shared implementation behind
`=`, `->`, `<-`, and every guarded clause - see the earlier session) now
breaks whenever this is true, not just when the source already had a break;
`Expr::Let`'s `in`-body check (which isn't routed through
`print_arrow_rhs`, since there's no `arrow` string to trim there) got the
same `|| self.paren_would_break(body)` addition directly. Nothing about
`Expr::App`'s own args - flat or one-per-line - changed at all, so the
`map (\x -> ...) xs` case is unaffected (and stayed idempotent throughout).

## Session: case branches and comment placement

Prompted by a real file (`../pay-backend/lib/TeslaCoil/QualityOfService.purs`)
whose `case`-branch spacing was getting silently deleted and whose comments
ended up "just whack." Both turned out to be real, fixable bugs - not the
usual "purs-tidy does something we deliberately don't" gap.

- **Case branches, `do`-statements, class members, and instance bindings now
  preserve blank-line presence (0-or-1)**, the same "Known gaps" item the
  previous "closing the purs-tidy gap" session explicitly left open for
  these sites (it only covered top-level decls and `let`-bindings then).
  All four are now routed through two new shared helpers,
  `Printer::print_siblings_body`/`print_indented_siblings`, which factor out
  the identical "one item per line, preserve a leading blank, flush a
  leading comment" loop `print_let_bindings` already had. `list()` (used by
  arrays/records/etc.) still has its own separate, longer-standing version of
  this same idea.

- **`GuardedExpr::Guarded`'s multiline branch never flushed comments per
  clause** - real bug, not a style gap: every leading comment on every
  clause of a multi-clause guarded function silently rode along to whatever
  flush point came next, landing in a dump at the very end of the function.
  Now flushed per-clause, same as every other sibling loop.

- **`list()`'s multiline branch flushed a comment *after* writing the
  leading `, `**, stranding the comma alone on a line by itself ahead of the
  comment instead of the comment sitting above the `, item` pair it
  precedes. Reordered.

- **`Expr::Let`'s body had no `flush_comments_before` of its own.** Every
  other "thing that follows a keyword" site does (list items, case
  branches, do-statements, let bindings...), but there's no natural
  sibling-loop for "the expression after `in`", so nobody flushed a comment
  sitting right before it - it rode along to whatever the body's own
  printing flushed next (observed: landing after a nested `case`'s own
  first branch's leading comment, instead of before the `case` itself).
  Fixed generally rather than as a one-off: `Printer::print_expr` now
  flushes comments before its own span as its first action, unconditionally
  - redundant (a no-op) at every site that already had its own flush (list
  items, branches, ...), and a real fix at every site that didn't (`Let`'s
  body, and any other single-expression-after-a-keyword site not yet hit in
  practice).

- **Trailing comments** (`foo = 1 -- like this`) are now supported at all,
  via `Printer::flush_trailing_comment(hi_line)`: if the very next pending
  comment starts on `hi_line`, glue it onto the current line instead of
  `flush_comments_before`'s always-its-own-leading-line treatment. Getting
  this right took two false starts, both caught by the corpus sweep, both
  informative about where this class of check is (and isn't) safe:

  1. First attempt: check at the end of *every* `print_expr` call (symmetric
     with the leading-flush fix above). Wrong - `print_expr` recurses into
     every subexpression, and most of them have *more of the same line*
     still to print after them. `Tuple a b -- c` became `Tuple -- c a b`:
     the check fired right after printing `Tuple` (the head), which happens
     to share the comment's line only because *everything* on that flat
     line does, not because `Tuple` is genuinely last.
  2. Second attempt: check inside `print_arrow_rhs` (the shared `=`/`->`/
     `<-` implementation), reasoning that its `e` is always the last thing
     printed by "its" caller. True for `Decl::Def`/`LetBinding`/guarded
     clauses, false for the two callers that aren't `print_guarded_expr`:
     `Expr::Lambda`'s `->` (a lambda can be nested arbitrarily deep inside a
     larger expression, with plenty more of that line still to come) and
     `Guard::Binder`'s `<-` (more guards can follow before the clause's own
     arrow). A comment trailing a whole line ended up glued mid-expression,
     right after a nested lambda's body specifically.

  The fix that actually holds: the check only lives at sites that have
  *positively confirmed* nothing else prints on that line afterward -
  `print_guarded_expr` (both arms - safe because `GuardedExpr` itself is
  only ever used as the tail of a decl/let-binding/case-branch, never
  nested), `print_siblings_body`/`print_indented_siblings` (each item is
  provably alone on its own line), `list()`'s multiline branch only (*not*
  the flat branch - see below), and `print_module`'s decl loop (a safety
  net for decl kinds that don't route through the others). Nowhere else.
  `print_arrow_rhs` and bare `print_expr` recursion deliberately do **not**
  call it.

  Two more subtleties, both found by the sweep, not by inspection:
  - **A trailing comment must end with its own `newline()`, not just
    `raw(" ") + text`.** A `--` line comment swallows everything after it on
    the same physical line - the very first version glued the comment
    straight onto the line with no break, and whatever the caller printed
    right after (a closing `}`, most commonly) silently became part of the
    comment, corrupting the source (`{ fileid: folderId -- comment }`
    reparsed as one unterminated line, `}` gone). Always followed by
    `newline()` now.
  - **`list()`'s *flat* branch cannot use this check at all**, even though
    its multiline branch can: several items share one physical line when
    flat, so "a pending comment starts on this item's own `hi()` line"
    doesn't mean *this* item is the last thing on that line - the same
    "Tuple a b" trap as false start #1, just via a different loop. Found
    against `Unsafe.purs`: `unsafeCrashWith { tag, trace: ..., m }
    -- NOTE[fh]: ...` (comment trailing the *entire call*, well outside the
    record) had its comment wrongly grabbed by `tag`, the record's *first*
    field, because it happened to share the comment's row along with
    everything else on that flat line.

- **`Printer::indent_out()` now fixes up stale indentation left by a
  trailing comment's own `newline()`.** The deepest bug of the session, and
  the reason the fix above isn't as simple as "add `newline()` and move on."
  `newline()` is idempotent by design (see "`newline()` semantics" above):
  once a line is "fresh," a later call trusts its indent is already correct
  and won't touch it. That assumption breaks when a trailing comment ends
  its line at a level that then gets `indent_out()`'d *before* anything else
  prints - e.g. a comment trailing the last branch of a `case` nested inside
  a `do`-statement: the comment's own `newline()` writes real indent spaces
  for the (soon to be abandoned) branches' level; `indent_out()` (twice,
  unwinding the case and the arrow break) changes `self.indent` but never
  touches those already-written spaces; the next sibling statement then
  prints glued to *that* stale, too-deep indent instead of its own. Fixed by
  having `indent_out()` check `at_fresh_line()` after decrementing, and if
  so, rewrite the trailing spaces for the new (shallower) level - cascades
  correctly through consecutive `indent_out()` calls, each re-checking
  against its own new level.

- **Two AST gaps, the same underlying pattern as the previous session's
  `P::prev()` parser fix**: a printer computing "was there a blank line
  before this sibling" from a span that's silently missing part of the
  construct it claims to represent.
  - `DoStmt::Let` carried no span for the `let` keyword itself - `.span()`
    (derived by merging every field) started at the first *binding*
    instead, which is *after* `let` whenever they print on separate lines
    (always, for our own output - bindings are always one-per-line). Every
    reparse of our own output undercounted the gap before a `let`-statement
    by exactly the row `let` itself occupies, inserting a spurious blank
    line. Fixed the way `Expr::Let`/`Do`/`Case` already do it: `DoStmt::Let`
    now carries the keyword's own `Span` (`nr.rs`/`style.rs`/`parser.rs`/
    `print.rs` all updated; one `insta` snapshot re-recorded).
  - `Binder::Array` carried no bracket spans at all (unlike `Expr::Array`,
    which already had them) - for a genuinely *empty* array binder (`[]`),
    `.span()` reduces to `Span::Zero` (nothing to merge), losing that
    binder's row entirely. A `case` branch whose sole pattern is `[]` then
    appeared to start wherever its *guarded expression* started instead -
    often a full row later - making the previous branch look further away
    than it is and inserting a spurious blank line. Fixed by giving
    `Binder::Array` open/close `Span`s, matching `Expr::Array`'s shape.
    (`Binder::Record` has the identical gap and isn't fixed - it's used
    extensively in `src/main.rs`, the language-server binary, which this
    work otherwise never touches, and it isn't demonstrated broken by the
    corpus sweep. Same fix if it ever needs it.)

- **`list()` now also flushes a comment sitting after the last item but
  before the closing bracket** - the one gap the trailing-comment work above
  couldn't close on its own, since neither `flush_comments_before(next
  item)` (there is no next item) nor `flush_trailing_comment` (only fires
  for a comment on the *last item's own* line, not one on a separate line
  still before the close) reaches it. `list()` gained a `close_span: Span`
  parameter - the closing bracket's own span where the caller has one
  (`Expr::Array`/`Record`/`Update`, `Binder::Array` after the fix above),
  `Span::zero()` otherwise (export/import lists, `Binder::Record`,
  `RecordUpdate::Branch` - `Span::zero().lo()` is `(0, 0)`, so the flush is
  a guaranteed no-op there, i.e. unchanged behavior) - and flushes
  `close_span.lo().0` right before printing `close`, in both branches and
  the empty-items case. Without it: a comment trailing the record's *last*
  field before its `}` rode past the record entirely into the middle of the
  next operator in an enclosing `#`-chain, again destabilizing that
  operator's own flat-vs-broken decision on reparse - the same class of
  span-instability bug as the very first `Expr::Paren` fix, just reached
  through a different construct. (`fn list` picked up an 8th parameter for
  this and needed `#[allow(clippy::too_many_arguments)]`.)

Everything above was found and fixed by iterating against the real 1422-file
corpus sweep, not by inspection - each bullet's "found against real-world
input" is literal.

One gap was deliberately left unfixed at the end of this session -
**`print_row`** (used for type-level rows: record types, and the `@(a ::
_, ...)` shape in a visible type application) **had no comment handling at
all**, the one remaining corpus-sweep failure at the time
(`Ctx/ContextProvider/Setup.purs`). A direct follow-up fixed it - see
"Session: the `print_row` rewrite" below.

## Session: the `print_row` rewrite

Closes the one gap the previous session left open. `print_row` used to be a
simple, always-flat, no-comment-handling loop (`{ a :: Int, b :: String }`,
unconditionally on one line, any comment silently riding past to the next
flush point). Rewritten to match `list()`'s architecture directly: a real
multiline decision via `any_breaks` over each field's (label ⊕ type) span
plus the tail's span if present, own bracket placement (`own_indent`, so it
can relocate to a fresh line exactly like `list()` does), and per-field
`flush_comments_before`/`flush_trailing_comment` plus one more flush for a
comment sitting after the last field but before the close - all copied
directly from `list()`, including the "flush before the leading comma, not
after" ordering and the "flat branch gets no trailing-comment check, only
the multiline branch does" asymmetry (see the false starts documented in the
previous session for why that asymmetry is load-bearing, not an oversight).

It isn't implemented by just *calling* `list()`, because a row's optional
`| tail` (`{ a :: Int | r }`) doesn't fit `list()`'s "comma-separated items
only" shape - it needed its own copy of the same pattern instead, with the
tail as one extra, non-comma segment before the close.

Two prerequisites, found while building this, not before:

- **`list()`-style flushing needs the closing bracket's own line, and
  `Typ::Row`'s parser arm was capturing the wrong one** - the exact same
  "off-by-one" class of bug as the `P::prev()` fix from an earlier session,
  just in a different spot: `kw_rp(p)?; let end = p.span();` captured
  *whatever comes after* the closing `)`, not the `)` itself, because the
  span was read *after* consuming the token instead of before (the
  `Typ::Paren` arm two lines below it already had this right - `let end =
  p.span(); kw_rp(p)?;` - which is what gave away that the `Typ::Row` arm
  was the odd one out). Since `Typ::Row`/`Typ::Record`'s `S<Row>` wrapper
  already merges an explicit open/close span (`start.merge(end)`) rather
  than deriving one from the row's own fields, this one is a one-line
  parser fix, not an AST change - `print_row` just reads `row.1.hi().0` for
  its close line, now that `end` (and so the merged span's `hi()`) actually
  points at `)`. Three `insta` parser snapshots needed re-recording; each
  diff was exactly this (an overly-wide/wrong span narrowing to the correct
  one), not new breakage.
- **Bracket printing had to move *into* `print_row`.** The old version was
  called as `raw("{"); print_row(&row.0, true); raw("}")` - the caller
  printed the brackets. `own_indent`-style relocation needs full control
  over *when* the open bracket prints (before or after a possible
  `indent_in()` + `newline()`), so `print_row` now takes `open`/`close`
  strings and prints them itself, matching `list()`'s own signature shape.

Verified against the real 1422-file corpus sweep: all 1422 clean (0 parse
failures, 0 reparse failures, 0 non-idempotent) - no gap remains from any
session documented in this file.

## Session: record fields hang one level deeper than the field itself

Found via a real remaining diff in `TeslaCoil/QualityOfService.purs`: a
record field whose value is a multiline `case`,
```
, shouldRetry: case _ of
    Left "timeout" -> true
    ...
```
printed with `case`'s branches only one level below the field (matching
`case`'s own single `indent_in()`, same as top-level `foo = case x of`),
but real purs-tidy output puts them *two* levels below the field. A second
real example (`Try.purs`, `tryResultCtors`) showed the same shape for a
nested record value instead of a `case`: `{ exit_reason:` breaks onto its
own line and the nested record's `{` lands two levels below `exit_reason`'s
own line, not one.

The two examples pin down the actual rule: **a record field's value always
sits one level deeper than the field itself, on top of whatever the value's
own construct does** - invisible when the value renders flat (`a: 1` is
unaffected), but stacking with the value's own indentation logic whenever it
doesn't. For `case`/`do` (`print_indented_siblings`, unconditional single
`indent_in()`, no `at_fresh_line()` check of its own) that's field-hang (+1)
then the construct's own +1 = two levels total. For a nested list-based value
(record/array, via `list()`'s `own_indent`) it's the same: the field's silent
`indent_in()` doesn't itself call `newline()`, so by the time `list()` runs
its own `!self.at_fresh_line()` check it's still mid-line - `list()` does its
*own* `indent_in()` + `newline()` on top, landing the value two levels below
the field and moving its own open bracket onto a fresh line, exactly matching
the `exit_reason:` example.

This is deliberately *not* the same behavior as `print_arrow_rhs` (`=`/`->`/
`<-`, decl/lambda/case-arrow/do-bind level) - `foo = case 1 of` stays at
`case`'s own single level (see `case_of_with_multiple_branches`), and that
established, corpus-verified behavior is untouched. The two are genuinely
different positions: a record field is one item of a list whose sibling
margin every other field also shares, so its value needs its own hang to
visually disambiguate "this indentation belongs to this field" from the
list's own item margin. A decl's or lambda's RHS has no such sibling-margin
ambiguity to resolve.

Fix: `print_record_label_expr`'s `RecordLabelExpr::Field` arm and
`print_record_update`'s `RecordUpdate::Leaf` arm (the exact same
"record-field-list-item" shape, just for `{ r | a = ... }` update syntax
instead of `{ a: ... }` construction - the second "similar delimiter" this
session covers) both now wrap their value print in `indent_in()`/
`indent_out()`, with **no `newline()` of their own** - purely an ambient
level bump, so it's a no-op unless the value's own printing calls `newline()`
for some other reason. Two new regression tests cover both sites with a
multiline `case` value. Verified against the real 1422-file corpus sweep:
0 parse failures, 0 reparse failures, 0 non-idempotent - and the
`QualityOfService.purs`/`Try.purs` diffs that motivated this are gone (the
only diff left in `Try.purs` is the pre-existing, unrelated data-constructor
trailing-comment placement issue, not touched by this fix).

## Session: operator chains and type formatting parity

Found via real user reports (not the corpus sweep, for once - all of this
was invisible to the 1422/1423-file sweep since it needs a right-associative
operator chain 3+ deep, or a `Typ::App`/`Typ::Paren` shape the corpus just
didn't happen to contain in that form). Four separate bugs, one running
theme: `Expr`'s and `Typ`'s printing had quietly drifted apart, and each gap
only showed up on a source shape the corpus sweep hadn't hit yet.

1. **Right-associative operator chains drifted one indent level per
   operator.** `Expr::Op`'s multiline branch did its own `indent_in()`
   around printing its right operand - fine for a *left*-nested chain (each
   node's own `indent_in`/`indent_out` is balanced and sequential before the
   next one starts), but a right-associative operator (`<>` is `R(6)`, see
   `op_fixity`) nests the tree on the *right*, so each subsequent `Op` node
   printed *inside* the previous one's own `indent_in` block - three or more
   chained `<>` visibly staircased deeper with every operator. Fixed by
   `op_spine`: flatten the tree (regardless of which way precedence nested
   it) into the flat in-order sequence of operands/operators the source
   actually wrote, and make one multiline decision for the whole chain
   instead of one independent decision per node. `Typ::Op` got the parallel
   `typ_op_spine` for the same one-decision-per-chain uniformity, though it
   was never exposed to the stacking bug itself - every type-level operator
   parses left-associative (`typ_fop` always returns `L(3)`), so a left-
   nested chain was already safe.

2. **`Typ::Paren` had no block-style multiline handling at all** - unlike
   `Expr::Paren` (which prints `( ` ... `)` on its own line when its contents
   don't fit flat, `print_paren_block`), a parenthesized type just glued
   `(inner)` together unconditionally, however large `inner` printed.
   Extracted `print_paren_block` as a shared helper (`render_indented` also
   generalized to take a print closure, not just `&Expr`) so both share the
   exact same block-style logic. Same gap in the "glue directly after `::`/
   `->`/`=>`, don't let the closing `)` look like it moved back" fix
   (`paren_would_break`/`print_arrow_rhs`) - added the `Typ` counterpart
   (`typ_paren_would_break`) and wired it into `print_sig_typ`,
   `print_typ_arrow_chain`, and `print_typ_constrained_chain`.

3. **`Typ::App` had no multiline handling at all** - always glued every
   argument flat with a single space, unlike `Expr::App` (`app_spine`,
   any-break-anywhere → one argument per line). A multi-argument type
   application whose arguments were deliberately one-per-line in the source
   (`Kanon.Table (...) TransactionRowR` with `Kanon.Table` and
   `TransactionRowR` each on their own line) printed with everything glued
   back onto one line instead. Fixed with the parallel `typ_app_spine` +
   the same any-break-anywhere decision `Expr::App` uses.

4. **Type operators/arrows/constraints don't get their own extra indent
   level** - deliberately different from how a value's operator chain
   works. Per explicit direction: a *non-operator* break (a `Typ::App`
   argument moving to its own line, a `Typ::Paren` block) still increases
   indent, but an *operator* break does not - `Typ::Op`/`Typ::Arr`/
   `Typ::Constrained` print each continuation at whatever indent is already
   active (`self.newline()`, no `indent_in()`), while `Expr::Op` keeps its
   own indent (values and types are allowed to look different here; only
   the *within-Typ* inconsistency in point 1 above was a bug). Also added
   the missing `type X = Typ` counterpart of `print_arrow_rhs`
   (`print_typ_alias_rhs`) - a type alias's `=` had no "break me instead of
   letting the paren move back" handling at all before this session.

Fixing 2-4 surfaced a real, pre-existing correctness bug once `Typ::App`
started actually nesting things: `in_broken_sig` (which forces a
deliberately-wrapped signature's chains to stay fully expanded even where
an individual segment looks flat) was leaking into parenthesized sub-
expressions, so a flat, single-line chain nested inside a paren got
force-broken purely because the *outer* declaration happened to be
multiline - directly violating "never break what the source wrote on one
line". Fixed by resetting `in_broken_sig` on entry to `print_paren_block`,
exactly the same reset `print_row` already does for record/row braces - a
paren is its own bracketed scope and must decide its own contents'
multiline-ness independently.

A second, narrower idempotence bug came out of testing the `Typ::Paren`
fix: `print_sig_typ` had grown two *different-shaped* branches for "the
type needs to break" (one where the source already had the break before
`::`, one where only the paren-would-break check fired), and only one of
them was a stable fixed point - printing the other shape moves the type
onto a line by itself, which makes the *first* branch's condition true on
the next parse, so it never stabilized on its own shape. Merged into a
single condition, always producing the shape that's already a fixed point.

7 new regression tests in `src/lib/print.rs` (53 → 60): the chain-stacking
case, `Typ::Paren`/`Typ::App` parity with their `Expr` counterparts, the
no-extra-indent-for-operators rule, the type alias `=` fix, the
`in_broken_sig`-leak regression (the exact `Kanon.Table (...) ...` shape
that motivated this session), and one asserting a fully single-line type
with nested parens/operators/application never gets broken up. Full corpus
sweep re-run clean (1423/1423: 0 parse failures, 0 reparse failures, 0
non-idempotent).

## Session: gluing after a multiline value/argument

Two more real user reports, both invisible to the corpus sweep for the same
reason as the previous session (needs a specific pre-broken source shape).
Both are the same underlying bug: something glued *after* a value/argument
without ever checking whether that value/argument itself needed to move,
so once the thing being glued to *did* print multiline, whatever followed
either glued onto its own first line (should have moved down entirely) or
right back onto its closing line (should have gotten its own line).

1. **A record field's value never checked whether it needed to move onto
   its own line** - `RecordLabelExpr::Field` (`{ label: value }`) and
   `RecordUpdate::Leaf` (`r { label = value }`) always glued `label:`/
   `label =` directly onto the value's first printed line, no matter what,
   relying entirely on the value's *own* construct to decide its own
   multiline-ness. That's correct for something like `case` (see the
   existing `record_field_with_case_value_hangs_one_level_deeper` test,
   which deliberately keeps `case` glued to `:`), but wrong for an `App`
   chain whose argument had already broken onto its own line in the source
   (`columnIn: List.singleton\n  (...)`, real code) - the field's value
   needs to move down as a whole here, the same way `print_arrow_rhs`
   already does for a decl's `=`. Fixed by giving records their own
   `print_record_field_rhs`: same `paren_would_break`/`breaks_before`
   decision as `print_arrow_rhs` for *whether* to move the value down, but
   - unlike `print_arrow_rhs` - keeping the unconditional extra hang level
   in *both* branches (not just the "stays glued" one), since that extra
   level is what the `case`-value tests above depend on and is orthogonal
   to whether the value also moves down.

2. **A constraint's/type-application's trailing argument could glue back
   onto a multiline argument's closing line.** `print_constraint` (a class
   constraint's `Name arg1 arg2 ...`) had no multiline handling at all -
   always glued every argument with a single space, so `Union a (row) b`
   with `row` printing as its own multiline block (correct) still glued
   ` b` right onto the row's closing `)` (wrong - `b` sits on its own
   source line right after the row). `Typ::App` already had *a* multiline
   policy (from the previous session) but the wrong shape for this case: it
   decides once, globally, for the *whole* argument list ("any break
   anywhere → every argument one-per-line, including ones before the first
   break"), which would have also incorrectly pulled `a` away from `Union`
   here even though nothing ever breaks between them. Replaced both with a
   shared `print_spine_args` helper: glue each argument with a space until
   the first source-span break, then switch to one-argument-per-line at a
   single shared indent level entered on that first break (not one
   `indent_in`/`indent_out` per argument) - so leading un-broken arguments
   stay glued, and everything from the first break onward, including a
   trailing argument after a multiline block, lands on its own line at the
   same level. `Typ::App`'s two existing regression tests already only
   ever exercised shapes where the very first argument was the one that
   broke, so this is a strict generalization - both still pass unchanged.

2 new regression tests in `src/lib/print.rs` (60 → 62): the record-field-
after-a-broken-`App` case and the `Union a (row) b` trailing-argument case,
both taken directly from the real reports. Full corpus sweep re-run clean
(1423/1423: 0 parse failures, 0 reparse failures, 0 non-idempotent).

## Session: the glued-token indent gap

A third real report, same shape as the previous two sessions: a nested block
looked shallower than it should - in one case shallower than *the very head
it's an argument of*, which reads as backward, not just "less indented."
Traced against real (git-verified, human/`purs-tidy`-formatted, not
hemlis-formatted) source from `../pay-backend/lib/Transaction/Storage.purs`
rather than synthetic examples, since the effect only shows up once a nested
block is reached through a specific kind of glued prefix.

Root cause: `:: `, ` . ` (`forall`'s continuation), and an operator chain's
`op ` are all printed as literal raw characters glued directly in front of
whatever comes next, *not* as a level bump - that's deliberate (it's how `.`
stays aligned under `::`), but it means the indent-level counter has no
memory of those characters' width. A plain continuation (another `->`/`=>`,
another chain operand) never needed that memory, because those print at the
*same* level as whatever glued them there by design (see "no extra indent
for operators", previous session). But a *nesting* shape reached the same
way - a constraint's own args, a bare `Array {...}` directly as a signature's
type, an `App` call as an operator chain's operand - does need one more
level when it breaks, or it lands at (or, worse, shallower than) the glued
prefix's own column instead of visibly deeper than it.

Fixed at three call sites, each an unconditional extra `indent_in`/
`indent_out` around printing the thing that's glued (same "invisible when
flat, stacks when it breaks" shape as `print_record_field_rhs`'s hang):
`print_constraint` (its own args, glued after a class name that's in turn
glued after `. `/`=> `), `print_sig_typ`'s already-broken branch (`typ`
glued after `:: ` - only when `typ` is itself a nesting shape: `App`/
`Record`/`Row`, never `Arr`/`Op`/`Constrained`/`Forall`, which would
wrongly push every `->`/`=>` continuation a level deeper), and `Expr::Op`
(each operand, glued after its own operator).

This can't fully close the gap to `purs-tidy`'s own output byte-for-byte in
the constraint/signature cases - `. `/`:: ` are 3 characters wide but
`INDENT` is a fixed 2, so a nesting shape reached through them still lands
one column short of lining up under the glued prefix's own text, an
architectural limit of a flat, level-multiple indent scheme (see "Layout
philosophy") rather than something fixable by another `indent_in`. The
operator-chain case (no glued-prefix width mismatch involved) closed
completely - reformatting the real `unpack`/`newBulkSql` functions this was
found against now reproduces the original source byte-for-byte for the
`Expr::Op`+`App` shape, and lands one column off (rather than a whole level
short, or backward past the head) for the constraint/signature shape.

Along the way, found (but did not fix, and did not introduce) a pre-existing,
separate bug: a comment sitting on its own line directly before an operator
in a chain (`# Kanon.unpack\n-- comment\n# R.modify ...`) gets split onto its
*own* orphaned line between the operator and its operand
(`#\n  -- comment\n  R.modify ...`) instead of staying attached ahead of the
whole `# R.modify` line. Confirmed present already in the prior commit,
unrelated to this session's `indent_in` additions - `Expr::Op`'s per-operand
comment flush point is simply after the operator token has already been
printed. Not fixed here; flagged for its own session.

2 new regression tests in `src/lib/print.rs` (62 → 64): the `Array {...}`-
directly-after-`::` case and the operator-chain-operand-that's-itself-a-
broken-call case, both taken directly from the real report and verified
byte-for-byte against the source they came from. Full corpus sweep re-run
clean (1423/1423: 0 parse failures, 0 reparse failures, 0 non-idempotent).

## Testing

- `cargo test --lib print::` — the real test suite, 53 tests in
  `src/lib/print.rs`. Includes `golden_fixtures_format_idempotently`, which
  sweeps every fixture under `tests/golden/**/*.purs` that parses cleanly and
  asserts `format(x) == format(format(x))`. This is the first line of
  defense against idempotence regressions and runs in every `cargo test`.
- Full workspace: `cargo test` (lexer/parser/style/golden), `cargo clippy
  --all-targets`.
- The **real** stress test is the external corpus sweep, not currently
  automated into `cargo test` (it lives outside this repo). To rerun it
  (`-P "$(nproc)"` runs files in parallel — each `hemlis -f` invocation is
  independent, so this is safe and considerably faster than the serial loop):
  ```bash
  cargo build --release --bin hemlis
  BIN=./target/release/hemlis
  SRC=/home/erik/Documents/Lesslie/pay-backend/lib   # sibling repo, read-only
  find "$SRC" -name "*.purs" | xargs -P "$(nproc)" -I{} sh -c '
    f="{}"
    once=$(mktemp); twice=$(mktemp); err1=$(mktemp); err2=$(mktemp)
    "'"$BIN"'" -f "$f" > "$once" 2>"$err1"
    if [ -s "$err1" ]; then echo "PARSE FAIL: $f"; exit 0; fi
    "'"$BIN"'" -f "$once" > "$twice" 2>"$err2"
    if [ -s "$err2" ]; then echo "REPARSE FAIL: $f"; exit 0; fi
    diff -q "$once" "$twice" >/dev/null || echo "NOT IDEMPOTENT: $f"
    rm -f "$once" "$twice" "$err1" "$err2"
  '
  ```
  Last run: all 1422 files clean (0 parse failures, 0 reparse failures, 0
  non-idempotent), most recently re-confirmed after "Session: the
  `print_row` rewrite" above. This sweep is what actually found nearly every
  real bug across every session documented in this file - not unit tests,
  not inspection. The "case branches and comment placement" session alone
  found and fixed six distinct real bugs this way (two of them from false
  starts within that same session), on top of two from "don't let a
  subexpression 'move back'" and several from "closing the purs-tidy gap"
  before it. If you change anything in `print.rs`, the lexer, or comment
  handling generally, rerun this - don't trust unit tests alone for this
  class of bug, and don't be surprised if it takes more than one round of
  fix-then-rerun to reach clean (it has, every time, this far).

## Known gaps / explicitly deferred

- **Blank-line preservation between declarations, `let` bindings,
  `do`-statements, case branches, class members, and instance bindings is
  done** (see "Session: closing the purs-tidy gap" and "Session: case
  branches and comment placement" above) — 0-or-1, never more, matching
  `purs-tidy`. Not extended to import merging's own internal grouping (bare
  vs. the rest) - hasn't shown up as a real diff or corpus-sweep failure.
  Same fix (`next_visible_line` + a `hi + 1` gap check, via
  `print_indented_siblings`/`print_siblings_body` if the site is a plain
  one-item-per-line list, `insert_blank_line()`/`write_indent()` directly
  otherwise) would apply if it ever does.
- `print_row` (type-level rows: record types, and `@(a :: _, ...)` visible
  type applications) now has full `list()`-equivalent comment handling and
  multiline layout - see "Session: the `print_row` rewrite" above. No known
  gaps remain in comment handling anywhere in the printer as of that
  session (verified: all 1422 corpus files clean).
- The header/import-block blank line (between a real export list and what
  follows) and `Expr::Paren`'s multiline block style are both now handled -
  see "Session: paren blocks + the export-list blank line" above. The header
  boundary is a hard "always blank", deliberately *not* folded into the
  general `next_visible_line`/`hi + 1` "preserve 0-or-1" mechanism used for
  declarations and let-bindings - purs-tidy's own behavior there is "always
  exactly one, regardless of source" rather than "preserve what was there",
  so a different (simpler) rule is the correct one for this specific
  boundary, not a gap to unify away.
- `App`'s "any break anywhere → expand every argument onto its own line"
  binary decision (see `Expr::App` above) doesn't match purs-tidy's true
  line-fitting behavior, which can keep some arguments inline while
  expanding others - e.g. purs-tidy keeps `Tuple (Just b)` together on one
  line (only the third argument, a multiline `case`, forces a break), while
  we put every argument of that same call on its own line once *any* of
  them needs to break. This is the one hunk left in the `Array.purs` diff
  after the fixes above. Deliberate - the whole point of this printer's
  design (see "Layout philosophy") is source-fidelity over line-fitting, and
  partial-inline expansion is exactly a line-fitting decision. Revisit only
  if closer purs-tidy parity specifically for multi-arg calls is wanted.
- Comment leading-vs-trailing placement **is** now distinguished (see
  "Session: case branches and comment placement" - `flush_trailing_comment`)
  at every site that's provably safe to check (guarded clauses, sibling
  lists, `list()`'s and `print_row`'s multiline branches, the top-level decl
  loop). Not wired into every conceivable expression position (e.g. a
  trailing comment on an `Op`'s left operand specifically, mid-chain) - only
  sites actually exercised by the 1422-file corpus so far.
- Multiline expansion for `forall`/arrow/constraint chains is wired through
  `print_sig_typ` (decl-level `name :: Typ` sites) and general `Typ::Op`/
  `Expr::Op`. `Row`/`Record` field types (`print_row`) have their own
  separate multiline handling now (see "Session: the `print_row` rewrite"),
  but a field's own arrow/constraint chain doesn't yet flatten the way a
  top-level signature's does. Not wired into `Typ::Kinded`, `Binder::Typed`,
  `Expr::Typed`, or `Binder::Op` either. None of these showed up as problems
  in the 1423-file sweep, but they're the same class of gap if a
  pathological case is found.
- No `textDocument/formatting` LSP handler yet (`src/main.rs`, the LSP
  binary) — `-f`/`-w` on the debug `hemlis` CLI only. This was next on the
  original plan (see "Original plan" below) but hasn't been started.
- Import merging concatenates name lists and sorts them, but doesn't attempt
  to match `purs-tidy`'s exact sort semantics beyond "sort by rendered text,
  case-sensitive" — verified consistent with observed real-world examples,
  not derived from `purs-tidy` source.
- No semantic-preservation check (parse(format(x)) AST == parse(x) AST,
  modulo spans) — only idempotence and clean-reparse are checked. Idempotence
  plus the 1422-file sweep catches almost everything in practice, but a
  targeted AST-diff test would be a stronger guarantee.

## Original plan

The original scoping/architecture plan (written before any code existed) is
still at `~/.claude/plans/what-would-be-required-harmonic-clock.md` — mostly
superseded by what's actually built now (described above), but has the
original phasing (comment capture → printer skeleton → fill out AST → CLI/LSP
wiring) and rationale for the no-Wadler-engine approach if useful context.

## Commits on this branch (`formatter`, oldest first)

1. `b8708ea` Capture comments separately from the layout token stream
2. `ef8ecb3` Add a printer skeleton and a -f/--format debug CLI flag
3. `9bae379` Fill out the remaining printer surface: full Decl/Expr/Binder coverage
4. `773ae7f` Add -w/--write to format files in place
5. `ca15f48` Fix double-parens, relocated comments, and multiline sig collapsing; mimic purs-tidy import grouping

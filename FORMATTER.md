# Formatter — status and notes

The PureScript formatter built on top of this repo's parser. Branch:
`formatter` (not yet merged to `main`).

## Status

Functionally complete. Covers the entire `Decl`/`Expr`/`Binder`/`Typ` AST
surface (only genuine `Error` parser-recovery nodes fall back to a verbatim
source-text slice). Verified idempotent and clean-reparsing against a large
external corpus of real-world `.purs` files (see "Testing" below). Unit
tests in `src/lib/print.rs` all passing; full suite (lib + style + golden)
and clippy clean.

Usage: `hemlis -f file.purs` prints formatted output to stdout; `hemlis -f
-w file.purs` writes in place (skips the write if already formatted);
`hemlis -f -c file.purs...` checks whether files are already formatted,
without writing, in parallel. This is the debug `hemlis` binary, not
`hemlis-language-server`.

## Architecture

- `src/lib/lexer.rs` — `lex()` returns `(tokens, comments)`. Comments are
  collected in a fully separate pass (`lex_comments`) that never touches the
  layout/offside-rule state machine, so the parser is provably unaffected by
  comment handling.
- `src/lib/source.rs` — `line_starts`/`span_to_byte_range`/`source_text`,
  shared between the printer and the style checker.
- `src/lib/print.rs` — the printer. Everything lives in a `Printer<'s>`
  struct with an eager indent-tracking `String` writer (no `Doc`/combinator
  IR, no line-fitting pass — see "Layout philosophy" below). Entry point:
  `print_module(source, module, comments) -> String`.
- CLI wiring: `Flag::Format`/`Flag::Write`/`Flag::Check` in `src/lib/lib.rs`
  (`parse_modules`/`check_format`), `-f`/`-w`/`-c` flags in `src/lib/main.rs`.

## Layout philosophy (why there's no Wadler/prettyplease-style engine)

The design goal: track whether the source had a construct expanded across
lines, and preserve that — not a general line-width-fitting algorithm. Every
AST node carries a `Span` with `(line, col)`, so "was this expanded in the
source" is answered directly from spans, no trivia-preserving CST needed.

Two helpers do almost all of it:

- `breaks_before(a: Span, b: Span) -> bool` — is there a source line break
  between the end of `a` and the start of `b`. Local, adjacent-boundary only.
- `any_breaks(spans: &[Span]) -> bool` — true if any *adjacent* pair in the
  list has a break between them.

**Gotcha:** never decide "is this multiline" from a whole construct's
*first-to-last* span (`first.lo() != last.hi()`). If the last item in a list
is something that always prints across multiple lines regardless of its own
source layout (a nested `case`/`do` block, for instance), that comparison
flips to `true` on the very next formatting pass even though nothing about
the item's own source layout changed — breaking idempotence.
`any_breaks`/`breaks_before` only ever look at the immediate boundary
between two adjacent pieces, which doesn't have this problem.

### Types are a floor; values relocate

A value's `=`/`->`/`<-`/an operator can and does move to its own line when
what follows would look bad glued (`print_arrow_rhs`, generalized over
`paren_would_break` for a parenthesized value and `keyword_block_would_break`
for a `case`/`do`/`ado`/`let` that's going to print multi-line - these have no
closing delimiter of their own to relocate around, so leaving their keyword
glued while their block's content hangs underneath looks just as wrong as a
paren's `)` regressing would). `Expr::Paren`'s own block-vs-flat choice stays
mostly content-driven (rendering `inner` and checking for a line break, so a
nested always-multiline construct still forces it regardless of layout) but
also treats a source break right after `(` or before `)` as forcing block
style too, even for trivial content that would otherwise print flat -
`print_paren_block`'s `force_block` parameter, computed by the caller from
the original span gap, not by `Expr::Paren` guessing at its own reprinted
position.
A type's `::`/`=>`/`->`/`.` never works that way: it is only ever a **floor**
that whatever comes right after it glues onto, permanently, no matter how
much that thing expands internally. Concretely: `Typ::Record`/`Typ::Row`
arguments hang glued in place under their own bracket rather than relocating
onto a fresh line (`print_row`/`print_paren_block`'s "own_indent" hang), the
opposite of how a value's own bracket behaves.

Because of this, `print_spine_args` — the shared "glue each argument until
something forces a break, then one-per-line from there" helper used by
`Typ::App`, `print_constraint`, and `print_inst_head` — treats a
`Typ::Paren` argument that would itself print multiline as a reason to
relocate it (and everything after it), the same as `Expr::App`'s own
arguments, but does *not* extend that to a bare `Typ::Record`/`Typ::Row`
argument, which already has its own correct hang-in-place behavior.

### Glued-prefix hangs

A raw token glued directly in front of something else (`:: `, `=> `, `. `,
an operator, a class name) is a fixed-width string the indent-level counter
has no memory of. If the thing glued after it is itself a nesting shape that
needs to break, it must hang under its own *real column* — captured via
`current_column()`/`with_indent_at`/`hang_glued`-style helpers — not an
approximate `indent_in()` level bump off the ambient baseline, or it lands
shallower than (sometimes even behind) the very prefix it's glued to.

### Own-relocation vs. double relocation

A construct glued after something else (an `App` call, a `list()`-based
value) relocates its own opening token/head onto a fresh line when it isn't
already at a fresh line and it's going to expand (`own_indent`). But a
*nested* instance of the same decision — e.g. a `list()` item that is itself
another `list()`-based value, or an `Expr::App` that is an `Op` chain's
operand — must not re-relocate on top of a position an *outer* construct
already committed to gluing something at. `Printer::glued_floor` marks that
position so a nested decision can tell the two apart and skip relocating.

### `Expr::Paren`'s block style

Decided by rendering `inner` into a scratch buffer and checking for an
actual line break in the result, not by comparing spans — a `case`/`do`
inside the parens can always print multiline regardless of its own source
layout, which would make a span-based decision unstable across formatting
passes. `Typ::Paren` shares the same block-style helper but hangs its
content under its own real column (see "Types are a floor" above) instead
of relocating, matching the different values-vs-types convention.

### `newline()` semantics

`newline()` is idempotent by design: calling it twice in a row with nothing
printed in between reuses the existing line rather than producing a blank
one, and does not re-indent it. A deliberate blank line (between top-level
decls, after a real export list) is always written as `self.raw("\n")`
directly, never via `newline()`.

### Comments

Comments live in a side channel (`Printer::comments`, a cursor into
`lex_comments`'s sorted list), not in the AST. Every loop that prints a
sequence of sibling items must call `flush_comments_before` before each
item, or a comment sitting between two items gets silently carried forward
to whatever flush point comes next. Trailing-vs-leading placement is
distinguished (`flush_trailing_comment`) only at call sites that can prove
nothing else prints on that physical line afterward — a naive "check after
every print" version misattaches a trailing comment to a subexpression that
merely happens to share its line, not the true last thing on it.

### Two parser-adjacent gotchas worth knowing

- `Symbol`'s span already includes its surrounding parens (the lexer
  captures `(<*>)` as one token). Print it bare; don't add parens.
- A bare `Qual` (e.g. the `A` in `A.do`) has its span trimmed to exclude the
  trailing `.`; printing one standalone needs the dot added back explicitly
  (`Printer::print_qual`).

## Testing

- `cargo test --lib print::` — the real regression suite in
  `src/lib/print.rs`. Includes `golden_fixtures_format_idempotently`, which
  sweeps every fixture under `tests/golden/**/*.purs` that parses cleanly and
  asserts `format(x) == format(format(x))`.
- Full workspace: `cargo test` (lexer/parser/style/golden), `cargo clippy
  --all-targets`.
- The real stress test is an external corpus sweep against a large body of
  real-world `.purs` files, not currently automated into `cargo test`:
  ```bash
  cargo build --release --bin hemlis
  BIN=./target/release/hemlis
  SRC=/path/to/some/real/purescript/project   # read-only, external to this repo
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
  This sweep is what has found nearly every real bug in this formatter —
  not unit tests, not inspection. If you change anything in `print.rs`, the
  lexer, or comment handling generally, rerun this. It can take more than
  one round of fix-then-rerun to reach clean.

  Idempotence is necessary but not sufficient: a bug can produce a stable,
  *wrong* fixed point every time (e.g. relocating something that should have
  stayed glued) and idempotence alone won't catch it — only a real user
  report or a byte-for-byte diff against known-good output surfaces that
  class of bug.

## Known gaps / explicitly deferred

- Import merging sorts a single import's name list to match `purs-tidy`'s
  5-tier kind order (class, type-operator, plain type, plain value,
  value-operator, alphabetical within each tier) — not extended to
  reordering *between* separate import declarations/blocks.
- `Expr::App`'s "any break anywhere → expand every argument onto its own
  line" is a binary, all-or-nothing decision — it doesn't match
  `purs-tidy`'s true line-fitting behavior, which can keep some arguments
  inline while expanding only the one that needs to break. Deliberate: the
  whole point of this printer's design is source-fidelity over line-fitting,
  and partial-inline expansion is a line-fitting decision. Revisit only if
  closer `purs-tidy` parity for multi-argument calls is wanted.
- Multiline expansion for `forall`/arrow/constraint chains is wired through
  `print_sig_typ` (decl-level `name :: Typ` sites) and `Typ::Op`/`Expr::Op`
  generally. A record field's own arrow/constraint chain doesn't flatten the
  way a top-level signature's does, and it's not wired into `Typ::Kinded`,
  `Binder::Typed`, `Expr::Typed`, or `Binder::Op`. Same class of gap if a
  case is found needing it.
- No `textDocument/formatting` LSP handler yet (`src/main.rs`) — `-f`/`-w`/
  `-c` on the debug `hemlis` CLI only.
- No semantic-preservation check (`parse(format(x))` AST equals `parse(x)`
  AST, modulo spans) — only idempotence and clean-reparse are checked in
  practice. A targeted AST-diff test would be a stronger guarantee.

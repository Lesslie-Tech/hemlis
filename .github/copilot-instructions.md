# Hemlis — Copilot Instructions

Hemlis is a fast, syntactic-only frontend/LSP for PureScript. It provides parsing, name resolution, goto-definition, and list-usages — but **no type information**.

## Crate layout

| Crate | Path | Role |
|---|---|---|
| `hemlis_lib` (lib) / `hemlis` (bin) | `src/` | Parser, lexer, AST, name resolution, CLI |
| `hemlis_macros` | `hemlis_macros/` | Proc-macro crate: `#[derive(Ast)]` |
| `hemlis-language-server` | `lsp/` | Tower-LSP server; shares `hemlis_lib` |

`lsp/` is a workspace member; `hemlis_macros` is a path dependency of the main crate.

## Build, test, lint

```bash
# Build everything
cargo build

# Build only the LSP binary (what CI ships)
cargo build --release --package=hemlis-language-server

# Run all tests
cargo test

# Run a single test by name
cargo test <test_name>

# Lint (warnings become errors)
cargo clippy --workspace --all-targets -- --deny warnings
```

Requires **nightly** Rust (see `rust-toolchains.toml`). CI uses `nightly` via `houseabsolute/actions-rust-cross`.

## Testing conventions

- Integration tests live in `tests/` as `.purs` source files.
- Golden/snapshot tests use the `goldentests` crate — expected output is embedded in or alongside the `.purs` files.
- More complex snapshots use `insta`.
- The binary (`src/main.rs`) is excluded from `cargo test` (`test = false` in `Cargo.toml`).

## Key source files

| File | What it does |
|---|---|
| `src/lexer.rs` | `logos`-based tokenizer; produces `Token` variants including layout tokens |
| `src/ast.rs` | All AST node types; `Span`, `Fi`, `Ud`, `S<T>` wrapper |
| `src/parser.rs` | Recursive-descent parser; entry point `module()` |
| `src/nr.rs` | Name resolution; entry point `resolve_names()` |
| `src/lib.rs` | Public API: `build_builtins()`, `parse_modules()`, `parse_and_resolve_names()` |
| `lsp/src/main.rs` | Full LSP backend (~2500 lines) |

## Parser macros (src/parser.rs)

Three local macros reduce repetition in the recursive-descent parser:

- `t!(TokenVariant)` — match and consume a token
- `kw!(keyword_str)` — match a keyword token
- `b!(expr)` — box an expression (`Box::new(...)`)

## AST conventions

### `#[derive(Ast)]` (from `hemlis_macros`)

Applied to almost every AST type. Derives two methods:

- `show(&self, indent: usize, w: &mut impl Write)` — pretty-print as indented tree
- `span(&self) -> Span` — recursively merge child spans

When adding new AST nodes, apply `#[derive(hemlis_macros::Ast)]` and ensure every field itself implements `Ast`.

### `S<T>` — spanned values

`S<T>` pairs a value with its `Span`. Use it to wrap any AST node that needs location tracking.

### `Ud` — unique identifiers

`Ud(u64_hash, char)` is a fast, hash-based name identity. The `char` is the first character for quick rejection before comparing hashes.

### `Fi` — file index

`Fi` is a `usize` wrapper representing a file. All spans carry a `Fi` so they can be traced back to source.

### `Span`

```rust
Span::Known(Fi, (lo_line, lo_col), (hi_line, hi_col))
Span::Zero  // unknown/missing
```

Merge spans with `span.merge(other)`.

## Name resolution conventions (src/nr.rs)

- Errors are **collected into `Vec<NRerrors>`** — no early returns on error; analysis continues.
- `Scope` enum partitions names: `Type | Term | Module | Class | Kind | Namespace | Label`.
- `Sort` enum annotates each usage: `Def | Ref | Import | Export`.
- `DefineSpans` groups the three parts of a definition: declaration, signature, body.
- Use `BTreeMap`/`BTreeSet` (not `HashMap`) for anything that must be deterministically ordered (most name tables).

## LSP backend conventions (lsp/src/main.rs)

- All shared state is stored in `DashMap` fields on the `Backend` struct — lock-free concurrent access.
- `or_!()` macro is used for optional-chaining inside LSP handlers.
- File ↔ index mapping: `fi_to_url: DashMap<Fi, Url>` and `url_to_fi: DashMap<Url, Fi>`.
- Re-analysis is triggered on `didOpen` / `didChange`; the LSP re-parses and re-resolves the whole workspace.

## PureScript built-ins

`build_builtins()` in `src/lib.rs` pre-populates `Prim`, `Prim.Boolean`, `Prim.Ordering`, `Prim.Row`, `Prim.RowList`, `Prim.Symbol`, `Prim.TypeError`, and `Prim.Coerce` so they are always available during name resolution without parsing source files.

## Release

CI builds `hemlis-language-server` for `x86_64-unknown-linux-gnu` and `aarch64-apple-darwin`, packages as `.tar.gz`, and attaches SHA-256 checksums. Triggered by a GitHub Release or `workflow_dispatch`. The build injects `GIT_COMMIT` and `BUILT_AT` as compile-time env vars (used in `version()`).

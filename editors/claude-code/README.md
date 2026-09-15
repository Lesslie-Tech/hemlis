# hemlis-lsp — Claude Code plugin

Gives [Claude Code](https://claude.com/claude-code) PureScript code
intelligence by running `hemlis-language-server` as an LSP server.

## What Claude gains

For every `.purs` file in the project:

- **Diagnostics after edits.** Claude sees unresolved terms
  (`Failed to resolve`) and unused definitions the moment it writes a file,
  rather than on the next compile.
- **Code navigation.** Go-to-definition, find references, hover, document
  symbols and workspace symbol search — more precise than grep on a large
  codebase.

Backed by the capabilities hemlis advertises: `definitionProvider`,
`referencesProvider`, `hoverProvider`, `documentSymbolProvider`,
`workspaceSymbolProvider`, `completionProvider`, `renameProvider`,
`codeActionProvider`, `documentFormattingProvider`.

## Install

`hemlis-language-server` must be on your `PATH` first — the plugin configures
the connection, it does not ship the binary:

```sh
which hemlis-language-server
```

Then, in Claude Code:

```
/plugin marketplace add Lesslie-Tech/hemlis
/plugin install hemlis-lsp@hemlis
```

Each person installs it for themselves. Pick **user** scope to get it in every
PureScript project you open, or **local** scope for a single repo.

Check it came up with `/plugin`: `hemlis-lsp` should appear under **Installed**
listing the `hemlis` LSP server, and the **Errors** tab should be empty. If the
binary isn't on your `PATH` the Errors tab shows
`Executable not found in $PATH`; nothing else in Claude Code is affected.

## Configuration

See [.lsp.json](.lsp.json).

| Field | Why |
| :--- | :--- |
| `command` | `hemlis-language-server` — the LSP binary, not the `hemlis` formatter CLI. |
| `extensionToLanguage` | `.purs` → `purescript`. Only one enabled plugin may claim `.purs`; if another also declares it, the first registered wins and this one never starts. |
| `workspaceFolder` | Pinned to `${CLAUDE_PROJECT_DIR}`. hemlis requests its workspace folders from the client on startup and indexes nothing until it gets an answer, so the root is stated explicitly. |
| `startupTimeout` | 30s. `initialize` returns in ~10ms and indexing happens after, so this is headroom rather than a measured requirement. |
| `maxRestarts` | 5 — restart a crashed server without looping forever. |
| `diagnostics` | `true` (also the default). Set `false` to keep navigation but stop diagnostics being pushed into Claude's context. |

`restartOnCrash` and `shutdownTimeout` are deliberately **not** set. They
require Claude Code v2.1.205 or later, and earlier versions skip an LSP server
entirely when it declares them. `restartOnCrash` already defaults to `true`.

### Startup behaviour

hemlis publishes diagnostics for every file in the workspace once, after it
finishes indexing; on a clean tree these are empty. Afterwards it only
republishes for files that change. On a ~2,800-file project indexing takes
about 6 seconds, during which navigation requests return empty.

### Not a typechecker

hemlis does syntactic and name analysis; it has no type information. Code that
is clean here can still fail to compile, so this does not replace running the
compiler or the tests.

## Troubleshooting

- **Server not starting** — check `/plugin` → **Errors**. A server skipped for
  an invalid config doesn't appear there; run `claude --debug` to see why.
- **No navigation or diagnostics** — hemlis may still be indexing. It reports
  its log file on stderr at startup
  (`Logging to "/var/folders/.../hemlis-<timestamp>.log"`).
- **Edited `.lsp.json`** — run `/reload-plugins` to restart the server.

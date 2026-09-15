# Hemlis
A faster frontend/lsp for PureScript.

## What currently exists
 - A simple parser that parses most of PureScript
 - Basic syntactical analysis (resolving names and references)
 - A simple goto-definition/list usages LSP
 - Most of it is somewhat fast

## Known limitations
 - Let-bindings (and where-bindings) in Purs are preprocessed to resolve some dependency orders. This is pretty wild and is currently not implemented - a simpler approach is used though this needs to be fixed. 
 - Only syntactical analysis - there is no type information
 - Comments are completely ignored - meaning they are not trivial to show in the LSP

## Possible extensions in no particular order (the short and incomplete list)
 - Rename symbol support
 - Supply the edtior with tokens to render things like resolved names
 - Better parser error recovery
 - Parse with correct operator precedence
 - Code actions
    - Import this symbol
    - Extract to function
    - Inline function
    - Remove unnessecary parenthesis
    - Add to exports
 - Find exports that are never imported
 - Pre-populate a match block with all constructors
 - A typechecker
 - Completions - list available names
 - Documentation on hover
 - Syntactic checks/linting (e.g. `$> pure` is probably wrong)
 - If-to-match and match-to-if

## Getting started

Getting started varies depending on which editor you use:

### Neovim - with LSP-config and not using Lazy
1. Download `hemlis-language-server` and add to path
2. Add this to LSP-config:
```lua
local util = require 'lspconfig.util'

local function client_with_fn(fn, req)
  return function()
    local bufnr = vim.api.nvim_get_current_buf()
    local client = util.get_active_client_by_name(bufnr, 'texlab')
    if not client then
      return vim.notify(('texlab client not found in bufnr %d'):format(bufnr), vim.log.levels.ERROR)
    end
    fn(client, bufnr, req)
  end
end

local function buf_build(client, bufnr, req)
  client.request(req, {}, function(err, result)
    if err then
      error(tostring(err))
    end
    local status = {
      [0] = 'Success',
      [1] = 'Error',
      [2] = 'Failure',
      [3] = 'Cancelled',
    }
    vim.notify('Got ' .. status[result.status], vim.log.levels.INFO)
  end, bufnr)
end

return {
  default_config = {
    cmd = { 'hemlis-language-server' },
    filetypes = { 'purescript', 'purs' },
    root_dir = util.root_pattern('.git'),
    single_file_support = true,
  },
  docs = {
    description = [[ ??? ]],
    default_config = {
      root_dir = [[util.root_pattern(".git")]],
    },
  },
}
```
3. Enable it by adding `nvim_lsp.hemlis.setup {}` to your config

### VS-code
https://github.com/pepebecker/vscode-lsp-config

### Helix
Add this to your Helix config to run Hemlis alongside the ordinary Purescript LSP:
```toml
[language-server.hemlis-language-server]
command = "hemlis-language-server"

[[language]]
name = "purescript"
language-servers = [ "hemlis-language-server", "purescript-language-server" ]
```

### Claude Code
This repo ships a Claude Code plugin that wires up `hemlis-language-server` as
an LSP server, giving Claude go-to-definition, references, hover, symbol search
and diagnostics on `.purs` files.

```
/plugin marketplace add Lesslie-Tech/hemlis
/plugin install hemlis-lsp@hemlis
```

See [editors/claude-code/README.md](editors/claude-code/README.md) for scopes,
configuration and troubleshooting.

#![allow(clippy::type_complexity)]
#![feature(btree_cursors)]

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs::File;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::ops::Bound;
use std::str::FromStr;
use std::sync::RwLock;
use std::thread::sleep;
use std::time::Duration;
// use tokio::sync::RwLock;

use ast::{Ast, Pos};
use dashmap::DashMap;
use futures::future::join_all;
use hemlis_lib::*;
use nr::{Export, NRerrors, Name, Scope, Visibility};
use rayon::iter::{IntoParallelRefIterator as _, ParallelIterator as _};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use tower_lsp_server::jsonrpc::{Error, ErrorCode, Result};
use tower_lsp_server::ls_types::notification::Notification;
use tower_lsp_server::ls_types::*;
use tower_lsp_server::{Client, LanguageServer, LspService, Server};
use tracing::instrument;
use tracing_subscriber::filter::FilterFn;
use tracing_subscriber::{layer::SubscriberExt, prelude::*, util::SubscriberInitExt};

macro_rules! or_ {
    ($e:expr, $b:block) => {
        if let Some(x) = $e {
            x
        } else $b
    }
}

fn span_to_range(s: &ast::Span) -> Range {
    range(s.lo(), s.hi())
}

fn range(lo: ast::Pos, hi: ast::Pos) -> Range {
    Range {
        start: pos_from_tup(lo),
        end: pos_from_tup(hi),
    }
}

#[derive(Debug)]
struct Backend {
    client: Client,

    prim: ast::Ud,

    locked: RwLock<()>,
    has_started: RwLock<bool>,
    names: DashMap<ast::Ud, String>,

    fi_to_uri: DashMap<ast::Fi, Uri>,
    fi_to_ud: DashMap<ast::Fi, ast::Ud>,
    fi_to_source: DashMap<ast::Fi, String>,
    uri_to_fi: DashMap<Uri, ast::Fi>,
    fi_to_version: DashMap<ast::Fi, Option<i32>>,
    ud_to_fi: DashMap<ast::Ud, ast::Fi>,

    importers: DashMap<ast::Ud, BTreeSet<ast::Ud>>,
    imports: DashMap<ast::Ud, BTreeMap<Option<ast::Ud>, Vec<Export>>>,

    previouse_global_usages: DashMap<ast::Fi, BTreeSet<(Name, ast::Span, nr::Sort)>>,
    // NOTE: Maybe I should remove these clones - but maybe there are bigger fish to fry in this
    // codebase.
    previouse_defines: DashMap<ast::Fi, BTreeSet<(Name, nr::DefineSpans)>>,

    // The option here should always be Some - but `None` lets us do a better partition search
    // here.
    available_locals: DashMap<ast::Fi, BTreeSet<((usize, usize), Option<Name>)>>,

    exports: DashMap<ast::Ud, Vec<Export>>,
    modules: DashMap<ast::Ud, ast::Module>,
    resolved: DashMap<ast::Ud, BTreeMap<(Pos, Pos), Name>>,
    defines: DashMap<Name, nr::DefineSpans>,
    // TODO: Fields are technically not memory managed here - they are just always appended. This
    // should probably be fixed - but ATM computers are fast LOL.
    //
    // This can easily be fixed by stripping out the field names if we come accross them - but we
    // can also like not do that.
    references: DashMap<ast::Ud, BTreeMap<Name, BTreeSet<(ast::Span, nr::Sort)>>>,

    syntax_errors: DashMap<ast::Fi, Vec<tower_lsp_server::ls_types::Diagnostic>>,
    name_resolution_errors: DashMap<ast::Fi, Vec<tower_lsp_server::ls_types::Diagnostic>>,
    fixables: DashMap<ast::Fi, Vec<(ast::Span, Fixable)>>,

    /// Whether the client supports dynamic registration of workspace/didChangeWatchedFiles.
    /// If false, the server sets up its own native file watcher.
    client_watch_dynamic_registration: std::sync::OnceLock<bool>,
}

impl Backend {
    fn resolve_name(&self, uri: &Uri, pos: Position) -> Option<Name> {
        let m = self
            .fi_to_ud
            .try_get(&*self.uri_to_fi.try_get(uri).try_unwrap()?)
            .try_unwrap()?;
        let pos = (pos.line as usize, pos.character as usize + 1);
        let lut = self.resolved.try_get(&m).try_unwrap()?;
        let cur = lut.lower_bound(Bound::Included(&(pos, pos)));
        let ((lo, hi), name) = cur.peek_prev()?;
        if !(*lo <= pos && pos <= *hi) {
            return None;
        }
        Some(*name)
    }

    fn resolve_name_and_range(&self, uri: &Uri, pos: Position) -> Option<(Name, Range)> {
        let m = self
            .fi_to_ud
            .try_get(&*self.uri_to_fi.try_get(uri).try_unwrap()?)
            .try_unwrap()?;
        let pos = (pos.line as usize, pos.character as usize + 1);
        let lut = self.resolved.try_get(&m).try_unwrap()?;
        let cur = lut.lower_bound(Bound::Included(&(pos, pos)));
        let ((lo, hi), name) = cur.peek_prev()?;
        if !(*lo <= pos && pos <= *hi) {
            return None;
        }
        Some((*name, range(*lo, *hi)))
    }

    fn got_refresh(&self, fi: ast::Fi, version: Option<i32>) -> bool {
        match self.fi_to_version.try_get(&fi) {
            dashmap::try_result::TryResult::Present(x) => x.value() != &version,
            dashmap::try_result::TryResult::Absent => true,
            dashmap::try_result::TryResult::Locked => true,
        }
    }

    fn get_documentation_for_name(&self, name: Name) -> String {
        use std::fmt::Write;
        let mut target = String::new();

        (|| {
            let def_at = self.defines.try_get(&name).try_unwrap()?;
            let fi = *self.ud_to_fi.try_get(&name.module()).try_unwrap()?;
            let source = self.fi_to_source.try_get(&fi).try_unwrap()?;

            let whole_thing = def_at
                .body
                .span()
                .merge(def_at.name)
                .merge(def_at.sig.unwrap_or(def_at.name));

            if whole_thing.line_range() < 8
                || (name.scope() != Scope::Module && name.name().is_proper())
            {
                // This is an artifact of the parser not knowing where comments belong - here it
                // thinks the comments are part of the tail of the def - not the head of the
                // next def.
                if let Some(x) = try_find_lines(
                    &source,
                    whole_thing.lo().0,
                    if whole_thing.hi().1 < 2 {
                        whole_thing.hi().0.saturating_sub(1)
                    } else {
                        whole_thing.hi().0
                    },
                ) {
                    writeln!(target, "```purescript").unwrap();
                    format_hover_snippet(x, true).split('\n').for_each(|x| {
                        writeln!(target, "{}", x).unwrap();
                    });
                    writeln!(target, "```").unwrap();
                }
            } else {
                let the_thing = def_at.name.merge(def_at.sig.unwrap_or(def_at.name));
                if let Some(x) = try_find_lines(&source, the_thing.lo().0, the_thing.hi().0) {
                    writeln!(target, "```purescript").unwrap();
                    format_hover_snippet(x, false).split('\n').for_each(|x| {
                        writeln!(target, "{}", x).unwrap();
                    });
                    writeln!(target, "```").unwrap();
                }
            }

            if let Some(x) =
                try_find_comments_before(&source, def_at.sig.unwrap_or(def_at.name).lo().0)
            {
                writeln!(target).unwrap();
                x.split("\n").for_each(|x| {
                    writeln!(target, "{}", strip_hover_comment_prefix(x)).unwrap();
                })
            }

            Some(())
        })();

        if !target.is_empty() {
            writeln!(target).unwrap();
        }
        write!(target, "{:?} {}", name.scope(), self.name_(&name.name())).unwrap();
        if let Some(module_name) = self.name(&name.module()) {
            write!(target, ", in {}", module_name).unwrap();
        }
        writeln!(target).unwrap();
        target
    }
}

fn try_find_word(source: &str, line: usize, offset: usize) -> Option<&str> {
    let mut it = source.match_indices("\n");
    let (line_start, _) = it.nth(line.saturating_sub(1))?;
    let (line_end, _) = it.next()?;
    let at = (line_start + 1 + offset).min(line_end);
    let start = source[..at].rfind(char::is_whitespace)?;
    let end = source[at..].find(char::is_whitespace)?;
    Some(&source[start + 1..end + at])
}

fn try_find_lines(source: &str, lo: usize, hi: usize) -> Option<&str> {
    let mut it = source.match_indices("\n");
    let (line_start, _) = it.nth(lo.saturating_sub(1))?;
    let (line_end, _) = it.nth(hi - lo)?;
    Some(&source[line_start + 1..line_end])
}

fn dedent(s: &str) -> String {
    let min_indent = s
        .split('\n')
        .filter(|line| !line.trim().is_empty())
        .map(|line| line.len() - line.trim_start().len())
        .min()
        .unwrap_or(0);
    s.split('\n')
        .map(|line| {
            if line.len() >= min_indent {
                &line[min_indent..]
            } else {
                line.trim_start()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn format_hover_snippet(source: &str, trim_trailing_comments: bool) -> String {
    let source = if trim_trailing_comments {
        source
            .split('\n')
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .skip_while(|line| {
                let line = line.trim();
                line.starts_with("--") || line.is_empty()
            })
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect::<Vec<_>>()
            .join("\n")
    } else {
        source.to_string()
    };
    dedent(&source)
        .split('\n')
        .map(|line| line.trim_end())
        .collect::<Vec<_>>()
        .join("\n")
}

fn strip_hover_comment_prefix(line: &str) -> &str {
    line.trim_start()
        .trim_start_matches("--")
        .trim_start()
        .trim_start_matches("|")
        .trim_start()
}

fn try_find_comments_before(source: &str, line: usize) -> Option<&str> {
    let mut it = source.match_indices("\n");
    let (at, _) = it.nth(line)?;
    let last = source[..at].rfind("\n")?;
    let mut first = last;
    while let Some(better_guess) = (|| {
        let better_guess = source[..first].rfind("\n")?;
        let comment_at = source[better_guess..first].find("--")?;
        if source[better_guess..better_guess + comment_at]
            .chars()
            .all(char::is_whitespace)
        {
            Some(better_guess)
        } else {
            None
        }
    })() {
        first = better_guess;
    }
    let first = first;
    if first == last {
        None
    } else {
        Some(&source[first + 1..last])
    }
}

#[cfg(test)]
mod tests {
    use super::{format_hover_snippet, strip_hover_comment_prefix};
    use std::str::FromStr;
    use tower_lsp_server::ls_types::{CodeActionOrCommand, TextEdit, Uri};

    #[test]
    fn hover_snippet_dedents_short_definitions() {
        let source = "        lookupSinkSatisfied :: Map StepId (Tuple StarBuck StarBuck) -> StarBuck\n        lookupSinkSatisfied amounts =\n\n          -- trailing comment";

        assert_eq!(
            format_hover_snippet(source, true),
            "lookupSinkSatisfied :: Map StepId (Tuple StarBuck StarBuck) -> StarBuck\nlookupSinkSatisfied amounts ="
        );
    }

    #[test]
    fn hover_doc_comments_strip_indented_haddock_prefixes() {
        assert_eq!(
            strip_hover_comment_prefix("        -- | The sum of the buy amounts"),
            "The sum of the buy amounts"
        );
        assert_eq!(
            strip_hover_comment_prefix("        -- NOTE[sg]: leave non-haddock text alone"),
            "NOTE[sg]: leave non-haddock text alone"
        );
    }

    /// Helper: apply a set of LSP TextEdits to a source string.
    /// Edits are applied in reverse order so that earlier edits don't
    /// shift the positions of later ones.
    fn apply_edits(source: &str, edits: &mut Vec<TextEdit>) -> String {
        // Convert (line, col) to byte offset
        let to_offset = |source: &str, line: u32, col: u32| -> usize {
            let mut offset = 0;
            for (i, l) in source.lines().enumerate() {
                if i == line as usize {
                    return offset + col as usize;
                }
                offset += l.len() + 1; // +1 for \n
            }
            offset
        };

        // Sort edits by start position in reverse so we can apply from end to start
        edits.sort_by(|a, b| {
            let a_start = (a.range.start.line, a.range.start.character);
            let b_start = (b.range.start.line, b.range.start.character);
            b_start.cmp(&a_start)
        });

        let mut result = source.to_string();
        for edit in edits.iter() {
            let start = to_offset(&result, edit.range.start.line, edit.range.start.character);
            let end = to_offset(&result, edit.range.end.line, edit.range.end.character);
            result.replace_range(start..end, &edit.new_text);
        }
        result
    }

    /// Send a JSON-RPC request through the LspService and return the response.
    async fn lsp_request(
        service: &mut super::LspService<super::Backend>,
        id: i64,
        method: &str,
        params: serde_json::Value,
    ) -> Option<tower_lsp_server::jsonrpc::Response> {
        use tower_service::Service;
        let req = tower_lsp_server::jsonrpc::Request::build(method.to_string())
            .params(params)
            .id(id)
            .finish();
        std::future::poll_fn(|cx| service.poll_ready(cx))
            .await
            .unwrap();
        service.call(req).await.unwrap()
    }

    /// Send a JSON-RPC notification (no id, no response expected).
    async fn lsp_notify(
        service: &mut super::LspService<super::Backend>,
        method: &str,
        params: serde_json::Value,
    ) {
        use tower_service::Service;
        let req = tower_lsp_server::jsonrpc::Request::build(method.to_string())
            .params(params)
            .finish();
        std::future::poll_fn(|cx| service.poll_ready(cx))
            .await
            .unwrap();
        let _ = service.call(req).await;
    }

    /// Build a Backend wrapped in an LspService, with an auto-responder
    /// for server→client requests (workspace_folders, registerCapability, etc.).
    fn build_test_service() -> super::LspService<super::Backend> {
        let (exports, prim, names) = hemlis_lib::build_builtins();
        let (service, socket) = super::LspService::build(|client| super::Backend {
            client,
            prim,
            names,
            locked: ().into(),
            has_started: false.into(),
            fi_to_uri: Default::default(),
            fi_to_ud: Default::default(),
            fi_to_source: Default::default(),
            ud_to_fi: Default::default(),
            uri_to_fi: Default::default(),
            fi_to_version: Default::default(),
            importers: Default::default(),
            imports: Default::default(),
            available_locals: Default::default(),
            previouse_defines: Default::default(),
            previouse_global_usages: Default::default(),
            exports,
            modules: Default::default(),
            resolved: Default::default(),
            defines: Default::default(),
            references: Default::default(),
            syntax_errors: Default::default(),
            name_resolution_errors: Default::default(),
            fixables: Default::default(),
            client_watch_dynamic_registration: std::sync::OnceLock::new(),
        })
        .finish();

        // Spawn a task to auto-respond to server→client requests.
        use futures::StreamExt as _;
        let (mut req_stream, mut resp_sink) = socket.split();
        tokio::spawn(async move {
            use futures::SinkExt as _;
            while let Some(req) = req_stream.next().await {
                if let Some(id) = req.id().cloned() {
                    // workspace/workspaceFolders → respond with []
                    // client/registerCapability → respond with null
                    // anything else → respond with null
                    let result = if req.method() == "workspace/workspaceFolders" {
                        serde_json::json!([])
                    } else {
                        serde_json::json!(null)
                    };
                    let response =
                        tower_lsp_server::jsonrpc::Response::from_ok(id, result);
                    let _ = resp_sink.send(response).await;
                }
            }
        });

        service
    }

    /// Run a code action test: parse source, trigger code actions at a position,
    /// find the action with the given title, apply its edits, and compare.
    async fn assert_code_action(
        source: &str,
        line: u32,
        character: u32,
        action_title: &str,
        expected: &str,
    ) {
        let uri = "file:///test.purs";
        let mut service = build_test_service();

        // Initialize
        lsp_request(
            &mut service,
            1,
            "initialize",
            serde_json::json!({
                "processId": null,
                "capabilities": {},
                "rootUri": null
            }),
        )
        .await;

        // Initialized (triggers has_started = true)
        lsp_notify(&mut service, "initialized", serde_json::json!({})).await;

        // Give the server a moment to finish initialized handler
        tokio::time::sleep(std::time::Duration::from_millis(50)).await;

        // Open document
        lsp_notify(
            &mut service,
            "textDocument/didOpen",
            serde_json::json!({
                "textDocument": {
                    "uri": uri,
                    "languageId": "purescript",
                    "version": 1,
                    "text": source
                }
            }),
        )
        .await;

        // Give on_change time to parse + resolve
        tokio::time::sleep(std::time::Duration::from_millis(100)).await;

        // Request code actions at the given position
        let resp = lsp_request(
            &mut service,
            2,
            "textDocument/codeAction",
            serde_json::json!({
                "textDocument": { "uri": uri },
                "range": {
                    "start": { "line": line, "character": character },
                    "end": { "line": line, "character": character }
                },
                "context": { "diagnostics": [] }
            }),
        )
        .await
        .expect("Expected a response from codeAction");

        let (_, body) = resp.into_parts();
        let result = body.expect("codeAction should succeed");

        let actions: Vec<CodeActionOrCommand> =
            serde_json::from_value(result).expect("Failed to parse code actions");

        let action = actions
            .iter()
            .find_map(|a| match a {
                CodeActionOrCommand::CodeAction(ca) if ca.title == action_title => Some(ca),
                _ => None,
            })
            .unwrap_or_else(|| {
                let titles: Vec<_> = actions
                    .iter()
                    .map(|a| match a {
                        CodeActionOrCommand::CodeAction(ca) => ca.title.as_str(),
                        CodeActionOrCommand::Command(c) => c.title.as_str(),
                    })
                    .collect();
                panic!(
                    "Code action {:?} not found. Available: {:?}",
                    action_title, titles
                );
            });

        let workspace_edit = action.edit.as_ref().expect("Code action should have edits");
        let changes = workspace_edit.changes.as_ref().expect("Should have changes");
        let file_edits = changes
            .get(&Uri::from_str(uri).unwrap())
            .expect("Should have edits for test file");

        let actual = apply_edits(source, &mut file_edits.clone());
        assert_eq!(actual, expected, "Code action {:?} produced wrong result", action_title);
    }

    #[tokio::test]
    async fn delete_unused_parameter() {
        let source = "\
module Test where

foo :: String -> Int -> Boolean
foo x y = y
";
        let expected = "\
module Test where

foo :: Int -> Boolean
foo y = y
";
        // Position on `x` (line 3, col 4)
        assert_code_action(source, 3, 4, "Delete unused parameter", expected).await;
    }
}

impl LanguageServer for Backend {
    #[instrument(skip(self))]
    async fn initialize(&self, params: InitializeParams) -> Result<InitializeResult> {
        let dynamic_watch = params
            .capabilities
            .workspace
            .as_ref()
            .and_then(|w| w.did_change_watched_files.as_ref())
            .and_then(|d| d.dynamic_registration)
            .unwrap_or(false);
        let _ = self.client_watch_dynamic_registration.set(dynamic_watch);
        Ok(InitializeResult {
            server_info: None,
            offset_encoding: None,
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Options(
                    TextDocumentSyncOptions {
                        open_close: Some(true),
                        change: Some(TextDocumentSyncKind::FULL),
                        save: Some(TextDocumentSyncSaveOptions::SaveOptions(SaveOptions {
                            include_text: Some(true),
                        })),
                        ..Default::default()
                    },
                )),
                hover_provider: Some(HoverProviderCapability::Options(HoverOptions {
                    work_done_progress_options: WorkDoneProgressOptions {
                        work_done_progress: Some(false),
                    },
                })),
                completion_provider: Some(CompletionOptions {
                    resolve_provider: Some(true),
                    trigger_characters: Some(vec![".".to_string()]),
                    work_done_progress_options: Default::default(),
                    all_commit_characters: None,
                    completion_item: Some(CompletionOptionsCompletionItem {
                        label_details_support: Some(true),
                    }),
                }),
                execute_command_provider: Some(ExecuteCommandOptions {
                    commands: vec!["load_workspace".to_string(), "random_command".to_string()],
                    work_done_progress_options: Default::default(),
                }),
                workspace: Some(WorkspaceServerCapabilities {
                    workspace_folders: Some(WorkspaceFoldersServerCapabilities {
                        supported: Some(true),
                        change_notifications: Some(OneOf::Left(true)),
                    }),
                    file_operations: None,
                }),
                semantic_tokens_provider: None,
                definition_provider: Some(OneOf::Left(true)),
                references_provider: Some(OneOf::Left(true)),
                rename_provider: Some(OneOf::Right(RenameOptions {
                    prepare_provider: Some(true),
                    work_done_progress_options: WorkDoneProgressOptions {
                        work_done_progress: Some(false),
                    },
                })),
                document_symbol_provider: Some(OneOf::Left(true)),
                workspace_symbol_provider: Some(OneOf::Left(true)),
                code_action_provider: Some(CodeActionProviderCapability::Options(
                    CodeActionOptions {
                        code_action_kinds: Some(Vec::new()),
                        work_done_progress_options: (WorkDoneProgressOptions {
                            work_done_progress: Some(false),
                        }),
                        resolve_provider: None,
                    },
                )),
                ..ServerCapabilities::default()
            },
        })
    }

    #[instrument(skip(self))]
    async fn initialized(&self, _: InitializedParams) {
        let folders = {
            tracing::info!("version {}", hemlis_lib::version());
            tracing::info!("Scanning...");
            let folders = self
                .client
                .workspace_folders()
                .await
                .ok()
                .flatten()
                .unwrap_or_default();
            self.load_workspace(folders.clone());
            tracing::info!("Done scanning");
            let mut futures = Vec::new();
            for i in self.fi_to_uri.iter() {
                futures.push(self.show_errors(*i.key(), None));
            }
            join_all(futures).await;
            folders
        };
        {
            let mut write = self.has_started.write().unwrap();
            *write = true;
        }
        {
            let registration = Registration {
                id: "workspace/didChangeWatchedFiles".to_string(),
                method: "workspace/didChangeWatchedFiles".to_string(),
                register_options: Some(serde_json::json!({
                    "watchers": [
                        {
                            "globPattern": "**/*.purs"
                        }
                    ]
                })),
            };

            self.client
                .register_capability(vec![registration])
                .await
                .unwrap();
        }

        // Fall back to a native file watcher when the client doesn't support dynamic
        // registration of workspace/didChangeWatchedFiles (e.g. neovim on Linux).
        let use_native_watcher = !self
            .client_watch_dynamic_registration
            .get()
            .copied()
            .unwrap_or(false);

        if use_native_watcher {
            let watch_dirs: Vec<std::path::PathBuf> = folders
                .iter()
                .filter_map(|f| {
                    let s = f.uri.to_string();
                    Some(std::path::PathBuf::from(s.strip_prefix("file://")?))
                })
                .collect();

            if !watch_dirs.is_empty() {
                // Build a Weak<Backend> from &self. tower-lsp-server wraps the backend in
                // Arc<S> inside its Router and dispatches by calling &*arc, so self is
                // always the interior of a live Arc<Backend>.
                let weak_self: std::sync::Weak<Backend> = unsafe {
                    std::sync::Arc::increment_strong_count(self as *const Backend);
                    let arc = std::sync::Arc::from_raw(self as *const Backend);
                    let weak = std::sync::Arc::downgrade(&arc);
                    // arc's drop restores the original refcount
                    weak
                };

                let (tx, mut rx) = tokio::sync::mpsc::unbounded_channel::<std::path::PathBuf>();

                std::thread::spawn(move || {
                    use notify::{Config, EventKind, RecommendedWatcher, RecursiveMode, Watcher};
                    let result = RecommendedWatcher::new(
                        move |result: notify::Result<notify::Event>| {
                            if let Ok(event) = result {
                                match event.kind {
                                    EventKind::Create(_) | EventKind::Modify(_) => {
                                        for path in event.paths {
                                            if path.extension().map_or(false, |e| e == "purs") {
                                                let _ = tx.send(path);
                                            }
                                        }
                                    }
                                    _ => {}
                                }
                            }
                        },
                        Config::default(),
                    );
                    match result {
                        Ok(mut watcher) => {
                            for dir in &watch_dirs {
                                if let Err(e) = watcher.watch(dir, RecursiveMode::Recursive) {
                                    tracing::error!("Failed to watch {:?}: {}", dir, e);
                                }
                            }
                            tracing::info!("Native file watcher active for {:?}", watch_dirs);
                            loop {
                                std::thread::sleep(Duration::from_secs(3600));
                            }
                        }
                        Err(e) => tracing::error!("Failed to create file watcher: {}", e),
                    }
                });

                tokio::spawn(async move {
                    while let Some(path) = rx.recv().await {
                        let backend = match weak_self.upgrade() {
                            Some(b) => b,
                            None => break,
                        };
                        let uri = match Uri::from_file_path(&path) {
                            Some(uri) => uri,
                            None => continue,
                        };
                        let source = match std::fs::read_to_string(&path) {
                            Ok(s) => s,
                            Err(_) => continue,
                        };
                        if let Some((fi, version, to_notify)) =
                            backend.on_change(TextDocumentItem {
                                text: &source,
                                uri,
                                version: None,
                            })
                        {
                            backend.show_errors(fi, version).await;
                            for (fi, v) in to_notify.iter() {
                                backend.show_errors(*fi, *v).await;
                            }
                        }
                    }
                });
            }
        }
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    #[instrument(skip(self, params))]
    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        if let Some((fi, version, to_notify)) = self.on_change(TextDocumentItem {
            text: &params.text_document.text,
            uri: params.text_document.uri.clone(),
            version: Some(params.text_document.version),
        }) {
            self.show_errors(fi, version).await;
            for (fi, v) in to_notify.iter() {
                self.show_errors(*fi, *v).await;
            }
            if !to_notify.is_empty() {
                let _ = self.client.workspace_diagnostic_refresh().await;
            }
        }

        tracing::info!(
            "!! {:?} FINISHED! {:?}",
            params.text_document.version,
            params.text_document.uri.to_string()
        );
    }

    #[instrument(skip(self, params))]
    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        if let Some((fi, version, to_notify)) = self.on_change(TextDocumentItem {
            text: &params.content_changes[0].text,
            uri: params.text_document.uri.clone(),
            version: Some(params.text_document.version),
        }) {
            self.show_errors(fi, version).await;
            for (fi, v) in to_notify.iter() {
                self.show_errors(*fi, *v).await;
            }
            if !to_notify.is_empty() {
                let _ = self.client.workspace_diagnostic_refresh().await;
            }
        }

        tracing::info!(
            "!! {:?} FINISHED! {:?}",
            params.text_document.version,
            params.text_document.uri.to_string()
        );
    }

    #[instrument(skip(self))]
    async fn did_save(&self, _: DidSaveTextDocumentParams) {}

    #[instrument(skip(self))]
    async fn did_close(&self, _: DidCloseTextDocumentParams) {}

    #[instrument(skip(self))]
    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let definition = || -> Option<GotoDefinitionResponse> {
            if let Some(name) = self.resolve_name(
                &params.text_document_position_params.text_document.uri,
                params.text_document_position_params.position,
            ) {
                let def_at = self.defines.try_get(&name).try_unwrap()?.value().clone();
                let uri = self
                    .fi_to_uri
                    .try_get(&def_at.name.fi()?)
                    .try_unwrap()?
                    .clone();
                Some(GotoDefinitionResponse::Scalar(Location {
                    uri,
                    range: span_to_range(&def_at.name),
                }))
            } else {
                let fi = *self
                    .uri_to_fi
                    .try_get(&params.text_document_position_params.text_document.uri)
                    .try_unwrap()?;
                let source = self.fi_to_source.try_get(&fi).try_unwrap()?;
                let position = params.text_document_position_params.position;
                let word_under_cursor =
                    try_find_word(&source, position.line as usize, position.character as usize)?;
                if word_under_cursor != "foreign" {
                    return None;
                };
                let mut uri = params
                    .text_document_position_params
                    .text_document
                    .uri
                    .to_file_path()?;
                uri.to_mut().set_extension("erl");
                Some(GotoDefinitionResponse::Scalar(Location {
                    uri: Uri::from_file_path(uri)?,
                    range: range((0, 0), (0, 0)),
                }))
            }
        }();
        Ok(definition)
    }

    #[instrument(skip(self))]
    async fn references(&self, params: ReferenceParams) -> Result<Option<Vec<Location>>> {
        let reference_list = || -> Option<Vec<Location>> {
            let name = self.resolve_name(
                &params.text_document_position.text_document.uri,
                params.text_document_position.position,
            )?;
            Some(
                self.references
                    .try_get(&name.module())
                    .try_unwrap()?
                    .get(&name)?
                    .iter()
                    .filter_map(|(s, sort): &(ast::Span, nr::Sort)| {
                        if !sort.is_def_or_ref() {
                            return None;
                        }
                        let uri = self.fi_to_uri.try_get(&s.fi()?).try_unwrap()?;
                        let range = span_to_range(s);

                        Some(Location::new(uri.clone(), range))
                    })
                    .collect::<Vec<_>>(),
            )
        }();
        Ok(reference_list)
    }

    #[instrument(skip(self))]
    async fn symbol(
        &self,
        params: WorkspaceSymbolParams,
    ) -> Result<Option<WorkspaceSymbolResponse>> {
        let mut symbols = Vec::new();
        for i in self.previouse_defines.iter() {
            let fi = i.key();
            let names = i.value();
            for (Name(scope, ns, n, vis), at) in names.iter() {
                if *vis != Visibility::Public {
                    continue;
                }
                let n = self.name_(n);
                let ns = self.name_(ns);
                if Some(fi) != at.name.fi().as_ref() {
                    continue;
                };
                if !(n.starts_with(&params.query)
                    || ns.starts_with(&params.query)
                    || format!("{:?}", scope).starts_with(&params.query))
                {
                    continue;
                };
                let name = format!("{}.{}", ns, n);
                #[allow(deprecated)]
                let out = SymbolInformation {
                    name,
                    kind: match scope {
                        Scope::Kind => SymbolKind::INTERFACE,
                        Scope::Type if n.starts_with(|c| matches!(c, 'a'..='z' | '_')) => {
                            SymbolKind::VARIABLE
                        }
                        Scope::Type => SymbolKind::INTERFACE,
                        Scope::Class => SymbolKind::CLASS,
                        Scope::Term if n.starts_with(|c| matches!(c, 'A'..='Z' | '_')) => {
                            SymbolKind::CONSTRUCTOR
                        }
                        Scope::Term => SymbolKind::FUNCTION,
                        Scope::Module => SymbolKind::MODULE,
                        Scope::Namespace => SymbolKind::NAMESPACE,
                        Scope::Label => SymbolKind::FIELD,
                    },
                    tags: None,

                    deprecated: None,

                    location: {
                        let uri = self.fi_to_uri.try_get(fi).unwrap().clone();
                        let range = span_to_range(&at.name);
                        Location::new(uri, range)
                    },

                    container_name: None,
                };
                symbols.push(out);
            }
        }
        Ok(Some(symbols.into()))
    }

    #[instrument(skip(self))]
    async fn document_symbol(
        &self,
        params: DocumentSymbolParams,
    ) -> Result<Option<DocumentSymbolResponse>> {
        let mut symbols = Vec::new();
        let fi_inner = if let Some(fi) = self
            .uri_to_fi
            .try_get(&params.text_document.uri)
            .try_unwrap()
        {
            *fi
        } else {
            return Err(error(line!(), "File not loaded"));
        };
        if let Some(names) = self.previouse_defines.try_get(&fi_inner).try_unwrap() {
            for (Name(scope, _, n, vis), at) in names.iter() {
                let at = at.name;
                if *vis != Visibility::Public {
                    continue;
                }
                let fi = if let Some(fi) = at.fi() { fi } else { continue };
                let name = match self.names.try_get(n).try_unwrap() {
                    Some(n) => n.clone(),
                    None => continue,
                };
                #[allow(deprecated)]
                let out = SymbolInformation {
                    name: name.clone(),
                    kind: match scope {
                        Scope::Kind => SymbolKind::INTERFACE,
                        Scope::Type if name.starts_with(|c| matches!(c, 'a'..='z' | '_')) => {
                            SymbolKind::VARIABLE
                        }
                        Scope::Type => SymbolKind::INTERFACE,
                        Scope::Class => SymbolKind::CLASS,
                        Scope::Term if name.starts_with(|c| matches!(c, 'A'..='Z' | '_')) => {
                            SymbolKind::CONSTRUCTOR
                        }
                        Scope::Term => SymbolKind::FUNCTION,
                        Scope::Module => SymbolKind::MODULE,
                        Scope::Namespace => SymbolKind::NAMESPACE,
                        Scope::Label => SymbolKind::FIELD,
                    },
                    tags: None,
                    deprecated: None,

                    location: {
                        let uri = self.fi_to_uri.try_get(&fi).unwrap().clone();
                        let range = span_to_range(&at);
                        Location::new(uri, range)
                    },

                    container_name: None,
                };
                symbols.push(out);
            }
        }
        Ok(Some(DocumentSymbolResponse::Flat(symbols)))
    }

    #[instrument(skip(self))]
    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;
        tracing::info!("completion..");
        let completions = || -> Option<Vec<CompletionItem>> {
            let fi = *self.uri_to_fi.try_get(&uri).try_unwrap()?;
            let me = *self.fi_to_ud.try_get(&fi).try_unwrap()?;
            let line = position.line as usize;
            let source = self.fi_to_source.try_get(&fi).try_unwrap()?;
            let to_complete =
                try_find_word(&source, line, position.character as usize)?.to_string();
            drop(source);

            tracing::info!("completion for \"{:?}\"", to_complete);
            let maybe_first_letter = to_complete.chars().nth(0);

            let mut out = Vec::new();

            // TODO: If the user has typed anything here - we can get an inference of the kind of
            // symbol and narrow the search significantly. If we know it's a type we can ignore
            // terms and vice versa.

            // Imported
            let (namespace, var) = if let Some(last) = to_complete.rfind('.') {
                (
                    Some(ast::Ud::new(to_complete[..last].into())),
                    to_complete[last + 1..].into(),
                )
            } else {
                (None, to_complete.clone())
            };
            if let Some(imports) = self
                .imports
                .try_get(&me)
                .try_unwrap()
                .and_then(|x| x.get(&namespace).cloned())
            {
                for n in imports.iter().flat_map(|x| x.to_names()) {
                    if n.scope() == Scope::Namespace {
                        continue;
                    }
                    let name = self.name_(&n.name());
                    if name.starts_with(&var) {
                        let mut completion = CompletionItem::new_simple(
                            name.to_string(),
                            format!("Imported {:?}", n.scope()),
                        );
                        completion.documentation =
                            Some(Documentation::MarkupContent(MarkupContent {
                                kind: MarkupKind::Markdown,
                                value: self.get_documentation_for_name(n),
                            }));
                        out.push(completion);
                    }
                }
            } else {
                let maybe_field = to_complete.split(".").last();
                tracing::info!("completion for field \"{:?}\"", maybe_field);
                let maybe_first_letter = maybe_field.and_then(|x| x.chars().next());
                // We're assuming it's a field we're looking at since there's not an imported
                // namespace with this name.
                let fields: Vec<_> = self
                    .references
                    .try_get(&ast::Ud::zero())
                    .try_unwrap()?
                    .iter()
                    .filter_map(|(k, v)| {
                        if k.scope() != nr::Scope::Label || v.is_empty() {
                            None
                        } else {
                            Some(*k)
                        }
                    })
                    .collect::<Vec<_>>();

                for n in fields.iter() {
                    if maybe_first_letter.is_none()
                        || n.name().starts_with(maybe_first_letter.unwrap())
                    {
                        // TODO: If this is nice - and people want more - I can add more info here when
                        // they know what they want.
                        let name = self.name_(&n.name());
                        let mut completion = CompletionItem::new_simple(
                            name.to_string(),
                            format!("Define {:?}", n.scope()),
                        );
                        completion.documentation =
                            Some(Documentation::MarkupContent(MarkupContent {
                                kind: MarkupKind::Markdown,
                                value: self.get_documentation_for_name(*n),
                            }));
                        out.push(completion);
                    }
                }
            }

            if namespace.is_none() {
                // Locals
                let lut = self.available_locals.try_get(&fi).try_unwrap()?;
                let mut cur = lut.lower_bound(Bound::Included(&((0, line), None)));
                while let Some(((l, h), n)) = cur.peek_next() {
                    let n = n.expect("This option is only for searching!");
                    if !(*l <= line && line <= *h) {
                        break;
                    }

                    if maybe_first_letter.is_none()
                        || n.name().starts_with(maybe_first_letter.unwrap())
                    {
                        let name = self.name_(&n.name());
                        let mut completion = CompletionItem::new_simple(
                            name.to_string(),
                            format!("Local {:?}", n.scope()),
                        );
                        completion.documentation =
                            Some(Documentation::MarkupContent(MarkupContent {
                                kind: MarkupKind::Markdown,
                                value: self.get_documentation_for_name(n),
                            }));
                        out.push(completion);
                    }

                    cur.next();
                }

                // Defines
                let defines: Vec<_> = self
                    .defines
                    .iter()
                    .filter_map(|x| {
                        let k = x.key();
                        if k.module() != me {
                            return None;
                        }
                        Some(*k)
                    })
                    .collect();
                for n in defines.iter() {
                    if n.module() != me {
                        continue;
                    }
                    if maybe_first_letter.is_none()
                        || n.name().starts_with(maybe_first_letter.unwrap())
                    {
                        // TODO: If this is nice - and people want more - I can add more info here when
                        // they know what they want.
                        let name = self.name_(&n.name());
                        let mut completion = CompletionItem::new_simple(
                            name.to_string(),
                            format!("Define {:?}", n.scope()),
                        );
                        completion.documentation =
                            Some(Documentation::MarkupContent(MarkupContent {
                                kind: MarkupKind::Markdown,
                                value: self.get_documentation_for_name(*n),
                            }));
                        out.push(completion);
                    }
                }
            }
            Some(out)
        }();
        Ok(completions.map(CompletionResponse::Array))
    }

    #[instrument(skip(self))]
    async fn rename(&self, params: RenameParams) -> Result<Option<WorkspaceEdit>> {
        let name = self
            .resolve_name(
                &params.text_document_position.text_document.uri,
                params.text_document_position.position,
            )
            .ok_or_else(|| error(line!(), "Failed to resolve name"))?;

        // NOTE: We don't validate the name here - so it is possible to end up in a state where the
        // codebase doesn't parse. I don't see this as a huge loss - since the edit can be undone.
        let new_text = params.new_name;
        let mut edits = HashMap::new();
        for at in self
            .references
            .try_get(&name.1)
            .try_unwrap()
            .ok_or_else(|| error(line!(), "Failed to read references"))?
            .get(&name)
            .ok_or_else(|| error(line!(), "Unknown name - how did we get here?"))?
            .iter()
            .map(|(at, _)| *at)
            .collect::<BTreeSet<_>>()
            .into_iter()
        {
            let uri = self
                .fi_to_uri
                .try_get(&if let Some(fi) = at.fi() { fi } else { continue })
                .try_unwrap()
                .ok_or_else(|| error(line!(), "Unknown file - how did we get here?"))?
                .clone();
            let range = span_to_range(&at);
            edits.entry(uri).or_insert(Vec::new()).push(TextEdit {
                range,
                new_text: new_text.clone(),
            });
        }
        // At least the neovim client is tricky when doing renames - it applies the edits one after
        // the other. This makes us validate EACH version of the document as the edits are applied.
        // If we want to keep the bandwith low the edits do make sense - but given the current
        // state of the LSP this isn't how it works.
        //
        // I tried adding a sleep to the sending of messages - but that doesn't really work
        // apparently.
        //
        // At the same time - I can't reasonably assume that all clients work this way. If I did it
        // could possible be fixed.
        //
        // The rust LSP waits a few seconds (or is just really slow).

        tracing::info!(
            "rename suggested with {:?} edits",
            edits.values().map(|x| x.len()).collect::<Vec<_>>()
        );

        Ok(Some(WorkspaceEdit::new(edits)))
    }

    #[instrument(skip(self))]
    async fn prepare_rename(
        &self,
        params: TextDocumentPositionParams,
    ) -> Result<Option<PrepareRenameResponse>> {
        if let Some((name, range)) =
            self.resolve_name_and_range(&params.text_document.uri, params.position)
        {
            Ok(Some(PrepareRenameResponse::RangeWithPlaceholder {
                range,
                placeholder: self.name_(&name.name()),
            }))
        } else {
            return Ok(None);
        }
    }

    #[instrument(skip(self))]
    async fn code_action(&self, params: CodeActionParams) -> Result<Option<CodeActionResponse>> {
        let uri = params.text_document.uri.clone();
        let fi = *or_!(self.uri_to_fi.try_get(&uri).try_unwrap(), {
            return Err(error(line!(), "File not loaded"));
        });
        let me = *or_!(self.fi_to_ud.try_get(&fi).try_unwrap(), {
            return Err(error(line!(), "File failed to load"));
        });

        // Extract end_of_imports and immediately drop the modules guard so background
        // loading is not blocked while we do the (potentially slow) fixable processing.
        let end_of_imports = {
            let qq = self.modules.try_get(&me).try_unwrap();
            let head = or_!(
                &or_!(&qq, {
                    return Err(error(line!(), "Module failed to load"));
                })
                .value()
                .0,
                {
                    return Err(error(line!(), "Module failed to load"));
                }
            );
            head.2
                .last()
                .map(|x| x.start.lo())
                .unwrap_or_else(|| head.4.next_line().lo())
            // qq (modules guard) dropped here
        };

        // Clone fixables and drop the guard immediately. Background loading writes fixables
        // first, then resolved/defines. Holding this guard blocks goto_definition from seeing
        // freshly resolved names.
        let fixables = {
            let guard = or_!(self.fixables.try_get(&fi).try_unwrap(), {
                return Err(error(line!(), "Module failed to load"));
            });
            guard.value().clone()
            // guard (fixables read lock) dropped here
        };

        let mut out = Vec::new();

        let mut delete_all = Vec::new();
        for (_, f) in fixables.iter() {
            match f {
                Fixable::DeleteUnusedImport(at) => {
                    delete_all.push(span_to_range(&at.and_one_more_char()))
                }
                _ => (),
            }
        }
        // Sort by start position, then merge overlapping/adjacent ranges so the
        // workspace-edit never contains invalid overlapping TextEdits.
        delete_all.sort_by_key(|r| (r.start.line, r.start.character));
        let mut merged: Vec<Range> = Vec::new();
        for r in delete_all {
            if let Some(last) = merged.last_mut() {
                if (r.start.line, r.start.character) <= (last.end.line, last.end.character) {
                    if (r.end.line, r.end.character) > (last.end.line, last.end.character) {
                        last.end = r.end;
                    }
                    continue;
                }
            }
            merged.push(r);
        }
        let delete_all = merged;
        if !delete_all.is_empty() {
            out.push(CodeAction {
                title: format!("BurnAllUnusedImport"),
                kind: Some(CodeActionKind::SOURCE_FIX_ALL),
                is_preferred: None,
                edit: Some(WorkspaceEdit::new(
                    [(
                        uri.clone(),
                        delete_all
                            .into_iter()
                            .map(|r| TextEdit::new(r, "".into()))
                            .collect(),
                    )]
                    .into(),
                )),
                ..CodeAction::default()
            });
        }

        for (s, f) in fixables.iter() {
            if !s.contains((
                params.range.start.line as usize,
                params.range.start.character as usize,
            )) {
                continue;
            }
            match f {
                Fixable::GuessImports(s, ns, n, at) => {
                    let imported = or_!(self.imports.try_get(&me).try_unwrap(), { continue })
                        .value()
                        .clone();

                    // Detect operators: names that start with a non-alphanumeric, non-underscore char.
                    // Operators should never be suggested as qualified imports (e.g. `Mod.(+)`).
                    let is_operator = |name_ud: ast::Ud| -> bool {
                        self.names
                            .try_get(&name_ud)
                            .try_unwrap()
                            .map(|s| {
                                let first = s.chars().next().unwrap_or('_');
                                !char::is_ascii_alphanumeric(&first) && first != '_'
                            })
                            .unwrap_or(false)
                    };

                    // Collect qualified import aliases for each module in this file:
                    // module_ud -> [alias_ud, ...]
                    let mut qualified_aliases: BTreeMap<ast::Ud, Vec<ast::Ud>> = BTreeMap::new();
                    for (alias_opt, exports) in imported.iter() {
                        let Some(alias) = alias_opt else { continue };
                        for export in exports.iter() {
                            for nm in export.to_names() {
                                let entry = qualified_aliases.entry(nm.module()).or_default();
                                if !entry.contains(alias) {
                                    entry.push(*alias);
                                }
                            }
                        }
                    }

                    // Modules imported unqualified in this file
                    let unqualified_modules: BTreeSet<ast::Ud> = imported
                        .iter()
                        .flat_map(|(alias_opt, exports)| {
                            if alias_opt.is_some() {
                                return vec![];
                            }
                            exports
                                .iter()
                                .flat_map(|e| e.to_names())
                                .map(|n| n.module())
                                .collect::<Vec<_>>()
                        })
                        .collect();

                    let all_exports: BTreeMap<ast::Ud, Vec<nr::Export>> = self
                        .exports
                        .iter()
                        .map(|x| (*x.key(), x.value().clone()))
                        .collect();

                    // Scored suggestions: (score, CodeAction).
                    // Higher score = more relevant. is_preferred mirrors score >= 1.5.
                    let mut scored: Vec<(f32, CodeAction)> = Vec::new();

                    if *s == Scope::Namespace {
                        // The user referenced an unknown namespace qualifier.
                        // Suggest: rename to an existing alias, or add a new qualified import.
                        let namespace_str = self.name_(n);
                        let target_alias = ns
                            .map(|a| self.name_(&a))
                            .unwrap_or_else(|| namespace_str.clone());

                        // Already-imported qualified aliases that are similar to the typed name
                        for (alias_opt, _) in imported.iter() {
                            let Some(alias) = alias_opt else { continue };
                            let alias_str = self.name_(alias);
                            let sim = similarity_score(
                                &alias_str.to_lowercase(),
                                &namespace_str.to_lowercase(),
                            );
                            if sim < 0.4 {
                                continue;
                            }
                            scored.push((
                                sim + 1.0,
                                CodeAction {
                                    title: format!("Use `{}` (already imported)", alias_str),
                                    kind: Some(CodeActionKind::QUICKFIX),
                                    is_preferred: Some(true),
                                    edit: Some(WorkspaceEdit::new(
                                        [(
                                            uri.clone(),
                                            vec![TextEdit::new(range(at.lo(), at.hi()), alias_str)],
                                        )]
                                        .into(),
                                    )),
                                    ..CodeAction::default()
                                },
                            ));
                        }

                        // Suggest importing any module with a name similar to the typed namespace
                        for (m, _xs) in all_exports.iter() {
                            if *m == me {
                                continue;
                            }
                            let module_str = self.name_(m);
                            let sim = alias_match_score(&module_str, &namespace_str);
                            if sim <= 0.0 {
                                continue;
                            }
                            let already_imported = qualified_aliases.contains_key(m);
                            let score = sim + if already_imported { 0.5 } else { 0.0 };
                            scored.push((
                                score,
                                CodeAction {
                                    title: format!("Import `{}` as `{}`", module_str, target_alias),
                                    kind: Some(CodeActionKind::QUICKFIX),
                                    is_preferred: Some(module_str == namespace_str),
                                    edit: Some(WorkspaceEdit::new(
                                        [(
                                            uri.clone(),
                                            vec![TextEdit::new(
                                                range(end_of_imports, end_of_imports),
                                                format!(
                                                    "import {} as {}\n",
                                                    module_str, target_alias
                                                ),
                                            )],
                                        )]
                                        .into(),
                                    )),
                                    ..CodeAction::default()
                                },
                            ));
                        }
                    } else {
                        // The user referenced an unknown name `n` with scope `s`.
                        let name_ud = *n;
                        let operator = is_operator(name_ud);

                        // When the user typed a bare name (no namespace qualifier) and it's not
                        // an operator, suggest using an already-imported qualified alias.
                        if ns.is_none() && !operator {
                            for (alias_opt, exports) in imported.iter() {
                                let Some(alias) = alias_opt else { continue };
                                for export in exports.iter() {
                                    for nm in export.to_names() {
                                        if nm.name() != name_ud || nm.scope() != *s {
                                            continue;
                                        }
                                        let alias_str = self.name_(alias);
                                        let name_str = self.name_(&nm.name());
                                        let module_str = self.name_(&nm.module());
                                        let usage = format!("{}.{}", alias_str, name_str);
                                        scored.push((
                                            2.0,
                                            CodeAction {
                                                title: format!(
                                                    "Use `{}` from `{}` (already imported as `{}`)",
                                                    usage, module_str, alias_str,
                                                ),
                                                kind: Some(CodeActionKind::QUICKFIX),
                                                is_preferred: Some(true),
                                                edit: Some(WorkspaceEdit::new(
                                                    [(
                                                        uri.clone(),
                                                        vec![TextEdit::new(
                                                            range(at.lo(), at.hi()),
                                                            usage,
                                                        )],
                                                    )]
                                                    .into(),
                                                )),
                                                ..CodeAction::default()
                                            },
                                        ));
                                    }
                                }
                            }
                        }

                        for (m, xs) in all_exports.iter() {
                            if *m == me {
                                continue;
                            }
                            for export in xs.iter() {
                                // usage_name: the name as it appears at the call site
                                // import_name: the name/type used for the import statement
                                // is_ctor: whether import_name is a type containing a constructor
                                let (usage_name, import_name, is_ctor): (nr::Name, nr::Name, bool) =
                                    match export {
                                        Export::ConstructorsSome(parent, constructors)
                                        | Export::ConstructorsAll(parent, constructors) => {
                                            if parent.name() == name_ud && parent.scope() == *s {
                                                // The type itself matched — import with (..) so
                                                // constructors are available too.
                                                (*parent, *parent, true)
                                            } else if let Some(c) = constructors.iter().find(|c| {
                                                c.name() == name_ud
                                                    && c.scope() == *s
                                                    && c.scope() == Scope::Term
                                            }) {
                                                (*c, *parent, true)
                                            } else {
                                                continue;
                                            }
                                        }
                                        Export::Just(name) => {
                                            if name.name() == name_ud && name.scope() == *s {
                                                (*name, *name, false)
                                            } else {
                                                continue;
                                            }
                                        }
                                    };

                                let module_ud = usage_name.module();
                                let module_str = self.name_(&module_ud);
                                let usage_str = self.name_(&usage_name.name());
                                let import_item = as_import(
                                    import_name.scope(),
                                    is_ctor,
                                    import_name.name(),
                                    &self.names,
                                );

                                let already_qualified = qualified_aliases.contains_key(&module_ud);
                                let already_unqualified = unqualified_modules.contains(&module_ud);

                                // Check if this module is *directly* imported in the current file
                                // (as opposed to being accessible only via a re-export from another
                                // module that is imported here). Re-export references live in the
                                // exporting module's file, not the current file.
                                let directly_imported = self
                                    .references
                                    .try_get(&module_ud)
                                    .try_unwrap()
                                    .and_then(|refs| {
                                        refs.get(&Name(
                                            Scope::Module,
                                            module_ud,
                                            module_ud,
                                            Visibility::Public,
                                        ))
                                        .map(|spans| {
                                            spans.iter().any(|(span, _)| span.fi() == Some(fi))
                                        })
                                    })
                                    .unwrap_or(false);
                                // A module is directly unqualified only when it's directly imported
                                // AND not qualified (a qualified import is never in the None key).
                                let directly_unqualified = directly_imported && !already_qualified;

                                // How similar is this module's name to what the user typed?
                                // When a namespace qualifier was typed (e.g. `Foo.bar`), use the
                                // structured alias-match scoring (exact > ends-with > contains >
                                // PascalCase letter overlap) so that e.g. `Kanon.Table` ranks above
                                // `Ganon` for qualifier `Kanon`.
                                // When a bare name was typed (e.g. `bar`), use edit-distance similarity
                                // against the export name as a weaker hint (e.g. `Map` for `map`).
                                let module_sim = if let Some(ns_alias) = ns {
                                    let alias_str = self.name_(ns_alias);
                                    alias_match_score(&module_str, &alias_str)
                                } else {
                                    similarity_score(
                                        &module_str.to_lowercase(),
                                        &usage_str.to_lowercase(),
                                    )
                                };
                                let import_bonus = if already_qualified || already_unqualified {
                                    0.5
                                } else {
                                    0.0
                                };

                                // Suggestion A: Add name to an existing unqualified import.
                                // Only when the module is directly and solely imported unqualified.
                                if directly_unqualified && ns.is_none() {
                                    (|| -> Option<()> {
                                        let (l, c) = self
                                            .references
                                            .try_get(&module_ud)
                                            .try_unwrap()?
                                            .get(&Name(
                                                Scope::Module,
                                                module_ud,
                                                module_ud,
                                                Visibility::Public,
                                            ))?
                                            .iter()
                                            .find_map(|(span, _): &(ast::Span, nr::Sort)| {
                                                if span.fi() == Some(fi) {
                                                    Some(*span)
                                                } else {
                                                    None
                                                }
                                            })?
                                            .hi();
                                        let c = c + 2;
                                        scored.push((
                                            1.5 + module_sim * 0.5,
                                            CodeAction {
                                                title: format!(
                                                    "Add `{}` to import of `{}`",
                                                    import_item, module_str,
                                                ),
                                                kind: Some(CodeActionKind::QUICKFIX),
                                                is_preferred: Some(true),
                                                edit: Some(WorkspaceEdit::new(
                                                    [(
                                                        uri.clone(),
                                                        vec![TextEdit::new(
                                                            range((l, c), (l, c)),
                                                            format!("{}, ", import_item),
                                                        )],
                                                    )]
                                                    .into(),
                                                )),
                                                ..CodeAction::default()
                                            },
                                        ));
                                        None
                                    })();
                                }

                                // Suggestion B: New unqualified import line.
                                // Only offered for bare-name references not already directly imported unqualified.
                                if ns.is_none() && !directly_unqualified {
                                    scored.push((
                                        0.3 + module_sim * 0.5 + import_bonus,
                                        CodeAction {
                                            title: format!(
                                                "Import `{}` from `{}`",
                                                import_item, module_str,
                                            ),
                                            kind: Some(CodeActionKind::QUICKFIX),
                                            is_preferred: Some(false),
                                            edit: Some(WorkspaceEdit::new(
                                                [(
                                                    uri.clone(),
                                                    vec![TextEdit::new(
                                                        range(end_of_imports, end_of_imports),
                                                        format!(
                                                            "import {} ({})\n",
                                                            module_str, import_item
                                                        ),
                                                    )],
                                                )]
                                                .into(),
                                            )),
                                            ..CodeAction::default()
                                        },
                                    ));
                                }

                                // Suggestion C: Qualified import (not for operators or type operators).
                                // Preferred over unqualified (higher base score).
                                // When ns=None, skip if already_qualified — the "use existing alias"
                                // suggestion (score 2.0) already covers this module.
                                if !operator {
                                    if let Some(ns_alias) = ns {
                                        // User typed `Alias.name` — suggest importing the module as that alias.
                                        let ns_str = self.name_(ns_alias);
                                        scored.push((
                                            module_sim + import_bonus,
                                            CodeAction {
                                                title: format!(
                                                    "Import `{}` as `{}`",
                                                    module_str, ns_str,
                                                ),
                                                kind: Some(CodeActionKind::QUICKFIX),
                                                is_preferred: Some(ns_str == module_str),
                                                edit: Some(WorkspaceEdit::new(
                                                    [(
                                                        uri.clone(),
                                                        vec![TextEdit::new(
                                                            range(end_of_imports, end_of_imports),
                                                            format!(
                                                                "import {} as {}\n",
                                                                module_str, ns_str
                                                            ),
                                                        )],
                                                    )]
                                                    .into(),
                                                )),
                                                ..CodeAction::default()
                                            },
                                        ));
                                    } else if !already_qualified {
                                        // User typed a bare name — suggest a qualified import using
                                        // a dotless alias (e.g. Data.Map -> DataMap) and rewrite usage.
                                        // Alias format:
                                        // - One dot (two segments) e.g. `Visma.Api` → `VismaApi`
                                        // - One dot with "Ctx" first e.g. `Ctx.Time` → `TimeCtx`
                                        // - Multiple dots e.g. `Data.Map.Strict` → `DataMapStrict`
                                        let alias = {
                                            let parts: Vec<&str> = module_str.split('.').collect();
                                            if parts.len() == 2 {
                                                if parts.get(0) == Some(&"Ctx") {
                                                    format!("{}{}", parts[1], parts[0])
                                                } else {
                                                    format!("{}{}", parts[0], parts[1])
                                                }
                                            } else {
                                                module_str.replace('.', "")
                                            }
                                        };
                                        let qualified_usage = format!("{}.{}", alias, usage_str);
                                        scored.push((
                                            0.5 + module_sim * 0.5 + import_bonus,
                                            CodeAction {
                                                title: format!(
                                                    "Import `{}` and use as `{}`",
                                                    module_str, qualified_usage,
                                                ),
                                                kind: Some(CodeActionKind::QUICKFIX),
                                                is_preferred: Some(already_qualified),
                                                edit: Some(WorkspaceEdit::new(
                                                    [(
                                                        uri.clone(),
                                                        vec![
                                                            TextEdit::new(
                                                                range(
                                                                    end_of_imports,
                                                                    end_of_imports,
                                                                ),
                                                                format!(
                                                                    "import {} as {}\n",
                                                                    module_str, alias
                                                                ),
                                                            ),
                                                            TextEdit::new(
                                                                range(at.lo(), at.hi()),
                                                                qualified_usage,
                                                            ),
                                                        ],
                                                    )]
                                                    .into(),
                                                )),
                                                ..CodeAction::default()
                                            },
                                        ));
                                    }
                                }
                            }
                        }
                    }

                    // Sort by score descending so the most relevant suggestions appear first,
                    // then cap to avoid overwhelming the editor with too many choices.
                    scored.sort_by(|(a, _), (b, _)| {
                        b.partial_cmp(a).unwrap_or(std::cmp::Ordering::Equal)
                    });
                    scored.truncate(25);
                    for (_, action) in scored {
                        out.push(action);
                    }
                }
                Fixable::RenameWithUnderscore(at) => out.push(CodeAction {
                    title: "Prefix `_` to mark unused".into(),
                    kind: Some(CodeActionKind::QUICKFIX),
                    diagnostics: None,
                    edit: Some(WorkspaceEdit::new(
                        [(
                            uri.clone(),
                            vec![TextEdit::new(span_to_range(&at.right_before()), "_".into())],
                        )]
                        .into(),
                    )),
                    is_preferred: None,
                    ..CodeAction::default()
                }),
                Fixable::Delete(at) => out.push(CodeAction {
                    title: "Delete".into(),
                    kind: Some(CodeActionKind::QUICKFIX),
                    diagnostics: None,
                    edit: Some(WorkspaceEdit::new(
                        [(
                            uri.clone(),
                            vec![TextEdit::new(
                                span_to_range(&at.and_one_more_char()),
                                "".into(),
                            )],
                        )]
                        .into(),
                    )),
                    is_preferred: Some(true),
                    ..CodeAction::default()
                }),
                Fixable::DeleteUnusedImport(at) => out.push(CodeAction {
                    title: "DeleteUnusedImport".into(),
                    kind: Some(CodeActionKind::QUICKFIX),
                    diagnostics: None,
                    edit: Some(WorkspaceEdit::new(
                        [(
                            uri.clone(),
                            vec![TextEdit::new(
                                span_to_range(&at.and_one_more_char()),
                                "".into(),
                            )],
                        )]
                        .into(),
                    )),
                    is_preferred: Some(true),
                    ..CodeAction::default()
                }),
            }
        }
        // Offer "Delete unused parameter" for unused function parameters
        // and "Delete unused record field" for unused record binder fields.
        if let Some(module_guard) = self.modules.try_get(&me).try_unwrap() {
            let module = module_guard.value();
            for (s, f) in fixables.iter() {
                if !s.contains((
                    params.range.start.line as usize,
                    params.range.start.character as usize,
                )) {
                    continue;
                }
                if let Fixable::RenameWithUnderscore(at) = f {
                    // Check if this is a simple function parameter.
                    let param_info = module.1.iter().find_map(|decl| {
                        if let ast::Decl::Def(name, binders, _) = decl {
                            binders.iter().enumerate().find_map(|(idx, binder)| {
                                if binder_is_simple_var(binder)
                                    && binder.span().contains(at.lo())
                                {
                                    Some((name.0 .0, idx))
                                } else {
                                    None
                                }
                            })
                        } else {
                            None
                        }
                    });

                    if let Some((func_ud, param_idx)) = param_info {
                        let mut edits = Vec::new();

                        for decl in module.1.iter() {
                            match decl {
                                ast::Decl::Def(name, binders, _)
                                    if name.0 .0 == func_ud && binders.len() > param_idx =>
                                {
                                    let source = self.fi_to_source.try_get(&fi).try_unwrap();
                                    let binder_spans: Vec<_> = binders.iter().map(|b| {
                                        match &source {
                                            Some(s) => correct_binder_span(b, s.value(), fi),
                                            None => b.span(),
                                        }
                                    }).collect();
                                    edits.push(TextEdit::new(
                                        remove_nth_range(&binder_spans, param_idx, true),
                                        "".into(),
                                    ));
                                }
                                ast::Decl::Sig(name, typ) if name.0 .0 == func_ud => {
                                    let types = flatten_arr_chain(typ);
                                    if param_idx < types.len().saturating_sub(1) {
                                    let type_spans: Vec<_> = types.iter().map(|t| t.span()).collect();
                                        edits.push(TextEdit::new(
                                            remove_nth_range(&type_spans, param_idx, false),
                                            "".into(),
                                        ));
                                    }
                                }
                                _ => {}
                            }
                        }

                        if !edits.is_empty() {
                            out.push(CodeAction {
                                title: "Delete unused parameter".into(),
                                kind: Some(CodeActionKind::QUICKFIX),
                                diagnostics: None,
                                edit: Some(WorkspaceEdit::new(
                                    [(uri.clone(), edits)].into(),
                                )),
                                is_preferred: Some(true),
                                ..CodeAction::default()
                            });
                        }
                        continue;
                    }

                    // Check if this is an unused field inside a record binder.
                    let record_info = module.1.iter().find_map(|decl| {
                        if let ast::Decl::Def(name, binders, _) = decl {
                            binders.iter().enumerate().find_map(|(param_idx, binder)| {
                                let record_fields = match binder {
                                    ast::Binder::Record(fields) => fields,
                                    ast::Binder::Typed(inner, _) => match inner.as_ref() {
                                        ast::Binder::Record(fields) => fields,
                                        _ => return None,
                                    },
                                    _ => return None,
                                };
                                record_fields.iter().find_map(|field| {
                                    let field_ud = match field {
                                        ast::RecordLabelBinder::Pun(n) => {
                                            if n.span().contains(at.lo()) {
                                                Some(n.0 .0)
                                            } else {
                                                None
                                            }
                                        }
                                        _ => None,
                                    };
                                    field_ud.map(|ud| (name.0 .0, param_idx, ud))
                                })
                            })
                        } else {
                            None
                        }
                    });

                    if let Some((func_ud, param_idx, field_ud)) = record_info {
                        // Check if this is the last field in the record. If so,
                        // remove the entire parameter and its type arrow instead.
                        let is_last_field = module.1.iter().any(|decl| {
                            if let ast::Decl::Def(name, binders, _) = decl {
                                if name.0 .0 != func_ud || binders.len() <= param_idx {
                                    return false;
                                }
                                let fields = match &binders[param_idx] {
                                    ast::Binder::Record(f) => f,
                                    ast::Binder::Typed(inner, _) => match inner.as_ref() {
                                        ast::Binder::Record(f) => f,
                                        _ => return false,
                                    },
                                    _ => return false,
                                };
                                fields.len() == 1
                            } else {
                                false
                            }
                        });

                        let mut edits = Vec::new();

                        for decl in module.1.iter() {
                            match decl {
                                ast::Decl::Def(name, binders, _)
                                    if name.0 .0 == func_ud && binders.len() > param_idx =>
                                {
                                    if is_last_field {
                                        let source = self.fi_to_source.try_get(&fi).try_unwrap();
                                        let binder_spans: Vec<_> = binders.iter().map(|b| {
                                            match &source {
                                                Some(s) => correct_binder_span(b, s.value(), fi),
                                                None => b.span(),
                                            }
                                        }).collect();
                                        edits.push(TextEdit::new(
                                            remove_nth_range(&binder_spans, param_idx, true),
                                            "".into(),
                                        ));
                                    } else {
                                        let record_fields = match &binders[param_idx] {
                                            ast::Binder::Record(fields) => Some(fields),
                                            ast::Binder::Typed(inner, _) => match inner.as_ref() {
                                                ast::Binder::Record(fields) => Some(fields),
                                                _ => None,
                                            },
                                            _ => None,
                                        };
                                        if let Some(fields) = record_fields {
                                            if let Some(idx) = fields.iter().position(|f| {
                                                matches!(f, ast::RecordLabelBinder::Pun(n) if n.0 .0 == field_ud)
                                                    || matches!(f, ast::RecordLabelBinder::Field(l, _) if l.0 .0 == field_ud)
                                            }) {
                                                let field_spans: Vec<_> = fields.iter().map(|f| f.span()).collect();
                                                edits.push(TextEdit::new(
                                                    remove_nth_range(&field_spans, idx, false),
                                                    "".into(),
                                                ));
                                            }
                                        }
                                    }
                                }
                                ast::Decl::Sig(name, typ) if name.0 .0 == func_ud => {
                                    let types = flatten_arr_chain(typ);
                                    if param_idx < types.len().saturating_sub(1) {
                                        if is_last_field {
                                            let type_spans: Vec<_> = types.iter().map(|t| t.span()).collect();
                                            edits.push(TextEdit::new(
                                                remove_nth_range(&type_spans, param_idx, false),
                                                "".into(),
                                            ));
                                        } else if let ast::Typ::Record(s_row) = types[param_idx] {
                                            let row = &s_row.0;
                                            if let Some(idx) = row.0.iter().position(|(l, _)| l.0 .0 == field_ud) {
                                                let row_spans: Vec<_> = row.0.iter().map(|f| f.span()).collect();
                                                edits.push(TextEdit::new(
                                                    remove_nth_range(&row_spans, idx, false),
                                                    "".into(),
                                                ));
                                            }
                                        }
                                    }
                                }
                                _ => {}
                            }
                        }

                        if !edits.is_empty() {
                            let title = if is_last_field {
                                "Delete unused parameter"
                            } else {
                                "Delete unused record field"
                            };
                            out.push(CodeAction {
                                title: title.into(),
                                kind: Some(CodeActionKind::QUICKFIX),
                                diagnostics: None,
                                edit: Some(WorkspaceEdit::new(
                                    [(uri.clone(), edits)].into(),
                                )),
                                is_preferred: Some(true),
                                ..CodeAction::default()
                            });
                        }
                    }
                }
            }
        }
        // Dedup by title while preserving insertion order (which encodes relevance score),
        // then stable-sort preferred items to the front without disturbing within-group order.
        let mut seen_titles = std::collections::HashSet::new();
        out.retain(|x| seen_titles.insert(x.title.clone()));
        out.sort_by(|a, b| b.is_preferred.cmp(&a.is_preferred));
        Ok(Some(out.into_iter().map(|x| x.into()).collect()))
    }

    #[instrument(skip(self))]
    async fn did_change_configuration(&self, _: DidChangeConfigurationParams) {}

    #[instrument(skip(self))]
    async fn did_change_workspace_folders(&self, _: DidChangeWorkspaceFoldersParams) {}

    #[instrument(skip(self, params))]
    async fn did_change_watched_files(&self, params: DidChangeWatchedFilesParams) {
        for event in params.changes {
            match event.typ {
                FileChangeType::CREATED | FileChangeType::CHANGED => {
                    let uri = event.uri;
                    let path = match uri.to_file_path() {
                        Some(p) => p,
                        None => continue,
                    };
                    let source = match std::fs::read_to_string(&path) {
                        Ok(s) => s,
                        Err(_) => continue,
                    };
                    if let Some((fi, version, to_notify)) = self.on_change(TextDocumentItem {
                        text: &source,
                        uri,
                        version: None,
                    }) {
                        self.show_errors(fi, version).await;
                        for (fi, v) in to_notify.iter() {
                            self.show_errors(*fi, *v).await;
                        }
                        if !to_notify.is_empty() {
                            let _ = self.client.workspace_diagnostic_refresh().await;
                        }
                    }
                }
                _ => {}
            }
        }
    }

    #[instrument(skip(self))]
    async fn execute_command(&self, params: ExecuteCommandParams) -> Result<Option<Value>> {
        if params.command == "load_workspace" {
            self.client
                .log_message(MessageType::INFO, "Loading entire workspace...".to_string())
                .await;

            let folders = self
                .client
                .workspace_folders()
                .await
                .ok()
                .flatten()
                .unwrap_or_default();
            self.load_workspace(folders);
            self.client
                .log_message(MessageType::INFO, "Done loading!".to_string())
                .await;
        } else {
            self.client
                .log_message(
                    MessageType::INFO,
                    format!("Unkown command: {}", params.command),
                )
                .await;
        }
        Ok(None)
    }

    #[instrument(skip(self))]
    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let name = or_!(
            self.resolve_name(
                &params.text_document_position_params.text_document.uri,
                params.text_document_position_params.position,
            ),
            {
                return Ok(None);
            }
        );

        let target = self.get_documentation_for_name(name);

        Ok(Some(Hover {
            contents: HoverContents::Markup(MarkupContent {
                kind: MarkupKind::Markdown,
                value: target,
            }),
            // This is possible to extract
            range: None,
        }))
    }
}

/// Score how well `qual` (the alias the user typed) matches `module_str` as an import alias.
/// Returns a float in (0.0, 1.0] where **higher is better**. Used for ranking qualified suggestions.
///
/// Algorithm (adapted from PureScript client-side ranking):
///   1. Exact match                                         → 1.0
///   2. Module ends with qual                              → ~0.9999
///   3. Module contains qual                               → ~0.9998
///   4. Count PascalCase-initial letters of qual that      → small positive (more = better)
///      appear anywhere in module name
fn alias_match_score(module_str: &str, qual_str: &str) -> f32 {
    if module_str == qual_str {
        return 1.0;
    }
    if module_str.ends_with(qual_str) {
        return 1.0 - 1e-4;
    }
    if module_str.contains(qual_str) {
        return 1.0 - 2e-4;
    }
    // Split qual into PascalCase segments (regex [A-Z][a-z]*) and take the first
    // character of each. Count how many of those characters appear in the module name.
    let count = qual_str
        .chars()
        .filter(|c| c.is_uppercase())
        .filter(|c| module_str.contains(*c))
        .count();
    count as f32 * 0.01
}

fn similarity_score(ax: &str, bx: &str) -> f32 {
    let ax: Vec<_> = ax.chars().collect();
    let bx: Vec<_> = bx.chars().collect();
    if ax.is_empty() {
        return bx.len() as f32;
    }
    if bx.is_empty() {
        return ax.len() as f32;
    }
    let mut distances: Vec<Vec<usize>> = Vec::new();
    for _ in bx.iter().chain([' '].iter()) {
        distances.push(vec![0; 1 + ax.len()]);
    }

    for i in 1..=ax.len() {
        distances[0][i] = i;
    }
    for j in 1..=bx.len() {
        distances[j][0] = j;
    }

    for (i, a) in ax.iter().enumerate() {
        for (j, b) in bx.iter().enumerate() {
            distances[j + 1][i + 1] = (distances[j][i] + (if a != b { 0 } else { 1 }))
                .min(distances[j][i + 1] + 1)
                .min(distances[j + 1][i] + 1);
        }
    }
    1.0 - (distances[bx.len() - 1][ax.len() - 1] as f32) / (bx.len().min(ax.len()) as f32)
}

fn error(code: u32, message: &str) -> Error {
    let mut err = Error::new(ErrorCode::ServerError(code.into()));
    err.message = message.to_string().into();
    err
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
enum Fixable {
    GuessImports(nr::Scope, Option<ast::Ud>, ast::Ud, ast::Span),
    Delete(ast::Span),
    DeleteUnusedImport(ast::Span),
    RenameWithUnderscore(ast::Span),
}

/// Check if a binder is a simple variable (possibly with a type annotation).
fn binder_is_simple_var(b: &ast::Binder) -> bool {
    match b {
        ast::Binder::Var(_) => true,
        ast::Binder::Typed(inner, _) => binder_is_simple_var(inner),
        _ => false,
    }
}

/// Flatten a Typ::Arr chain into [param0, param1, ..., return_type].
/// Unwraps top-level Forall, Constrained, and Paren wrappers.
fn flatten_arr_chain(typ: &ast::Typ) -> Vec<&ast::Typ> {
    let mut current = typ;
    loop {
        match current {
            ast::Typ::Forall(_, inner) | ast::Typ::Constrained(_, inner) => current = inner,
            ast::Typ::Paren(inner) => current = inner,
            _ => break,
        }
    }
    let mut result = Vec::new();
    loop {
        match current {
            ast::Typ::Arr(left, right) => {
                result.push(left.as_ref());
                current = right;
            }
            _ => {
                result.push(current);
                break;
            }
        }
    }
    result
}

/// Correct a binder's span to include `{` and `}` for record binders,
/// whose derived span only covers the inner fields.
fn correct_binder_span(binder: &ast::Binder, source: &str, fi: ast::Fi) -> ast::Span {
    let span = binder.span();
    let is_record = matches!(binder, ast::Binder::Record(_))
        || matches!(binder, ast::Binder::Typed(inner, _) if matches!(inner.as_ref(), ast::Binder::Record(_)));
    if !is_record {
        return span;
    }
    let lines: Vec<&str> = source.lines().collect();
    let (lo_line, lo_col) = span.lo();
    let (hi_line, hi_col) = span.hi();
    let brace_lo = lines
        .get(lo_line)
        .and_then(|line| line[..lo_col].rfind('{').map(|off| (lo_line, off)));
    let brace_hi = lines
        .get(hi_line)
        .and_then(|line| line[hi_col..].find('}').map(|off| (hi_line, hi_col + off + 1)));
    match (brace_lo, brace_hi) {
        (Some(lo), Some(hi)) => ast::Span::Known(fi, lo, hi),
        _ => span,
    }
}

/// Compute the Range to delete the `idx`-th item from a spanned list,
/// eating the separator (comma, arrow, whitespace) between neighbors.
/// When removing the only item, `only_item_extra_char` extends by one char
/// (for space-separated lists like binders).
fn remove_nth_range(spans: &[ast::Span], idx: usize, only_item_extra_char: bool) -> Range {
    if spans.len() == 1 {
        if only_item_extra_char {
            span_to_range(&spans[0].and_one_more_char())
        } else {
            span_to_range(&spans[0])
        }
    } else if idx < spans.len() - 1 {
        // First or middle item: delete from its start to the next item's start (eats trailing separator).
        range(spans[idx].lo(), spans[idx + 1].lo())
    } else {
        // Last item: delete from previous item's end to this item's end (eats leading separator).
        range(spans[idx - 1].hi(), spans[idx].hi())
    }
}

fn create_error(
    span: ast::Span,
    code: String,
    message: String,
    related: Vec<(String, Location)>,
) -> tower_lsp_server::ls_types::Diagnostic {
    let range = Range::new(pos_from_tup(span.lo()), pos_from_tup(span.hi()));
    Diagnostic::new(
        range,
        Some(DiagnosticSeverity::ERROR),
        Some(NumberOrString::String(code)),
        Some("hemlis".into()),
        message,
        {
            let related: Vec<_> = related
                .into_iter()
                .map(|(message, location)| DiagnosticRelatedInformation { message, location })
                .collect();
            if related.is_empty() {
                None
            } else {
                Some(related)
            }
        },
        None,
    )
}

fn create_warning(
    span: ast::Span,
    code: String,
    message: String,
    related: Vec<(String, Location)>,
) -> tower_lsp_server::ls_types::Diagnostic {
    let range = Range::new(pos_from_tup(span.lo()), pos_from_tup(span.hi()));
    Diagnostic::new(
        range,
        Some(DiagnosticSeverity::WARNING),
        Some(NumberOrString::String(code)),
        Some("hemlis".into()),
        message,
        {
            let related: Vec<_> = related
                .into_iter()
                .map(|(message, location)| DiagnosticRelatedInformation { message, location })
                .collect();
            if related.is_empty() {
                None
            } else {
                Some(related)
            }
        },
        None,
    )
}

fn nrerror_turn_into_fixables(error: &NRerrors) -> Vec<(ast::Span, Fixable)> {
    match error {
        NRerrors::Unknown(scope, ns, n, s) => {
            vec![(*s, Fixable::GuessImports(*scope, *ns, *n, *s))]
        }
        NRerrors::CannotImportSelf(s) => {
            vec![(*s, Fixable::Delete(*s))]
        }

        NRerrors::NameConflict(_, _)
        | NRerrors::MultipleDefinitions(_, _, _)
        | NRerrors::NotAConstructor(_, _)
        | NRerrors::NoConstructors(_, _)
        | NRerrors::NotExportedOrDoesNotExist(_, _, _, _)
        | NRerrors::CouldNotFindImport(_, _) => Vec::new(),

        NRerrors::UnusedLocal(_, s) => {
            vec![(*s, Fixable::RenameWithUnderscore(*s))]
        }

        NRerrors::ImportDoesNothing(_, s) => {
            vec![(
                s.span(),
                Fixable::DeleteUnusedImport(s.span().entire_line()),
            )]
        }

        NRerrors::UnusedImport(_, _, s)
        | NRerrors::UnusedImportedConstructor(_, s)
        | NRerrors::UnusedImportTypeAndConstructor(_, _, s) => {
            vec![(*s, Fixable::DeleteUnusedImport(*s))]
        }

        NRerrors::UnusedImportQualified(_, s) | NRerrors::UnusedImportUnqualified(_, s) => {
            vec![(*s, Fixable::DeleteUnusedImport(s.entire_line()))]
        }

        NRerrors::UnusedDefinition(n, s) if n.scope() == nr::Scope::Namespace => {
            vec![(
                s.name.entire_line(),
                Fixable::DeleteUnusedImport(s.name.entire_line()),
            )]
        }

        NRerrors::UnusedDefinition(_, _) => Vec::new(),
        NRerrors::UnusedConstructor(_, _) => Vec::new(),
        // Unsure about this
        // NRerrors::UnusedDefinition(_, s) => {
        //     vec![(
        //         s.span().entire_line(),
        //         Fixable::DeleteUnusedImport(s.span()),
        //     )]
        // }
    }
}

fn format_name(ns: Option<ast::Ud>, n: ast::Ud, names: &DashMap<ast::Ud, String>) -> String {
    match (
        names
            .try_get(&ns.unwrap_or(ast::Ud(0, '_')))
            .try_unwrap()
            .map(|x| x.clone()),
        names.try_get(&n).try_unwrap().map(|x| x.clone()),
    ) {
        (None, Some(name)) => name,
        (Some(ns), Some(name)) => format!("{}.{}", ns, name),
        // This case is reached in practice due to racey-ness
        (_, _) => "?".into(),
    }
}

fn as_import(
    scope: nr::Scope,
    is_constructor: bool,
    name: ast::Ud,
    names: &DashMap<ast::Ud, String>,
) -> String {
    assert!(!is_constructor || scope == nr::Scope::Type);
    let name = if let Some(name) = names.try_get(&name).try_unwrap() {
        name.value().clone()
    } else {
        "?".into()
    };
    let first = name.chars().next().unwrap();
    let is_identifier = char::is_ascii_alphanumeric(&first) || first == '_';
    match scope {
        _ if is_constructor => format!("{}(..)", name),

        Scope::Kind | Scope::Type if is_identifier => {
            format!("{}", name)
        }
        Scope::Kind | Scope::Type => {
            format!("type ({})", name)
        }
        Scope::Class => format!("class {}", name),
        Scope::Namespace | Scope::Module => format!("module {}", name),

        Scope::Term if is_identifier => format!("{}", name),
        Scope::Term => format!("({})", name),
        Scope::Label => "".to_string(),
    }
}

pub fn nrerror_turn_into_diagnostic(
    error: NRerrors,
    names: &DashMap<ast::Ud, String>,
) -> tower_lsp_server::ls_types::Diagnostic {
    match error {
        NRerrors::Unknown(scope, ns, n, s) => create_error(
            s,
            "Unknown".into(),
            format!(
                "{:?} {}\nFailed to resolve",
                scope,
                format_name(ns, n, names)
            ),
            Vec::new(),
        ),
        NRerrors::NameConflict(ns, s) => create_error(
            s,
            "NameConflict".into(),
            format!(
                "This name is imported from {} different modules\n{}",
                ns.len(),
                ns.iter()
                    .map(|Name(s, m, n, x)| {
                        format!("{:?} {} {:?}", s, format_name(Some(*m), *n, names), x,)
                    })
                    .collect::<Vec<_>>()
                    .join("\n")
            ),
            Vec::new(),
        ),
        NRerrors::MultipleDefinitions(Name(scope, _m, i, _), _first, second) => create_error(
            second,
            "MultipleDefinitions".into(),
            format!(
                "{:?} {:?} is defined multiple times",
                scope,
                names
                    .try_get(&i)
                    .try_unwrap()
                    .map(|x| x.clone())
                    .unwrap_or_else(|| "?".into())
            ),
            Vec::new(),
        ),
        NRerrors::NotAConstructor(d, m) => create_error(
            m.0.1,
            "NotAConstructor".into(),
            format!(
                "{} does not have a constructors {}",
                names
                    .try_get(&d.2)
                    .try_unwrap()
                    .map(|x| x.clone())
                    .unwrap_or_else(|| "?".into()),
                names
                    .try_get(&m.0.0)
                    .try_unwrap()
                    .map(|x| x.clone())
                    .unwrap_or_else(|| "?".into())
            ),
            Vec::new(),
        ),
        NRerrors::NoConstructors(m, s) => create_error(
            s,
            "NoConstructors".into(),
            format!(
                "{} does not have constructors",
                names
                    .try_get(&m.2)
                    .try_unwrap()
                    .map(|x| x.clone())
                    .unwrap_or_else(|| "?".into()),
            ),
            Vec::new(),
        ),
        NRerrors::NotExportedOrDoesNotExist(m, scope, ud, s) => create_error(
            s,
            "NotExportedOrDoesNotExist".into(),
            format!(
                "{:?} {} is not exported or does not exist",
                scope,
                format_name(Some(m), ud, names),
            ),
            Vec::new(),
        ),
        NRerrors::CannotImportSelf(s) => create_error(
            s,
            "CannotImportSelf".into(),
            "A module cannot import itself".to_string(),
            Vec::new(),
        ),
        NRerrors::CouldNotFindImport(n, s) => create_error(
            s,
            "CouldNotFindImport".into(),
            format!(
                "Could not find the import {}",
                names
                    .try_get(&n)
                    .try_unwrap()
                    .map(|x| x.clone())
                    .unwrap_or_else(|| "?".into()),
            ),
            Vec::new(),
        ),

        NRerrors::UnusedImport(scope, ud, s) => create_warning(
            s,
            "UnusedImport".into(),
            format!(
                "Import of {:?} {} is unused",
                scope,
                format_name(None, ud, names),
            ),
            Vec::new(),
        ),
        NRerrors::UnusedImportQualified(ud, s) => create_warning(
            s,
            "UnusedImportQualified".into(),
            format!(
                "The qualified import {} is unused",
                format_name(None, ud, names),
            ),
            Vec::new(),
        ),
        NRerrors::UnusedImportUnqualified(ud, s) => create_warning(
            s,
            "UnusedImportUnqualified".into(),
            format!(
                "The unqualified import {} is unused",
                format_name(None, ud, names),
            ),
            Vec::new(),
        ),
        NRerrors::UnusedImportedConstructor(ud, s) => create_warning(
            s,
            "UnusedImportedConstructor".into(),
            format!(
                "The import constructor {} is unused",
                format_name(None, ud, names),
            ),
            Vec::new(),
        ),

        NRerrors::UnusedImportTypeAndConstructor(ud, _, s) => create_warning(
            s,
            "UnusedImportTypeAndConstructor".into(),
            format!(
                "Both type and constructors for {} are unused",
                format_name(None, ud, names),
            ),
            Vec::new(),
        ),

        NRerrors::UnusedLocal(name, s) => create_warning(
            s,
            "UnusedLocal".into(),
            format!(
                "Local {:?} {} is unused",
                name.scope(),
                format_name(None, name.name(), names),
            ),
            Vec::new(),
        ),

        NRerrors::UnusedDefinition(name, s) if name.scope() == Scope::Namespace => create_warning(
            s.span().entire_line(),
            "UnusedDefinition".into(),
            format!(
                "Namespace {} is unused",
                format_name(None, name.name(), names),
            ),
            Vec::new(),
        ),
        NRerrors::UnusedConstructor(u, s) => create_warning(
            s,
            "UnusedDefinition".into(),
            format!(
                "Constructor {} can be safely removed",
                format_name(None, u.name(), names)
            ),
            Vec::new(),
        ),

        NRerrors::UnusedDefinition(name, s) => create_warning(
            s.name,
            "UnusedDefinition".into(),
            format!(
                "Definition {:?} {} is unused",
                name.scope(),
                format_name(None, name.name(), names),
            ),
            Vec::new(),
        ),
        NRerrors::ImportDoesNothing(u, s) => create_warning(
            s,
            "ImportDoesNothing".into(),
            format!(
                "Import {} can be safely removed",
                format_name(None, u, names)
            ),
            Vec::new(),
        ),
    }
}

#[allow(unused)]
#[derive(Debug, Deserialize, Serialize)]
struct InlayHintParams {
    path: String,
}

#[allow(unused)]
enum CustomNotification {}
impl Notification for CustomNotification {
    type Params = InlayHintParams;
    const METHOD: &'static str = "custom/notification";
}

#[derive(Debug)]
struct TextDocumentItem<'a> {
    uri: Uri,
    text: &'a str,
    version: Option<i32>,
}

impl Backend {
    fn name_(&self, ud: &ast::Ud) -> String {
        self.name(ud).unwrap_or_else(|| "?".into())
    }

    fn name(&self, ud: &ast::Ud) -> Option<String> {
        Some(self.names.try_get(ud).try_unwrap()?.value().clone())
    }

    #[instrument(skip(self))]
    fn load_workspace(&self, folders: Vec<WorkspaceFolder>) -> Option<()> {
        tracing::info!("Load start");

        for folder in folders {
            use glob::glob;
            let deps = glob(&format!(
                "{}/lib/**/*.purs",
                folder.uri.to_string().strip_prefix("file://")?
            ))
            .ok()?
            .collect::<Vec<_>>()
            .par_iter()
            .filter_map(|path| {
                let path = path.as_ref().ok()?;
                let x = (|| {
                    let source = std::fs::read_to_string(path.clone()).ok()?;
                    let uri = Uri::from_str(&format!(
                        "file://{}",
                        &path.clone().into_os_string().into_string().ok()?
                    ))
                    .ok()?;
                    let fi = loop {
                        if let Some(fi) = self.find_fi(uri.clone()) {
                            break fi;
                        }
                        tracing::error!("FAILED TO GENERATE FI");
                    };
                    self.fi_to_source.insert(fi, source.to_string());
                    self.fi_to_uri.insert(fi, uri.clone());
                    self.fi_to_version.insert(fi, None);
                    let (m, fi) = self.parse(fi, &source);
                    let m = m?;
                    let (me, imports) = {
                        let header = m.0.clone()?;
                        let me = header.0.0.0;
                        (
                            me,
                            header.2.iter().map(|x| x.from.0.0).collect::<BTreeSet<_>>(),
                        )
                    };
                    self.modules.insert(me, m.clone());
                    self.fi_to_ud.insert(fi, me);
                    self.ud_to_fi.insert(me, fi);
                    Some((me, fi, imports, m))
                })();
                if x.is_none() {
                    tracing::error!(
                        "FAILED: {:?}",
                        &path.clone().into_os_string().into_string().ok()?
                    );
                }
                x
            })
            .collect::<Vec<_>>();
            tracing::info!("=========");

            // NOTE: Not adding them to the name lookup
            fn h(s: &'static str) -> ast::Ud {
                ast::Ud::new(s)
            }

            let mut done: BTreeSet<_> = [
                h("Prim.Row"),
                h("Prim.Ordering"),
                h("Prim.RowList"),
                h("Prim.TypeError"),
                h("Prim.Boolean"),
                h("Prim.Coerce"),
                h("Prim.Symbol"),
                h("Prim.Int"),
            ]
            .into();
            loop {
                let todo: Vec<_> = deps
                    .iter()
                    .filter(|(m, _, deps, _)| (!done.contains(m)) && deps.is_subset(&done))
                    .collect();
                if todo.is_empty() {
                    let left: Vec<_> = deps
                        .iter()
                        .filter(|(m, _, _, _)| !done.contains(m))
                        .collect();
                    if !left.is_empty() {
                        tracing::warn!(
                            "{} modules have unresolvable dependencies (external packages not in lib/); resolving with partial information",
                            left.len()
                        );
                        // Resolve them anyway so that goto-definition works for names
                        // defined in these modules, even if some of their imports are unknown.
                        left.par_iter().for_each(|(_, fi, _, m)| {
                            self.resolve_module(m, *fi, None);
                        });
                    }
                    break;
                }
                todo.par_iter().for_each(|(_, fi, _, m)| {
                    self.resolve_module(m, *fi, None);
                });
                done.append(&mut todo.into_iter().map(|(me, _, _, _)| *me).collect());
            }
        }
        tracing::info!("LOAD_WORKSPACE - DONE");
        Some(())
    }

    #[instrument(skip(self, m))]
    fn resolve_module(
        &self,
        m: &ast::Module,
        fi: ast::Fi,
        version: Option<i32>,
    ) -> Option<(bool, ast::Ud)> {
        let me = m.0.as_ref()?.0.0.0;
        let mut n = nr::N::new(me, &self.exports);
        nr::resolve_names(&mut n, self.prim, m);

        let nr::N {
            me,
            errors,
            resolved,
            references,
            defines,
            global_usages,
            exports,
            ..
        } = n;

        self.fixables.insert(
            fi,
            errors
                .iter()
                .flat_map(nrerror_turn_into_fixables)
                .collect::<Vec<_>>(),
        );

        self.name_resolution_errors.insert(
            fi,
            errors
                .into_iter()
                .map(|x| nrerror_turn_into_diagnostic(x, &self.names))
                .collect::<Vec<_>>(),
        );

        self.resolved.insert(me, resolved);

        {
            let mut us = self.references.entry(me).or_insert(BTreeMap::new());
            for (k, v) in us.iter_mut() {
                v.retain(|(x, _)| x.fi() != Some(fi));
                v.append(&mut references.get(k).cloned().unwrap_or_default());
            }
            for (k, v) in references.into_iter() {
                if us.contains_key(&k) {
                    continue;
                }
                assert!(us.insert(k, v).is_none());
            }
        }

        {
            let defined_scopes = defines
                .iter()
                .filter_map(|(a, spans)| spans.body.iter().map(|x| (x.lines(), Some(*a))).min())
                .collect::<BTreeSet<_>>();
            self.available_locals.insert(fi, defined_scopes);
        }

        {
            let new = defines.into_iter().collect::<BTreeSet<_>>();
            let old = self
                .previouse_defines
                .insert(fi, new.clone())
                .unwrap_or_default();

            // Technically, we only need to remove the names which are not just deleted and not
            // moved. But this is easier to reason about.
            for (name, _) in old.difference(&new) {
                self.defines.remove(name);
            }
            for (name, pos) in new.difference(&old) {
                self.defines.insert(*name, pos.clone());
            }
        }

        {
            let new = global_usages
                .into_iter()
                .flat_map(|(name, xx)| xx.into_iter().map(move |(pos, sort)| (name, pos, sort)))
                .collect::<BTreeSet<_>>();
            let old = self
                .previouse_global_usages
                .insert(fi, new.clone())
                .unwrap_or_default();
            for (name, pos, sort) in old.difference(&new) {
                if let Some(mut e) = self.references.get_mut(&name.1) {
                    if let Some(e) = e.get_mut(name) {
                        e.remove(&(*pos, *sort));
                    }
                }
            }

            for (name, pos, sort) in new.difference(&old) {
                let mut e = self.references.entry(name.1).or_insert(BTreeMap::new());
                e.entry(*name)
                    .or_insert(BTreeSet::new())
                    .insert((*pos, *sort));
            }
        }

        let exports_changed = {
            let new_hash = hash_exports(&exports);
            let exports_changed = if let Some(old) = self.exports.insert(me, exports) {
                new_hash != hash_exports(&old)
            } else {
                true
            };
            tracing::info!(
                "exports_changed={:?} {:?} {:?}",
                exports_changed,
                fi,
                new_hash
            );
            exports_changed
        };

        {
            let new_imports: BTreeMap<_, _> = n
                .imports
                .into_iter()
                .map(|(k, v)| (k, v.into_iter().flat_map(|(_, x)| x).collect::<Vec<_>>()))
                .collect();
            let old_imports = self
                .imports
                .insert(me, new_imports.clone())
                .unwrap_or_else(BTreeMap::new);
            let new_imports = new_imports
                .values()
                .flat_map(|x| {
                    x.iter()
                        .flat_map(|x| x.to_names().into_iter().map(|x| x.module()))
                })
                .collect::<BTreeSet<ast::Ud>>();
            let old_imports = old_imports
                .values()
                .flat_map(|x| {
                    x.iter()
                        .flat_map(|x| x.to_names().into_iter().map(|x| x.module()))
                })
                .collect::<BTreeSet<ast::Ud>>();
            for x in old_imports.difference(&new_imports) {
                self.importers
                    .entry(*x)
                    .or_insert(BTreeSet::new())
                    .remove(&me);
            }
            for x in new_imports.difference(&old_imports) {
                self.importers
                    .entry(*x)
                    .or_insert(BTreeSet::new())
                    .insert(me);
            }
        }
        Some((exports_changed, n.me))
    }

    #[instrument(skip(self))]
    fn resolve_cascading(
        &self,
        me: ast::Ud,
        fi: ast::Fi,
        version: Option<i32>,
    ) -> Vec<(ast::Fi, Option<i32>)> {
        // TODO: This can be way way smarter, currently it only runs on changed exports.
        // Some exteions include: Lineage tracking - saying letting me know what parts actually
        // changed.
        let name = Name(Scope::Module, me, me, Visibility::Public);
        let mut to_notify = Vec::new();
        let mut checked = BTreeSet::new();
        let mut to_check: BTreeSet<ast::Ud> = self
            .importers
            .try_get(&me)
            .try_unwrap()
            .iter()
            .flat_map(|x| x.iter())
            .copied()
            .collect();
        let mut size_last_iter = 0;
        loop {
            if size_last_iter == to_check.len() {
                break;
            }
            tracing::info!("CASCADE ITER {:?} {:?}", size_last_iter, to_check.len());
            size_last_iter = to_check.len();
            let done = to_check
                .difference(&checked)
                .collect::<Vec<_>>()
                .par_iter()
                .filter_map(|x| {
                    let m = &*self.modules.try_get(x).try_unwrap()?;
                    let fi = *self.ud_to_fi.try_get(x).try_unwrap()?;
                    let version = *self.fi_to_version.try_get(&fi).try_unwrap()?;
                    tracing::info!("RESOLVING {:?} {}", x, to_check.len());
                    let _ = self.resolve_module(m, fi, version);
                    Some((
                        **x,
                        if self
                            .exports
                            .try_get(x)
                            .try_unwrap()
                            .map(|ex| ex.iter().any(|x| x.contains(name)))
                            .unwrap_or(false)
                        {
                            tracing::info!("REEXPORT {:?} {}", x, to_check.len());
                            // It's a re-export which means we need to check everything that imports this as well!
                            self.importers
                                .try_get(x)
                                .try_unwrap()
                                .iter()
                                .flat_map(|x| x.iter().copied())
                                .collect::<BTreeSet<_>>()
                        } else {
                            BTreeSet::new()
                        },
                        fi,
                        version,
                    ))
                })
                .collect::<Vec<_>>();
            for (x, mut extra, fi, version) in done.into_iter() {
                tracing::info!("DONE CHECK {:?}", x);
                checked.insert(x);
                to_check.append(&mut extra);
                to_notify.push((fi, version));
            }
        }
        to_notify
    }

    #[instrument(skip(self))]
    async fn show_errors(&self, fi: ast::Fi, version: Option<i32>) {
        if self.got_refresh(fi, version) {
            return;
        }
        let uri = if let Some(uri) = self.fi_to_uri.try_get(&fi).try_unwrap() {
            uri.value().clone()
        } else {
            return;
        };

        let se = if let Some(x) = self.syntax_errors.try_get(&fi).try_unwrap() {
            x.value().clone()
        } else {
            Vec::new()
        };
        let re = if let Some(x) = self.name_resolution_errors.try_get(&fi).try_unwrap() {
            x.value().clone()
        } else {
            Vec::new()
        };
        let v = if let Some(v) = self.fi_to_version.try_get(&fi).try_unwrap() {
            *v
        } else {
            None
        };
        // tracing::info!("PRESENTING DIAGNOSTICS {:?}", uri.to_string());
        self.client
            .publish_diagnostics(uri.clone(), [se, re].concat(), v)
            .await
    }

    #[instrument(skip(self, source))]
    fn parse(&self, fi: ast::Fi, source: &'_ str) -> (Option<ast::Module>, ast::Fi) {
        let l = lexer::lex(source, fi);
        let mut p = parser::P::new(&l, &self.names);
        let m = parser::module(&mut p);
        self.syntax_errors.insert(
            fi,
            p.errors
                .into_iter()
                .map(|err| {
                    let message = match err {
                        parser::Serror::Info(_, s) => format!("Info: {}", s),
                        parser::Serror::Unexpected(_, t, s) => format!("Unexpected {:?}: {}", t, s),
                        parser::Serror::NotSimpleTypeVarBinding(_) => {
                            "Not a simple type-var binding".to_string()
                        }
                        parser::Serror::NotAConstraint(_) => "Not a constraint".to_string(),
                        parser::Serror::NotAtEOF(_, _) => "Not at end of file".to_string(),
                        parser::Serror::FailedToParseDecl(_, _, _, _) => {
                            "Failed to parse this declaration".to_string()
                        }
                    };
                    let span = err.span();
                    create_error(span, "Syntax".into(), message, Vec::new())
                })
                .collect::<Vec<_>>(),
        );
        (m, fi)
    }

    #[instrument(skip(self))]
    fn find_fi(&self, uri: Uri) -> Option<ast::Fi> {
        match self.uri_to_fi.try_entry(uri.clone()) {
            Some(dashmap::Entry::Occupied(v)) => Some(*v.get()),
            Some(dashmap::Entry::Vacant(v)) => {
                let fi = ast::Fi(sungod::Ra::ggen::<usize>());
                v.insert(fi);
                Some(fi)
            }
            None => None,
        }
    }

    #[instrument(skip(self, params))]
    fn on_change(
        &self,
        params: TextDocumentItem<'_>,
    ) -> Option<(
        ast::Fi,
        std::option::Option<i32>,
        Vec<(ast::Fi, std::option::Option<i32>)>,
    )> {
        if !self.has_started.try_read().map(|x| *x).unwrap_or(false) {
            tracing::error!("Aborting since not started");
            return None;
        }

        let uri = params.uri.clone();
        let source = params.text;
        let version = params.version;

        let fi = loop {
            if let Some(fi) = self.find_fi(uri.clone()) {
                break fi;
            }
            tracing::error!("FAILED TO GENERATE FI");
        };

        // TODO: How to handle two files with the same module name?
        match self.fi_to_version.try_entry(fi) {
            Some(dashmap::Entry::Occupied(mut o)) => {
                if o.get().is_some() && o.get() > &version {
                    return None;
                }
                o.insert(version);
            }
            Some(dashmap::Entry::Vacant(v)) => {
                v.insert(version);
            }
            None => return None,
        }
        sleep(Duration::from_millis(1));
        let lock = self.locked.write().unwrap();
        if self.got_refresh(fi, version) {
            tracing::info!("!! {:?} ABORTED {:?}", version, uri.to_string());
            return None;
        }
        tracing::info!("!! {:?} GOT LOCK {:?}", version, uri.to_string());

        // I have to copy it! :(
        self.fi_to_source.insert(fi, source.to_string());
        tracing::info!("!! {:?} A {:?}", version, uri.to_string());
        self.fi_to_uri.insert(fi, uri.clone());
        tracing::info!("!! {:?} B {:?}", version, uri.to_string());
        let (m, fi) = self.parse(fi, source);

        tracing::info!("!! {:?} PARSING DONE {:?}", version, uri.to_string());

        // TODO: We could exit earlier if we have the same syntactical structure here
        let to_notify = if let Some(m) = m {
            tracing::info!("!! {:?} PRE RESOLVE {:?}", version, uri.to_string());
            if let Some((exports_changed, me)) = self.resolve_module(&m, fi, version) {
                // If the module name changed (e.g. user is typing a new name),
                // clean up stale entries keyed by the old Ud.
                if let Some(old_me) = self.fi_to_ud.get(&fi) {
                    let old_me = *old_me;
                    if old_me != me {
                        self.modules.remove(&old_me);
                        self.ud_to_fi.remove(&old_me);
                        self.exports.remove(&old_me);
                        self.resolved.remove(&old_me);
                        self.imports.remove(&old_me);
                        self.importers.remove(&old_me);
                        self.references.remove(&old_me);
                    }
                }
                self.modules.insert(me, m);
                tracing::info!("!! {:?} H {:?}", version, uri.to_string());
                self.fi_to_ud.insert(fi, me);
                tracing::info!("!! {:?} I {:?}", version, uri.to_string());
                self.ud_to_fi.insert(me, fi);
                tracing::info!("!! {:?} J {:?}", version, uri.to_string());

                if exports_changed {
                    tracing::info!("CASCADE CHANGE - START");
                    let to_notify = self.resolve_cascading(me, fi, version);
                    tracing::info!("CASCADE CHANGE - END");
                    to_notify
                } else {
                    Vec::new()
                }
            } else {
                Vec::new()
            }
        } else {
            Vec::new()
        };
        tracing::info!("!! {:?} DROP LOCK {:?}", version, uri.to_string());
        drop(lock);
        Some((fi, version, to_notify))
    }
}

fn hash_exports(exports: &[Export]) -> u64 {
    let mut hasher = DefaultHasher::new();
    exports.hash(&mut hasher);
    hasher.finish()
}

fn pos_from_tup((line, col): ast::Pos) -> Position {
    Position::new(
        line.try_into().unwrap_or(u32::MAX),
        col.try_into().unwrap_or(u32::MAX),
    )
}

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let mut logging = true;
    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "--no-log" => {
                logging = false;
            }
            "--version" | "-v" => {
                eprintln!("{}", hemlis_lib::version());
                std::process::exit(0);
            }
            x => {
                eprintln!("Unknown arg: {}", x);
                std::process::exit(1);
            }
        }
    }
    if logging {
        let log_file_path =
            std::env::temp_dir().join(format!("hemlis-{}.log", chrono::Local::now().to_rfc3339()));
        let log_file = File::create(&log_file_path).unwrap();
        eprintln!("Logging to {:?}", log_file_path);

        let layer = json_subscriber::layer()
            .with_file(true)
            .with_line_number(true)
            .with_thread_ids(true)
            .with_level(true)
            .with_writer(log_file)
            .with_filter(tracing::level_filters::LevelFilter::TRACE)
            .with_filter(FilterFn::new(|x| x.target() != "tower_lsp_server::codec"));

        std::panic::set_hook(Box::new(|panic| {
            if let Some(location) = panic.location() {
                tracing::error!(
                    message= %panic,
                    panic.file = location.file(),
                    panic.line = location.line(),
                    panic.column = location.column(),
                );
            } else {
                tracing::error!(message= %panic);
            }
        }));

        tracing_subscriber::registry().with(layer).init();
    } else {
        eprintln!("Logging is disabled");
    }

    tracing::info!("{}", hemlis_lib::version());

    let (exports, prim, names) = hemlis_lib::build_builtins();

    let (service, socket) = LspService::build(|client| Backend {
        client,

        locked: ().into(),
        has_started: false.into(),
        prim,
        names,

        fi_to_uri: DashMap::new(),
        fi_to_ud: DashMap::new(),
        fi_to_source: DashMap::new(),
        ud_to_fi: DashMap::new(),
        uri_to_fi: DashMap::new(),
        fi_to_version: DashMap::new(),

        importers: DashMap::new(),
        imports: DashMap::new(),

        available_locals: DashMap::new(),

        previouse_defines: DashMap::new(),
        previouse_global_usages: DashMap::new(),

        exports,
        modules: DashMap::new(),
        resolved: DashMap::new(),
        defines: DashMap::new(),
        references: DashMap::new(),

        syntax_errors: DashMap::new(),
        name_resolution_errors: DashMap::new(),
        fixables: DashMap::new(),

        client_watch_dynamic_registration: std::sync::OnceLock::new(),
    })
    .finish();

    Server::new(stdin, stdout, socket).serve(service).await;
}

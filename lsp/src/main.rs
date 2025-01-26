#![allow(clippy::type_complexity)]
#![feature(btree_cursors)]

use std::collections::{BTreeMap, BTreeSet};
use std::fs::File;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::ops::Bound;
use std::sync::RwLock;

use ast::{Ast, Pos};
use futures::future::join_all;
use hemlis_lib::*;
use nr::{Export, NRerrors, Name, Scope, Visibility};
use papaya::Operation;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use tower_lsp::jsonrpc::{Error, ErrorCode, Result};
use tower_lsp::lsp_types::notification::Notification;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};
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

// fn range_to_span(fi: ast::Fi, s: Range) -> ast::Span {
//     let Position {
//         line: lo_l,
//         character: lo_c,
//     } = s.start;
//     let Position {
//         line: hi_l,
//         character: hi_c,
//     } = s.end;
//     ast::Span::Known(
//         fi,
//         (lo_l as usize, lo_c as usize),
//         (hi_l as usize, hi_c as usize),
//     )
// }

#[derive(Debug)]
struct Backend {
    client: Client,

    prim: ast::Ud,

    locked: RwLock<()>,
    has_started: RwLock<bool>,
    names: papaya::HashMap<ast::Ud, String>,

    fi_to_url: papaya::HashMap<ast::Fi, Url>,
    fi_to_ud: papaya::HashMap<ast::Fi, ast::Ud>,
    fi_to_source: papaya::HashMap<ast::Fi, String>,
    url_to_fi: papaya::HashMap<Url, ast::Fi>,
    fi_to_version: papaya::HashMap<ast::Fi, Option<i32>>,
    ud_to_fi: papaya::HashMap<ast::Ud, ast::Fi>,

    importers: papaya::HashMap<ast::Ud, BTreeSet<ast::Ud>>,
    imports: papaya::HashMap<ast::Ud, BTreeMap<Option<ast::Ud>, Vec<Export>>>,

    previouse_global_usages: papaya::HashMap<ast::Fi, BTreeSet<(Name, ast::Span, nr::Sort)>>,
    previouse_defines: papaya::HashMap<ast::Fi, BTreeSet<(Name, ast::Span)>>,

    // The option here should always be Some - but `None` lets us do a better partition search
    // here.
    available_locals: papaya::HashMap<ast::Fi, BTreeSet<((usize, usize), Option<Name>)>>,

    exports: papaya::HashMap<ast::Ud, Vec<Export>>,
    modules: papaya::HashMap<ast::Ud, ast::Module>,
    resolved: papaya::HashMap<ast::Ud, BTreeMap<(Pos, Pos), Name>>,
    defines: papaya::HashMap<Name, ast::Span>,
    // TODO: Fields are technically not memory managed here - they are just always appended. This
    // should probably be fixed - but ATM computers are fast LOL.
    //
    // This can easily be fixed by stripping out the field names if we come accross them - but we
    // can also like not do that.
    references: papaya::HashMap<ast::Ud, BTreeMap<Name, BTreeSet<(ast::Span, nr::Sort)>>>,

    syntax_errors: papaya::HashMap<ast::Fi, Vec<tower_lsp::lsp_types::Diagnostic>>,
    name_resolution_errors: papaya::HashMap<ast::Fi, Vec<tower_lsp::lsp_types::Diagnostic>>,
    fixables: papaya::HashMap<ast::Fi, Vec<(ast::Span, Fixable)>>,
}

impl Backend {
    fn resolve_name(&self, url: &Url, pos: Position) -> Option<Name> {
        let m = *self.fi_to_ud.pin().get(self.url_to_fi.pin().get(url)?)?;
        let pos = (pos.line as usize, pos.character as usize + 1);
        let resolved = self.resolved.pin();
        let cur = resolved.get(&m)?.lower_bound(Bound::Included(&(pos, pos)));
        let ((lo, hi), name) = cur.peek_prev()?;
        if !(*lo <= pos && pos <= *hi) {
            return None;
        }
        Some(*name)
    }

    fn resolve_name_and_range(&self, url: &Url, pos: Position) -> Option<(Name, Range)> {
        let m = *self.fi_to_ud.pin().get(self.url_to_fi.pin().get(url)?)?;
        let pos = (pos.line as usize, pos.character as usize + 1);
        let resolved = self.resolved.pin();
        let lut = resolved.get(&m)?;
        let cur = lut.lower_bound(Bound::Included(&(pos, pos)));
        let ((lo, hi), name) = cur.peek_prev()?;
        if !(*lo <= pos && pos <= *hi) {
            return None;
        }
        Some((*name, range(*lo, *hi)))
    }

    fn got_refresh(&self, fi: ast::Fi, version: Option<i32>) -> bool {
        self.fi_to_version.pin().get(&fi) != Some(&version)
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

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    #[instrument(skip(self))]
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
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
        {
            tracing::info!("version {}", hemlis_lib::version());
            tracing::info!("Scanning...");
            self.load_workspace().await;
            tracing::info!("Done scanning");
            let mut futures = Vec::new();
            for k in self.fi_to_url.pin().keys().copied() {
                futures.push(self.show_errors(k, None));
            }
            join_all(futures).await;
        }
        {
            let mut write = self.has_started.write().unwrap();
            *write = true;
        }
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    #[instrument(skip(self, params))]
    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        self.on_change(TextDocumentItem {
            uri: params.text_document.uri,
            text: &params.text_document.text,
            version: Some(params.text_document.version),
        })
        .await
    }

    #[instrument(skip(self, params))]
    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        self.on_change(TextDocumentItem {
            text: &params.content_changes[0].text,
            uri: params.text_document.uri,
            version: Some(params.text_document.version),
        })
        .await
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
                let def_at = *self.defines.pin().get(&name)?;
                let uri = self.fi_to_url.pin().get(&def_at.fi()?)?.clone();
                Some(GotoDefinitionResponse::Scalar(Location {
                    uri,
                    range: span_to_range(&def_at),
                }))
            } else {
                let fi = *self
                    .url_to_fi
                    .pin()
                    .get(&params.text_document_position_params.text_document.uri)?;
                let fi_to_source = self.fi_to_source.pin();
                let source = fi_to_source.get(&fi)?;
                let position = params.text_document_position_params.position;
                let word_under_cursor =
                    try_find_word(source, position.line as usize, position.character as usize)?;
                if word_under_cursor != "foreign" {
                    return None;
                };
                drop(fi_to_source);
                let mut uri = params
                    .text_document_position_params
                    .text_document
                    .uri
                    .to_file_path()
                    .ok()?;
                uri.set_extension("erl");
                Some(GotoDefinitionResponse::Scalar(Location {
                    uri: Url::from_file_path(uri).ok()?,
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
                    .pin()
                    .get(&name.1)?
                    .get(&name)?
                    .iter()
                    .filter_map(|(s, sort): &(ast::Span, nr::Sort)| {
                        if !sort.is_def_or_ref() {
                            return None;
                        }
                        let url = self.fi_to_url.pin().get(&s.fi()?)?.clone();
                        let range = span_to_range(s);

                        Some(Location::new(url, range))
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
    ) -> Result<Option<Vec<SymbolInformation>>> {
        let mut symbols = Vec::new();
        for (fi, names) in self.previouse_defines.pin().iter() {
            for (Name(scope, ns, n, vis), at) in names.iter() {
                if *vis != Visibility::Public {
                    continue;
                }
                let n = self.name_(n);
                let ns = self.name_(ns);
                if Some(fi) != at.fi().as_ref() {
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
                        let url = self.fi_to_url.pin().get(fi).unwrap().clone();
                        let range = span_to_range(at);
                        Location::new(url, range)
                    },

                    container_name: None,
                };
                symbols.push(out);
            }
        }
        Ok(Some(symbols))
    }

    #[instrument(skip(self))]
    async fn document_symbol(
        &self,
        params: DocumentSymbolParams,
    ) -> Result<Option<DocumentSymbolResponse>> {
        let mut symbols = Vec::new();
        let fi_inner = if let Some(fi) = self.url_to_fi.pin().get(&params.text_document.uri) {
            *fi
        } else {
            return Err(error(line!(), "File not loaded"));
        };
        if let Some(names) = self.previouse_defines.pin().get(&fi_inner) {
            for (Name(scope, _, n, vis), at) in names.iter() {
                if *vis != Visibility::Public {
                    continue;
                }
                let fi = if let Some(fi) = at.fi() { fi } else { continue };
                let name = match self.names.pin().get(n) {
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
                        let url = self.fi_to_url.pin().get(&fi).unwrap().clone();
                        let range = span_to_range(at);
                        Location::new(url, range)
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
            let fi = *self.url_to_fi.pin().get(&uri)?;
            let me = *self.fi_to_ud.pin().get(&fi)?;
            let line = position.line as usize;
            let fi_to_source = self.fi_to_source.pin();
            let source = fi_to_source.get(&fi)?;
            let to_complete = try_find_word(source, line, position.character as usize)?.to_string();
            drop(fi_to_source);

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
                .pin()
                .get(&me)
                .and_then(|x| x.get(&namespace).cloned())
            {
                for n in imports.iter().flat_map(|x| x.to_names()) {
                    if n.scope() == Scope::Namespace {
                        continue;
                    }
                    let name = self.name_(&n.name());
                    if name.starts_with(&var) {
                        out.push(CompletionItem::new_simple(
                            name.to_string(),
                            format!("Imported {:?}", n.scope()),
                        ));
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
                    .pin()
                    .get(&ast::Ud::zero())?
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
                        out.push(CompletionItem::new_simple(
                            name.to_string(),
                            format!("Define {:?}", n.scope()),
                        ));
                    }
                }
            }

            if namespace.is_none() {
                // Locals
                let available_locals = self.available_locals.pin();
                let lut = available_locals.get(&fi)?;
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
                        out.push(CompletionItem::new_simple(
                            name.to_string(),
                            format!("Local {:?}", n.scope()),
                        ));
                    }

                    cur.next();
                }

                // Defines
                // let lock = self.locked.write();
                let defines: Vec<_> = self
                    .defines
                    .pin()
                    .keys()
                    .filter_map(|k| {
                        if k.module() != me {
                            return None;
                        }
                        Some(*k)
                    })
                    .collect();
                // drop(lock);
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
                        out.push(CompletionItem::new_simple(
                            name.to_string(),
                            format!("Define {:?}", n.scope()),
                        ));
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
        let mut edits = std::collections::HashMap::new();
        for at in self
            .references
            .pin()
            .get(&name.1)
            .ok_or_else(|| error(line!(), "Failed to read references"))?
            .get(&name)
            .ok_or_else(|| error(line!(), "Unknown name - how did we get here?"))?
            .iter()
            .map(|(at, _)| *at)
            .collect::<BTreeSet<_>>()
            .into_iter()
        {
            let url = self
                .fi_to_url
                .pin()
                .get(&if let Some(fi) = at.fi() { fi } else { continue })
                .ok_or_else(|| error(line!(), "Unknown file - how did we get here?"))?
                .clone();
            let range = span_to_range(&at);
            edits.entry(url).or_insert(Vec::new()).push(TextEdit {
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

        let foo = 1;
        println!("{foo}");

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
        let fi = *or_!(self.url_to_fi.pin().get(&uri), {
            return Err(error(line!(), "File not loaded"));
        });
        let me = *or_!(self.fi_to_ud.pin().get(&fi), {
            return Err(error(line!(), "File failed to load"));
        });

        let (l, c) = or_!(
            &or_!(&self.modules.pin().get(&me), {
                return Err(error(line!(), "Module failed to load"));
            })
            .0,
            {
                return Err(error(line!(), "Module failed to load"));
            }
        )
        .span()
        .hi();
        let end_of_imports = (l, c + 1);

        let mut out = Vec::new();
        for (s, f) in or_!(self.fixables.pin().get(&fi), {
            return Err(error(line!(), "Module failed to load"));
        })
        .iter()
        {
            if !s.contains((
                params.range.start.line as usize,
                params.range.start.character as usize,
            )) {
                continue;
            }
            match f {
                Fixable::GuessImports(s, ns, n, at) => {
                    // Assume `n` is spelt correctly

                    // 1. Find all possible imports with `n`
                    // 1a. Figure out what edits need to be done

                    let imported = or_!(self.imports.pin().get(&me), { continue }).clone();
                    let seen: BTreeSet<nr::Name> = imported
                        .values()
                        .flat_map(|x| x.iter().flat_map(|x| x.to_names()))
                        .collect();

                    let handle = |ns: Option<ast::Ud>, name: &nr::Name, out: &mut Vec<_>| {
                        out.push(CodeAction {
                            title: format!(
                                "[QUSE {:?}] Qualified use {} ({})",
                                name.scope(),
                                format_name(ns, name.name(), &self.names),
                                self.name_(&name.module()),
                            ),
                            kind: Some(CodeActionKind::QUICKFIX),
                            is_preferred: Some(true),
                            edit: Some(WorkspaceEdit::new(
                                [(
                                    uri.clone(),
                                    vec![TextEdit::new(
                                        range(at.lo(), at.hi()),
                                        format_name(ns, name.name(), &self.names),
                                    )],
                                )]
                                .into(),
                            )),
                            ..CodeAction::default()
                        });
                    };

                    for (m, xs) in imported.iter() {
                        for export in xs.iter() {
                            match export {
                                Export::ConstructorsSome(name, constructors)
                                | Export::ConstructorsAll(name, constructors) => {
                                    if name.name() == *n && name.scope() == *s {
                                        handle(*m, name, &mut out);
                                    }
                                    for c in constructors.iter() {
                                        if c.name() == *n
                                            && c.scope() == *s
                                            && c.scope() == nr::Scope::Term
                                        {
                                            handle(*m, name, &mut out);
                                        }
                                    }
                                }
                                Export::Just(name) => {
                                    if name.name() == *n && name.scope() == *s {
                                        handle(*m, name, &mut out);
                                    }
                                }
                            }
                        }
                    }

                    // let lock = self.locked.write();
                    let exports: BTreeMap<ast::Ud, Vec<nr::Export>> = self
                        .exports
                        .pin()
                        .iter()
                        .map(|(k, v)| (*k, v.clone()))
                        .collect();
                    // drop(lock);

                    let handle = |name: &nr::Name, _is_constructor: bool, out: &mut Vec<_>| {
                        if let Some(ns) = ns {
                            let ns_name = self.name_(ns);
                            let name_name = self.name_(&name.module());
                            out.push(CodeAction {
                                title: format!(
                                    "[QIMPORT {:?}] Qualified from {} as {}",
                                    name.scope(),
                                    name_name,
                                    ns_name
                                ),
                                kind: Some(CodeActionKind::QUICKFIX),
                                is_preferred: Some(
                                    ns_name.contains(&name_name) || name_name.contains(&ns_name),
                                ),
                                edit: Some(WorkspaceEdit::new(
                                    [(
                                        uri.clone(),
                                        vec![TextEdit::new(
                                            range(end_of_imports, end_of_imports),
                                            format!(
                                                "\nimport {} as {}",
                                                self.name_(&name.module()),
                                                self.name_(ns)
                                            ),
                                        )],
                                    )]
                                    .into(),
                                )),
                                ..CodeAction::default()
                            });
                        } else {
                            out.push(CodeAction {
                                title: format!(
                                    "[QIMPORT {:?}] Qualified from {}",
                                    name.scope(),
                                    self.name_(&name.module())
                                ),
                                kind: Some(CodeActionKind::QUICKFIX),
                                edit: Some(WorkspaceEdit::new(
                                    [(
                                        uri.clone(),
                                        vec![
                                            TextEdit::new(
                                                range(end_of_imports, end_of_imports),
                                                format!(
                                                    "\nimport {} as {}",
                                                    self.name_(&name.module()),
                                                    self.name_(&name.module())
                                                ),
                                            ),
                                            TextEdit::new(
                                                range(at.lo(), at.hi()),
                                                format!(
                                                    "{}.{}",
                                                    self.name_(&name.module()),
                                                    self.name_(&name.name())
                                                ),
                                            ),
                                        ],
                                    )]
                                    .into(),
                                )),
                                ..CodeAction::default()
                            });
                            // TODO: This needs to also find imports if they exist and add it
                            // to them.
                            //
                            // out.push(
                            //     CodeAction {
                            //         title: format!(
                            //             "[SIMPORT {:?}] {}.{}",
                            //             name.scope(),
                            //             self.name (&name.module()),
                            //             self.name (&name.name())
                            //         ),
                            //         kind: Some(CodeActionKind::QUICKFIX),
                            //         edit: Some(WorkspaceEdit::new(
                            //             [(
                            //                 uri.clone(),
                            //                 vec![TextEdit::new(
                            //                     range(end_of_imports, end_of_imports),
                            //                     format!(
                            //                         "\nimport {} ({})",
                            //                         self.name (&name.module()),
                            //                         as_import(
                            //                             name.scope(),
                            //                             is_constructor,
                            //                             name.name(),
                            //                             &self.names
                            //                         )
                            //                     ),
                            //                 )],
                            //             )]
                            //             .into(),
                            //         )),
                            //         ..CodeAction::default()
                            //     }
                            // )
                        }
                    };

                    for (m, xs) in exports.iter() {
                        if *m == me {
                            continue;
                        }
                        for export in xs.iter() {
                            match export {
                                Export::ConstructorsSome(name, constructors)
                                | Export::ConstructorsAll(name, constructors) => {
                                    if name.name() == *n
                                        && name.scope() == *s
                                        && !seen.contains(name)
                                    {
                                        handle(name, false, &mut out);
                                    }
                                    for c in constructors.iter() {
                                        if c.name() == *n
                                            && c.scope() == *s
                                            && c.scope() == nr::Scope::Term
                                            && !seen.contains(c)
                                        {
                                            handle(name, true, &mut out);
                                        }
                                    }
                                }
                                Export::Just(name) => {
                                    if name.name() == *n
                                        && name.scope() == *s
                                        && !seen.contains(name)
                                    {
                                        handle(name, false, &mut out);
                                    }
                                }
                            }
                        }
                    }
                }
                Fixable::Delete(at) => out.push(CodeAction {
                    title: "Delete".into(),
                    kind: Some(CodeActionKind::QUICKFIX),
                    diagnostics: None,
                    edit: Some(WorkspaceEdit::new(
                        [(
                            uri.clone(),
                            vec![TextEdit::new(span_to_range(at), "".into())],
                        )]
                        .into(),
                    )),
                    is_preferred: Some(true),
                    ..CodeAction::default()
                }),
            }
        }
        // Place the best matches at the top of the list
        out.sort_by_key(|x| x.is_preferred);
        out.reverse();
        Ok(Some(out.into_iter().map(|x| x.into()).collect()))
    }

    #[instrument(skip(self))]
    async fn did_change_configuration(&self, _: DidChangeConfigurationParams) {}

    #[instrument(skip(self))]
    async fn did_change_workspace_folders(&self, _: DidChangeWorkspaceFoldersParams) {}

    #[instrument(skip(self))]
    async fn did_change_watched_files(&self, _: DidChangeWatchedFilesParams) {
        self.client
            .log_message(
                MessageType::INFO,
                "Does not handle changed watched files".to_string(),
            )
            .await;
    }

    #[instrument(skip(self))]
    async fn execute_command(&self, params: ExecuteCommandParams) -> Result<Option<Value>> {
        if params.command == "load_workspace" {
            self.client
                .log_message(MessageType::INFO, "Loading entire workspace...".to_string())
                .await;
            self.load_workspace().await;
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

        use std::fmt::Write;
        let mut target = String::new();

        (|| {
            let def_at = *self.defines.pin().get(&name)?;
            let fi = *self.ud_to_fi.pin().get(&name.module())?;
            let fi_to_source = self.fi_to_source.pin();
            let source = fi_to_source.get(&fi)?;
            if let Some(x) = try_find_comments_before(source, def_at.lo().0) {
                writeln!(target).unwrap();
                x.split("\n").for_each(|x| {
                    writeln!(
                        target,
                        "{}",
                        x.trim_start_matches("--")
                            .trim_start_matches("|")
                            .trim_start_matches(" |")
                    )
                    .unwrap();
                })
            }
            if let Some(x) = try_find_lines(source, def_at.lo().0, def_at.hi().0) {
                writeln!(target, "```purescript").unwrap();
                x.split("\n").for_each(|x| {
                    writeln!(target, "{}", x.trim_end()).unwrap();
                });
                writeln!(target, "```").unwrap();
            }
            Some(())
        })();

        write!(target, "{:?} {}", name.scope(), self.name_(&name.name())).unwrap();
        if let Some(module_name) = self.name(&name.module()) {
            write!(target, ", in {}", module_name).unwrap();
        }
        writeln!(target).unwrap();

        (|| {
            let references = self
                .references
                .pin()
                .get(&name.module())?
                .get(&name)?
                .clone();
            let num_references = references.len();
            let num_usages = references.iter().filter(|(_, x)| x.is_ref()).count();
            writeln!(
                target,
                "{} references\n{} usages",
                num_references, num_usages
            )
            .unwrap();
            Some(())
        })();

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

fn error(code: u32, message: &str) -> Error {
    let mut err = Error::new(ErrorCode::ServerError(code.into()));
    err.message = message.to_string().into();
    err
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
enum Fixable {
    GuessImports(nr::Scope, Option<ast::Ud>, ast::Ud, ast::Span),
    Delete(ast::Span),
}

fn create_error(
    span: ast::Span,
    code: String,
    message: String,
    related: Vec<(String, Location)>,
) -> tower_lsp::lsp_types::Diagnostic {
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
) -> tower_lsp::lsp_types::Diagnostic {
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
        | NRerrors::CouldNotFindImport(_, _)
        | NRerrors::Unused(_, _) => Vec::new(),
    }
}

fn format_name(
    ns: Option<ast::Ud>,
    n: ast::Ud,
    names: &papaya::HashMap<ast::Ud, String>,
) -> String {
    match (
        names.pin().get(&ns.unwrap_or(ast::Ud(0, '_'))).cloned(),
        names.pin().get(&n).cloned(),
    ) {
        (None, Some(name)) => name,
        (Some(ns), Some(name)) => format!("{}.{}", ns, name),
        (_, _) => "!! UNREACHABLE - PLEASE REPORT".into(),
    }
}

// fn as_import(
//     scope: nr::Scope,
//     is_constructor: bool,
//     name: ast::Ud,
//     names: &DashMap<ast::Ud, String>,
// ) -> String {
//     assert!(!is_constructor || scope == nr::Scope::Type);
//     let name = if let Some(name) = names.pin().get(&name) {
//         name.value().clone()
//     } else {
//         "?".into()
//     };
//     let first = name.chars().next().unwrap();
//     let is_identifier = char::is_ascii_alphanumeric(&first) || first == '_';
//     match scope {
//         _ if is_constructor => format!("{}(..)", name),
//
//         Scope::Kind | Scope::Type if is_identifier => {
//             format!("{}", name)
//         }
//         Scope::Kind | Scope::Type => {
//             format!("type ({})", name)
//         }
//         Scope::Class => format!("class {}", name),
//         Scope::Namespace | Scope::Module => format!("module {}", name),
//
//         Scope::Term if is_identifier => format!("{}", name),
//         Scope::Term => format!("({})", name),
//     }
// }

pub fn nrerror_turn_into_diagnostic(
    error: NRerrors,
    names: &papaya::HashMap<ast::Ud, String>,
) -> tower_lsp::lsp_types::Diagnostic {
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
                names.pin().get(&i).cloned().unwrap_or_else(|| "?".into())
            ),
            Vec::new(),
        ),
        NRerrors::NotAConstructor(d, m) => create_error(
            m.0 .1,
            "NotAConstructor".into(),
            format!(
                "{} does not have a constructors {}",
                names.pin().get(&d.2).cloned().unwrap_or_else(|| "?".into()),
                names
                    .pin()
                    .get(&m.0 .0)
                    .cloned()
                    .unwrap_or_else(|| "?".into())
            ),
            Vec::new(),
        ),
        NRerrors::NoConstructors(m, s) => create_error(
            s,
            "NoConstructors".into(),
            format!(
                "{} does not have constructors",
                names.pin().get(&m.2).cloned().unwrap_or_else(|| "?".into()),
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
                "Could not find this import {}",
                names.pin().get(&n).cloned().unwrap_or_else(|| "?".into()),
            ),
            Vec::new(),
        ),
        NRerrors::Unused(info, s) => create_warning(s, "Unused".into(), info, Vec::new()),
    }
}

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
    uri: Url,
    text: &'a str,
    version: Option<i32>,
}

impl Backend {
    fn name_(&self, ud: &ast::Ud) -> String {
        self.name(ud).unwrap_or_else(|| "?".into())
    }

    fn name(&self, ud: &ast::Ud) -> Option<String> {
        Some(self.names.pin().get(ud)?.clone())
    }

    #[instrument(skip(self))]
    fn load_file(
        &self,
        path: std::path::PathBuf,
    ) -> Option<(ast::Ud, ast::Fi, BTreeSet<ast::Ud>, hemlis_lib::ast::Module)> {
        let file_name = path.clone().into_os_string().into_string().ok()?;
        let source = std::fs::read_to_string(path.clone()).ok()?;
        let uri = Url::parse(&format!("file://{}", file_name)).ok()?;
        let x = || {
            let fi = self.find_fi(uri.clone());
            self.fi_to_source.pin().insert(fi, source.to_string());
            self.fi_to_url.pin().insert(fi, uri.clone());
            self.fi_to_version.pin().insert(fi, None);
            let (m, fi) = self.parse(fi, &source);
            let m = m?;
            let (me, imports) = {
                let header = m.0.clone()?;
                let me = header.0 .0 .0;
                (
                    me,
                    header
                        .2
                        .iter()
                        .map(|x| x.from.0 .0)
                        .collect::<BTreeSet<_>>(),
                )
            };
            self.modules.pin().insert(me, m.clone());
            self.fi_to_ud.pin().insert(fi, me);
            self.ud_to_fi.pin().insert(me, fi);
            Some((me, fi, imports, m))
        };
        let out = x();
        if out.is_none() {
            tracing::error!("Failed to load {}", &file_name);
        }
        out
    }

    #[instrument(skip(self))]
    async fn load_workspace(&self) -> Option<()> {
        tracing::info!("Load start");
        let folders = self.client.workspace_folders().await.ok()??;

        for folder in folders {
            use glob::glob;
            let mut deps_future: Vec<_> = Vec::new();
            for path in glob(&format!(
                "{}/lib/**/*.purs",
                folder.uri.to_string().strip_prefix("file://")?
            ))
            .ok()?
            {
                let path = path.as_ref().ok()?.clone();
                deps_future.push(async { self.load_file(path) });
            }
            tracing::info!("=========");
            let deps: Vec<_> = join_all(deps_future).await.into_iter().flatten().collect();
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
                        self.client
                            .log_message(
                                MessageType::ERROR,
                                &format!("Dependency cycle detected: {}", left.len()),
                            )
                            .await;
                    }
                    break;
                }
                tracing::info!("BULK {:?}", todo.len());
                let mut futures = Vec::new();
                for (_, fi, _, m) in todo.iter() {
                    futures.push(async {
                        self.resolve_module(m, *fi, None);
                    });
                }
                join_all(futures).await;
                done.append(&mut todo.into_iter().map(|(m, _, _, _)| *m).collect());
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
        tracing::info!("RESOLVE_STARTED {:?} {:?}", fi, version);
        let me = m.0.as_ref()?.0 .0 .0;
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

        if self.got_refresh(fi, version) {
            tracing::info!("EARLY OUT 1 {:?} {:?}", fi, version);
            return None;
        }
        tracing::info!("GETTING LOCK {:?} {:?}", fi, version);
        // let lock = self.locked.write();
        if self.got_refresh(fi, version) {
            tracing::info!("EARLY OUT 2 {:?} {:?}", fi, version);
            return None;
        }
        tracing::info!("HOLDING LOCK {:?} {:?}", fi, version);

        self.modules.pin().insert(me, m.clone());
        self.fi_to_ud.pin().insert(fi, me);
        self.ud_to_fi.pin().insert(me, fi);

        self.fixables.pin().insert(
            fi,
            errors
                .iter()
                .flat_map(nrerror_turn_into_fixables)
                .collect::<Vec<_>>(),
        );

        self.name_resolution_errors.pin().insert(
            fi,
            errors
                .into_iter()
                .map(|x| nrerror_turn_into_diagnostic(x, &self.names))
                .collect::<Vec<_>>(),
        );

        self.resolved.pin().insert(me, resolved);

        {
            self.references.pin().get_or_insert_with(me, BTreeMap::new);
            self.references.pin().update(me, |us| {
                let mut us = us.clone();
                for (k, v) in us.iter_mut() {
                    v.retain(|(x, _)| x.fi() != Some(fi));
                    v.append(&mut references.get(k).cloned().unwrap_or_default());
                }
                for (k, v) in references.iter() {
                    if us.contains_key(k) {
                        continue;
                    }
                    assert!(us.insert(*k, v.clone()).is_none());
                }
                us
            });
        }

        {
            let defined_scopes = defines
                .iter()
                .filter_map(|(a, (_, available_in))| available_in.map(|x| (x.lines(), Some(*a))))
                .collect::<BTreeSet<_>>();
            self.available_locals.pin().insert(fi, defined_scopes);
        }

        {
            let new = defines
                .into_iter()
                .map(|(a, (at, _))| (a, at))
                .collect::<BTreeSet<_>>();
            let old = self
                .previouse_defines
                .pin()
                .insert(fi, new.clone())
                .cloned()
                .unwrap_or_default();

            // Technically, we only need to remove the names which are not just deleted and not
            // moved. But this is easier to reason about.
            for (name, _) in old.difference(&new) {
                self.defines.pin().remove(name);
            }
            for (name, pos) in new.difference(&old) {
                self.defines.pin().insert(*name, *pos);
            }
        }

        {
            let new = global_usages
                .into_iter()
                .flat_map(|(name, xx)| xx.into_iter().map(move |(pos, sort)| (name, pos, sort)))
                .collect::<BTreeSet<_>>();
            let old = self
                .previouse_global_usages
                .pin()
                .insert(fi, new.clone())
                .cloned()
                .unwrap_or_default();
            for (name, pos, sort) in old.difference(&new) {
                self.references.pin().update(name.1, |e| {
                    let mut e = e.clone();
                    if let Some(e) = e.get_mut(name) {
                        e.remove(&(*pos, *sort));
                    }
                    e
                });
            }

            for (name, pos, sort) in new.difference(&old) {
                self.references
                    .pin()
                    .get_or_insert_with(name.1, BTreeMap::new);
                self.references.pin().update(name.1, |e| {
                    let mut e = e.clone();
                    e.entry(*name).or_default().insert((*pos, *sort));
                    e
                });
            }
        }

        let exports_changed = {
            let new_hash = hash_exports(&exports);
            let exports_changed = if let Some(old) = self.exports.pin().insert(me, exports) {
                new_hash != hash_exports(old)
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
                .pin()
                .insert(me, new_imports.clone())
                .cloned()
                .unwrap_or_default();
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
                self.importers.pin().update_or_insert_with(
                    *x,
                    |x| {
                        let mut x = x.clone();
                        x.remove(&me);
                        x
                    },
                    BTreeSet::new,
                );
            }
            for x in new_imports.difference(&old_imports) {
                self.importers.pin().update_or_insert_with(
                    *x,
                    |x| {
                        let mut x = x.clone();
                        x.insert(me);
                        x
                    },
                    || [me].into(),
                );
            }
        }
        // drop(lock);
        tracing::info!("RESOLVE_ENDED {:?} {:?}", fi, version);
        Some((exports_changed, n.me))
    }

    #[instrument(skip(self))]
    async fn resolve_cascading(&self, me: ast::Ud, fi: ast::Fi, version: Option<i32>) {
        // TODO: This can be way way smarter, currently it only runs on changed exports.
        // Some exteions include: Lineage tracking - saying letting me know what parts actually
        // changed.
        let name = Name(Scope::Module, me, me, Visibility::Public);
        let mut checked = BTreeSet::new();
        let mut to_check: Vec<ast::Ud> = self
            .importers
            .pin()
            .get(&me)
            .iter()
            .flat_map(|x| x.iter())
            .copied()
            .collect();
        while let Some(x) = to_check.pop() {
            if self.got_refresh(fi, version) {
                tracing::info!("GOT REFRESH - ABORTING");
                continue;
            }
            if checked.contains(&x) {
                continue;
            }
            tracing::info!("TO CHECK {:?} {}", x, to_check.len());
            checked.insert(x);
            if let (Some(m), Some(fi), Some(version)) = (
                self.modules.pin().get(&x),
                self.ud_to_fi.pin().get(&x),
                self.fi_to_version.pin().get(&fi),
            ) {
                tracing::info!("RESOLVING {:?} {}", x, to_check.len());
                let _ = self.resolve_module(m, *fi, *version);
                if self
                    .exports
                    .pin()
                    .get(&x)
                    .map(|ex| ex.iter().any(|x| x.contains(name)))
                    .unwrap_or(false)
                {
                    tracing::info!("REEXPORT {:?} {}", x, to_check.len());
                    // It's a re-export which means we need to check everything that imports this as well!
                    to_check.append(
                        &mut self
                            .importers
                            .pin()
                            .get(&x)
                            .iter()
                            .flat_map(|x| x.iter())
                            .copied()
                            .collect::<Vec<_>>(),
                    );
                }
            }
            tracing::info!("DONE CHECK {:?}", x);
        }
    }

    #[instrument(skip(self))]
    async fn show_errors(&self, fi: ast::Fi, version: Option<i32>) {
        if self.got_refresh(fi, version) {
            return;
        }
        let url = if let Some(url) = self.fi_to_url.pin().get(&fi).cloned() {
            url
        } else {
            return;
        };
        let se = self
            .syntax_errors
            .pin()
            .get(&fi)
            .cloned()
            .unwrap_or_default();
        let ne = self
            .name_resolution_errors
            .pin()
            .get(&fi)
            .cloned()
            .unwrap_or_default();
        let v = self.fi_to_version.pin().get(&fi).cloned().flatten();
        tracing::info!("PRESENTING DIAGNOSTICS {:?}", url.to_string());
        self.client
            .publish_diagnostics(url, [se, ne].concat(), v)
            .await;
    }

    #[instrument(skip(self, source))]
    fn parse(&self, fi: ast::Fi, source: &'_ str) -> (Option<ast::Module>, ast::Fi) {
        let l = lexer::lex(source, fi);
        let mut p = parser::P::new(&l, &self.names);
        let m = parser::module(&mut p);
        self.syntax_errors.pin().insert(
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

    fn find_fi(&self, uri: Url) -> ast::Fi {
        *self.url_to_fi
            .pin()
            .get_or_insert_with(uri.clone(), || ast::Fi(sungod::Ra::ggen::<usize>()))
    }

    #[instrument(skip(self, params))]
    async fn on_change(&self, params: TextDocumentItem<'_>) {
        if !self.has_started.try_read().map(|x| *x).unwrap_or(false) {
            self.client
                .log_message(MessageType::INFO, "Blocking since not started")
                .await;
            return;
        }

        let uri = params.uri.clone();
        let source = params.text;
        let version = params.version;

        tracing::info!("{:?} A {:?}", params.version, params.uri.to_string());

        let fi = self.find_fi(uri.clone());
        // TODO: How to handle two files with the same module name?
        self.fi_to_version.pin().compute(fi, |c| match c {
            Some(v) if v.1 > &version => Operation::Insert(version),
            Some(_) => Operation::Abort(()),
            None => Operation::Insert(version),
        });
        if self.got_refresh(fi, version) {
            return;
        }

        tracing::info!("!! {:?} B {:?}", params.version, params.uri.to_string());

        // I have to copy it! :(
        self.fi_to_source.pin().insert(fi, source.to_string());
        self.fi_to_url.pin().insert(fi, uri.clone());
        let (m, fi) = self.parse(fi, source);

        tracing::info!("!! {:?} C {:?}", params.version, params.uri.to_string());

        // TODO: We could exit earlier if we have the same syntactical structure here
        if let Some(m) = m {
            tracing::info!(
                "!! {:?} PRE RESOLVE {:?}",
                params.version,
                params.uri.to_string()
            );
            if let Some((exports_changed, me)) = self.resolve_module(&m, fi, params.version) {
                tracing::info!(
                    "!! {:?} POST RESOLVE {:?}",
                    params.version,
                    params.uri.to_string()
                );

                if self.got_refresh(fi, version) {
                    return;
                }

                if exports_changed {
                    tracing::info!("CASCADE CHANGE - START");
                    self.resolve_cascading(me, fi, params.version).await;
                    let _ = self.client.workspace_diagnostic_refresh().await;
                    tracing::info!("CASCADE CHANGE - END");
                }
            }
        }
        tracing::info!(
            "!! {:?} FINISHED! {:?}",
            params.version,
            params.uri.to_string()
        );
        self.show_errors(fi, params.version).await;
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

#[tokio::main(flavor = "multi_thread", worker_threads = 10)]
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
            .with_filter(FilterFn::new(|x| x.target() != "tower_lsp::codec"));

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

        fi_to_url: papaya::HashMap::new(),
        fi_to_ud: papaya::HashMap::new(),
        fi_to_source: papaya::HashMap::new(),
        ud_to_fi: papaya::HashMap::new(),
        url_to_fi: papaya::HashMap::new(),
        fi_to_version: papaya::HashMap::new(),

        importers: papaya::HashMap::new(),
        imports: papaya::HashMap::new(),

        available_locals: papaya::HashMap::new(),

        previouse_defines: papaya::HashMap::new(),
        previouse_global_usages: papaya::HashMap::new(),

        exports,
        modules: papaya::HashMap::new(),
        resolved: papaya::HashMap::new(),
        defines: papaya::HashMap::new(),
        references: papaya::HashMap::new(),

        syntax_errors: papaya::HashMap::new(),
        name_resolution_errors: papaya::HashMap::new(),
        fixables: papaya::HashMap::new(),
    })
    .finish();

    Server::new(stdin, stdout, socket).serve(service).await;
}

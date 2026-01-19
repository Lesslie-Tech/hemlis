#![allow(clippy::type_complexity)]
#![feature(btree_cursors)]

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs::File;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::ops::Bound;
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
    names: DashMap<ast::Ud, String>,

    fi_to_url: DashMap<ast::Fi, Url>,
    fi_to_ud: DashMap<ast::Fi, ast::Ud>,
    fi_to_source: DashMap<ast::Fi, String>,
    url_to_fi: DashMap<Url, ast::Fi>,
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

    syntax_errors: DashMap<ast::Fi, Vec<tower_lsp::lsp_types::Diagnostic>>,
    name_resolution_errors: DashMap<ast::Fi, Vec<tower_lsp::lsp_types::Diagnostic>>,
    fixables: DashMap<ast::Fi, Vec<(ast::Span, Fixable)>>,
}

impl Backend {
    fn resolve_name(&self, url: &Url, pos: Position) -> Option<Name> {
        let m = self
            .fi_to_ud
            .try_get(&*self.url_to_fi.try_get(url).try_unwrap()?)
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

    fn resolve_name_and_range(&self, url: &Url, pos: Position) -> Option<(Name, Range)> {
        let m = self
            .fi_to_ud
            .try_get(&*self.url_to_fi.try_get(url).try_unwrap()?)
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
                    x.split("\n")
                        .collect::<Vec<_>>()
                        .into_iter()
                        .rev()
                        .skip_while(|x| {
                            let xx = x.trim();
                            xx.starts_with("--") || xx.is_empty()
                        })
                        .collect::<Vec<_>>()
                        .into_iter()
                        .rev()
                        .for_each(|x| {
                            writeln!(target, "{}", x.trim_end()).unwrap();
                        });
                    writeln!(target, "```").unwrap();
                }
            } else {
                let the_thing = def_at.name.merge(def_at.sig.unwrap_or(def_at.name));
                if let Some(x) = try_find_lines(&source, the_thing.lo().0, the_thing.hi().0) {
                    writeln!(target, "```purescript").unwrap();
                    x.split("\n").for_each(|x| {
                        writeln!(target, "{}", x.trim_end()).unwrap();
                    });
                    writeln!(target, "```").unwrap();
                }
            }

            if let Some(x) =
                try_find_comments_before(&source, def_at.sig.unwrap_or(def_at.name).lo().0)
            {
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

            Some(())
        })();

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
            let folders = self
                .client
                .workspace_folders()
                .await
                .ok()
                .flatten()
                .unwrap_or_default();
            self.load_workspace(folders);
            tracing::info!("Done scanning");
            let mut futures = Vec::new();
            for i in self.fi_to_url.iter() {
                futures.push(self.show_errors(*i.key(), None));
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
                    .fi_to_url
                    .try_get(&def_at.name.fi()?)
                    .try_unwrap()?
                    .clone();
                Some(GotoDefinitionResponse::Scalar(Location {
                    uri,
                    range: span_to_range(&def_at.name),
                }))
            } else {
                let fi = *self
                    .url_to_fi
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
                    .try_get(&name.module())
                    .try_unwrap()?
                    .get(&name)?
                    .iter()
                    .filter_map(|(s, sort): &(ast::Span, nr::Sort)| {
                        if !sort.is_def_or_ref() {
                            return None;
                        }
                        let url = self.fi_to_url.try_get(&s.fi()?).try_unwrap()?;
                        let range = span_to_range(s);

                        Some(Location::new(url.clone(), range))
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
                        let url = self.fi_to_url.try_get(fi).unwrap().clone();
                        let range = span_to_range(&at.name);
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
        let fi_inner = if let Some(fi) = self
            .url_to_fi
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
                        let url = self.fi_to_url.try_get(&fi).unwrap().clone();
                        let range = span_to_range(&at);
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
            let fi = *self.url_to_fi.try_get(&uri).try_unwrap()?;
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
            let url = self
                .fi_to_url
                .try_get(&if let Some(fi) = at.fi() { fi } else { continue })
                .try_unwrap()
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
        let fi = *or_!(self.url_to_fi.try_get(&uri).try_unwrap(), {
            return Err(error(line!(), "File not loaded"));
        });
        let me = *or_!(self.fi_to_ud.try_get(&fi).try_unwrap(), {
            return Err(error(line!(), "File failed to load"));
        });

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
        let end_of_imports = head
            .2
            .last()
            .map(|x| x.start.lo())
            .unwrap_or_else(|| head.4.next_line().lo());

        let fixables = or_!(self.fixables.try_get(&fi).try_unwrap(), {
            return Err(error(line!(), "Module failed to load"));
        });

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
        if !delete_all.is_empty() {
            out.push(CodeAction {
                title: format!("BurnAllUnusedImport"),
                kind: Some(CodeActionKind::SOURCE_FIX_ALL),
                is_preferred: Some(false),
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
                    // Assume `n` is spelled correctly

                    // 1. Find all possible imports with `n`
                    // 1a. Figure out what edits need to be done
                    // TODO: Filter by first letter
                    // TODO: Search with some kind of hemming distance, like everything
                    // TODO: Drop the assumptions about `n` being spelt correctly
                    // TODO: Score each of these and limit the number of responses
                    // TODO: Remove unused imports
                    // TODO: Import ska funka på namespace för do-block
                    //
                    // TODO: Add `_` to unused variables
                    //
                    // TODO: Qualified imports to unqualified imports
                    // TODO: Handle unqualified imports
                    //
                    // TODO: Parse operators with operators table
                    // TODO: Report on unnessecary parens, and then fix them? :o
                    //
                    // Fun stuff:
                    // TODO: # <-> $
                    // TODO: <#> <-> <$>
                    // TODO: (...) <-> $
                    // TODO: >>> <-> \x -> x

                    let imported = or_!(self.imports.try_get(&me).try_unwrap(), { continue })
                        .value()
                        .clone();
                    let seen: BTreeSet<nr::Name> = imported
                        .values()
                        .flat_map(|x| x.iter().flat_map(|x| x.to_names()))
                        .collect();

                    let handle_quse = |ns: Option<ast::Ud>, name: &nr::Name, out: &mut Vec<_>| {
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

                    let imported_unqualified_names: BTreeSet<_> = imported
                        .iter()
                        .flat_map(|(m, xs)| match m {
                            Some(_) => [].into(),
                            None => xs
                                .iter()
                                .flat_map(|x| x.to_names())
                                .map(|x| x.module())
                                .collect::<BTreeSet<_>>(),
                        })
                        .collect();
                    for (m, xs) in imported.iter() {
                        if *s == Scope::Namespace {
                            let m = if let Some(m) = m { m } else { continue };
                            // NOTE: Maybe this heuristic can be better
                            // NOTE: This will give poor suggestions on most usages
                            let apply = ast::Ud::new("apply");
                            let bind = ast::Ud::new("bind");
                            let pure = ast::Ud::new("pure");
                            if xs.iter().any(|export| match export {
                                Export::ConstructorsSome(_, _) | Export::ConstructorsAll(_, _) => {
                                    false
                                }
                                Export::Just(name) => {
                                    name.name() == apply
                                        || name.name() == bind
                                        || name.name() == pure
                                }
                            }) {
                                let imported_as = self.name_(&m);
                                let invalid_name = self.name_(&n);
                                if similarity_score(
                                    &imported_as.to_lowercase(),
                                    &invalid_name.to_lowercase(),
                                ) < 0.4
                                {
                                    continue;
                                }
                                out.push(CodeAction {
                                    title: format!(
                                        "[QUSE {:?}] Qualified use {} ({})",
                                        *s, imported_as, invalid_name,
                                    ),
                                    kind: Some(CodeActionKind::QUICKFIX),
                                    is_preferred: Some(true),
                                    edit: Some(WorkspaceEdit::new(
                                        [(
                                            uri.clone(),
                                            vec![TextEdit::new(
                                                range(at.lo(), at.hi()),
                                                imported_as,
                                            )],
                                        )]
                                        .into(),
                                    )),
                                    ..CodeAction::default()
                                });
                            }
                        } else {
                            for export in xs.iter() {
                                match export {
                                    Export::ConstructorsSome(name, constructors)
                                    | Export::ConstructorsAll(name, constructors) => {
                                        if name.name() == *n && name.scope() == *s {
                                            handle_quse(*m, name, &mut out);
                                        }
                                        for c in constructors.iter() {
                                            if c.name() == *n
                                                && c.scope() == *s
                                                && c.scope() == nr::Scope::Term
                                            {
                                                handle_quse(*m, c, &mut out);
                                            }
                                        }
                                    }
                                    Export::Just(name) => {
                                        if name.name() == *n && name.scope() == *s {
                                            handle_quse(*m, name, &mut out);
                                        }
                                    }
                                }
                            }
                        }
                    }

                    let exports: BTreeMap<ast::Ud, Vec<nr::Export>> = self
                        .exports
                        .iter()
                        .map(|x| (*x.key(), x.value().clone()))
                        .collect();

                    let handle_qimport =
                        |name: &nr::Name, constructor: &Option<nr::Name>, out: &mut Vec<_>| {
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
                                    is_preferred: Some(ns_name == name_name),
                                    edit: Some(WorkspaceEdit::new(
                                        [(
                                            uri.clone(),
                                            vec![TextEdit::new(
                                                range(end_of_imports, end_of_imports),
                                                format!(
                                                    "import {} as {}\n",
                                                    self.name_(&name.module()),
                                                    self.name_(ns)
                                                ),
                                            )],
                                        )]
                                        .into(),
                                    )),
                                    ..CodeAction::default()
                                });
                                return;
                            }
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
                                                    "import {} as {}\n",
                                                    self.name_(&name.module()),
                                                    self.name_(&name.module())
                                                ),
                                            ),
                                            TextEdit::new(
                                                range(at.lo(), at.hi()),
                                                format!(
                                                    "{}.{}",
                                                    self.name_(&name.module()),
                                                    self.name_(
                                                        &constructor.unwrap_or(*name).name()
                                                    )
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
                            if imported_unqualified_names.contains(&name.module()) {
                                (|| -> Option<()> {
                                    // TODO: This won't work with re-exports
                                    let (l, c) =
                                        self.references
                                            .try_get(&name.module())
                                            .try_unwrap()?
                                            .get(&nr::Name(
                                                nr::Scope::Module,
                                                name.module(),
                                                name.module(),
                                                nr::Visibility::Public,
                                            ))?
                                            .iter()
                                            .find_map(|(s, _): &(ast::Span, nr::Sort)| {
                                                if s.fi() == Some(fi) {
                                                    Some(*s)
                                                } else {
                                                    None
                                                }
                                            })?
                                            .hi();
                                    let c = c + 2;
                                    out.push(CodeAction {
                                        title: format!(
                                            "[SUSE {:?}] Unqualified use {} ({})",
                                            name.scope(),
                                            format_name(None, name.name(), &self.names),
                                            self.name_(&name.module()),
                                        ),
                                        kind: Some(CodeActionKind::QUICKFIX),
                                        is_preferred: Some(true),
                                        edit: Some(WorkspaceEdit::new(
                                            [(
                                                uri.clone(),
                                                vec![TextEdit::new(
                                                    range((l, c), (l, c)),
                                                    format!(
                                                        "{}, ",
                                                        as_import(
                                                            name.scope(),
                                                            constructor.is_some(),
                                                            name.name(),
                                                            &self.names
                                                        )
                                                    ),
                                                )],
                                            )]
                                            .into(),
                                        )),
                                        ..CodeAction::default()
                                    });
                                    None
                                })();
                            } else {
                                out.push(CodeAction {
                                    title: format!(
                                        "[SIMPORT {:?}] import {} ({})",
                                        name.scope(),
                                        self.name_(&name.module()),
                                        self.name_(&name.name())
                                    ),
                                    kind: Some(CodeActionKind::QUICKFIX),
                                    edit: Some(WorkspaceEdit::new(
                                        [(
                                            uri.clone(),
                                            vec![TextEdit::new(
                                                range(end_of_imports, end_of_imports),
                                                format!(
                                                    "import {} ({})\n",
                                                    self.name_(&name.module()),
                                                    as_import(
                                                        name.scope(),
                                                        constructor.is_some(),
                                                        name.name(),
                                                        &self.names
                                                    )
                                                ),
                                            )],
                                        )]
                                        .into(),
                                    )),
                                    ..CodeAction::default()
                                });
                            }
                        };

                    for (m, xs) in exports.iter() {
                        if *m == me {
                            continue;
                        }
                        if *s == Scope::Namespace {
                            // NOTE: Maybe this heuristic can be better
                            // NOTE: This will give poor suggestions on most usages
                            let apply = ast::Ud::new("apply");
                            let bind = ast::Ud::new("bind");
                            let pure = ast::Ud::new("pure");
                            if xs.iter().any(|export| match export {
                                Export::ConstructorsSome(_, _) | Export::ConstructorsAll(_, _) => {
                                    false
                                }
                                Export::Just(name) => {
                                    name.name() == apply
                                        || name.name() == bind
                                        || name.name() == pure
                                }
                            }) {
                                let module_name = self.name_(&m);
                                let namespace_name = self.name_(&n);
                                if similarity_score(
                                    &module_name.to_lowercase(),
                                    &namespace_name.to_lowercase(),
                                ) < 0.4
                                {
                                    continue;
                                }
                                out.push(CodeAction {
                                    title: format!(
                                        "[QIMPORT {:?}] Qualified import {} as {}",
                                        Scope::Namespace,
                                        module_name,
                                        namespace_name
                                    ),
                                    kind: Some(CodeActionKind::QUICKFIX),
                                    is_preferred: Some(false),
                                    edit: Some(WorkspaceEdit::new(
                                        [(
                                            uri.clone(),
                                            vec![TextEdit::new(
                                                range(end_of_imports, end_of_imports),
                                                format!(
                                                    "import {} as {}\n",
                                                    module_name, namespace_name
                                                ),
                                            )],
                                        )]
                                        .into(),
                                    )),
                                    ..CodeAction::default()
                                });
                            }
                        } else {
                            for export in xs.iter() {
                                match export {
                                    Export::ConstructorsSome(name, constructors)
                                    | Export::ConstructorsAll(name, constructors) => {
                                        if name.name() == *n && name.scope() == *s {
                                            handle_qimport(name, &None, &mut out);
                                        }
                                        for c in constructors.iter() {
                                            if c.name() == *n
                                                && c.scope() == *s
                                                && c.scope() == nr::Scope::Term
                                            {
                                                handle_qimport(name, &Some(*c), &mut out);
                                            }
                                        }
                                    }
                                    Export::Just(name) => {
                                        if name.name() == *n
                                            && name.scope() == *s
                                            && !seen.contains(name)
                                        {
                                            handle_qimport(name, &None, &mut out);
                                        }
                                    }
                                }
                            }
                        }
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
                    is_preferred: Some(true),
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
        // Place the best matches at the top of the list
        out.sort_by_key(|x| (x.is_preferred, x.title.clone()));
        out.dedup_by_key(|x| x.title.clone());
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
                names
                    .try_get(&i)
                    .try_unwrap()
                    .map(|x| x.clone())
                    .unwrap_or_else(|| "?".into())
            ),
            Vec::new(),
        ),
        NRerrors::NotAConstructor(d, m) => create_error(
            m.0 .1,
            "NotAConstructor".into(),
            format!(
                "{} does not have a constructors {}",
                names
                    .try_get(&d.2)
                    .try_unwrap()
                    .map(|x| x.clone())
                    .unwrap_or_else(|| "?".into()),
                names
                    .try_get(&m.0 .0)
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
                    let uri = Url::parse(&format!(
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
                    self.fi_to_url.insert(fi, uri.clone());
                    self.fi_to_version.insert(fi, None);
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
                        tracing::error!("Dependency cycle detected: {}", left.len());
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
        let url = if let Some(url) = self.fi_to_url.try_get(&fi).try_unwrap() {
            url.value().clone()
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
        // tracing::info!("PRESENTING DIAGNOSTICS {:?}", url.to_string());
        self.client
            .publish_diagnostics(url.clone(), [se, re].concat(), v)
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
    fn find_fi(&self, uri: Url) -> Option<ast::Fi> {
        match self.url_to_fi.try_entry(uri.clone()) {
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
        self.fi_to_url.insert(fi, uri.clone());
        tracing::info!("!! {:?} B {:?}", version, uri.to_string());
        let (m, fi) = self.parse(fi, source);

        tracing::info!("!! {:?} PARSING DONE {:?}", version, uri.to_string());

        // TODO: We could exit earlier if we have the same syntactical structure here
        let to_notify = if let Some(m) = m {
            tracing::info!("!! {:?} PRE RESOLVE {:?}", version, uri.to_string());
            if let Some((exports_changed, me)) = self.resolve_module(&m, fi, version) {
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

        fi_to_url: DashMap::new(),
        fi_to_ud: DashMap::new(),
        fi_to_source: DashMap::new(),
        ud_to_fi: DashMap::new(),
        url_to_fi: DashMap::new(),
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
    })
    .finish();

    Server::new(stdin, stdout, socket).serve(service).await;
}

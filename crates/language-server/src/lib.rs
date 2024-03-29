use compiler::{Span, SpanMapEntry};
use dashmap::DashMap;
use itertools::Itertools;
use rustc_hash::FxHashMap;
use std::sync::Arc;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};
use typed_arena::Arena;

type HoverMap = Vec<Vec<Option<Arc<Hover>>>>;

#[derive(Debug, PartialEq, Eq)]
struct TokenCache {
    hover_map: HoverMap,
    state: TokenCacheState,
}

#[derive(Debug, PartialEq, Eq)]
enum TokenCacheState {
    Fresh,
    Unsaved,
}

#[derive(Debug)]
struct Backend {
    client: Client,
    tokens: DashMap<Url, TokenCache>,
    minimize_type: bool,
    polymorphism_threshold: usize,
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        self.client
            .log_message(MessageType::INFO, "initializing")
            .await;
        Ok(InitializeResult {
            server_info: None,
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::INCREMENTAL,
                )),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                ..ServerCapabilities::default()
            },
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "initialized")
            .await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_change_configuration(&self, _: DidChangeConfigurationParams) {
        self.client
            .log_message(MessageType::INFO, "configuration changed")
            .await;
    }

    async fn did_change_watched_files(&self, _: DidChangeWatchedFilesParams) {
        self.client
            .log_message(MessageType::INFO, "watched files changed")
            .await;
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        self.client
            .log_message(
                MessageType::INFO,
                &format!("opened {}.", params.text_document.uri),
            )
            .await;
        self.compile_uri(params.text_document.uri).await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        self.client
            .log_message(
                MessageType::INFO,
                &format!("changed {}", params.text_document.uri),
            )
            .await;
        if let Some(mut t) = self.tokens.get_mut(&params.text_document.uri) {
            t.state = TokenCacheState::Unsaved;
        }
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        self.client
            .log_message(MessageType::INFO, "file saved.")
            .await;
        let uri = params.text_document.uri;
        if let Some(r) = self.tokens.get_mut(&uri) {
            self.client
                .log_message(MessageType::INFO, "document found")
                .await;
            let is_fresh = r.value().state == TokenCacheState::Fresh;
            if is_fresh {
                self.client
                    .log_message(MessageType::INFO, "already cached.")
                    .await;
                return;
            }
        } else {
            self.client
                .log_message(MessageType::INFO, "not cached yet.")
                .await;
        }
        self.compile_uri(uri).await;
    }

    async fn did_close(&self, _: DidCloseTextDocumentParams) {
        self.client
            .log_message(MessageType::INFO, "file closed.")
            .await;
    }

    async fn hover(&self, params: HoverParams) -> tower_lsp::jsonrpc::Result<Option<Hover>> {
        let position = params.text_document_position_params.position;
        let url = params.text_document_position_params.text_document.uri;
        if let Some(hover_map) = self.tokens.get(&url) {
            Ok(hover_map
                .value()
                .hover_map
                .get(position.line as usize)
                .and_then(|t| {
                    let rc = t.get(position.character as usize)?.as_ref()?;
                    Some((**rc).clone())
                }))
        } else {
            Ok(None)
        }
    }
}

impl Backend {
    async fn compile_uri(&self, uri: Url) {
        self.client
            .log_message(MessageType::INFO, "compiling.")
            .await;
        let minimize_type = self.minimize_type;
        let polymorphism_threshold = self.polymorphism_threshold;
        let uri_s = uri.path().to_string();
        if let Ok(Some(hover_map)) = tokio::task::spawn_blocking(move || {
            let arena = Arena::new();
            let m = make_hover_map(
                arena.alloc(uri_s),
                &mut FxHashMap::default(),
                minimize_type,
                &arena,
                polymorphism_threshold,
            );
            drop(arena);
            m
        })
        .await
        {
            self.tokens.insert(
                uri,
                TokenCache {
                    hover_map,
                    state: TokenCacheState::Fresh,
                },
            );
            self.client
                .log_message(MessageType::INFO, "successfully compiled.")
                .await;
        } else {
            self.client
                .log_message(MessageType::INFO, "could not compile.")
                .await;
        }
    }
}

#[tokio::main]
pub async fn run(minimize_type: bool, polymorphism_threshold: usize) {
    let (stdin, stdout) = (tokio::io::stdin(), tokio::io::stdout());
    let (service, socket) = LspService::new(|client| Backend {
        client,
        tokens: Default::default(),
        minimize_type,
        polymorphism_threshold,
    });
    Server::new(stdin, stdout, socket).serve(service).await;
}

fn make_hover_map<'a>(
    file_name: &'a str,
    src_files: &mut FxHashMap<&'a str, &'a str>,
    minimize_type: bool,
    arena: &'a Arena<String>,
    polymorphism_threshold: usize,
) -> Option<HoverMap> {
    let r = compiler::token_map(
        file_name,
        src_files,
        minimize_type,
        arena,
        polymorphism_threshold,
    )
    .ok()?;
    let (utf8_to_utf16_map, utf16_to_utf8_map) = make_map(src_files[file_name]);
    let mut span_map = r.span_map;
    let mut working_span_list: Vec<(Span, _)> = Vec::new();
    let mut cache: Option<Arc<Hover>> = None;
    let utf16_to_token_map = utf16_to_utf8_map
        .into_iter()
        .map(|utf16_to_utf8_line| {
            utf16_to_utf8_line
                .into_iter()
                .map(|utf8| {
                    utf8.and_then(|utf8| -> Option<Arc<Hover>> {
                        let working_span_list_len = working_span_list.len();
                        working_span_list.retain(|(s, _)| s.contains(utf8));
                        if working_span_list.len() != working_span_list_len {
                            cache = None;
                        }
                        while let Some(e) = span_map.first_entry() {
                            if e.key().contains(utf8) {
                                working_span_list.push(e.remove_entry());
                                cache = None;
                            } else {
                                break;
                            }
                        }
                        if let Some(a) = &cache {
                            Some(a.clone())
                        } else if let Some((span, l)) = working_span_list
                            .iter()
                            .min_by_key(|(s, _)| s.end - s.start)
                        {
                            let value = match l {
                                SpanMapEntry::Expr(ts) => {
                                    if ts.is_empty() {
                                        "eliminated".to_string()
                                    } else {
                                        format!(
                                            "```\n{}\n```",
                                            ts.iter().enumerate().format_with("\n", |(i, t), f| {
                                                let d = compiler::DisplayTypeWithEnv(
                                                    t,
                                                    &r.constructor_names,
                                                );
                                                f(&format_args!("{}. {d}", i + 1))
                                            })
                                        )
                                    }
                                }
                                SpanMapEntry::GlobalVariable { ts } => {
                                    if ts.is_empty() {
                                        "eliminated".to_string()
                                    } else {
                                        format!(
                                            "```\n{}\n```",
                                            ts.iter().enumerate().format_with("\n", |(i, t), f| {
                                                let d = compiler::DisplayTypeWithEnv(
                                                    t,
                                                    &r.constructor_names,
                                                );
                                                f(&format_args!("{}. {d}", i + 1))
                                            })
                                        )
                                    }
                                }
                            };
                            let a = Arc::new(Hover {
                                contents: HoverContents::Markup(MarkupContent {
                                    value,
                                    kind: MarkupKind::Markdown,
                                }),
                                range: Some(Range {
                                    start: Position {
                                        line: utf8_to_utf16_map[span.start].0,
                                        character: utf8_to_utf16_map[span.start].1,
                                    },
                                    end: Position {
                                        line: utf8_to_utf16_map[span.end].0,
                                        character: utf8_to_utf16_map[span.end].1,
                                    },
                                }),
                            });
                            cache = Some(a.clone());
                            Some(a)
                        } else {
                            None
                        }
                    })
                })
                .collect()
        })
        .collect();
    Some(utf16_to_token_map)
}

type Utf16ToUtf8Map = Vec<Vec<Option<usize>>>;

fn make_map(src: &str) -> (Vec<(u32, u32)>, Utf16ToUtf8Map) {
    let mut utf8_to_utf16_map = Vec::with_capacity(src.len());
    let mut utf16_to_utf8_map = Vec::new();
    let mut utf16_to_utf8_line = Vec::new();
    utf8_to_utf16_map.push((0, 0));
    let mut line = 0;
    let mut col_utf16 = 0;
    let mut utf8_i = 0;
    for c in src.chars() {
        if c == '\n' {
            utf16_to_utf8_map.push(utf16_to_utf8_line);
            utf16_to_utf8_line = Vec::new();
            line += 1;
            col_utf16 = 0;
        } else {
            utf16_to_utf8_line.resize(col_utf16 as usize, None);
            col_utf16 += c.len_utf16() as u32;
        }
        utf16_to_utf8_line.push(Some(utf8_i));
        for _ in 0..c.len_utf8() {
            utf8_to_utf16_map.push((line, col_utf16));
        }
        utf8_i += c.len_utf8();
    }
    utf16_to_utf8_map.push(utf16_to_utf8_line);
    (utf8_to_utf16_map, utf16_to_utf8_map)
}

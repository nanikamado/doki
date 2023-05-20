use compiler::Span;
use dashmap::DashMap;
use std::fs;
use std::sync::Arc;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

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
        self.compile_uri(params.text_document.uri, Some(params.text_document.text))
            .await;
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
        self.compile_uri(uri, params.text).await;
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
    async fn compile_uri(&self, uri: Url, text: Option<String>) {
        self.client
            .log_message(MessageType::INFO, "compiling.")
            .await;
        if let Some(src) = text.or_else(|| fs::read_to_string(uri.path()).ok()) {
            if let Ok(Some(hover_map)) =
                tokio::task::spawn_blocking(move || make_hover_map(&src)).await
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
                    .log_message(MessageType::INFO, format!("could not compile {uri}."))
                    .await;
            }
        } else {
            self.client
                .log_message(MessageType::INFO, format!("{uri} not found."))
                .await;
        }
    }
}

#[tokio::main]
pub async fn run() {
    let (stdin, stdout) = (tokio::io::stdin(), tokio::io::stdout());
    let (service, socket) = LspService::new(|client| Backend {
        client,
        tokens: Default::default(),
    });
    Server::new(stdin, stdout, socket).serve(service).await;
}

fn make_hover_map(src: &str) -> Option<HoverMap> {
    let (char_to_utf16_map, utf16_to_char_map) = make_map(src);
    let mut span_map = compiler::token_map(src).ok()?;
    let mut working_span_list: Vec<(Span, _)> = Vec::new();
    let mut cache: Option<Arc<Hover>> = None;
    let utf16_to_token_map = utf16_to_char_map
        .into_iter()
        .map(|utf16_to_char_line| {
            utf16_to_char_line
                .into_iter()
                .map(|char| {
                    char.and_then(|char| {
                        let working_span_list_len = working_span_list.len();
                        working_span_list.retain(|(s, _)| s.contains(char));
                        if working_span_list.len() != working_span_list_len {
                            cache = None;
                        }
                        while let Some(e) = span_map.first_entry() {
                            if e.key().contains(char) {
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
                            let a = Arc::new(Hover {
                                contents: HoverContents::Markup(MarkupContent {
                                    value: format!("```\n{}\n```", l),
                                    kind: MarkupKind::Markdown,
                                }),
                                range: Some(Range {
                                    start: Position {
                                        line: char_to_utf16_map[span.start].0,
                                        character: char_to_utf16_map[span.start].1,
                                    },
                                    end: Position {
                                        line: char_to_utf16_map[span.end].0,
                                        character: char_to_utf16_map[span.end].1,
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

type Utf16ToCharMap = Vec<Vec<Option<usize>>>;

fn make_map(src: &str) -> (Vec<(u32, u32)>, Utf16ToCharMap) {
    let mut char_to_utf16_map = Vec::with_capacity(src.len());
    let mut utf16_to_char_map = Vec::new();
    let mut utf16_to_char_line = Vec::new();
    char_to_utf16_map.push((0, 0));
    let mut line = 0;
    let mut col_utf16 = 0;
    for (char_i, c) in src.chars().enumerate() {
        if c == '\n' {
            utf16_to_char_map.push(utf16_to_char_line);
            utf16_to_char_line = Vec::new();
            line += 1;
            col_utf16 = 0;
        } else {
            utf16_to_char_line.resize(col_utf16 as usize, None);
            col_utf16 += c.len_utf16() as u32;
        }
        utf16_to_char_line.push(Some(char_i));
        char_to_utf16_map.push((line, col_utf16));
    }
    utf16_to_char_map.push(utf16_to_char_line);
    (char_to_utf16_map, utf16_to_char_map)
}

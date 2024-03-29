use ariadne::{sources, Color, Label, Report, ReportKind};
use chumsky::prelude::*;
use chumsky::text::unicode::keyword;
use chumsky::text::{int, Char};
use std::io::Write;

#[derive(Clone, Debug)]
pub struct Ast<'a> {
    pub data_decls: Vec<DataDecl<'a>>,
    pub variable_decls: Vec<VariableDecl<'a>>,
    pub imports: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct DataDecl<'a> {
    pub name: &'a str,
    pub field_len: usize,
}

#[derive(Clone, Debug)]
pub struct VariableDecl<'a> {
    pub name: &'a str,
    pub ident_span: Span<'a>,
    pub expr: ExprWithSpan<'a>,
}

pub type ExprWithSpan<'a> = (Expr<'a>, Span<'a>);

#[derive(Clone, Debug)]
pub enum Expr<'a> {
    Ident(&'a str),
    Lambda {
        param: PatternWithSpan<'a>,
        expr: Box<ExprWithSpan<'a>>,
    },
    Call(Box<ExprWithSpan<'a>>, Box<ExprWithSpan<'a>>),
    I64(i64),
    F64(f64),
    U8(u8),
    Str(String),
    Match {
        operand: Box<ExprWithSpan<'a>>,
        branches: Vec<(PatternWithSpan<'a>, ExprWithSpan<'a>)>,
    },
    Let(
        PatternWithSpan<'a>,
        Box<ExprWithSpan<'a>>,
        Box<ExprWithSpan<'a>>,
    ),
}

pub type PatternWithSpan<'a> = (Pattern<'a>, Span<'a>);

#[derive(Clone, Debug)]
pub enum Pattern<'a> {
    Bind(&'a str),
    Wildcard,
    Constructor {
        name: &'a str,
        span: Span<'a>,
        fields: Vec<PatternWithSpan<'a>>,
    },
    Or(Box<PatternWithSpan<'a>>, Box<PatternWithSpan<'a>>),
    Num(&'a str),
}

enum Decl<'a> {
    Data(DataDecl<'a>),
    Variable(VariableDecl<'a>),
    Imports(String),
}

fn raw_string<'a>() -> impl Parser<'a, &'a str, &'a str, extra::Err<Rich<'a, char>>> + Copy {
    just('r').ignore_then(custom(move |inp| {
        match inp.parse(just('#').repeated().count().then_ignore(just('\"'))) {
            Ok(h) => {
                let start_offset = inp.offset();
                loop {
                    let marker = inp.save();
                    let end_offset = inp.offset();
                    if inp
                        .parse(just('\"').then(just('#').repeated().exactly(h)))
                        .is_ok()
                    {
                        break Ok(inp.slice(std::ops::Range {
                            start: start_offset,
                            end: end_offset,
                        }));
                    } else {
                        inp.rewind(marker);
                        if let Err(e) = inp.parse(any()) {
                            break Err(e);
                        }
                    }
                }
            }
            Err(e) => Err(e),
        }
    }))
}

fn parser(file_name: &str) -> impl Parser<'_, &str, Vec<Decl<'_>>, extra::Err<Rich<'_, char>>> {
    let comment = just("//")
        .then(any().and_is(just('\n').not()).repeated())
        .ignored();
    let whitespace = any()
        .filter(|c: &char| c.is_whitespace())
        .ignored()
        .or(comment)
        .repeated();
    let ident = any()
        .filter(|c: &char| c.is_ident_start() || *c == '_')
        .then(any().filter(|c: &char| c.is_ident_continue()).repeated())
        .to_slice()
        .filter(|s| !["match", "with", "end", "let", "in", "data", "import"].contains(s));
    let (string, char_) = {
        let escape = choice((
            just('\\'),
            just('n').to('\n'),
            just('r').to('\r'),
            just('t').to('\t'),
            just('0').to('\0'),
            just('"'),
            just('\''),
            just('x').ignore_then(text::digits(16).exactly(2).to_slice().validate(
                |digits, s: &mut chumsky::input::MapExtra<'_, '_, &str, _>, emitter| {
                    char::from_u32(u32::from_str_radix(digits, 16).unwrap()).unwrap_or_else(|| {
                        emitter.emit(Rich::custom(s.span(), "invalid unicode character"));
                        '\u{FFFD}'
                    })
                },
            )),
            text::digits(16)
                .at_most(6)
                .to_slice()
                .validate(
                    |digits, s: &mut chumsky::input::MapExtra<'_, '_, &str, _>, emitter| {
                        char::from_u32(u32::from_str_radix(digits, 16).unwrap()).unwrap_or_else(
                            || {
                                emitter.emit(Rich::custom(s.span(), "invalid unicode character"));
                                '\u{FFFD}'
                            },
                        )
                    },
                )
                .delimited_by(just("u{"), just("}")),
        ));
        let string = none_of(r#"\""#)
            .or(just('\\').ignore_then(escape))
            .repeated()
            .collect()
            .delimited_by(just('"'), just('"'));
        let char_ = none_of(r"\'")
            .or(just('\\').ignore_then(escape))
            .delimited_by(just('\''), just('\''))
            .map(|c| U8(c as u8));
        (string, char_)
    };
    let string = choice((string, raw_string().map(|s| s.to_string())));
    use Expr::*;
    let pattern = recursive(|pattern| {
        let p = choice((
            pattern.delimited_by(just('('), just(')')),
            just('-')
                .or_not()
                .then(text::int(10))
                .to_slice()
                .map(Pattern::Num)
                .map_with(|p, s| (p, Span::from(s.span(), file_name))),
            ident.map_with(|name, s| {
                (
                    if name == "_" {
                        Pattern::Wildcard
                    } else {
                        Pattern::Constructor {
                            name,
                            fields: Vec::new(),
                            span: Span::from(s.span(), file_name),
                        }
                    },
                    Span::from(s.span(), file_name),
                )
            }),
        ));
        let p = ident
            .then(whitespace.ignore_then(p.clone()).repeated().collect())
            .map_with(|(name, fields), e| {
                (
                    Pattern::Constructor {
                        name,
                        fields,
                        span: Span::from(e.span(), file_name),
                    },
                    Span::from(e.span(), file_name),
                )
            })
            .or(p);
        p.clone().foldl(
            just('|').padded_by(whitespace).ignore_then(p).repeated(),
            |a, b| {
                let span = Span {
                    file_name,
                    start: a.1.start,
                    end: b.1.end,
                };
                (Pattern::Or(Box::new(a), Box::new(b)), span)
            },
        )
    });
    let expr = recursive(|expr| {
        let branches = pattern
            .clone()
            .then_ignore(just("=>").padded_by(whitespace))
            .then(expr.clone())
            .separated_by(just(',').padded_by(whitespace))
            .collect::<Vec<_>>()
            .then_ignore(just(',').or_not())
            .padded_by(whitespace);
        let match_expr = expr
            .clone()
            .padded_by(whitespace)
            .delimited_by(keyword("match"), keyword("with"))
            .then(branches)
            .then_ignore(keyword("end"))
            .map(|(operand, branches)| Match {
                operand: Box::new(operand),
                branches,
            });
        let let_expr = keyword("let")
            .ignore_then(pattern.clone().padded_by(whitespace))
            .then_ignore(just("=").padded_by(whitespace))
            .then(expr.clone())
            .then_ignore(keyword("in").padded_by(whitespace))
            .then(expr.clone())
            .map(|((v, e1), e2)| Let(v, Box::new(e1), Box::new(e2)));
        let paren = expr
            .padded_by(whitespace)
            .delimited_by(just('('), just(')'))
            .map(|(e, _)| e);
        let u8_decimal = int(10)
            .then_ignore(just("u8"))
            .map(|s| U8(str::parse(s).unwrap()));
        let decimal = just('-')
            .or_not()
            .then(text::int(10))
            .to_slice()
            .map(|a| I64(str::parse(a).unwrap()));
        let f64_lit = just('-')
            .or_not()
            .then(text::int(10))
            .then(just('.'))
            .then(text::digits(10))
            .then(
                just('E')
                    .or(just('e'))
                    .then(just('+').or(just('-')))
                    .then(text::digits(10))
                    .or_not(),
            )
            .to_slice()
            .map(|a| F64(str::parse(a).unwrap()));
        let u8_binary = text::digits(2)
            .to_slice()
            .delimited_by(just("0b"), just("u8"))
            .map(|a| U8(u8::from_str_radix(a, 2).unwrap()));
        let binary = just("0b")
            .ignore_then(text::digits(2).to_slice())
            .map(|a| I64(i64::from_str_radix(a, 2).unwrap()));
        let u8_hex = text::digits(16)
            .to_slice()
            .delimited_by(just("0x"), just("u8"))
            .map(|a| U8(u8::from_str_radix(a, 16).unwrap()));
        let hex = just("0x")
            .ignore_then(text::digits(16).to_slice())
            .map(|a| I64(i64::from_str_radix(a, 16).expect(a)));
        let e = choice((
            paren,
            match_expr,
            let_expr,
            f64_lit,
            u8_decimal,
            u8_binary,
            binary,
            u8_hex,
            hex,
            char_,
            decimal,
            string.map(Str),
            ident
                .then_ignore(
                    whitespace
                        .then_ignore(none_of("=").ignored().or(end()))
                        .rewind(),
                )
                .map(Ident),
        ))
        .map_with(|e, s| (e, Span::from(s.span(), file_name)));
        let e = e
            .clone()
            .foldl(whitespace.ignore_then(e).repeated(), |a, b| {
                let span = Span {
                    file_name,
                    start: a.1.start,
                    end: b.1.end,
                };
                (Call(Box::new(a), Box::new(b)), span)
            });
        pattern
            .map_with(|p, s| (p, s.span()))
            .then_ignore(just(":").padded_by(whitespace))
            .repeated()
            .foldr(e, |(param, span), acc| {
                let span = Span {
                    file_name,
                    start: span.start,
                    end: acc.1.end,
                };
                (
                    Lambda {
                        param,
                        expr: Box::new(acc),
                    },
                    span,
                )
            })
    });
    let variable_decl = ident
        .map_with(|i, s| (i, s.span()))
        .then_ignore(just("=").padded_by(whitespace))
        .then(expr)
        .padded_by(whitespace)
        .map(|((i, span), e)| {
            Decl::Variable(VariableDecl {
                name: i,
                ident_span: Span::from(span, file_name),
                expr: e,
            })
        });
    let data_decl = keyword("data")
        .ignore_then(ident.padded_by(whitespace))
        .then(int(10))
        .padded_by(whitespace)
        .map(|(name, len): (&str, &str)| {
            Decl::Data(DataDecl {
                name,
                field_len: len.parse().unwrap(),
            })
        });
    let import = keyword("import")
        .ignore_then(string.padded_by(whitespace))
        .padded_by(whitespace)
        .map(Decl::Imports);
    choice((variable_decl, data_decl, import))
        .repeated()
        .at_least(1)
        .collect()
}

pub fn parse<'a>(src: &'a str, file_name: &'a str) -> Result<Ast<'a>, ParseError<'a>> {
    let mut data_decls = Vec::new();
    let mut variable_decls = Vec::new();
    let mut imports = Vec::new();
    match parser(file_name).parse(src).into_result() {
        Ok(ds) => {
            for d in ds {
                match d {
                    Decl::Data(d) => data_decls.push(d),
                    Decl::Variable(d) => variable_decls.push(d),
                    Decl::Imports(d) => imports.push(d),
                }
            }
            Ok(Ast {
                data_decls,
                variable_decls,
                imports,
            })
        }
        Err(es) => Err(ParseError { es }),
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Span<'a> {
    pub file_name: &'a str,
    pub start: usize,
    pub end: usize,
}

impl<'a> Span<'a> {
    fn from(span: SimpleSpan, file_name: &'a str) -> Self {
        Self {
            file_name,
            start: span.start,
            end: span.end,
        }
    }

    pub fn contains(self, i: usize) -> bool {
        self.start <= i && i < self.end
    }
}

pub struct ParseError<'a> {
    es: Vec<Rich<'a, char>>,
}

impl<'a> ParseError<'a> {
    pub fn write(&self, mut w: impl Write, file_name: &str, src: &str) -> std::io::Result<()> {
        for e in &self.es {
            Report::build(ReportKind::Error, file_name, e.span().start)
                .with_message(e.to_string())
                .with_label(
                    Label::new((file_name.to_string(), e.span().into_range()))
                        .with_message(e.reason().to_string())
                        .with_color(Color::Red),
                )
                .finish()
                .write(sources([(file_name.to_string(), src)]), &mut w)?
        }
        Ok(())
    }
}

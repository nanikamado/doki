use ariadne::{sources, Color, Label, Report, ReportKind};
use chumsky::prelude::*;
use chumsky::text::{ident, int, keyword};
use std::process::exit;

#[derive(Clone, Debug)]
pub struct Ast<'a> {
    pub data_decls: Vec<DataDecl<'a>>,
    pub variable_decls: Vec<VariableDecl<'a>>,
}

#[derive(Clone, Debug)]
pub struct DataDecl<'a> {
    pub name: &'a str,
    pub field_len: usize,
}

#[derive(Clone, Debug)]
pub struct VariableDecl<'a> {
    pub name: &'a str,
    pub expr: Expr<'a>,
}

#[derive(Clone, Debug)]
pub enum Expr<'a> {
    Ident(&'a str),
    Lambda {
        param: Pattern<'a>,
        expr: Box<Expr<'a>>,
    },
    Call(Box<Expr<'a>>, Box<Expr<'a>>),
    Num(&'a str),
    Str(String),
    Match {
        operand: Box<Expr<'a>>,
        branches: Vec<(Pattern<'a>, Expr<'a>)>,
    },
    Let(Pattern<'a>, Box<Expr<'a>>, Box<Expr<'a>>),
}

#[derive(Clone, Debug)]
pub enum Pattern<'a> {
    Bind(&'a str),
    Wildcard,
    Constructor {
        name: &'a str,
        fields: Vec<Pattern<'a>>,
    },
    Or(Box<Pattern<'a>>, Box<Pattern<'a>>),
    Str(String),
    Num(&'a str),
}

enum Decl<'a> {
    Data(DataDecl<'a>),
    Variable(VariableDecl<'a>),
}

fn parser<'a>() -> impl Parser<'a, &'a str, Vec<Decl<'a>>, extra::Err<Rich<'a, char>>> {
    let comment = just("//")
        .then(any().and_is(just('\n').not()).repeated())
        .ignored();
    let whitespace = any()
        .filter(|c: &char| c.is_whitespace())
        .ignored()
        .or(comment)
        .repeated();
    let ident = ident()
        .filter(|s| !["match", "with", "end", "let", "in", "data"].contains(s))
        .padded_by(whitespace);

    // This `escape` is a modified version of https://github.com/zesterer/chumsky/blob/7e8d01f647640428871944885a1bb02e8a865895/examples/json.rs#L39
    // MIT License: https://github.com/zesterer/chumsky/blob/7e8d01f647640428871944885a1bb02e8a865895/LICENSE
    let escape = just('\\').ignore_then(choice((
        just('\\'),
        just('/'),
        just('"'),
        just('b').to('\x08'),
        just('f').to('\x0C'),
        just('n').to('\n'),
        just('r').to('\r'),
        just('t').to('\t'),
        just('u').ignore_then(text::digits(16).exactly(4).slice().validate(
            |digits, span, emitter| {
                char::from_u32(u32::from_str_radix(digits, 16).unwrap()).unwrap_or_else(|| {
                    emitter.emit(Rich::custom(span, "invalid unicode character"));
                    '\u{FFFD}' // unicode replacement character
                })
            },
        )),
    )));

    let string = none_of("\\\"")
        .or(escape)
        .repeated()
        .collect()
        .delimited_by(just('"'), just('"'));

    use Expr::*;
    let pattern = recursive(|pattern| {
        let p = choice((
            pattern.delimited_by(just('('), just(')')),
            just("_").to(Pattern::Wildcard),
            int(10).map(Pattern::Num),
            string.map(Pattern::Str),
            ident.map(|name| Pattern::Constructor {
                name,
                fields: Vec::new(),
            }),
        ))
        .padded_by(whitespace);
        let p = ident
            .then(p.clone().repeated().collect())
            .map(|(name, fields)| Pattern::Constructor { name, fields })
            .or(p);
        p.clone()
            .foldl(just('|').ignore_then(p).repeated(), |a, b| {
                Pattern::Or(Box::new(a), Box::new(b))
            })
    });
    let expr = recursive(|expr| {
        let branches = pattern
            .clone()
            .then_ignore(just("=>"))
            .then(expr.clone())
            .separated_by(just(','))
            .allow_trailing()
            .collect::<Vec<_>>()
            .padded_by(whitespace);
        let match_expr = expr
            .clone()
            .delimited_by(keyword("match"), keyword("with"))
            .then(branches)
            .then_ignore(keyword("end"))
            .map(|(operand, branches)| Match {
                operand: Box::new(operand),
                branches,
            });
        let let_expr = keyword("let")
            .ignore_then(pattern.clone())
            .then_ignore(just("="))
            .then(expr.clone())
            .then_ignore(keyword("in"))
            .then(expr.clone())
            .map(|((v, e1), e2)| Let(v, Box::new(e1), Box::new(e2)));
        let e = choice((
            expr.delimited_by(just('('), just(')')),
            match_expr,
            let_expr,
            int(10).map(Num),
            string.map(Str),
            ident
                .then_ignore(none_of("=").ignored().or(end().ignored()).rewind())
                .map(Ident),
        ))
        .padded_by(whitespace);
        let e = e
            .clone()
            .foldl(e.repeated(), |a, b| Call(Box::new(a), Box::new(b)));
        pattern
            .then_ignore(just(":"))
            .repeated()
            .foldr(e, |param, acc| Lambda {
                param,
                expr: Box::new(acc),
            })
    });
    let variable_decl = ident
        .then_ignore(just("="))
        .then(expr)
        .map(|(i, e)| Decl::Variable(VariableDecl { name: i, expr: e }));
    let data_decl = keyword("data")
        .then(whitespace)
        .ignore_then(ident)
        .then(int(10))
        .padded_by(whitespace)
        .map(|(name, len): (&str, &str)| {
            Decl::Data(DataDecl {
                name,
                field_len: len.parse().unwrap(),
            })
        });
    variable_decl.or(data_decl).repeated().at_least(1).collect()
}

pub fn parse<'a>(src: &'a str, file_name: &str) -> Ast<'a> {
    let mut data_decls = Vec::new();
    let mut variable_decls = Vec::new();
    match parser().parse(src).into_result() {
        Ok(ds) => {
            for d in ds {
                match d {
                    Decl::Data(d) => data_decls.push(d),
                    Decl::Variable(d) => variable_decls.push(d),
                }
            }
            Ast {
                data_decls,
                variable_decls,
            }
        }
        Err(es) => {
            es.into_iter().for_each(|e| {
                Report::build(ReportKind::Error, file_name, e.span().start)
                    .with_message(e.to_string())
                    .with_label(
                        Label::new((file_name.to_string(), e.span().into_range()))
                            .with_message(e.reason().to_string())
                            .with_color(Color::Red),
                    )
                    .finish()
                    .print(sources([(file_name.to_string(), src)]))
                    .unwrap()
            });
            exit(1)
        }
    }
}

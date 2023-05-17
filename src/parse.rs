use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::prelude::*;
use chumsky::text::{ident, int, whitespace};
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
    Lambda { param: &'a str, expr: Box<Expr<'a>> },
    Call(Box<Expr<'a>>, Box<Expr<'a>>),
    Num(&'a str),
    Str(String),
}

enum Decl<'a> {
    Data(DataDecl<'a>),
    Variable(VariableDecl<'a>),
}

fn parser<'a>() -> impl Parser<'a, &'a str, Vec<Decl<'a>>, extra::Err<Rich<'a, char>>> {
    let ident = ident().padded();

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
    let expr = recursive(|expr| {
        let lambda = ident.then_ignore(just(":")).then(expr.clone());
        let e = choice((
            lambda.map(|(param, e)| Lambda {
                param,
                expr: Box::new(e),
            }),
            int(10).map(Num),
            string.map(Str),
            ident.map(Ident),
        ))
        .padded();
        e.clone().foldl(
            expr.delimited_by(just('('), just(')')).repeated(),
            |a, b| Call(Box::new(a), Box::new(b)),
        )
    });
    let variable_decl = ident
        .then_ignore(just("="))
        .then(expr)
        .map(|(i, e)| Decl::Variable(VariableDecl { name: i, expr: e }));
    let data_decl = just("data")
        .then(whitespace().at_least(1))
        .ignore_then(ident)
        .then(int(10))
        .padded()
        .map(|(name, len): (&str, &str)| {
            Decl::Data(DataDecl {
                name,
                field_len: len.parse().unwrap(),
            })
        });
    variable_decl.or(data_decl).repeated().at_least(1).collect()
}

pub fn parse(src: &str) -> Ast {
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
                Report::build(ReportKind::Error, (), e.span().start)
                    .with_message(e.to_string())
                    .with_label(
                        Label::new(e.span().into_range())
                            .with_message(e.reason().to_string())
                            .with_color(Color::Red),
                    )
                    .finish()
                    .print(Source::from(&src))
                    .unwrap()
            });
            exit(1)
        }
    }
}

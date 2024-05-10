use chumsky::extra;
use chumsky::prelude::*;
use chumsky::util::MaybeRef;
use string_interner::{DefaultBackend, StringInterner};

use self::symbol::Symbol;

pub mod ast;
pub mod crc;
mod symbol;

pub type Span = SimpleSpan<usize>;

#[derive(Default)]
pub struct Context {
    interner: StringInterner<DefaultBackend>,
}

impl Context {
    pub fn get_symbol<T: AsRef<str>>(&self, string: T) -> Option<Symbol> {
        self.interner.get(string).map(Into::into)
    }

    pub fn resolve_symbol(&self, symbol: Symbol) -> Option<&str> {
        self.interner.resolve(symbol.into())
    }

    pub fn intern_symbol<T: AsRef<str>>(&mut self, string: T) -> Symbol {
        self.interner.get_or_intern(string).into()
    }
}

impl ast::Scheme {
    pub fn parse(ctx: &mut Context, input: &str) -> Result<Self, Vec<ParserError>> {
        scheme().parse_with_state(input, ctx).into_result()
    }
}

impl ast::Constructor {
    pub fn parse(ctx: &mut Context, input: &str) -> Result<Self, Vec<ParserError>> {
        constructor()
            .padded()
            .parse_with_state(input, ctx)
            .into_result()
    }
}

fn scheme<'a>() -> impl Parser<'a, &'a str, ast::Scheme, State> + Clone {
    let comment = comment().repeated();

    constructor()
        .padded_by(comment.clone())
        .recover_with(skip_then_retry_until(any().ignored(), text::newline()))
        .repeated()
        .collect()
        .padded()
        .padded_by(comment)
        .map(|items| ast::Scheme {
            declarations: items,
        })
}

fn constructor<'a>() -> impl Parser<'a, &'a str, ast::Constructor, State> + Clone {
    let term = term();

    let name_opt = choice((just('_').to(None), name(IdentType::Lowercase).map(Some))).then(choice(
        (just("$_").to(None), just("#_").to(None), tag().or_not()),
    ));
    let fields = field_list(term.clone());

    name_opt
        .padded()
        .then(fields)
        .then_ignore(just('='))
        .then(name(IdentType::Uppercase).padded())
        .then(term.padded().repeated().collect::<Vec<_>>())
        .then_ignore(just(';'))
        .map_with(
            |((((name, tag), fields), output_type), output_type_args), e| ast::Constructor {
                span: e.span(),
                name,
                tag,
                fields,
                output_type,
                output_type_args,
            },
        )
        .boxed()
}

fn tag<'a>() -> impl Parser<'a, &'a str, ast::ConstructorTag, State> + Clone {
    use chumsky::input::MapExtra;

    let binary = just('$')
        .ignore_then(one_of("01").repeated().at_least(1).to_slice())
        .try_map_with(|s, e: &mut MapExtra<_, State>| {
            let value = u32::from_str_radix(s, 2).map_err(|source| ParserError::InvalidInt {
                span: e.span(),
                source,
            })?;

            Ok(ast::ConstructorTag {
                span: e.span(),
                bits: (s.len() as u8).try_into().unwrap(),
                value,
            })
        });

    let hex = just('#')
        .ignore_then(
            any()
                .filter(|&c: &char| c.is_ascii_hexdigit())
                .repeated()
                .at_least(1)
                .to_slice(),
        )
        .try_map_with(|s, e: &mut MapExtra<_, State>| {
            let value = u32::from_str_radix(s, 16).map_err(|source| ParserError::InvalidInt {
                span: e.span(),
                source,
            })?;

            Ok(ast::ConstructorTag {
                span: e.span(),
                bits: (4 * s.len() as u8).try_into().unwrap(),
                value,
            })
        });

    choice((binary, hex)).boxed()
}

fn field_list<'a>(
    term: Recursive<dyn Parser<'a, &'a str, ast::TypeExpr, State> + 'a>,
) -> impl Parser<'a, &'a str, Vec<ast::Field>, State> + Clone {
    field(term)
        .padded()
        .padded_by(comment().repeated())
        .repeated()
        .collect()
        .boxed()
}

fn field<'a>(
    term: Recursive<dyn Parser<'a, &'a str, ast::TypeExpr, State> + 'a>,
) -> impl Parser<'a, &'a str, ast::Field, State> + Clone {
    let implicit_param = ident(IdentType::Any)
        .then_ignore(just(':').padded())
        .then(implicit_ty())
        .map_with(|(ident, ty), e| ast::Field::ImplicitParam {
            span: e.span(),
            ident,
            ty,
        });

    let constraint = expr(term.clone()).map_with(|expr, e| ast::Field::Constraint {
        span: e.span(),
        expr: Box::new(expr),
    });

    let param = name(IdentType::Any)
        .then_ignore(just(':').padded())
        .or_not()
        .then(expr_95(term.clone()))
        .map_with(|(ident, ty), e| ast::Field::Param {
            span: e.span(),
            name: ident,
            ty: Box::new(ty),
        });

    choice((
        choice((implicit_param, constraint))
            .padded()
            .delimited_by(just('{'), just('}')),
        param,
    ))
    .boxed()
}

fn term<'a>() -> Recursive<dyn Parser<'a, &'a str, ast::TypeExpr, State> + 'a> {
    recursive(move |term| {
        choice((
            expr(term.clone())
                .padded()
                .delimited_by(just('('), just(')')),
            field_list(term.clone())
                .padded()
                .delimited_by(just('['), just(']'))
                .map_with(|fields, e| ast::TypeExpr::AnonConstructor {
                    span: e.span(),
                    fields,
                }),
            just('#').map_with(|_, e| ast::TypeExpr::Nat { span: e.span() }),
            nat_const().map_with(|value, e| ast::TypeExpr::Const {
                span: e.span(),
                value,
            }),
            just('^')
                .ignore_then(term.clone())
                .map_with(|value, e| ast::TypeExpr::Ref {
                    span: e.span(),
                    value: Box::new(value),
                }),
            just('~')
                .ignore_then(term)
                .map_with(|value, e| ast::TypeExpr::Negate {
                    span: e.span(),
                    value: Box::new(value),
                }),
            ident(IdentType::Any).map_with(|ident, e| ast::TypeExpr::Apply {
                span: e.span(),
                ident,
                args: Vec::new(),
            }),
        ))
    })
}

fn expr<'a>(
    term: Recursive<dyn Parser<'a, &'a str, ast::TypeExpr, State> + 'a>,
) -> impl Parser<'a, &'a str, ast::TypeExpr, State> + Clone {
    let expr_20 = expr_20(term);
    let op = choice((just("<="), just(">="), one_of("=<>").to_slice()));

    expr_20
        .clone()
        .then(op.padded().then(expr_20.clone()).or_not())
        .map_with(|(mut left, right), e| match right {
            None => left,
            Some((op, mut right)) => {
                let op = match op {
                    "=" => ast::ConstraintOp::Eq,
                    "<" => ast::ConstraintOp::Lt,
                    "<=" => ast::ConstraintOp::Le,
                    ">" => {
                        std::mem::swap(&mut left, &mut right);
                        ast::ConstraintOp::Lt
                    }
                    ">=" => {
                        std::mem::swap(&mut left, &mut right);
                        ast::ConstraintOp::Le
                    }
                    _ => unreachable!(),
                };
                ast::TypeExpr::Constraint {
                    span: e.span(),
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                }
            }
        })
        .boxed()
}

fn expr_20<'a>(
    term: Recursive<dyn Parser<'a, &'a str, ast::TypeExpr, State> + 'a>,
) -> impl Parser<'a, &'a str, ast::TypeExpr, State> + Clone {
    let expr_30 = expr_30(term);

    expr_30
        .clone()
        .foldl_with(
            just('+').padded().ignore_then(expr_30).repeated(),
            |left, right, e| ast::TypeExpr::Add {
                span: e.span(),
                left: Box::new(left),
                right: Box::new(right),
            },
        )
        .boxed()
}

fn expr_30<'a>(
    term: Recursive<dyn Parser<'a, &'a str, ast::TypeExpr, State> + 'a>,
) -> impl Parser<'a, &'a str, ast::TypeExpr, State> + Clone {
    let expr_90 = expr_90(term);

    expr_90
        .clone()
        .foldl_with(
            just('*').padded().ignore_then(expr_90).repeated(),
            |left, right, e| ast::TypeExpr::Mul {
                span: e.span(),
                left: Box::new(left),
                right: Box::new(right),
            },
        )
        .boxed()
}

fn expr_90<'a>(
    term: Recursive<dyn Parser<'a, &'a str, ast::TypeExpr, State> + 'a>,
) -> impl Parser<'a, &'a str, ast::TypeExpr, State> + Clone {
    use chumsky::input::MapExtra;
    use chumsky::span::Span as _;

    let expr_95 = expr_95(term).padded();

    let alt_nat = choice((just("##"), just("#<="), just("#<")))
        .to_slice()
        .padded()
        .then(expr_95.clone())
        .map_with(|(kind, arg), e| ast::TypeExpr::AltNat {
            span: e.span(),
            kind: match kind {
                "##" => ast::AltNat::Width,
                "#<" => ast::AltNat::Less,
                "#<=" => ast::AltNat::Leq,
                _ => unreachable!(),
            },
            arg: Box::new(arg),
        });

    let res = expr_95
        .clone()
        .then(expr_95.repeated().collect::<Vec<_>>())
        .validate(|(mut res, mut new), e: &mut MapExtra<_, State>, emitter| {
            if new.is_empty() {
                return res;
            }

            let ast::TypeExpr::Apply { span, args, .. } = &mut res else {
                emitter.emit(ParserError::InvalidApply { span: e.span() });
                return res;
            };

            args.reserve(new.len());
            for arg in new.drain(..) {
                *span = span.union(arg.span());
                args.push(arg);
            }

            res
        });

    choice((alt_nat, res)).boxed()
}

fn expr_95<'a>(
    term: Recursive<dyn Parser<'a, &'a str, ast::TypeExpr, State> + 'a>,
) -> impl Parser<'a, &'a str, ast::TypeExpr, State> + Clone {
    expr_97(term.clone())
        .padded()
        .then(just('?').ignore_then(term.padded()).or_not())
        .map_with(|(left, right), e| match right {
            None => left,
            Some(right) => ast::TypeExpr::Cond {
                span: e.span(),
                cond: Box::new(left),
                value: Box::new(right),
            },
        })
        .boxed()
}

fn expr_97<'a>(
    term: Recursive<dyn Parser<'a, &'a str, ast::TypeExpr, State> + 'a>,
) -> impl Parser<'a, &'a str, ast::TypeExpr, State> + Clone {
    let term = term.padded();

    term.clone()
        .then(just('.').ignore_then(term).or_not())
        .map_with(|(left, right), e| match right {
            None => left,
            Some(right) => ast::TypeExpr::GetBit {
                span: e.span(),
                value: Box::new(left),
                bit: Box::new(right),
            },
        })
        .boxed()
}

fn nat_const<'a>() -> impl Parser<'a, &'a str, u32, State> + Clone {
    any()
        .filter(|&c: &char| c.is_ascii_digit())
        .repeated()
        .at_least(1)
        .to_slice()
        .validate(|s: &str, e, emitter| match s.parse::<u32>() {
            Ok(value) => value,
            Err(source) => {
                emitter.emit(ParserError::InvalidInt {
                    span: e.span(),
                    source,
                });
                0
            }
        })
}

fn implicit_ty<'a>() -> impl Parser<'a, &'a str, ast::GenericType, State> + Clone {
    use chumsky::input::MapExtra;

    any()
        .filter(|&c: &char| c.is_ascii_alphanumeric() || matches!(c, '#' | '_'))
        .repeated()
        .at_least(1)
        .to_slice()
        .validate(
            move |ident: &str, e: &mut MapExtra<_, State>, emitter| match ident {
                "Type" => ast::GenericType::Type,
                "#" => ast::GenericType::Nat,
                _ => {
                    emitter.emit(ParserError::InvalidImplicit { span: e.span() });
                    ast::GenericType::Type
                }
            },
        )
}

fn name<'a>(ty: IdentType) -> impl Parser<'a, &'a str, ast::Name, State> + Clone {
    ident(ty)
        .map_with(|ident, e| ast::Name {
            span: e.span(),
            ident,
        })
        .boxed()
}

fn ident<'a>(ty: IdentType) -> impl Parser<'a, &'a str, Symbol, State> + Clone {
    use chumsky::input::MapExtra;

    any()
        .filter(|&c: &char| matches!(c, 'a'..='z' | 'A'..='Z' | '0'..='9' | '_' | '!'))
        .repeated()
        .at_least(1)
        .to_slice()
        .validate(move |ident: &str, e: &mut MapExtra<_, State>, emitter| {
            let ident = 'ident: {
                if !ident.chars().all(|c| c.is_ascii_digit()) {
                    let first = ident.chars().next().expect("non-empty string");
                    match ty {
                        IdentType::Lowercase
                            if !first.is_ascii_lowercase() && first != '!' && ident != "_" =>
                        {
                            emitter.emit(ParserError::LowercastIdentExpected { span: e.span() })
                        }
                        IdentType::Uppercase if !first.is_ascii_uppercase() => {
                            emitter.emit(ParserError::UppercaseIdentExpected { span: e.span() })
                        }
                        _ => break 'ident ident,
                    }
                } else {
                    emitter.emit(ParserError::IdentExpected { span: e.span() });
                }
                INVALID_IDENT
            };
            e.state().intern_symbol(ident)
        })
}

fn comment<'a>() -> impl Parser<'a, &'a str, (), State> + Clone {
    let single_line_comment = just("//")
        .then(any().and_is(just('\n').not()).repeated())
        .padded()
        .ignored();

    let multi_line_comment = recursive(|comment| {
        choice((
            comment,
            none_of('*').ignored(),
            just('*').then_ignore(none_of('/').rewind()).ignored(),
        ))
        .repeated()
        .ignored()
        .delimited_by(just("/*"), just("*/"))
        .padded()
    });

    choice((single_line_comment, multi_line_comment))
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
enum IdentType {
    #[default]
    Any,
    Lowercase,
    Uppercase,
}

type State = extra::Full<ParserError, Context, ()>;

#[derive(thiserror::Error, Debug)]
pub enum ParserError {
    #[error("unexpected character found: {found:?}")]
    UnexpectedChar { span: Span, found: Option<char> },
    #[error("identifier expected")]
    IdentExpected { span: Span },
    #[error("lowercase identifier expected")]
    LowercastIdentExpected { span: Span },
    #[error("uppercase identifier expected")]
    UppercaseIdentExpected { span: Span },
    #[error("invalid integer: {source}")]
    InvalidInt {
        span: Span,
        #[source]
        source: std::num::ParseIntError,
    },
    #[error("either `Type` or `#` implicit parameter expected")]
    InvalidImplicit { span: Span },
    #[error("cannot apply one expression to another")]
    InvalidApply { span: Span },
    #[error("unknown error")]
    Unknown,
}

impl<'a> chumsky::error::Error<'a, &'a str> for ParserError {
    fn expected_found<Iter: IntoIterator<Item = Option<MaybeRef<'a, char>>>>(
        _: Iter,
        found: Option<MaybeRef<'a, char>>,
        span: Span,
    ) -> Self {
        Self::UnexpectedChar {
            span,
            found: found.as_deref().copied(),
        }
    }

    fn merge(self, _: Self) -> Self {
        self
    }
}

const INVALID_IDENT: &str = "#INVALID#";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hashmap_scheme() {
        let mut ctx = Context::default();
        let input = include_str!("./test/hashmap.tlb");
        let result = ast::Scheme::parse(&mut ctx, input);
        println!("{:#?}", result.unwrap());
    }

    #[test]
    fn full_scheme() {
        let mut ctx = Context::default();
        let input = include_str!("./test/block.tlb");
        let result = ast::Scheme::parse(&mut ctx, input);
        println!("{:#?}", result.unwrap());
    }
}

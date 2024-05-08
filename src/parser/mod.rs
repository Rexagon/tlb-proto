use chumsky::extra;
use chumsky::prelude::*;
use chumsky::util::MaybeRef;
use string_interner::{DefaultBackend, StringInterner};

use self::symbol::Symbol;

pub mod ast;
// mod crc;
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
        constructor().parse_with_state(input, ctx).into_result()
    }
}

fn scheme<'a>() -> impl Parser<'a, &'a str, ast::Scheme, State> + Clone {
    constructor()
        .recover_with(skip_then_retry_until(any().ignored(), text::newline()))
        .padded()
        .repeated()
        .collect()
        .map(|items| ast::Scheme {
            declarations: items,
        })
}

fn constructor<'a>() -> impl Parser<'a, &'a str, ast::Constructor, State> + Clone {
    let term = term();

    let name_opt =
        choice((just('_').to(None), name(IdentType::Lowercase).map(Some))).then(tag().or_not());
    let fields = field_list(term.clone());

    name_opt
        .padded()
        .then(fields)
        .then_ignore(just('=').padded())
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
    none_of("=]")
        .ignore_then(field(term).padded())
        .repeated()
        .collect()
}

fn field<'a>(
    term: Recursive<dyn Parser<'a, &'a str, ast::TypeExpr, State> + 'a>,
) -> impl Parser<'a, &'a str, ast::Field, State> + Clone {
    let implicit_param = ident(IdentType::Any)
        .then_ignore(just(':'))
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

    let param = name(IdentType::Lowercase)
        .then_ignore(just(':'))
        .or_not()
        .then(expr_95(term.clone()))
        .map_with(|(ident, ty), e| ast::Field::Param {
            span: e.span(),
            ident,
            ty: Box::new(ty),
        });

    choice((
        choice((implicit_param, constraint)).delimited_by(just('{'), just('}')),
        param,
    ))
    .boxed()
}

fn term<'a>() -> Recursive<dyn Parser<'a, &'a str, ast::TypeExpr, State> + 'a> {
    recursive(move |term| {
        choice((
            expr(term.clone())
                .padded()
                .delimited_by(just('('), just(')'))
                .map_with(|res, e| res),
            nat_const().map_with(|value, e| ast::TypeExpr::Const {
                span: e.span(),
                value,
            }),
            just('^')
                .ignore_then(term)
                .map(|value| ast::TypeExpr::Ref(Box::new(value))),
            just('~')
                .ignore_then(ident(IdentType::Lowercase))
                .map_with(|ident, e| ast::TypeExpr::Negate {
                    span: e.span(),
                    ident,
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

    let alt_nat = choice((just("##"), just("#<"), just("#<=")))
        .to_slice()
        .padded()
        .then(nat_const())
        .map_with(|(kind, arg), e| ast::TypeExpr::AltNat {
            span: e.span(),
            kind: match kind {
                "##" => ast::AltNat::Width,
                "#<" => ast::AltNat::Less,
                "#<=" => ast::AltNat::Leq,
                _ => unreachable!(),
            },
            arg,
        });

    let res = expr_95
        .clone()
        .then(expr_95.repeated().collect::<Vec<_>>())
        .try_map_with(|(mut res, mut new), e: &mut MapExtra<_, State>| {
            let ast::TypeExpr::Apply { span, args, .. } = &mut res else {
                return Err(ParserError::InvalidApply { span: e.span() });
            };

            args.reserve(new.len());
            for arg in new.drain(..) {
                *span = span.union(arg.span());
                args.push(arg);
            }

            Ok(res)
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
    text::int(10).try_map(|s, span| {
        u32::from_str_radix(s, 10).map_err(move |source| ParserError::InvalidInt { span, source })
    })
}

fn implicit_ty<'a>() -> impl Parser<'a, &'a str, ast::GenericType, State> + Clone {
    use chumsky::input::MapExtra;

    any()
        .filter(|&c: &char| c.is_ascii_alphanumeric() || c == '_')
        .repeated()
        .at_least(1)
        .to_slice()
        .try_map_with(move |ident: &str, e: &mut MapExtra<_, State>| match ident {
            "Type" => Ok(ast::GenericType::Type),
            "#" => Ok(ast::GenericType::Nat),
            _ => Err(ParserError::InvalidImplicit { span: e.span() }),
        })
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
        .filter(|&c: &char| c.is_ascii_alphanumeric() || c == '_')
        .repeated()
        .at_least(1)
        .to_slice()
        .try_map_with(move |ident: &str, e: &mut MapExtra<_, State>| {
            if ident.chars().all(|c| c.is_ascii_digit()) {
                return Err(ParserError::IdentExpected { span: e.span() });
            }

            let first = ident.chars().next().expect("non-empty string");
            match ty {
                IdentType::Lowercase if !first.is_ascii_lowercase() => {
                    Err(ParserError::LowercastIdentExpected { span: e.span() })
                }
                IdentType::Uppercase if !first.is_ascii_uppercase() => {
                    Err(ParserError::UppercaseIdentExpected { span: e.span() })
                }
                _ => Ok(e.state().intern_symbol(ident)),
            }
        })
}

// fn comment<'a>() -> impl Parser<'a, &'a str, (), State> + Clone {
//     just("//")
//         .then(any().and_is(just('\n').not()).repeated())
//         .padded()
//         .ignored()
// }

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scheme() {
        let mut ctx = Context::default();
        let input = r####"
        addr_none$00 = MsgAddressExt;
        addr_extern$01 len:(## 9) external_address:(bits len)
                     = MsgAddressExt;
        anycast_info$_ depth:(#<= 30) { depth >= 1 }
           rewrite_pfx:(bits depth) = Anycast;
        addr_std$10 anycast:(Maybe Anycast)
           workchain_id:int8 address:bits256  = MsgAddressInt;
        addr_var$11 anycast:(Maybe Anycast) addr_len:(## 9)
           workchain_id:int32 address:(bits addr_len) = MsgAddressInt;
        _ _:MsgAddressInt = MsgAddress;
        _ _:MsgAddressExt = MsgAddress;
        "####;

        let result = ast::Scheme::parse(&mut ctx, input);
        println!("{result:#?}");
    }
}

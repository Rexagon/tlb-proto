use pest::iterators::{Pair, Pairs};
use pest::Parser;
use string_interner::StringInterner;

use self::ast::*;
use self::crc::compute_tag;
use self::grammar::{Grammar, Rule};
pub use self::symbol::Symbol;

pub mod ast;
mod crc;
mod grammar;
mod symbol;

#[derive(Default)]
pub struct Context {
    interner: StringInterner,
}

impl Context {
    pub fn resolve_symbol(&self, symbol: Symbol) -> Option<&str> {
        self.interner.resolve(symbol.into())
    }

    pub fn make_symbol(&mut self, pair: &Pair<'_, Rule>) -> Symbol {
        self.interner.get_or_intern(pair.as_str()).into()
    }
}

impl Scheme {
    pub fn parse(ctx: &mut Context, s: &str) -> Result<Self, ParserError> {
        let pairs = Grammar::parse(Rule::tlb_scheme, s)
            .map_err(|e| ParserError::InvalidInput(Box::new(e)))?;

        let mut declarations = Vec::new();
        for pair in pairs {
            if pair.as_rule() == Rule::constructor {
                declarations.push(parse_constructor(ctx, pair)?);
            }
        }

        Ok(Self { declarations })
    }
}

impl Constructor {
    pub fn parse(ctx: &mut Context, s: &str) -> Result<Self, ParserError> {
        let constructor = Grammar::parse(Rule::tlb_constructor, s)
            .map_err(|e| ParserError::InvalidInput(Box::new(e)))?
            .into_iter()
            .next()
            .unwrap();
        parse_constructor(ctx, constructor)
    }
}

fn parse_constructor(ctx: &mut Context, pair: Pair<'_, Rule>) -> Result<Constructor, ParserError> {
    let mut pairs = pair.into_inner();

    let (name, tag) = {
        let pair = pairs.next().unwrap();
        ensure_rule(&pair, Rule::constructor_name)?;
        parse_constructor_name(ctx, pair)?
    };

    let mut generics = Vec::new();
    read_same_rules(&mut pairs, Rule::generic, |pair| {
        generics.push(parse_type_arg(ctx, pair)?);
        Ok(())
    })?;

    let mut fields = Vec::new();
    read_same_rules(&mut pairs, Rule::field_group_item, |pair| {
        fields.push(parse_field_group_item(ctx, pair)?);
        Ok(())
    })?;

    let output_type = {
        let pair = pairs.next().unwrap();
        ensure_rule(&pair, Rule::output_type)?;
        parse_output_type(ctx, pair)?
    };

    let (tag, should_compute) = match tag {
        Some(tag) => (tag, false),
        None => (ConstructorTag::Empty, name.is_some()),
    };

    let mut result = Constructor {
        name,
        tag,
        generics,
        fields,
        output_type,
    };

    if should_compute {
        result.tag = compute_tag(ctx, &result);
    }

    Ok(result)
}

fn parse_constructor_name(
    ctx: &mut Context,
    pair: Pair<'_, Rule>,
) -> Result<(Option<Symbol>, Option<ConstructorTag>), ParserError> {
    let mut pairs = pair.into_inner().peekable();

    let mut name = None;
    if let Some(next) = pairs.peek() {
        if next.as_rule() == Rule::lc_ident {
            name = Some(ctx.make_symbol(next));
            pairs.next();
        }
    }

    let mut constructor_tag = None;
    if let Some(next) = pairs.next() {
        constructor_tag = Some(parse_constructor_tag(next)?);
    }

    Ok((name, constructor_tag))
}

fn parse_constructor_tag(pair: Pair<'_, Rule>) -> Result<ConstructorTag, ParserError> {
    let tag_raw = pair.as_str();
    let (radix, bits) = match pair.as_rule() {
        Rule::constructor_tag_empty => return Ok(ConstructorTag::Empty),
        Rule::constructor_tag_binary => (2, tag_raw.len() as u8),
        Rule::constructor_tag_hex => (16, (tag_raw.len() * 4) as u8),
        rule => return Err(ParserError::UnexpectedRule(rule)),
    };

    let value = u32::from_str_radix(tag_raw, radix).map_err(ParserError::InvalidConstructorTag)?;

    Ok(ConstructorTag::Explicit { value, bits })
}

fn parse_type_arg(ctx: &mut Context, pair: Pair<'_, Rule>) -> Result<Generic, ParserError> {
    let mut pairs = pair.into_inner();
    let ident = ctx.make_symbol(&pairs.next().unwrap());
    let ty = match pairs.next().unwrap().as_rule() {
        Rule::nat_type => GenericType::Nat,
        Rule::r#type => GenericType::Type,
        rule => return Err(ParserError::UnexpectedRule(rule)),
    };
    Ok(Generic { ident, ty })
}

fn parse_field_group_item(
    ctx: &mut Context,
    pair: Pair<'_, Rule>,
) -> Result<FieldGroupItem, ParserError> {
    let mut pairs = pair.into_inner().peekable();

    if let Some(next) = pairs.peek() {
        match next.as_rule() {
            Rule::field => {
                return Ok(FieldGroupItem::Field(parse_field(
                    ctx,
                    pairs.next().unwrap(),
                )?))
            }
            Rule::constraint_expr => {
                return Ok(FieldGroupItem::Constraint(parse_constraint_expr(
                    ctx,
                    pairs.next().unwrap(),
                )?))
            }
            _ => {}
        }
    }

    let mut fields = Vec::new();
    for pair in pairs {
        fields.push(parse_field_group_item(ctx, pair)?);
    }

    return Ok(FieldGroupItem::ChildCell(fields));
}

fn parse_field(ctx: &mut Context, pair: Pair<'_, Rule>) -> Result<Field, ParserError> {
    let mut pairs = pair.into_inner().peekable();

    let mut ident = None;
    if let Some(next) = pairs.peek() {
        if next.as_rule() == Rule::ident {
            ident = Some(ctx.make_symbol(next));
            pairs.next();
        }
    }

    let mut condition = None;
    if let Some(next) = pairs.peek() {
        if next.as_rule() == Rule::field_condition {
            if let Some(pair) = pairs.next() {
                let mut pairs = pair.into_inner();

                let ident = ctx.make_symbol(&pairs.next().unwrap());
                let bit = pairs.next().unwrap().as_str();

                condition = Some(FieldCondition {
                    ident,
                    bit: bit.parse().map_err(ParserError::InvalidNatConst)?,
                });
            }
        }
    }

    let ty = parse_type_expr(ctx, pairs.next().unwrap())?;

    Ok(Field {
        ident,
        condition,
        ty,
    })
}

fn parse_output_type(
    ctx: &mut Context,
    pair: Pair<'_, Rule>,
) -> Result<(Symbol, Vec<TypeExpr>), ParserError> {
    let mut pairs = pair.into_inner();

    let name = ctx.make_symbol(&pairs.next().unwrap());

    let mut types = Vec::new();
    for pair in pairs {
        types.push(parse_type_expr(ctx, pair)?);
    }

    Ok((name, types))
}

fn parse_type_expr(ctx: &mut Context, pair: Pair<'_, Rule>) -> Result<TypeExpr, ParserError> {
    let mut pairs = pair.into_inner();

    let pair = pairs.next().unwrap();
    Ok(match pair.as_rule() {
        Rule::nat_const => {
            let value = pair
                .as_str()
                .parse()
                .map_err(ParserError::InvalidNatConst)?;
            TypeExpr::Const(value)
        }
        Rule::nat_type => TypeExpr::Nat,
        Rule::nat_type_width => TypeExpr::AltNat(AltNat::Width(parse_nat_value(
            ctx,
            pair.into_inner().next().unwrap(),
        )?)),
        Rule::nat_type_leq => TypeExpr::AltNat(AltNat::Leq(parse_nat_value(
            ctx,
            pair.into_inner().next().unwrap(),
        )?)),
        Rule::nat_type_less => TypeExpr::AltNat(AltNat::Less(parse_nat_value(
            ctx,
            pair.into_inner().next().unwrap(),
        )?)),
        Rule::nat_expr => TypeExpr::NatExpr(parse_nat_expr(ctx, pair)?),
        Rule::ident => {
            let mut types = Vec::new();
            for pair in pairs {
                types.push(parse_type_expr(ctx, pair)?);
            }
            TypeExpr::Ident(ctx.make_symbol(&pair), types)
        }
        Rule::type_in_cell => {
            let inner = pair.into_inner().next().unwrap();
            TypeExpr::ChildCell(Box::new(parse_type_expr(ctx, inner)?))
        }
        rule => return Err(ParserError::UnexpectedRule(rule)),
    })
}

fn parse_nat_expr(ctx: &mut Context, pair: Pair<'_, Rule>) -> Result<NatExpr, ParserError> {
    let mut pairs = pair.into_inner();

    let left = parse_nat_value(ctx, pairs.next().unwrap())?;
    let op = match pairs.next().unwrap().as_str() {
        "+" => NatOperator::Add,
        "-" => NatOperator::Sub,
        "*" => NatOperator::Mul,
        _ => return Err(ParserError::UnknownOperator),
    };
    let right = parse_nat_value(ctx, pairs.next().unwrap())?;

    Ok(NatExpr { left, right, op })
}

fn parse_constraint_expr(
    ctx: &mut Context,
    pair: Pair<'_, Rule>,
) -> Result<ConstraintExpr, ParserError> {
    let mut pairs = pair.into_inner();

    let left = parse_nat_value(ctx, pairs.next().unwrap())?;
    let op = match pairs.next().unwrap().as_str() {
        "<" => ConstraintOperator::Lt,
        "<=" => ConstraintOperator::Le,
        "=" => ConstraintOperator::Eq,
        ">=" => ConstraintOperator::Ge,
        ">" => ConstraintOperator::Gt,
        _ => return Err(ParserError::UnknownOperator),
    };
    let right = parse_nat_value(ctx, pairs.next().unwrap())?;

    Ok(ConstraintExpr { left, right, op })
}

fn parse_nat_value(ctx: &mut Context, pair: Pair<'_, Rule>) -> Result<NatValue, ParserError> {
    match pair.as_rule() {
        Rule::ident => Ok(NatValue::Ident(ctx.make_symbol(&pair))),
        Rule::nat_const => pair
            .as_str()
            .parse()
            .map(NatValue::Const)
            .map_err(ParserError::InvalidNatConst),
        rule => Err(ParserError::UnexpectedRule(rule)),
    }
}

fn read_same_rules<'a, F>(
    pairs: &mut Pairs<'a, Rule>,
    rule: Rule,
    mut f: F,
) -> Result<(), ParserError>
where
    F: FnMut(Pair<'a, Rule>) -> Result<(), ParserError>,
{
    while pairs
        .peek()
        .map(|pair| pair.as_rule() == rule)
        .unwrap_or_default()
    {
        if let Some(pair) = pairs.next() {
            f(pair)?;
        }
    }
    Ok(())
}

fn ensure_rule(pair: &Pair<'_, Rule>, rule: Rule) -> Result<(), ParserError> {
    let pair_rule = pair.as_rule();
    if pair_rule == rule {
        Ok(())
    } else {
        Err(ParserError::UnexpectedRule(pair_rule))
    }
}

#[derive(Debug, Clone, thiserror::Error)]
pub enum ParserError {
    #[error("invalid input:\n{0}")]
    InvalidInput(Box<pest::error::Error<Rule>>),
    #[error("unexpected rule: {0:?}")]
    UnexpectedRule(Rule),
    #[error("invalid constructor tag")]
    InvalidConstructorTag(#[source] std::num::ParseIntError),
    #[error("invalid integer constant")]
    InvalidNatConst(#[source] std::num::ParseIntError),
    #[error("unknown operator")]
    UnknownOperator,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check_scheme(s: &str) {
        let s = Scheme::parse(&mut Default::default(), s).unwrap();
        println!("{s:#?}");
    }

    fn check_constructor(s: &str) {
        let c = Constructor::parse(&mut Default::default(), s).unwrap();
        println!("{c:#?}");
    }

    #[test]
    fn simple_scheme() {
        check_constructor("unit$_ = Unit");
        check_constructor("true$_ = True");
        check_constructor("bool_false$0 = Bool");
        check_constructor("bool_true$1 = Bool");
        check_constructor("bool_false$0 = BoolFalse");
        check_constructor("bool_true$1 = BoolTrue");
        check_constructor("nothing$0 {X:Type} = Maybe X");
        check_constructor("just$1 {X:Type} value:X = Maybe X");
        check_constructor("left$0 {X:Type} {Y:Type} value:X = Either X Y");
        check_constructor("right$1 {X:Type} {Y:Type} value:Y = Either X Y");
        check_constructor("pair$_ {X:Type} {Y:Type} first:X second:Y = Both X Y");

        check_constructor("bit$_ (## 1) = Bit");
    }

    #[test]
    fn scheme_with_constraints() {
        check_scheme(
            r####"
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
            "####,
        );
    }
}

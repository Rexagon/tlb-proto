use pest::iterators::{Pair, Pairs};
use pest::Parser;

use crate::grammar::*;
use crate::tokens::*;

impl<'a> Scheme<'a> {
    pub fn parse(s: &'a str) -> Result<Self, ParserError> {
        let pairs = Grammar::parse(Rule::tlb_scheme, s)
            .map_err(|e| ParserError::InvalidInput(Box::new(e)))?;

        let mut declarations = Vec::new();
        for pair in pairs {
            if pair.as_rule() == Rule::constructor {
                declarations.push(parse_constructor(pair)?);
            }
        }

        Ok(Self { declarations })
    }
}

impl<'a> Constructor<'a> {
    pub fn parse(s: &'a str) -> Result<Self, ParserError> {
        Grammar::parse(Rule::tlb_constructor, s)
            .map_err(|e| ParserError::InvalidInput(Box::new(e)))?
            .into_iter()
            .next()
            .ok_or(ParserError::UnexpectedEof)
            .and_then(parse_constructor)
    }
}

fn parse_constructor(pair: Pair<'_, Rule>) -> Result<Constructor<'_>, ParserError> {
    let mut pairs = pair.into_inner();

    let (name, id) = {
        let pair = pairs.next().unwrap();
        ensure_rule(&pair, Rule::constructor_name)?;
        parse_constructor_name(pair)?
    };

    let mut generics = Vec::new();
    read_same_rules(&mut pairs, Rule::generic, |pair| {
        generics.push(parse_type_arg(pair)?);
        Ok(())
    })?;

    let mut fields = Vec::new();
    read_same_rules(&mut pairs, Rule::field_group_item, |pair| {
        fields.push(parse_field_group_item(pair)?);
        Ok(())
    })?;

    let output_type = {
        let pair = pairs.next().unwrap();
        ensure_rule(&pair, Rule::output_type)?;
        parse_output_type(pair)?
    };

    Ok(Constructor {
        name,
        id,
        generics,
        fields,
        output_type,
    })
}

fn parse_constructor_name(
    pair: Pair<'_, Rule>,
) -> Result<(Option<&'_ str>, Option<ConstructorId>), ParserError> {
    let mut pairs = pair.into_inner().peekable();

    let mut name = None;
    if let Some(next) = pairs.peek() {
        if next.as_rule() == Rule::lc_ident {
            name = Some(next.as_str());
            pairs.next();
        }
    }

    let mut constructor_id = None;
    if let Some(next) = pairs.next() {
        constructor_id = Some(parse_constructor_id(next)?);
    }

    Ok((name, constructor_id))
}

fn parse_constructor_id(pair: Pair<'_, Rule>) -> Result<ConstructorId, ParserError> {
    let radix = match pair.as_rule() {
        Rule::constructor_id_empty => return Ok(ConstructorId::Empty),
        Rule::constructor_id_binary => ConstructorRadix::Binary,
        Rule::constructor_id_hex => ConstructorRadix::Binary,
        rule => return Err(ParserError::UnexpectedRule(rule)),
    };
    let id_raw = pair.as_str();

    let value =
        u32::from_str_radix(id_raw, radix.into()).map_err(ParserError::InvalidConstructorId)?;

    let bits = match radix {
        ConstructorRadix::Binary => id_raw.len(),
        ConstructorRadix::Hex => id_raw.len() * 4,
    } as u8;

    Ok(ConstructorId::Explicit { radix, value, bits })
}

fn parse_type_arg(pair: Pair<'_, Rule>) -> Result<Generic<'_>, ParserError> {
    let mut pairs = pair.into_inner();
    let ident = pairs.next().unwrap().as_str();
    let ty = match pairs.next().unwrap().as_rule() {
        Rule::nat_type => GenericType::Nat,
        Rule::r#type => GenericType::Type,
        rule => return Err(ParserError::UnexpectedRule(rule)),
    };
    Ok(Generic { ident, ty })
}

fn parse_field_group_item(pair: Pair<'_, Rule>) -> Result<FieldGroupItem<'_>, ParserError> {
    let mut pairs = pair.into_inner().peekable();

    if let Some(next) = pairs.peek() {
        match next.as_rule() {
            Rule::field => return Ok(FieldGroupItem::Field(parse_field(pairs.next().unwrap())?)),
            Rule::guard_expr => {
                return Ok(FieldGroupItem::Guard(parse_guard_expr(
                    pairs.next().unwrap(),
                )?))
            }
            _ => {}
        }
    }

    let mut fields = Vec::new();
    for pair in pairs {
        fields.push(parse_field_group_item(pair)?);
    }

    return Ok(FieldGroupItem::ChildCell(fields));
}

fn parse_field(pair: Pair<'_, Rule>) -> Result<Field<'_>, ParserError> {
    let mut pairs = pair.into_inner().peekable();

    let mut ident = None;
    if let Some(next) = pairs.peek() {
        if next.as_rule() == Rule::ident {
            ident = Some(next.as_str());
            pairs.next();
        }
    }

    let mut condition = None;
    if let Some(next) = pairs.peek() {
        if next.as_rule() == Rule::field_condition {
            if let Some(pair) = pairs.next() {
                let mut pairs = pair.into_inner();

                let ident = pairs.next().unwrap().as_str();
                let bit = pairs.next().unwrap().as_str();

                condition = Some(FieldCondition {
                    ident,
                    bit: bit.parse().map_err(ParserError::InvalidNatConst)?,
                });
            }
        }
    }

    let ty = parse_type_expr(pairs.next().unwrap())?;

    Ok(Field {
        ident,
        condition,
        ty,
    })
}

fn parse_output_type(pair: Pair<'_, Rule>) -> Result<(&'_ str, Vec<TypeExpr<'_>>), ParserError> {
    let mut pairs = pair.into_inner();

    let name = pairs.next().unwrap().as_str();

    let mut types = Vec::new();
    for pair in pairs {
        types.push(parse_type_expr(pair)?);
    }

    Ok((name, types))
}

fn parse_type_expr(pair: Pair<'_, Rule>) -> Result<TypeExpr<'_>, ParserError> {
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
            pair.into_inner().next().unwrap(),
        )?)),
        Rule::nat_type_leq => TypeExpr::AltNat(AltNat::Leq(parse_nat_value(
            pair.into_inner().next().unwrap(),
        )?)),
        Rule::nat_type_less => TypeExpr::AltNat(AltNat::Less(parse_nat_value(
            pair.into_inner().next().unwrap(),
        )?)),
        Rule::nat_expr => TypeExpr::NatExpr(parse_nat_expr(pair)?),
        Rule::ident => {
            let mut types = Vec::new();
            for pair in pairs {
                types.push(parse_type_expr(pair)?);
            }
            TypeExpr::Ident(pair.as_str(), types)
        }
        Rule::type_in_cell => {
            let inner = pair.into_inner().next().unwrap();
            TypeExpr::ChildCell(Box::new(parse_type_expr(inner)?))
        }
        rule => return Err(ParserError::UnexpectedRule(rule)),
    })
}

fn parse_nat_expr(pair: Pair<'_, Rule>) -> Result<NatExpr<'_>, ParserError> {
    let mut pairs = pair.into_inner();

    let left = parse_nat_value(pairs.next().unwrap())?;
    let op = match pairs.next().unwrap().as_str() {
        "+" => NatOperator::Add,
        "-" => NatOperator::Sub,
        "*" => NatOperator::Mul,
        "/" => NatOperator::Div,
        _ => return Err(ParserError::UnknownOperator),
    };
    let right = parse_nat_value(pairs.next().unwrap())?;

    Ok(NatExpr { left, right, op })
}

fn parse_guard_expr(pair: Pair<'_, Rule>) -> Result<GuardExpr<'_>, ParserError> {
    let mut pairs = pair.into_inner();

    let left = parse_nat_value(pairs.next().unwrap())?;
    let op = match pairs.next().unwrap().as_str() {
        "<" => GuardOperator::Lt,
        "<=" => GuardOperator::Le,
        "=" => GuardOperator::Eq,
        ">=" => GuardOperator::Ge,
        ">" => GuardOperator::Gt,
        _ => return Err(ParserError::UnknownOperator),
    };
    let right = parse_nat_value(pairs.next().unwrap())?;

    Ok(GuardExpr { left, right, op })
}

fn parse_nat_value(pair: Pair<'_, Rule>) -> Result<NatValue<'_>, ParserError> {
    match pair.as_rule() {
        Rule::ident => Ok(NatValue::Ident(pair.as_str())),
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
    #[error("unexpected end of input")]
    UnexpectedEof,
    #[error("invalid constructor id")]
    InvalidConstructorId(#[source] std::num::ParseIntError),
    #[error("invalid integer constant")]
    InvalidNatConst(#[source] std::num::ParseIntError),
    #[error("unknown operator")]
    UnknownOperator,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check_scheme(s: &str) {
        let s = Scheme::parse(s).unwrap();
        println!("{s:#?}");
    }

    fn check_constructor(s: &str) {
        let c = Constructor::parse(s).unwrap();
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
    fn scheme_with_guards() {
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

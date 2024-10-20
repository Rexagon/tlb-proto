use crate::parser::{ParserContext, Symbol};
use crate::resolver::{Constructor, Field, TypeExpr, TypeExprValue};

use super::TypeArg;

impl Constructor {
    pub fn display<'a>(&'a self, ctx: &'a ParserContext) -> impl std::fmt::Display + 'a {
        DisplayCtx {
            data: &(),
            constructor: self,
            parser_context: ctx,
            priority: 0,
            flags: ModeFlags::empty(),
        }
    }

    pub fn display_for_crc<'a>(&'a self, ctx: &'a ParserContext) -> impl std::fmt::Display + 'a {
        DisplayCtx {
            data: &(),
            constructor: self,
            parser_context: ctx,
            priority: 0,
            flags: ModeFlags::HIDE_TAG | ModeFlags::CRC,
        }
    }
}

impl std::fmt::Display for DisplayCtx<'_, ()> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let is_anon = self.flags.contains(ModeFlags::ANONYMOUS);
        if is_anon {
            f.write_str("[")
        } else if let Some(name) = self.constructor.name {
            write!(f, "{}", self.display_symbol(name))
        } else {
            f.write_str("_")
        }?;

        for field in &self.constructor.fields {
            write!(f, " {}", self.child(field, 0, self.flags))?;
        }

        if is_anon {
            f.write_str("]")?;
        }

        let output_type = self.constructor.output_type;
        write!(f, " = {}", self.display_symbol(output_type))?;

        for ty in &self.constructor.output_type_args {
            let ty = self.child(ty, 100, self.flags | ModeFlags::AUTO_NEGATE);
            write!(f, " {ty}")?;
        }

        if !self.flags.contains(ModeFlags::CRC) {
            f.write_str(";")?;
        }
        Ok(())
    }
}

impl std::fmt::Display for DisplayCtx<'_, Field> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let field = self.data;

        let not_field = field.is_implicit() || field.is_constraint();
        let show_braces = not_field && !self.flags.contains(ModeFlags::CRC);
        let priority = if not_field { 0 } else { 95 };

        if show_braces {
            f.write_str("{")?;
        }

        if let Some(name) = field.name {
            write!(f, "{}:", self.display_symbol(name))?;
        }

        let flags = self.flags & !ModeFlags::AUTO_NEGATE;
        std::fmt::Display::fmt(&self.child(field.ty.as_ref(), priority, flags), f)?;

        if show_braces {
            f.write_str("}")?;
        }

        Ok(())
    }
}

impl std::fmt::Display for DisplayCtx<'_, TypeArg> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.data.negate {
            f.write_str("~")?;
        }

        let flags = self.flags | ModeFlags::AUTO_NEGATE;
        std::fmt::Display::fmt(&self.child(self.data.ty.as_ref(), 100, flags), f)
    }
}

impl std::fmt::Display for DisplayCtx<'_, TypeExpr> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let priority = if self.flags.contains(ModeFlags::CRC) {
            0
        } else {
            self.priority
        };

        match &self.data.value {
            TypeExprValue::Type => f.write_str("Type"),
            TypeExprValue::Nat { .. } => f.write_str("#"),
            TypeExprValue::AltNat { kind, arg } => {
                write!(f, "{kind} {}", self.child(arg.as_ref(), 91, self.flags))
            }
            TypeExprValue::Param { index } => {
                if self.data.is_negated() ^ self.flags.contains(ModeFlags::AUTO_NEGATE) {
                    f.write_str("~")?;
                }
                match self.constructor.fields[*index].name {
                    Some(ident) => write!(f, "{}", self.display_symbol(ident)),
                    None => write!(f, "_{}", index + 1),
                }
            }
            TypeExprValue::Apply { type_id, args } => {
                // TODO: show anonymous constructor
                let show_paren = priority > 90 && !args.is_empty();
                if show_paren {
                    f.write_str("(")?;
                }

                std::fmt::Display::fmt(&self.display_symbol(*type_id), f)?;
                for arg in args {
                    let arg = self.child(arg.as_ref(), 91, self.flags);
                    f.write_fmt(format_args!(" {arg}"))?;
                }

                if show_paren {
                    f.write_str(")")?;
                }
                Ok(())
            }
            TypeExprValue::Add { left, right } => {
                let show_paren = priority > 20;
                if show_paren {
                    f.write_str("(")?;
                }

                let left = self.child(left.as_ref(), 20, self.flags);
                let right = self.child(right.as_ref(), 21, self.flags);
                write!(f, "{left} + {right}")?;

                if show_paren {
                    f.write_str(")")?;
                }
                Ok(())
            }
            TypeExprValue::GetBit { field, bit } => {
                let show_paren = priority > 97;
                if show_paren {
                    f.write_str("(")?;
                }

                let field = self.child(field.as_ref(), 98, self.flags);
                let bit = self.child(bit.as_ref(), 98, self.flags);
                write!(f, "{field}.{bit}")?;

                if show_paren {
                    f.write_str(")")?;
                }
                Ok(())
            }
            TypeExprValue::MulConst { left, right } => {
                let show_paren = priority > 30;
                if show_paren {
                    f.write_str("(")?;
                }

                let right = self.child(right.as_ref(), 31, self.flags);
                write!(f, "{left} * {right}")?;

                if show_paren {
                    f.write_str(")")?;
                }
                Ok(())
            }
            TypeExprValue::IntConst { value, .. } => std::fmt::Display::fmt(value, f),
            TypeExprValue::Tuple { count, item } => {
                let show_paren = priority > 30;
                if show_paren {
                    f.write_str("(")?;
                }

                let count = self.child(count.as_ref(), 30, self.flags);
                let item = self.child(item.as_ref(), 31, self.flags);
                write!(f, "{count} * {item}")?;

                if show_paren {
                    f.write_str(")")?;
                }
                Ok(())
            }
            TypeExprValue::Ref { value } => {
                write!(f, "^{}", self.child(value.as_ref(), 100, self.flags))
            }
            TypeExprValue::CondType { cond, value } => {
                let show_paren = priority > 95;
                if show_paren {
                    f.write_str("(")?;
                }

                let cond = self.child(cond.as_ref(), 96, self.flags);
                let value = self.child(value.as_ref(), 96, self.flags);
                write!(f, "{cond}?{value}")?;

                if show_paren {
                    f.write_str(")")?;
                }
                Ok(())
            }
            TypeExprValue::Constraint { op, left, right } => {
                let show_paren = priority > 90;
                if show_paren {
                    f.write_str("(")?;
                }

                let left = self.child(left.as_ref(), 91, self.flags);
                let right = self.child(right.as_ref(), 91, self.flags);

                if self.flags.contains(ModeFlags::CRC) {
                    write!(f, "{op} {left} {right}")
                } else {
                    write!(f, "{left} {op} {right}")
                }?;

                if show_paren {
                    f.write_str(")")?;
                }
                Ok(())
            }
        }
    }
}

impl std::fmt::Display for DisplayCtx<'_, Symbol> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.display_symbol(*self.data), f)
    }
}

struct DisplayCtx<'a, T> {
    data: &'a T,
    constructor: &'a Constructor,
    parser_context: &'a crate::parser::ParserContext,
    priority: u32,
    flags: ModeFlags,
}

impl<'a, T> DisplayCtx<'a, T> {
    fn display_symbol(&self, symbol: Symbol) -> DisplaySymbol<'_> {
        DisplaySymbol {
            parser_context: self.parser_context,
            symbol,
        }
    }

    fn child<U>(&self, data: &'a U, priority: u32, flags: ModeFlags) -> DisplayCtx<'a, U> {
        DisplayCtx {
            data,
            constructor: self.constructor,
            parser_context: self.parser_context,
            priority,
            flags,
        }
    }
}

bitflags::bitflags! {
    #[derive(Default, Clone, Copy, Eq, PartialEq)]
    struct ModeFlags: u32 {
        const AUTO_NEGATE = 1 << 0;
        const CRC = 1 << 1;
        const ANONYMOUS = 1 << 2;
        const HIDE_TAG = 1 << 3;
    }
}

struct DisplaySymbol<'a> {
    parser_context: &'a crate::parser::ParserContext,
    symbol: Symbol,
}

impl std::fmt::Display for DisplaySymbol<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.parser_context.resolve_symbol(self.symbol) {
            Some(s) => f.write_str(s),
            None => Err(std::fmt::Error),
        }
    }
}

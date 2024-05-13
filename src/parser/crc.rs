use crc::{Crc, CRC_32_ISO_HDLC};

use crate::parser::ast::*;
use crate::parser::{Context, Symbol};

pub fn compute_tag(ctx: &Context, constructor: &Constructor) -> u32 {
    use std::fmt::Write;

    struct Checksum<'a>(crc::Digest<'a, u32>);

    impl Write for Checksum<'_> {
        #[inline(always)]
        fn write_str(&mut self, s: &str) -> std::fmt::Result {
            self.0.update(s.as_bytes());
            Ok(())
        }
    }

    let mut checksum = Checksum(CRC.digest());
    write!(&mut checksum, "{}", CrcCtx(constructor, ctx)).unwrap();

    checksum.0.finalize()
}

impl std::fmt::Display for CrcCtx<'_, &'_ Constructor> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(name) = self.0.name {
            f.write_str(self.1.resolve_symbol(name.ident).expect("shouldn't fail"))?;
        } else {
            f.write_str("_")?;
        }

        for field in &self.0.fields {
            write!(f, " {}", CrcCtx(field, self.1))?;
        }

        write!(f, " = {}", CrcCtx(&self.0.output_type.ident, self.1))?;
        for ty in &self.0.output_type_args {
            write!(f, " {}", CrcCtx(ty, self.1))?;
        }

        Ok(())
    }
}

impl std::fmt::Display for CrcCtx<'_, &'_ Field> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            Field::ImplicitParam { ident, ty, .. } => {
                let ident = CrcCtx(ident, self.1);
                write!(f, "{ident}:{ty}")
            }
            Field::Constraint { expr, .. } => {
                std::fmt::Display::fmt(&CrcCtx(expr.as_ref(), self.1), f)
            }
            Field::Param { name, ty, .. } => {
                let ty = CrcCtx(ty.as_ref(), self.1);
                match name {
                    Some(name) => {
                        write!(f, "{}:{ty}", CrcCtx(&name.ident, self.1))
                    }
                    None => std::fmt::Display::fmt(&ty, f),
                }
            }
        }
    }
}

impl std::fmt::Display for CrcCtx<'_, &'_ OutputTypeExpr> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.negate {
            f.write_str("~")?;
        }
        std::fmt::Display::fmt(&CrcCtx(&self.0.ty, self.1), f)
    }
}

impl std::fmt::Display for CrcCtx<'_, &'_ TypeExpr> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.0 {
            TypeExpr::Const { value, .. } => std::fmt::Display::fmt(value, f),
            TypeExpr::Nat { .. } => f.write_str("#"),
            TypeExpr::AltNat { kind, arg, .. } => {
                write!(f, "{kind} {}", CrcCtx(arg.as_ref(), self.1))
            }
            TypeExpr::Add { left, right, .. } => {
                let left = CrcCtx(left.as_ref(), self.1);
                let right = CrcCtx(right.as_ref(), self.1);
                write!(f, "{left} + {right}")
            }
            TypeExpr::Mul { left, right, .. } => {
                let left = CrcCtx(left.as_ref(), self.1);
                let right = CrcCtx(right.as_ref(), self.1);
                write!(f, "{left} * {right}")
            }
            TypeExpr::Constraint {
                op, left, right, ..
            } => {
                let left = CrcCtx(left.as_ref(), self.1);
                let right = CrcCtx(right.as_ref(), self.1);
                write!(f, "{op} {left} {right}")
            }
            TypeExpr::Cond { cond, value, .. } => {
                let cond = CrcCtx(cond.as_ref(), self.1);
                let value = CrcCtx(value.as_ref(), self.1);
                write!(f, "{cond}?{value}")
            }
            TypeExpr::GetBit { value, bit, .. } => {
                let value = CrcCtx(value.as_ref(), self.1);
                let bit = CrcCtx(bit.as_ref(), self.1);
                write!(f, "{value}.{bit}")
            }
            TypeExpr::Apply {
                ident,
                args,
                negate,
                ..
            } => {
                if *negate {
                    f.write_str("~")?;
                }
                std::fmt::Display::fmt(&CrcCtx(ident, self.1), f)?;
                for arg in args {
                    f.write_fmt(format_args!(" {}", CrcCtx(arg, self.1)))?;
                }
                Ok(())
            }
            TypeExpr::Ref { value, .. } => write!(f, "^{}", CrcCtx(value.as_ref(), self.1)),
            TypeExpr::AnonConstructor { fields, .. } => {
                f.write_str("[")?;
                for field in fields {
                    write!(f, " {}", CrcCtx(field, self.1))?;
                }
                f.write_str(" ]")
            }
        }
    }
}

impl std::fmt::Display for CrcCtx<'_, &'_ Symbol> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.1.resolve_symbol(*self.0) {
            Some(s) => f.write_str(s),
            None => Err(std::fmt::Error),
        }
    }
}

struct CrcCtx<'a, T>(T, &'a Context);

static CRC: Crc<u32> = Crc::<u32>::new(&CRC_32_ISO_HDLC);

#[cfg(test)]
mod tests {
    use super::*;

    fn check_tag(tlb: &str, tag: u32) {
        let mut ctx = Context::default();
        let constructor = Constructor::parse(&mut ctx, tlb).unwrap();
        println!("{}", CrcCtx(&constructor, &ctx));
        assert_eq!(constructor.tag, None);

        let computed = compute_tag(&ctx, &constructor);
        assert_eq!(computed, tag);
    }

    #[test]
    fn correct_tags() {
        check_tag(
            r###"
            block_extra in_msg_descr:^InMsgDescr
                out_msg_descr:^OutMsgDescr
                account_blocks:^ShardAccountBlocks
                rand_seed:bits256
                created_by:bits256
                custom:(Maybe ^McBlockExtra) = BlockExtra;
            "###,
            0x4a33f6fd,
        );

        // TODO: Add support for unonymous constructors

        check_tag(
            r###"
            test {x:#} {y:#} asd:# qwe:(## 4) bbb:(#<= 1) ^[ qqq:# tt:bits256 ] = Test (x + 1) y;
            "###,
            0x3afc7f4c,
        );

        check_tag(
            r###"
            with_guard {x:#}
                some:(#<= 10)
                other:(#<= 10)
                { some >= 1 }
                { other <= some }
                { other >= some } = WithGuard (x * 2);
            "###,
            0xd0bd258f,
        );

        check_tag(
            r###"
            hm_edge {n:#} {X:Type} {l:#} {m:#} label:(HmLabel ~l n) {n = (~m) + l} node:(HashmapNode m X) = Hashmap n X;
            "###,
            0x2002a049,
        );
    }
}

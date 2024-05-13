use bitflags::bitflags;
use std::rc::Rc;

use crate::parser::{self, ast, Symbol};
use crate::util::{BinTrie, BitPfxCollection, FastHashMap, FastHashSet, Recurse, SizeRange};

pub struct Resolver<'a> {
    parser_context: &'a mut parser::Context,
    types: FastHashMap<Symbol, Rc<Type>>,
}

impl<'a> Resolver<'a> {
    pub fn new(parser_context: &'a mut parser::Context) -> Self {
        let mut res = Self {
            parser_context,
            types: FastHashMap::default(),
        };
        res.def_builtin_types().unwrap();
        res
    }

    pub fn import(&mut self, constructors: &[ast::Constructor]) -> Result<(), ImportError> {
        // Group constructors by output type name
        let mut constructors_by_output =
            FastHashMap::<Symbol, Vec<&ast::Constructor>>::with_capacity_and_hasher(
                constructors.len(),
                Default::default(),
            );

        for constructor in constructors {
            constructors_by_output
                .entry(constructor.output_type.ident)
                .or_default()
                .push(constructor);
        }

        // Start importing constructors
        struct ResolverContext<'a> {
            types: &'a FastHashMap<Symbol, Rc<Type>>,
            constructors_by_output: &'a FastHashMap<Symbol, Vec<&'a ast::Constructor>>,
            unresolved: FastHashSet<Symbol>,
        }

        impl ResolverContext<'_> {
            fn check_expr(&mut self, expr: &ast::TypeExpr) -> bool {
                match expr {
                    ast::TypeExpr::Apply { ident, .. } => {
                        if !self.constructors_by_output.contains_key(ident)
                            && !self.types.contains_key(ident)
                        {
                            self.unresolved.insert(*ident);
                        }

                        true
                    }
                    ast::TypeExpr::Constraint { .. } => false,
                    ast::TypeExpr::Cond { value, .. } => {
                        value.recurse(self, Self::check_expr);
                        false
                    }
                    ast::TypeExpr::GetBit { .. } => false,
                    _ => true,
                }
            }
        }

        let mut ctx = ResolverContext {
            types: &self.types,
            constructors_by_output: &constructors_by_output,
            unresolved: FastHashSet::default(),
        };
        for constructor in constructors {
            constructor.recurse(&mut ctx, ResolverContext::check_expr);
        }

        // TEMP
        for name in ctx.unresolved {
            println!(
                "Unresolved type: {:?}",
                self.parser_context.resolve_symbol(name)
            );
        }

        Ok(())
    }

    pub fn get_type(&self, symbol: Symbol) -> Option<&Rc<Type>> {
        self.types.get(&symbol)
    }

    pub fn get_type_by_name(&self, name: &str) -> Option<&Rc<Type>> {
        self.parser_context
            .get_symbol(name)
            .and_then(|symbol| self.get_type(symbol))
    }

    fn def_builtin_types(&mut self) -> Result<(), ImportError> {
        self.def_builtin_type("Any", 0, SizeRange::any(), TypeKind::Type)?;
        self.def_builtin_type("Cell", 0, SizeRange::exact_refs(1), TypeKind::Type)?;

        self.def_builtin_type("int", 1, SizeRange::bits(0..=257), TypeKind::Int)?;
        self.def_builtin_type("uint", 1, SizeRange::bits(0..=256), TypeKind::Int)?;
        self.def_builtin_type("bits", 1, SizeRange::bits(0..=1023), TypeKind::Type)?;

        for i in 0..=257 {
            let name = format!("uint{i}");
            self.def_builtin_type(&name[1..], 0, SizeRange::exact_bits(i), TypeKind::Int)?;
            if i <= 256 {
                self.def_builtin_type(&name, 0, SizeRange::exact_bits(i), TypeKind::Int)?;
            }
        }

        for i in 0..=1023 {
            let name = format!("bits{i}");
            self.def_builtin_type(&name, 0, SizeRange::exact_bits(i), TypeKind::Int)?;
        }

        Ok(())
    }

    fn def_builtin_type(
        &mut self,
        name: &str,
        argc: usize,
        size: SizeRange,
        produces: TypeKind,
    ) -> Result<(), ImportError> {
        let name = self.parser_context.intern_symbol(name);

        let ty = Type {
            size,
            constructors: Vec::new(),
            starts_with: BitPfxCollection::all(),
            prefix_trie: Default::default(),
            flags: TypeFlags::BUILTIN,
            produces,
            args: vec![TypeArgFlags::IS_POS | TypeArgFlags::IS_NAT; argc],
        };
        self.types.insert(name, Rc::new(ty));

        Ok(())
    }
}

#[derive(Debug)]
pub struct Type {
    pub size: SizeRange,
    pub constructors: Vec<Constructor>,
    pub starts_with: BitPfxCollection,
    pub prefix_trie: BinTrie,
    pub flags: TypeFlags,
    pub produces: TypeKind,
    pub args: Vec<TypeArgFlags>,
}

impl Type {
    pub fn is_nat(&self) -> bool {
        self.flags.contains(TypeFlags::IS_NAT)
    }
}

bitflags! {
    #[derive(Default, Debug, Clone, Copy, Eq, PartialEq)]
    pub struct TypeFlags: u32 {
        const BUILTIN = 1 << 0;
        const IS_NAT = 1 << 1;
    }

    #[derive(Default, Debug, Clone, Copy, Eq, PartialEq)]
    pub struct TypeArgFlags: u32 {
        const IS_TYPE = 1 << 0;
        const IS_NAT = 1 << 1;
        const IS_POS = 1 << 2;
        const IS_NEG = 1 << 3;
        const NON_CONST = 1 << 4;
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeKind {
    Unit,
    Bool,
    Int,
    Type,
}

#[derive(Debug)]
pub struct Constructor {
    pub name: Option<Symbol>,
    pub size: SizeRange,
    pub starts_with: BitPfxCollection,
    pub fields: Vec<Field>,
}

#[derive(Debug)]
pub struct Field {
    flags: FieldFlags,
}

impl Field {
    pub fn is_known(&self) -> bool {
        self.flags.contains(FieldFlags::IS_KNOWN)
    }
}

bitflags! {
    #[derive(Default, Debug, Clone, Copy, Eq, PartialEq)]
    pub struct FieldFlags: u32 {
        const IS_KNOWN = 1 << 0;
    }
}

#[derive(Debug)]
pub struct TypeExprContext<'a> {
    pub constructor: &'a mut Constructor,
    pub global_symbols: &'a mut FastHashMap<Symbol, Rc<Type>>,
    pub local_symbols: &'a mut FastHashMap<Symbol, SymbolValue>,
    pub allow_nat: bool,
    pub allow_type: bool,
    pub auto_negate: bool,
    pub typecheck: bool,
}

impl TypeExprContext<'_> {
    fn lookup(&self, symbol: Symbol) -> Option<SymbolValue> {
        self.local_symbols.get(&symbol).cloned().or_else(|| {
            self.global_symbols
                .get(&symbol)
                .cloned()
                .map(SymbolValue::Type)
        })
    }

    fn without_typecheck(&'_ mut self) -> TypeExprContext<'_> {
        let mut res = self.subcontext();
        res.typecheck = false;
        res
    }

    fn with_typecheck(&'_ mut self) -> TypeExprContext<'_> {
        let mut res = self.subcontext();
        res.typecheck = true;
        res
    }

    fn expect_any(&'_ mut self) -> TypeExprContext<'_> {
        let mut res = self.subcontext();
        res.allow_nat = true;
        res.allow_type = true;
        res
    }

    fn expect_only_nat(&'_ mut self) -> TypeExprContext<'_> {
        let mut res = self.subcontext();
        res.allow_nat = true;
        res.allow_type = false;
        res
    }

    fn expect_only_type(&'_ mut self) -> TypeExprContext<'_> {
        let mut res = self.subcontext();
        res.allow_nat = false;
        res.allow_type = true;
        res
    }

    fn subcontext(&'_ mut self) -> TypeExprContext<'_> {
        TypeExprContext {
            constructor: self.constructor,
            global_symbols: self.global_symbols,
            local_symbols: self.local_symbols,
            allow_nat: self.allow_nat,
            allow_type: self.allow_type,
            auto_negate: self.auto_negate,
            typecheck: self.typecheck,
        }
    }
}

#[derive(Debug, Clone)]
pub enum SymbolValue {
    Type(Rc<Type>),
    Param { index: usize, value: Rc<TypeExpr> },
}

#[derive(Debug)]
pub struct TypeExpr {
    pub span: parser::Span,
    pub value: TypeExprValue,
    pub flags: TypeExprFlags,
}

impl TypeExpr {
    fn new(ast: &ast::TypeExpr, ctx: &mut TypeExprContext) -> Result<Self, ImportError> {
        match ast {
            ast::TypeExpr::Const { span, value } => Ok(Self::new_const(*value, span)),
            ast::TypeExpr::Nat { span } => Ok(Self::new_nat(span)),
            ast::TypeExpr::AltNat { span, kind, arg } => todo!(),
            ast::TypeExpr::Add { span, left, right } => Self::new_add(left, right, span, ctx),
            ast::TypeExpr::Mul { span, left, right } => Self::new_mul(left, right, span, ctx),
            ast::TypeExpr::Constraint {
                span,
                op,
                left,
                right,
            } => Self::new_constraint(op, left, right, span, ctx),
            ast::TypeExpr::Cond { span, cond, value } => Self::new_cond(cond, value, span, ctx),
            ast::TypeExpr::GetBit { span, value, bit } => Self::new_get_bit(value, bit, span, ctx),
            ast::TypeExpr::Apply {
                span,
                ident,
                args,
                negate,
            } => Self::new_apply(*ident, args, *negate, span, ctx),
            ast::TypeExpr::Ref { span, value } => Self::new_ref(value, span, ctx),
            ast::TypeExpr::AnonConstructor { span, fields } => todo!(),
        }
    }

    fn new_const(value: u32, span: &parser::Span) -> Self {
        Self {
            span: *span,
            value: TypeExprValue::IntConst { value },
            flags: TypeExprFlags::IS_NAT,
        }
    }

    fn new_apply(
        ident: Symbol,
        args: &[ast::TypeExpr],
        mut negate: bool,
        span: &parser::Span,
        ctx: &mut TypeExprContext,
    ) -> Result<Self, ImportError> {
        let args = {
            let ctx = &mut ctx.expect_any();
            args.iter()
                .map(|arg| Self::new(arg, ctx).map(Rc::new))
                .collect::<Result<Vec<_>, _>>()?
        };

        let value = match ctx.lookup(ident) {
            None if negate => {
                return Err(ImportError::TypeMismatch {
                    span: *span,
                    message: "field identifier expected",
                });
            }
            Some(value) => value,
            None => todo!("implicitly define new type"),
        };

        Ok(match value {
            SymbolValue::Type(ty) => {
                if negate {
                    return Err(ImportError::TypeMismatch {
                        span: *span,
                        message: "cannot negate a type",
                    });
                }

                if ty.args.len() != args.len() {
                    return Err(ImportError::TypeMismatch {
                        span: *span,
                        message: "type applied with incorrent number of arguments",
                    });
                }

                for (arg, flags) in std::iter::zip(&args, &ty.args) {
                    if arg.is_negated() {
                        negate = true; // Type can only be negated by its arguments

                        if flags.contains(TypeArgFlags::IS_POS) {
                            return Err(ImportError::TypeMismatch {
                                span: arg.span,
                                message: "passed an argument of incorrect polarity",
                            });
                        }
                        // TODO: *flags |= TypeArgFlags::IS_NEG;
                    }

                    arg.ensure_no_typecheck()?;

                    if arg.is_nat() {
                        // TODO: *flags |= TypeArgFlags::IS_NAT;
                    } else {
                        // TODO: *flags |= TypeArgFlags::IS_TYPE;
                        if arg.is_negated() {
                            return Err(ImportError::TypeMismatch {
                                span: arg.span,
                                message: "cannot use negative types as arguments to other types",
                            });
                        }
                    }
                }

                let mut flags = TypeExprFlags::empty();
                if ty.is_nat() {
                    flags |= TypeExprFlags::IS_NAT;
                }
                if negate {
                    flags |= TypeExprFlags::NEGATED | TypeExprFlags::TYPECHECK_ONLY;
                }

                Self {
                    span: *span,
                    value: TypeExprValue::Apply { ty, args },
                    flags,
                }
            }
            SymbolValue::Param { index, value: ty } => {
                // NOTE: Params cannot have arguments (yet?)
                if let Some(arg) = args.first() {
                    return Err(ImportError::TypeMismatch {
                        span: arg.span,
                        message: "cannot apply one expression to the other",
                    });
                }

                let field = &ctx.constructor.fields[index];

                if ctx.auto_negate && !field.is_known() {
                    negate = true;
                }

                if !ty.is_nat() && !matches!(&ty.value, TypeExprValue::Type) {
                    return Err(ImportError::TypeMismatch {
                        span: *span,
                        message: "cannot use a field in an expression unless \
                                it is either an integer or a type",
                    });
                }

                let mut flags = ty.flags;
                if negate {
                    flags |= TypeExprFlags::NEGATED;
                }

                Self {
                    span: *span,
                    value: TypeExprValue::Param { index },
                    flags,
                }
            }
        })
    }

    fn new_nat(span: &parser::Span) -> Self {
        Self {
            span: *span,
            value: TypeExprValue::Nat,
            flags: TypeExprFlags::IS_NAT,
        }
    }

    fn new_constraint(
        op: &ast::ConstraintOp,
        left: &ast::TypeExpr,
        right: &ast::TypeExpr,
        span: &parser::Span,
        ctx: &mut TypeExprContext,
    ) -> Result<Self, ImportError> {
        // NOTE: Constraint result is always a UNIT type
        if !ctx.allow_type {
            return Err(ImportError::TypeMismatch {
                span: *span,
                message: "comparison result used as an integer",
            });
        }

        let left_ty = Self::new(left, &mut ctx.expect_only_nat())?;
        let right_ty = Self::new(right, &mut ctx.expect_only_nat())?;

        if !left_ty.is_nat() {
            return Err(ImportError::TypeMismatch {
                span: left.span(),
                message: "cannot apply integer comparison to types",
            });
        }

        if !right_ty.is_nat() {
            return Err(ImportError::TypeMismatch {
                span: right.span(),
                message: "cannot apply integer comparison to types",
            });
        }

        Ok(Self {
            span: *span,
            value: TypeExprValue::Constraint {
                op: *op,
                left: Rc::new(left_ty),
                right: Rc::new(right_ty),
            },
            flags: TypeExprFlags::IS_NAT,
        })
    }

    fn new_add(
        left: &ast::TypeExpr,
        right: &ast::TypeExpr,
        span: &parser::Span,
        ctx: &mut TypeExprContext,
    ) -> Result<Self, ImportError> {
        // NOTE: nat+nat = nat
        if !ctx.allow_nat {
            return Err(ImportError::TypeMismatch {
                span: *span,
                message: "sum cannot be used as a type expression",
            });
        }

        let left_ty = Self::new(left, &mut ctx.expect_only_nat())?;
        let right_ty = Self::new(right, &mut ctx.expect_only_nat())?;

        if !left_ty.is_nat() {
            return Err(ImportError::TypeMismatch {
                span: left.span(),
                message: "expected natural number",
            });
        }

        if !right_ty.is_nat() {
            return Err(ImportError::TypeMismatch {
                span: right.span(),
                message: "expected natural number",
            });
        }

        if left_ty.is_negated() && right_ty.is_negated() {
            return Err(ImportError::TypeMismatch {
                span: left.span(),
                message: "cannot add two values of negative polarity",
            });
        }

        let negated = TypeExprFlags::NEGATED & (left_ty.flags | right_ty.flags);

        Ok(Self {
            span: *span,
            value: TypeExprValue::Add {
                left: Rc::new(left_ty),
                right: Rc::new(right_ty),
            },
            flags: TypeExprFlags::IS_NAT | negated,
        })
    }

    fn new_mul(
        left: &ast::TypeExpr,
        right: &ast::TypeExpr,
        span: &parser::Span,
        ctx: &mut TypeExprContext,
    ) -> Result<Self, ImportError> {
        let left_ty = Self::new(left, &mut ctx.expect_only_nat())?;
        let right_ty = Self::new(right, &mut ctx.expect_any())?;

        if !left_ty.is_nat() {
            return Err(ImportError::TypeMismatch {
                span: left.span(),
                message: "cannot apply `*` to types",
            });
        }

        if right_ty.is_nat() {
            match (&left_ty.value, &right_ty.value) {
                (
                    TypeExprValue::IntConst { value: left, .. },
                    TypeExprValue::IntConst { value: right },
                ) => {
                    let value = left
                        .checked_mul(*right)
                        .ok_or_else(|| ImportError::IntOverflow { span: *span })?;
                    Ok(Self::new_const(value, span))
                }
                // TODO: Add special cases for 0 and 1
                (TypeExprValue::IntConst { value, .. }, _) => {
                    let negated = TypeExprFlags::NEGATED & right_ty.flags;
                    Ok(Self {
                        span: *span,
                        value: TypeExprValue::MulConst {
                            left: *value,
                            right: Rc::new(right_ty),
                        },
                        flags: TypeExprFlags::IS_NAT | negated,
                    })
                }
                _ => Err(ImportError::TypeMismatch {
                    span: *span,
                    message: "multiplication is allowed only by constant values",
                }),
            }
        } else {
            right_ty.ensure_no_typecheck()?;
            Ok(Self {
                span: *span,
                value: TypeExprValue::Tuple {
                    count: Rc::new(left_ty),
                    item: Rc::new(right_ty),
                },
                flags: TypeExprFlags::IS_NAT,
            })
        }
    }

    fn new_cond(
        cond: &ast::TypeExpr,
        value: &ast::TypeExpr,
        span: &parser::Span,
        ctx: &mut TypeExprContext,
    ) -> Result<Self, ImportError> {
        let cond_expr = Self::new(cond, &mut ctx.expect_only_nat())?;
        let value_expr = Self::new(value, &mut ctx.expect_only_type().without_typecheck())?;

        if !cond_expr.is_nat() {
            return Err(ImportError::TypeMismatch {
                span: cond.span(),
                message: "cannot apply `?` with non-integer condition",
            });
        }

        value_expr.ensure_no_typecheck()?;

        Ok(Self {
            span: *span,
            value: TypeExprValue::CondType {
                cond: Rc::new(cond_expr),
                value: Rc::new(value_expr),
            },
            flags: TypeExprFlags::empty(),
        })
    }

    fn new_get_bit(
        value: &ast::TypeExpr,
        bit: &ast::TypeExpr,
        span: &parser::Span,
        ctx: &mut TypeExprContext,
    ) -> Result<Self, ImportError> {
        // NOTE: nat.nat = nat
        if !ctx.allow_nat {
            return Err(ImportError::TypeMismatch {
                span: *span,
                message: "sum cannot be used as a type expression",
            });
        }

        let value_expr = Self::new(value, &mut ctx.expect_only_nat())?;
        let bit_expr = Self::new(bit, &mut ctx.expect_only_nat())?;

        if !value_expr.is_nat() {
            return Err(ImportError::TypeMismatch {
                span: value.span(),
                message: "cannot apply bit selection operator `.` to types",
            });
        }

        if value_expr.is_negated() || bit_expr.is_negated() {
            return Err(ImportError::TypeMismatch {
                span: *span,
                message: "cannot apply bit selection operator `.` to types of negative polarity",
            });
        }

        Ok(Self {
            span: *span,
            value: TypeExprValue::GetBit {
                field: Rc::new(value_expr),
                bit: Rc::new(bit_expr),
            },
            flags: TypeExprFlags::IS_NAT,
        })
    }

    fn new_ref(
        value: &ast::TypeExpr,
        span: &parser::Span,
        ctx: &mut TypeExprContext,
    ) -> Result<Self, ImportError> {
        let value_expr = Self::new(value, &mut ctx.expect_only_type())?;

        if value_expr.is_nat() {
            return Err(ImportError::TypeMismatch {
                span: *span,
                message: "cannot create a cell reference type to a natural number",
            });
        }

        Ok(Self {
            span: *span,
            value: TypeExprValue::Ref {
                value: Rc::new(value_expr),
            },
            flags: TypeExprFlags::empty(),
        })
    }

    fn is_nat(&self) -> bool {
        self.flags.contains(TypeExprFlags::IS_NAT)
    }

    fn is_negated(&self) -> bool {
        self.flags.contains(TypeExprFlags::NEGATED)
    }

    fn ensure_no_typecheck(&self) -> Result<(), ImportError> {
        if self.flags.contains(TypeExprFlags::TYPECHECK_ONLY) {
            Err(ImportError::TypeMismatch {
                span: self.span,
                message: "type expression can be used only in a type-checking context",
            })
        } else {
            Ok(())
        }
    }
}

bitflags! {
    #[derive(Default, Debug, Clone, Copy, Eq, PartialEq)]
    pub struct TypeExprFlags: u32 {
        const TYPECHECK_ONLY = 1 << 1;
        const IS_NAT = 1 << 2;
        const NEGATED = 1 << 3;
    }
}

#[derive(Debug)]
pub enum TypeExprValue {
    Type,
    Nat,
    Param {
        index: usize,
    },
    Apply {
        ty: Rc<Type>,
        args: Vec<Rc<TypeExpr>>,
    },
    Add {
        left: Rc<TypeExpr>,
        right: Rc<TypeExpr>,
    },
    GetBit {
        field: Rc<TypeExpr>,
        bit: Rc<TypeExpr>,
    },
    MulConst {
        left: u32,
        right: Rc<TypeExpr>,
    },
    IntConst {
        value: u32,
    },
    Tuple {
        count: Rc<TypeExpr>,
        item: Rc<TypeExpr>,
    },
    Ref {
        value: Rc<TypeExpr>,
    },
    CondType {
        cond: Rc<TypeExpr>,
        value: Rc<TypeExpr>,
    },
    Constraint {
        op: ast::ConstraintOp,
        left: Rc<TypeExpr>,
        right: Rc<TypeExpr>,
    },
}

#[derive(thiserror::Error, Debug)]
pub enum ImportError {
    #[error("type mismatch: {message}")]
    TypeMismatch {
        span: parser::Span,
        message: &'static str,
    },
    #[error("integer overflow")]
    IntOverflow { span: parser::Span },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn full_block() {
        let input = include_str!("../test/block.tlb");

        let mut ctx = parser::Context::default();
        let scheme = ast::Scheme::parse(&mut ctx, input).unwrap();

        let mut ctx = Resolver::new(&mut ctx);
        ctx.import(&scheme.constructors).unwrap();
    }
}

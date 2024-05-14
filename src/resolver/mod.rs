use std::rc::Rc;

use bitflags::bitflags;

use crate::parser::{self, ast, Symbol};
use crate::util::{BinTrie, BitPfxCollection, FastHashMap, SizeRange};

pub struct Resolver<'a> {
    global: GlobalSymbolTable,
    parser_context: &'a mut parser::Context,
}

impl<'a> Resolver<'a> {
    pub fn new(parser_context: &'a mut parser::Context) -> Self {
        let mut res = Self {
            global: Default::default(),
            parser_context,
        };
        res.def_builtin_types().unwrap();
        res
    }

    pub fn import(&mut self, scheme: &ast::Scheme) -> Result<(), ImportError> {
        for ast in &scheme.constructors {
            self.def_constructor(ast)?;
        }
        Ok(())
    }

    pub fn get_type(&self, symbol: Symbol) -> Option<&Type> {
        self.global.lookup(&symbol)
    }

    pub fn get_type_by_name(&self, name: &str) -> Option<&Type> {
        self.parser_context
            .get_symbol(name)
            .and_then(|symbol| self.get_type(symbol))
    }

    fn def_builtin_types(&mut self) -> Result<(), ImportError> {
        self.def_builtin_type("Any", &[], SizeRange::any(), TypeKind::Type)?;
        self.def_builtin_type("Cell", &[], SizeRange::exact_refs(1), TypeKind::Type)?;

        let nat_arg = TypeArgFlags::IS_POS | TypeArgFlags::IS_NAT;
        self.def_builtin_type("int", &[nat_arg], SizeRange::bits(0..=257), TypeKind::Int)?;
        self.def_builtin_type("uint", &[nat_arg], SizeRange::bits(0..=256), TypeKind::Int)?;
        self.def_builtin_type(
            "bits",
            &[nat_arg],
            SizeRange::bits(0..=1023),
            TypeKind::Type,
        )?;

        for i in 0..=257 {
            let name = format!("uint{i}");
            self.def_builtin_type(&name[1..], &[], SizeRange::exact_bits(i), TypeKind::Int)?;
            if i <= 256 {
                self.def_builtin_type(&name, &[], SizeRange::exact_bits(i), TypeKind::Int)?;
            }
        }

        for i in 0..=1023 {
            let name = format!("bits{i}");
            self.def_builtin_type(&name, &[], SizeRange::exact_bits(i), TypeKind::Int)?;
        }

        Ok(())
    }

    fn def_builtin_type(
        &mut self,
        name: &str,
        args: &[TypeArgFlags],
        size: SizeRange,
        produces: TypeKind,
    ) -> Result<(), ImportError> {
        let name = self.parser_context.intern_symbol(name);

        let ty = Box::new(Type {
            size,
            constructors: Vec::new(),
            starts_with: BitPfxCollection::all(),
            prefix_trie: Default::default(),
            flags: TypeFlags::BUILTIN,
            produces,
            args: args.to_vec(),
        });
        self.global.register_type(name, ty);

        Ok(())
    }

    fn def_constructor(&mut self, ast: &ast::Constructor) -> Result<(), ImportError> {
        let mut constructor = Constructor {
            name: ast.name.map(|name| name.ident),
            size: SizeRange::any(),
            starts_with: Default::default(),
            fields: Vec::with_capacity(ast.fields.len()),
            output_type: ast.output_type.ident,
            output_type_args: Vec::with_capacity(ast.output_type_args.len()),
        };

        let ctx = &mut TypeExprContext {
            constructor: &mut constructor,
            scope: &mut self.global.begin_scope(),
            allow_nat: true,
            allow_type: true,
            auto_negate: false,
            typecheck: false,
        };

        // Parse fields list
        for (field_index, field) in ast.fields.iter().enumerate() {
            let name_ident = match field.name_ident() {
                Some(ident) => ident,
                None => self
                    .parser_context
                    .intern_symbol(format!("__field{field_index}")),
            };

            if ctx.scope.local.lookup(name_ident).is_some() {
                return Err(ImportError::TypeMismatch {
                    span: field.span(),
                    message: "redefined field or parameter",
                });
            }

            let parsed_field = match field {
                ast::Field::ImplicitParam { span, ty, .. } => Field::new_implicit_param(*ty, span),
                ast::Field::Constraint { expr, .. } => Field::new_constraint(expr, ctx)?,
                ast::Field::Param { ty, .. } => Field::new_param(ty, ctx)?,
            };

            ctx.scope.local.register_param(
                name_ident,
                LocalSymbol {
                    index: field_index,
                    value: parsed_field.ty.clone(),
                },
            );

            ctx.constructor.fields.push(parsed_field);
        }

        // Define output type
        let _ty = ctx
            .scope
            .global
            .register_type(ast.output_type.ident, Default::default());

        // Parse output type args
        for ast in &ast.output_type_args {
            let mut ctx = ctx.expect_any();
            ctx.auto_negate = !ast.negate;

            let arg = TypeExpr::new(&ast.ty, &mut ctx)?;

            // TODO: Bind value

            let const_value = match &arg.value {
                TypeExprValue::IntConst { value } if !ast.negate => Some(*value),
                _ => None,
            };

            ctx.constructor.output_type_args.push(OutputTypeArg {
                ty: Rc::new(arg),
                negate: ast.negate,
                const_value,
            });
        }

        // TODO: Bind constructor

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

impl Default for Type {
    fn default() -> Self {
        Self {
            size: SizeRange::any(),
            constructors: Vec::new(),
            starts_with: BitPfxCollection::all(),
            prefix_trie: Default::default(),
            flags: TypeFlags::empty(),
            produces: TypeKind::Type,
            args: Vec::new(),
        }
    }
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
    Type,
    Unit,
    Bool,
    Int,
}

#[derive(Debug)]
pub struct Constructor {
    pub name: Option<Symbol>,
    pub size: SizeRange,
    pub starts_with: BitPfxCollection,
    pub fields: Vec<Field>,
    pub output_type: Symbol,
    pub output_type_args: Vec<OutputTypeArg>,
}

#[derive(Debug)]
pub struct OutputTypeArg {
    pub ty: Rc<TypeExpr>,
    pub negate: bool,
    pub const_value: Option<u32>,
}

#[derive(Debug)]
pub struct Field {
    pub ty: Rc<TypeExpr>,
    pub flags: FieldFlags,
}

impl Field {
    pub fn new_implicit_param(ty: ast::GenericType, span: &parser::Span) -> Self {
        Self {
            ty: Rc::new(match ty {
                ast::GenericType::Type => TypeExpr::new_type(span),
                ast::GenericType::Nat => TypeExpr::new_nat(span),
            }),
            flags: FieldFlags::IS_IMPLICIT,
        }
    }

    pub fn new_constraint(
        expr: &ast::TypeExpr,
        ctx: &mut TypeExprContext,
    ) -> Result<Self, ImportError> {
        let expr = TypeExpr::new(expr, &mut ctx.expect_only_type().with_typecheck())?;

        Ok(Self {
            ty: Rc::new(expr),
            flags: FieldFlags::IS_CONSTRAINT,
        })
    }

    pub fn new_param(expr: &ast::TypeExpr, ctx: &mut TypeExprContext) -> Result<Self, ImportError> {
        let expr = TypeExpr::new(expr, &mut ctx.expect_only_type().with_typecheck())?;

        Ok(Self {
            ty: Rc::new(expr),
            flags: FieldFlags::empty(),
        })
    }

    pub fn is_known(&self) -> bool {
        self.flags.contains(FieldFlags::IS_KNOWN)
    }
}

bitflags! {
    #[derive(Default, Debug, Clone, Copy, Eq, PartialEq)]
    pub struct FieldFlags: u32 {
        const IS_IMPLICIT = 1 << 0;
        const IS_CONSTRAINT = 1 << 1;
        const IS_KNOWN = 1 << 2;
        const IS_USED = 1 << 3;
    }
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
            ast::TypeExpr::AltNat { span, kind, arg } => Self::new_alt_nat(*kind, arg, span, ctx),
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
            ast::TypeExpr::AnonConstructor { .. } => todo!(),
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

        let value = match ctx.scope.lookup_mut(ident) {
            None if negate => {
                return Err(ImportError::TypeMismatch {
                    span: *span,
                    message: "field identifier expected",
                });
            }
            None => ctx.scope.register_type(ident, Default::default()),
            Some(value) => value,
        };

        Ok(match value {
            SymbolValue::Type { type_id, ty } => {
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

                for (arg, flags) in std::iter::zip(&args, &mut ty.args) {
                    if arg.is_negated() {
                        negate = true; // Type can only be negated by its arguments

                        if flags.contains(TypeArgFlags::IS_POS) {
                            return Err(ImportError::TypeMismatch {
                                span: arg.span,
                                message: "passed an argument of incorrect polarity",
                            });
                        }
                        *flags |= TypeArgFlags::IS_NEG;
                    }

                    arg.ensure_no_typecheck()?;

                    if arg.is_nat() {
                        *flags |= TypeArgFlags::IS_NAT;
                    } else {
                        *flags |= TypeArgFlags::IS_TYPE;

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
                    value: TypeExprValue::Apply { type_id, args },
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

    fn new_type(span: &parser::Span) -> Self {
        Self {
            span: *span,
            value: TypeExprValue::Type,
            flags: TypeExprFlags::empty(),
        }
    }

    fn new_nat(span: &parser::Span) -> Self {
        Self {
            span: *span,
            value: TypeExprValue::Nat,
            flags: TypeExprFlags::IS_NAT,
        }
    }

    fn new_alt_nat(
        kind: ast::AltNat,
        arg: &ast::TypeExpr,
        span: &parser::Span,
        ctx: &mut TypeExprContext,
    ) -> Result<Self, ImportError> {
        let arg = Self::new(arg, &mut ctx.expect_only_nat())?;

        if arg.is_negated() {
            return Err(ImportError::TypeMismatch {
                span: arg.span,
                message: "passed an argument of incorrect polarity",
            });
        }

        if !arg.is_nat() {
            return Err(ImportError::TypeMismatch {
                span: arg.span,
                message: "expected natural number",
            });
        }

        arg.ensure_no_typecheck()?;

        Ok(Self {
            span: *span,
            value: TypeExprValue::AltNat {
                kind,
                arg: Rc::new(arg),
            },
            flags: TypeExprFlags::IS_NAT,
        })
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
    AltNat {
        kind: ast::AltNat,
        arg: Rc<TypeExpr>,
    },
    Param {
        index: usize,
    },
    Apply {
        type_id: Symbol,
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

#[derive(Debug)]
pub struct TypeExprContext<'a, 's> {
    pub constructor: &'a mut Constructor,
    pub scope: &'a mut SymbolTableScope<'s>,
    pub allow_nat: bool,
    pub allow_type: bool,
    pub auto_negate: bool,
    pub typecheck: bool,
}

impl<'s> TypeExprContext<'_, 's> {
    fn without_typecheck(&'_ mut self) -> TypeExprContext<'_, 's> {
        let mut res = self.subcontext();
        res.typecheck = false;
        res
    }

    fn with_typecheck(&'_ mut self) -> TypeExprContext<'_, 's> {
        let mut res = self.subcontext();
        res.typecheck = true;
        res
    }

    fn expect_any(&'_ mut self) -> TypeExprContext<'_, 's> {
        let mut res = self.subcontext();
        res.allow_nat = true;
        res.allow_type = true;
        res
    }

    fn expect_only_nat(&'_ mut self) -> TypeExprContext<'_, 's> {
        let mut res = self.subcontext();
        res.allow_nat = true;
        res.allow_type = false;
        res
    }

    fn expect_only_type(&'_ mut self) -> TypeExprContext<'_, 's> {
        let mut res = self.subcontext();
        res.allow_nat = false;
        res.allow_type = true;
        res
    }

    fn subcontext(&'_ mut self) -> TypeExprContext<'_, 's> {
        TypeExprContext {
            constructor: self.constructor,
            scope: self.scope,
            allow_nat: self.allow_nat,
            allow_type: self.allow_type,
            auto_negate: self.auto_negate,
            typecheck: self.typecheck,
        }
    }
}

#[derive(Debug)]
pub struct SymbolTableScope<'a> {
    global: &'a mut GlobalSymbolTable,
    local: LocalSymbolTable,
}

impl SymbolTableScope<'_> {
    pub fn lookup_mut(&mut self, symbol: Symbol) -> Option<SymbolValue<'_>> {
        if let Some(local) = self.local.symbols.get(&symbol) {
            return Some(SymbolValue::Param {
                index: local.index,
                value: local.value.as_ref(),
            });
        }

        self.global
            .symbols
            .get_mut(&symbol)
            .map(|ty| SymbolValue::Type {
                type_id: symbol,
                ty,
            })
    }

    pub fn register_type(&mut self, symbol: Symbol, ty: Box<Type>) -> SymbolValue<'_> {
        let ty = self.global.register_type(symbol, ty);
        SymbolValue::Type {
            type_id: symbol,
            ty,
        }
    }

    pub fn register_param(&mut self, symbol: Symbol, value: LocalSymbol) -> SymbolValue<'_> {
        let local = self.local.register_param(symbol, value);
        SymbolValue::Param {
            index: local.index,
            value: local.value.as_ref(),
        }
    }
}

#[derive(Default, Debug)]
pub struct LocalSymbolTable {
    symbols: FastHashMap<Symbol, LocalSymbol>,
}

impl LocalSymbolTable {
    pub fn lookup(&self, symbol: Symbol) -> Option<&LocalSymbol> {
        self.symbols.get(&symbol)
    }

    pub fn register_param(&mut self, symbol: Symbol, value: LocalSymbol) -> &mut LocalSymbol {
        self.symbols.entry(symbol).or_insert(value)
    }
}

#[derive(Debug, Clone)]
pub struct LocalSymbol {
    pub index: usize,
    pub value: Rc<TypeExpr>,
}

#[derive(Default, Debug)]
pub struct GlobalSymbolTable {
    symbols: FastHashMap<Symbol, Box<Type>>,
}

impl GlobalSymbolTable {
    pub fn begin_scope(&mut self) -> SymbolTableScope<'_> {
        SymbolTableScope {
            global: self,
            local: LocalSymbolTable::default(),
        }
    }

    pub fn lookup(&self, symbol: &Symbol) -> Option<&Type> {
        self.symbols.get(symbol).map(|ty| ty.as_ref())
    }

    pub fn register_type(&mut self, symbol: Symbol, ty: Box<Type>) -> &mut Type {
        self.symbols.entry(symbol).or_insert(ty)
    }
}

pub enum SymbolValue<'a> {
    Type { type_id: Symbol, ty: &'a mut Type },
    Param { index: usize, value: &'a TypeExpr },
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
    fn simple() {
        let input = r###"
        test field:# = Test;
        "###;

        let mut ctx = parser::Context::default();
        let scheme = ast::Scheme::parse(&mut ctx, input).unwrap();

        let mut ctx = Resolver::new(&mut ctx);
        ctx.import(&scheme).unwrap();

        for (symbol, ty) in &ctx.global.symbols {
            let name = ctx.parser_context.resolve_symbol(*symbol).unwrap();
            println!("{name}: {ty:?}");
        }
    }

    #[test]
    fn full_block() {
        let input = include_str!("../test/block.tlb");

        let mut ctx = parser::Context::default();
        let scheme = ast::Scheme::parse(&mut ctx, input).unwrap();

        let mut ctx = Resolver::new(&mut ctx);
        ctx.import(&scheme).unwrap();
    }
}

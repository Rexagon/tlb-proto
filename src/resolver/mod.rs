use std::rc::Rc;

use bitflags::bitflags;

use crate::parser::{self, ast, Symbol};
use crate::util::{BinTrie, BitPfxCollection, FastHashMap, SizeRange};

mod display;

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
        self.global.lookup(symbol)
    }

    pub fn get_type_by_name(&self, name: &str) -> Option<&Type> {
        self.parser_context
            .get_symbol(name)
            .and_then(|symbol| self.get_type(symbol))
    }

    fn def_builtin_types(&mut self) -> Result<(), ImportError> {
        self.def_builtin_type("Any", &[], SizeRange::any(), TypeFlags::empty())?;
        self.def_builtin_type("Cell", &[], SizeRange::exact_refs(1), TypeFlags::empty())?;

        let nat_arg = TypeArgFlags::IS_POS | TypeArgFlags::IS_NAT;
        self.def_builtin_type(
            "int",
            &[nat_arg],
            SizeRange::bits(0..=257),
            TypeFlags::PRODUCES_NAT,
        )?;
        self.def_builtin_type(
            "uint",
            &[nat_arg],
            SizeRange::bits(0..=256),
            TypeFlags::PRODUCES_NAT,
        )?;
        self.def_builtin_type(
            "bits",
            &[nat_arg],
            SizeRange::bits(0..=1023),
            TypeFlags::PRODUCES_NAT,
        )?;

        for i in 0..=257 {
            let name = format!("uint{i}");
            self.def_builtin_type(
                &name[1..],
                &[],
                SizeRange::exact_bits(i),
                TypeFlags::PRODUCES_NAT,
            )?;
            if i <= 256 {
                self.def_builtin_type(
                    &name,
                    &[],
                    SizeRange::exact_bits(i),
                    TypeFlags::PRODUCES_NAT,
                )?;
            }
        }

        for i in 0..=1023 {
            let name = format!("bits{i}");
            self.def_builtin_type(
                &name,
                &[],
                SizeRange::exact_bits(i),
                TypeFlags::PRODUCES_NAT,
            )?;
        }

        Ok(())
    }

    fn def_builtin_type(
        &mut self,
        name: &str,
        args: &[TypeArgFlags],
        size: SizeRange,
        flags: TypeFlags,
    ) -> Result<(), ImportError> {
        let name = self.parser_context.intern_symbol(name);

        let ty = Box::new(Type {
            size,
            constructors: Vec::new(),
            starts_with: BitPfxCollection::all(),
            prefix_trie: Default::default(),
            flags: flags | TypeFlags::BUILTIN,
            args: args.to_vec(),
        });
        self.global.register_type(name, ty);

        Ok(())
    }

    fn def_constructor(&mut self, ast: &ast::Constructor) -> Result<(), ImportError> {
        let mut constructor = Box::new(Constructor {
            name: ast.name.map(|name| name.ident),
            tag: match &ast.tag {
                Some(tag) => ConstructorTag {
                    bits: tag.bits,
                    value: tag.value,
                },
                None => ConstructorTag::new_invalid(),
            },
            flags: ConstructorFlags::empty(),
            size: SizeRange::any(),
            starts_with: Default::default(),
            fields: Vec::with_capacity(ast.fields.len()),
            output_type: ast.output_type.ident,
            output_type_args: Vec::with_capacity(ast.output_type_args.len()),
        });

        let ctx = &mut TypeExprContext {
            constructor: &mut constructor,
            scope: &mut self.global.begin_scope(),
            allow_nat: true,
            allow_type: true,
            auto_negate: false,
            typecheck: false,
        };

        // Parse fields list
        let mut field_flags = Vec::with_capacity(ast.fields.len());
        for (field_index, field) in ast.fields.iter().enumerate() {
            let name_ident = match field.name_ident() {
                Some(ident) => ident,
                None => self.parser_context.intern_symbol(format!("_{field_index}")),
            };

            if ctx.scope.local.lookup(name_ident).is_some() {
                return Err(ImportError::TypeMismatch {
                    span: field.span(),
                    message: "redefined field or parameter",
                });
            }

            let parsed_field = match field {
                ast::Field::ImplicitParam { span, ident, ty } => {
                    Field::new_implicit_param(field_index, *ident, *ty, span)
                }
                ast::Field::Constraint { expr, .. } => {
                    Field::new_constraint(field_index, expr, ctx)?
                }
                ast::Field::Param { name, ty, .. } => {
                    Field::new_param(field_index, name.as_ref().map(|n| n.ident), ty, ctx)?
                }
            };

            field_flags.push(parsed_field.flags);

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
        ctx.scope
            .global
            .register_type(ast.output_type.ident, Default::default());

        // Parse output type args
        for ast in &ast.output_type_args {
            let mut ctx = ctx.expect_any();
            ctx.auto_negate = !ast.negate;

            let arg = TypeExpr::new(&ast.ty, &mut ctx)?;

            if !ast.negate {
                arg.bind_value(&mut field_flags, false, false)?;
            } else if !arg.is_nat() {
                return Err(ImportError::TypeMismatch {
                    span: ast.ty.span(),
                    message: "cannot negate a type",
                });
            }

            let const_value = match &arg.value {
                TypeExprValue::IntConst { value } if !ast.negate => Some(*value),
                _ => None,
            };

            ctx.constructor.output_type_args.push(TypeArg {
                ty: Rc::new(arg),
                negate: ast.negate,
                const_value,
            });
        }

        if let Some(ty) = self.global.lookup_mut(ast.output_type.ident) {
            ty.bind_constructor(
                constructor,
                &mut field_flags,
                &ast.span,
                &self.parser_context,
            )?;
        }

        Ok(())
    }
}

#[derive(Debug)]
pub struct Type {
    pub size: SizeRange,
    pub constructors: Vec<Box<Constructor>>,
    pub starts_with: BitPfxCollection,
    pub prefix_trie: BinTrie,
    pub flags: TypeFlags,
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
            args: Vec::new(),
        }
    }
}

impl Type {
    fn bind_constructor(
        &mut self,
        mut constructor: Box<Constructor>,
        field_flags: &mut [FieldFlags],
        span: &parser::Span,
        parser_context: &parser::Context,
    ) -> Result<(), ImportError> {
        // Check type arguments arity
        if self.constructors.is_empty() && self.args.is_empty() {
            self.args
                .resize(constructor.output_type_args.len(), TypeArgFlags::empty());
        } else if self.args.len() != constructor.output_type_args.len() {
            return Err(ImportError::TypeMismatch {
                span: *span,
                message: "parametrized type redefined with different arity",
            });
        }

        // Check type arguments
        let mut has_pos_params = false;
        for (arg, flags) in std::iter::zip(&constructor.output_type_args, &mut self.args) {
            *flags |= if arg.ty.is_nat() {
                TypeArgFlags::IS_NAT
            } else {
                TypeArgFlags::IS_TYPE
            };

            if flags.contains(TypeArgFlags::IS_NAT | TypeArgFlags::IS_TYPE) {
                return Err(ImportError::TypeMismatch {
                    span: arg.ty.span,
                    message: "formal parameter to type has incorrect type",
                });
            }

            *flags |= if arg.negate {
                TypeArgFlags::IS_NEG
            } else {
                TypeArgFlags::IS_POS
            };

            if flags.contains(TypeArgFlags::IS_POS | TypeArgFlags::IS_NEG) {
                return Err(ImportError::TypeMismatch {
                    span: arg.ty.span,
                    message: "formal parameter to type has incorrect polarity",
                });
            }

            if arg.const_value.is_none() {
                *flags |= TypeArgFlags::NON_CONST;
            }

            has_pos_params |= !arg.negate;
        }

        // Check fields
        let mut has_explicit_fields = false;
        for (i, field) in constructor.fields.iter_mut().enumerate() {
            if field.is_constraint() || !field.is_implicit() {
                field.ty.bind_value(field_flags, false, true)?;
                field_flags[i] |= FieldFlags::IS_KNOWN;
            }

            has_explicit_fields |= !field.is_implicit();
            field.flags |= field_flags[i];
        }

        if !has_explicit_fields {
            constructor.flags |= ConstructorFlags::IS_ENUM;
        }

        if !has_explicit_fields && !has_pos_params {
            constructor.flags |= ConstructorFlags::IS_SIMPLE_ENUM;
        }

        // Bind type arguments
        for arg in &constructor.output_type_args {
            if arg.negate {
                arg.ty.bind_value(field_flags, true, false)?;
            }
        }

        // Apply modified field flags and check known fields
        for (field, flags) in std::iter::zip(&mut constructor.fields, field_flags) {
            field.flags |= *flags;

            if !field.is_known() {
                return Err(ImportError::TypeMismatch {
                    span: field.ty.span,
                    message: "field is left unbound",
                });
            }
        }

        // Check constructor name
        if let Some(name) = constructor.name {
            if self.constructors.iter().any(|c| c.name == Some(name)) {
                return Err(ImportError::TypeMismatch {
                    span: *span,
                    message: "constructor redefined",
                });
            }
        }

        // Assign tag
        if !constructor.tag.is_set() {
            constructor.tag = if constructor.name.is_some() {
                ConstructorTag {
                    bits: 32,
                    value: self::display::compute_tag(parser_context, &constructor),
                }
            } else {
                ConstructorTag::new_empty()
            };
        }

        self.constructors.push(constructor);
        Ok(())
    }

    pub fn is_builtin(&self) -> bool {
        self.flags.contains(TypeFlags::BUILTIN)
    }

    pub fn produces_nat(&self) -> bool {
        self.flags.contains(TypeFlags::PRODUCES_NAT)
    }
}

bitflags! {
    #[derive(Default, Debug, Clone, Copy, Eq, PartialEq)]
    pub struct TypeFlags: u32 {
        const BUILTIN = 1 << 0;
        const PRODUCES_NAT = 1 << 1;
    }
}

#[derive(Debug)]
pub struct TypeArg {
    pub ty: Rc<TypeExpr>,
    pub negate: bool,
    pub const_value: Option<u32>,
}

bitflags! {
    #[derive(Default, Debug, Clone, Copy, Eq, PartialEq)]
    pub struct TypeArgFlags: u32 {
        const IS_TYPE = 1 << 0;
        const IS_NAT = 1 << 1;
        const IS_POS = 1 << 2;
        const IS_NEG = 1 << 3;
        const NON_CONST = 1 << 4;
    }
}

#[derive(Debug)]
pub struct Constructor {
    pub name: Option<Symbol>,
    pub tag: ConstructorTag,
    pub flags: ConstructorFlags,
    pub size: SizeRange,
    pub starts_with: BitPfxCollection,
    pub fields: Vec<Field>,
    pub output_type: Symbol,
    pub output_type_args: Vec<TypeArg>,
}

impl Constructor {
    pub fn is_isomorphic_to(&self, other: &Self, allow_other_names: bool) -> bool {
        if self.name != other.name
            || self.tag != other.tag
            || self.fields.len() != other.fields.len()
            || self.output_type_args.len() != other.output_type_args.len()
        {
            return false;
        }

        for (field, other_field) in std::iter::zip(&self.fields, &other.fields) {
            if !field.is_isomorphic_to(other_field, allow_other_names) {
                return false;
            }
        }

        for (arg, other_arg) in std::iter::zip(&self.output_type_args, &other.output_type_args) {
            if arg.ty != other_arg.ty {
                return false;
            }
        }

        true
    }
}

bitflags! {
    #[derive(Default, Debug, Clone, Copy, Eq, PartialEq)]
    pub struct ConstructorFlags: u32 {
        const IS_ENUM = 1 << 0;
        const IS_SIMPLE_ENUM = 1 << 1;
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct ConstructorTag {
    pub bits: u8,
    pub value: u32,
}

impl ConstructorTag {
    const fn new_invalid() -> Self {
        Self {
            bits: u8::MAX,
            value: 0,
        }
    }

    const fn new_empty() -> Self {
        Self { bits: 0, value: 0 }
    }

    const fn is_set(&self) -> bool {
        self.bits != u8::MAX
    }

    #[allow(unused)]
    const fn as_u64(&self) -> u64 {
        let termination_bit = 1 << (63 - self.bits);
        if self.bits == 0 {
            termination_bit
        } else {
            ((self.value as u64) << (64 - self.bits)) | termination_bit
        }
    }
}

#[derive(Debug)]
pub struct Field {
    pub index: usize,
    pub name: Option<Symbol>,
    pub ty: Rc<TypeExpr>,
    pub flags: FieldFlags,
}

impl Field {
    pub fn new_implicit_param(
        index: usize,
        name: Symbol,
        ty: ast::GenericType,
        span: &parser::Span,
    ) -> Self {
        Self {
            index,
            name: Some(name),
            ty: Rc::new(match ty {
                ast::GenericType::Type => TypeExpr::new_type(span),
                ast::GenericType::Nat => TypeExpr::new_nat(span),
            }),
            flags: FieldFlags::IS_IMPLICIT,
        }
    }

    pub fn new_constraint(
        index: usize,
        expr: &ast::TypeExpr,
        ctx: &mut TypeExprContext,
    ) -> Result<Self, ImportError> {
        let expr = TypeExpr::new(expr, &mut ctx.expect_only_type().with_typecheck())?;

        Ok(Self {
            index,
            name: None,
            ty: Rc::new(expr),
            flags: FieldFlags::IS_CONSTRAINT,
        })
    }

    pub fn new_param(
        index: usize,
        ident: Option<Symbol>,
        expr: &ast::TypeExpr,
        ctx: &mut TypeExprContext,
    ) -> Result<Self, ImportError> {
        let expr = TypeExpr::new(expr, &mut ctx.expect_only_type().with_typecheck())?;

        Ok(Self {
            index,
            name: ident,
            ty: Rc::new(expr),
            flags: FieldFlags::empty(),
        })
    }

    pub fn is_isomorphic_to(&self, other: &Self, allow_other_names: bool) -> bool {
        self.index == other.index
            && self.is_implicit() == other.is_implicit()
            && self.is_constraint() == other.is_constraint()
            && (allow_other_names || self.name == other.name)
            && self.ty == other.ty
    }

    pub fn is_constraint(&self) -> bool {
        self.flags.contains(FieldFlags::IS_CONSTRAINT)
    }

    pub fn is_implicit(&self) -> bool {
        self.flags.contains(FieldFlags::IS_IMPLICIT)
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

                if ty.constructors.is_empty() && ty.args.is_empty() {
                    ty.args.resize(args.len(), TypeArgFlags::empty());
                } else if ty.args.len() != args.len() {
                    return Err(ImportError::TypeMismatch {
                        span: *span,
                        message: "type applied with incorrent number of arguments",
                    });
                }

                for (arg, flags) in std::iter::zip(&args, &mut ty.args) {
                    if arg.is_negated() {
                        negate = true; // Type can only be marked as negated by its arguments

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
                if ty.produces_nat() {
                    flags |= TypeExprFlags::IS_NAT_SUBTYPE;
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

                let mut flags = TypeExprFlags::empty();
                if negate {
                    flags |= TypeExprFlags::NEGATED;
                }
                if ty.is_nat_subtype() {
                    flags |= TypeExprFlags::IS_NAT;
                }

                if !ty.is_nat_subtype() && !matches!(&ty.value, TypeExprValue::Type) {
                    println!("TYPE: {ty:#?}");
                    return Err(ImportError::TypeMismatch {
                        span: *span,
                        message: "cannot use a field in an expression unless \
                                it is either an integer or a type",
                    });
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
            flags: TypeExprFlags::IS_NAT_SUBTYPE,
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
            flags: TypeExprFlags::IS_NAT_SUBTYPE,
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

        let left_negated = left_ty.is_negated();
        let right_negated = right_ty.is_negated();

        match op {
            ast::ConstraintOp::Eq => {
                if left_negated && right_negated {
                    return Err(ImportError::TypeMismatch {
                        span: *span,
                        message: "cannot equate two expressions of negative polarity",
                    });
                }
            }
            ast::ConstraintOp::Lt | ast::ConstraintOp::Le => {
                if left_negated {
                    return Err(ImportError::TypeMismatch {
                        span: left.span(),
                        message: "passed an argument of incorrect polarity",
                    });
                }
                if right_negated {
                    return Err(ImportError::TypeMismatch {
                        span: right.span(),
                        message: "passed an argument of incorrect polarity",
                    });
                }
            }
        }

        let mut flags = TypeExprFlags::empty();
        if left_negated || right_negated {
            flags |= TypeExprFlags::NEGATED | TypeExprFlags::TYPECHECK_ONLY;
        }

        Ok(Self {
            span: *span,
            value: TypeExprValue::Constraint {
                op: *op,
                left: Rc::new(left_ty),
                right: Rc::new(right_ty),
            },
            flags,
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
                flags: TypeExprFlags::empty(),
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

    pub fn bind_value(
        &self,
        field_flags: &mut [FieldFlags],
        negate: bool,
        typecheck: bool,
    ) -> Result<(), ImportError> {
        // typecheck=true:
        //   value_negated must be false
        // typecheck=false:
        //   negate=false, value_negated=false:
        //     compute expression, compare to value (only for integers)
        //   negate=false, value_negated=true:
        //     compute expression, return it to the "value"
        //   negate=true, value_negated=false:
        //     assign the value to the expression to compare some of the
        //     variables present in the expression

        if typecheck {
            if self.is_nat() {
                return Err(ImportError::TypeMismatch {
                    span: self.span,
                    message: "cannot check type against an integer expression",
                });
            }
            if negate {
                return Err(ImportError::TypeMismatch {
                    span: self.span,
                    message: "cannot compute a value knowing only its type",
                });
            }
        } else {
            self.ensure_no_typecheck()?;
        }

        if negate && self.is_negated() {
            return Err(ImportError::TypeMismatch {
                span: self.span,
                message: "expression has wrong polarity",
            });
        }

        if !typecheck && !self.is_nat() {
            // "true" equality/assignment of type expressions
            if !negate && !self.is_negated() {
                match &self.value {
                    TypeExprValue::Apply { args, .. } if args.is_empty() => {
                        return Err(ImportError::TypeMismatch {
                            span: self.span,
                            message: "use of a global type or an underclared variable",
                        });
                    }
                    _ => {
                        return Err(ImportError::TypeMismatch {
                            span: self.span,
                            message: "cannot check type expressions for equality",
                        })
                    }
                }
            }

            // Available only if the expression is a free variable
            if self.is_negated() && !matches!(&self.value, TypeExprValue::Param { .. }) {
                return Err(ImportError::TypeMismatch {
                    span: self.span,
                    message: "types can be assigned only to free type variables",
                });
            }
        }

        match &self.value {
            TypeExprValue::Type => {
                debug_assert!(!self.is_nat() && !self.is_negated());
            }
            TypeExprValue::Nat => {
                debug_assert!(!self.is_negated() || typecheck);
            }
            TypeExprValue::AltNat { arg, .. } => {
                debug_assert!(!self.is_negated() || typecheck);
                arg.bind_value(field_flags, !arg.is_negated(), false)?;
            }
            TypeExprValue::Param { index } => {
                let field_flags = &mut field_flags[*index];
                if !self.is_negated() || typecheck {
                    if !field_flags.contains(FieldFlags::IS_KNOWN) {
                        return Err(ImportError::TypeMismatch {
                            span: self.span,
                            message: "variable is used before being assigned to",
                        });
                    }
                    *field_flags |= FieldFlags::IS_USED;
                } else if !field_flags.contains(FieldFlags::IS_KNOWN) {
                    *field_flags |= FieldFlags::IS_KNOWN;
                }
            }
            TypeExprValue::Apply { args, .. } => {
                debug_assert!(!self.is_negated() || typecheck);
                for arg in args {
                    if !arg.is_negated() {
                        arg.bind_value(field_flags, true, false)?;
                    }
                }
                for arg in args {
                    if arg.is_negated() {
                        arg.bind_value(field_flags, false, false)?;
                    }
                }
            }
            TypeExprValue::Add { left, right } => {
                debug_assert!(self.is_nat() && (!left.is_negated() || !right.is_negated()));
                left.bind_value(field_flags, !left.is_negated() && self.is_negated(), false)?;
                right.bind_value(field_flags, !right.is_negated() && self.is_negated(), false)?;
            }
            TypeExprValue::GetBit { field, bit } => {
                debug_assert!(self.is_nat() && !field.is_negated() && !bit.is_negated());
                debug_assert!(!self.is_negated());
                field.bind_value(field_flags, false, false)?;
                bit.bind_value(field_flags, false, false)?;
            }
            TypeExprValue::MulConst { right, .. } => {
                debug_assert!(self.is_nat() && self.is_negated() == right.is_negated());
                right.bind_value(field_flags, negate, false)?;
            }
            TypeExprValue::IntConst { .. } => {
                debug_assert!(self.is_nat() && !self.is_negated());
            }
            TypeExprValue::Tuple { count, item }
            | TypeExprValue::CondType {
                cond: count,
                value: item,
            } => {
                debug_assert!(!self.is_negated() && !count.is_negated() && !item.is_negated());
                debug_assert!(count.is_nat());
                debug_assert!(!item.is_nat());
                count.bind_value(field_flags, true, false)?;
                item.bind_value(field_flags, true, false)?;
            }
            TypeExprValue::Ref { value } => {
                value.bind_value(field_flags, negate, typecheck)?;
            }
            TypeExprValue::Constraint { op, left, right } => {
                let is_negated = self.is_negated();
                match op {
                    ast::ConstraintOp::Eq => {
                        debug_assert!(is_negated == (left.is_negated() || right.is_negated()));
                        left.bind_value(field_flags, !left.is_negated() && is_negated, false)?;
                        right.bind_value(field_flags, !right.is_negated() && is_negated, false)?;
                    }
                    ast::ConstraintOp::Le | ast::ConstraintOp::Lt => {
                        debug_assert!(!is_negated || typecheck);
                        for arg in &[left, right] {
                            if !arg.is_negated() {
                                arg.bind_value(field_flags, true, false)?;
                            }
                        }
                        for arg in &[left, right] {
                            if arg.is_negated() {
                                arg.bind_value(field_flags, false, false)?;
                            }
                        }
                    }
                }
            }
        }

        Ok(())
    }

    pub fn is_nat(&self) -> bool {
        self.flags.contains(TypeExprFlags::IS_NAT)
    }

    pub fn is_nat_subtype(&self) -> bool {
        self.flags.contains(TypeExprFlags::IS_NAT_SUBTYPE)
    }

    pub fn is_negated(&self) -> bool {
        self.flags.contains(TypeExprFlags::NEGATED)
    }

    pub fn ensure_no_typecheck(&self) -> Result<(), ImportError> {
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

impl Eq for TypeExpr {}
impl PartialEq for TypeExpr {
    fn eq(&self, other: &Self) -> bool {
        match (&self.value, &other.value) {
            (TypeExprValue::Type, TypeExprValue::Type)
            | (TypeExprValue::Nat, TypeExprValue::Nat) => true,

            (
                TypeExprValue::AltNat { kind, arg },
                TypeExprValue::AltNat {
                    kind: other_kind,
                    arg: other_arg,
                },
            ) => kind == other_kind && arg == other_arg,
            (TypeExprValue::Param { index }, TypeExprValue::Param { index: other_index }) => {
                index == other_index
            }
            (
                TypeExprValue::Apply { type_id, args },
                TypeExprValue::Apply {
                    type_id: other_type_id,
                    args: other_args,
                },
            ) => type_id == other_type_id && args == other_args,
            (
                TypeExprValue::Add { left, right },
                TypeExprValue::Add {
                    left: other_left,
                    right: other_right,
                },
            ) => left == other_left && right == other_right,
            (
                TypeExprValue::GetBit { field, bit },
                TypeExprValue::GetBit {
                    field: other_field,
                    bit: other_bit,
                },
            ) => field == other_field && bit == other_bit,
            (
                TypeExprValue::MulConst { left, right },
                TypeExprValue::MulConst {
                    left: other_left,
                    right: other_right,
                },
            ) => left == other_left && right == other_right,
            (TypeExprValue::IntConst { value }, TypeExprValue::IntConst { value: other_value }) => {
                value == other_value
            }
            (
                TypeExprValue::Tuple { count, item },
                TypeExprValue::Tuple {
                    count: other_count,
                    item: other_item,
                },
            ) => count == other_count && item == other_item,
            (TypeExprValue::Ref { value }, TypeExprValue::Ref { value: other_value }) => {
                value == other_value
            }
            (
                TypeExprValue::CondType { cond, value },
                TypeExprValue::CondType {
                    cond: other_cond,
                    value: other_value,
                },
            ) => cond == other_cond && value == other_value,
            (
                TypeExprValue::Constraint { op, left, right },
                TypeExprValue::Constraint {
                    op: other_op,
                    left: other_left,
                    right: other_right,
                },
            ) => op == other_op && left == other_left && right == other_right,
            _ => false,
        }
    }
}

bitflags! {
    #[derive(Default, Debug, Clone, Copy, Eq, PartialEq)]
    pub struct TypeExprFlags: u32 {
        /// Expression can only be used in type-checking context.
        const TYPECHECK_ONLY = 1 << 0;
        /// An integer expression.
        const IS_NAT = 1 << 1;
        /// A type that produces integer expressions.
        const IS_NAT_SUBTYPE = 1 << 2;
        /// Expression is linearly negative.
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

    pub fn lookup(&self, symbol: Symbol) -> Option<&Type> {
        self.symbols.get(&symbol).map(|ty| ty.as_ref())
    }

    pub fn lookup_mut(&mut self, symbol: Symbol) -> Option<&mut Type> {
        self.symbols.get_mut(&symbol).map(|ty| ty.as_mut())
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

impl ImportError {
    pub fn span(&self) -> &parser::Span {
        match self {
            ImportError::TypeMismatch { span, .. } => span,
            ImportError::IntOverflow { span } => span,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple() {
        let input = include_str!("../test/hashmap.tlb");

        let mut ctx = parser::Context::default();
        let scheme = ast::Scheme::parse(&mut ctx, input).unwrap();

        let mut ctx = Resolver::new(&mut ctx);
        if let Err(e) = ctx.import(&scheme) {
            let span = e.span();
            let text = &input[span.start..span.end];
            panic!("{e:?}, text: {text}");
        }

        for (symbol, ty) in &ctx.global.symbols {
            if ty.is_builtin() {
                continue;
            }

            let name = ctx.parser_context.resolve_symbol(*symbol).unwrap();
            println!("{name}: {ty:#?}");
        }
    }

    #[test]
    fn full_block() {
        let input = include_str!("../test/block.tlb");

        let mut ctx = parser::Context::default();
        let scheme = ast::Scheme::parse(&mut ctx, input).unwrap();

        let mut ctx = Resolver::new(&mut ctx);
        if let Err(e) = ctx.import(&scheme) {
            let span = e.span();
            let text = &input[span.start..span.end];
            panic!("{e:?}, text: {text}");
        }
    }
}

use std::rc::Rc;

use bitflags::bitflags;

use crate::parser::{self, ast, Symbol};
use crate::util::{
    AbstractNat, AdmissibilityInfo, BinTrie, BitPfxCollection, FastHashMap, SizeRange,
};

mod define;
mod display;

pub struct Resolver<'a> {
    global: GlobalSymbolTable,
    parser_context: &'a mut parser::ParserContext,
}

impl<'a> Resolver<'a> {
    pub fn new(parser_context: &'a mut parser::ParserContext) -> Self {
        let mut res = Self {
            global: Default::default(),
            parser_context,
        };
        res.define_builtin_types().unwrap();
        res
    }

    pub fn import(&mut self, scheme: &ast::Scheme) -> Result<(), ImportError> {
        for ast in &scheme.constructors {
            self.define_constructor(ast)?;
        }

        for ty in self.global.symbols.values_mut() {
            ty.compute_admissible_params();
        }

        let mut type_prefixes =
            FastHashMap::with_capacity_and_hasher(self.global.symbols.len(), Default::default());

        let mut begins_with_changed = true;
        while begins_with_changed {
            begins_with_changed = false;
            for (type_id, ty) in self.global.symbols.iter_mut() {
                begins_with_changed |=
                    ty.compute_constructor_prefixes(*type_id, &mut type_prefixes);
            }
        }

        for (type_id, begins_with) in type_prefixes {
            if let Some(ty) = self.global.lookup_mut(type_id) {
                ty.begins_with = begins_with;
            }
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

    fn define_builtin_types(&mut self) -> Result<(), ImportError> {
        self.define_builtin_type("Any", &[], SizeRange::any(), TypeFlags::empty())?;
        self.define_builtin_type("Cell", &[], SizeRange::exact_refs(1), TypeFlags::empty())?;

        let nat_arg = TypeArgFlags::IS_POS | TypeArgFlags::IS_NAT;
        self.define_builtin_type(
            "int",
            &[nat_arg],
            SizeRange::bits(0..=257),
            TypeFlags::PRODUCES_NAT,
        )?;
        self.define_builtin_type(
            "uint",
            &[nat_arg],
            SizeRange::bits(0..=256),
            TypeFlags::PRODUCES_NAT,
        )?;
        self.define_builtin_type(
            "bits",
            &[nat_arg],
            SizeRange::bits(0..=1023),
            TypeFlags::PRODUCES_NAT,
        )?;

        for i in 0..=257 {
            let name = format!("uint{i}");
            self.define_builtin_type(
                &name[1..],
                &[],
                SizeRange::exact_bits(i),
                TypeFlags::PRODUCES_NAT,
            )?;
            if i <= 256 {
                self.define_builtin_type(
                    &name,
                    &[],
                    SizeRange::exact_bits(i),
                    TypeFlags::PRODUCES_NAT,
                )?;
            }
        }

        for i in 0..=1023 {
            let name = format!("bits{i}");
            self.define_builtin_type(
                &name,
                &[],
                SizeRange::exact_bits(i),
                TypeFlags::PRODUCES_NAT,
            )?;
        }

        Ok(())
    }

    fn define_builtin_type(
        &mut self,
        name: &str,
        args: &[TypeArgFlags],
        size: SizeRange,
        flags: TypeFlags,
    ) -> Result<(), ImportError> {
        define::builtin_type(
            &mut self.global,
            &mut self.parser_context,
            name,
            args,
            size,
            flags,
        )
    }

    fn define_constructor(&mut self, ast: &ast::Constructor) -> Result<(), ImportError> {
        define::constructor(&mut self.global, &mut self.parser_context, ast)
    }
}

#[derive(Debug)]
pub struct Type {
    pub size: SizeRange,
    pub constructors: Vec<Box<Constructor>>,
    pub begins_with: BitPfxCollection,
    pub prefix_trie: BinTrie,
    pub admissible_params: AdmissibilityInfo,
    pub flags: TypeFlags,
    pub args: Vec<TypeArgFlags>,
}

impl Default for Type {
    fn default() -> Self {
        Self {
            size: SizeRange::any(),
            constructors: Vec::new(),
            begins_with: BitPfxCollection::all(),
            prefix_trie: Default::default(),
            admissible_params: Default::default(),
            flags: TypeFlags::empty(),
            args: Vec::new(),
        }
    }
}

impl Type {
    pub fn is_builtin(&self) -> bool {
        self.flags.contains(TypeFlags::BUILTIN)
    }

    pub fn produces_nat(&self) -> bool {
        self.flags.contains(TypeFlags::PRODUCES_NAT)
    }

    fn compute_admissible_params(&mut self) -> bool {
        let mut admissible = false;
        for constructor in &mut self.constructors {
            admissible |= constructor.compute_admissible_params();
            self.admissible_params
                .combine(&constructor.admissible_params);
        }
        admissible
    }

    fn compute_constructor_prefixes(
        &mut self,
        type_id: Symbol,
        type_prefixes: &mut FastHashMap<Symbol, BitPfxCollection>,
    ) -> bool {
        let mut changed = false;

        for constructor in &mut self.constructors {
            if !constructor.recompute_begins_with(type_prefixes) {
                continue;
            }

            changed |= type_prefixes
                .entry(type_id)
                .or_insert_with(BitPfxCollection::empty)
                .merge(&constructor.begins_with);
        }

        changed
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
pub struct Constructor {
    pub name: Option<Symbol>,
    pub tag: ConstructorTag,
    pub flags: ConstructorFlags,
    pub size: SizeRange,
    pub begins_with: BitPfxCollection,
    pub admissible_params: AdmissibilityInfo,
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

    fn compute_admissible_params(&mut self) -> bool {
        let mut dimension = 0;

        // TODO: add params check
        let mut abstract_params = [AbstractNat::NAN; 4];

        for type_arg in &self.output_type_args {
            if type_arg.negate || !type_arg.ty.is_nat() {
                continue;
            }

            let t = type_arg.ty.abstract_interpret_nat();
            if t.is_nan() {
                self.admissible_params.set_all(false);
                return false;
            }

            abstract_params[dimension] = t;
            dimension += 1;
            if dimension == 4 {
                break;
            }
        }

        while dimension > 0 && abstract_params[dimension - 1].is_any() {
            dimension -= 1;
        }

        if dimension == 0 {
            self.admissible_params.set_all(true);
        } else {
            self.admissible_params
                .set_by_pattern(&abstract_params[..dimension]);
        }

        true
    }

    fn recompute_begins_with(
        &mut self,
        type_prefixes: &mut FastHashMap<Symbol, BitPfxCollection>,
    ) -> bool {
        // Search for the first field
        for field in &self.fields {
            if field.is_implicit() || field.is_constraint() {
                continue;
            }

            match &field.ty.value {
                // Skip references
                TypeExprValue::Ref { .. } => continue,
                // Combine the first field prefix with tag to get the prefix
                TypeExprValue::Apply { type_id, .. } => match type_prefixes.get(type_id) {
                    Some(begins_with) => {
                        let mut field_prefix = begins_with.clone();
                        field_prefix.prepend(self.tag.as_u64());
                        return self.begins_with.merge(&field_prefix);
                    }
                    None => break,
                },
                _ => break,
            }
        }

        // Fallback to the tag
        let tag_prefix = BitPfxCollection::new(self.tag.as_u64());
        self.begins_with.merge(&tag_prefix)
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
    pub fn abstract_interpret_nat(&self) -> AbstractNat {
        if !self.is_nat() || self.flags.contains(TypeExprFlags::TYPECHECK_ONLY) {
            return AbstractNat::NAN;
        }

        match &self.value {
            TypeExprValue::Add { left, right } => {
                left.abstract_interpret_nat() + right.abstract_interpret_nat()
            }
            TypeExprValue::GetBit { field, bit } => field
                .abstract_interpret_nat()
                .get_bit(bit.abstract_interpret_nat()),
            TypeExprValue::MulConst { left, right } => {
                AbstractNat::new(*left) * right.abstract_interpret_nat()
            }
            TypeExprValue::IntConst { value } => AbstractNat::new(*value),
            _ => AbstractNat::ANY,
        }
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

impl PartialEq for TypeExpr {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.value.eq(&other.value)
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

impl Eq for TypeExprValue {}
impl PartialEq for TypeExprValue {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Type, Self::Type) | (Self::Nat, Self::Nat) => true,

            (
                Self::AltNat { kind, arg },
                Self::AltNat {
                    kind: other_kind,
                    arg: other_arg,
                },
            ) => kind == other_kind && arg == other_arg,
            (Self::Param { index }, Self::Param { index: other_index }) => index == other_index,
            (
                Self::Apply { type_id, args },
                Self::Apply {
                    type_id: other_type_id,
                    args: other_args,
                },
            ) => type_id == other_type_id && args == other_args,
            (
                Self::Add { left, right },
                Self::Add {
                    left: other_left,
                    right: other_right,
                },
            ) => left == other_left && right == other_right,
            (
                Self::GetBit { field, bit },
                Self::GetBit {
                    field: other_field,
                    bit: other_bit,
                },
            ) => field == other_field && bit == other_bit,
            (
                Self::MulConst { left, right },
                Self::MulConst {
                    left: other_left,
                    right: other_right,
                },
            ) => left == other_left && right == other_right,
            (Self::IntConst { value }, Self::IntConst { value: other_value }) => {
                value == other_value
            }
            (
                Self::Tuple { count, item },
                Self::Tuple {
                    count: other_count,
                    item: other_item,
                },
            ) => count == other_count && item == other_item,
            (Self::Ref { value }, Self::Ref { value: other_value }) => value == other_value,
            (
                Self::CondType { cond, value },
                Self::CondType {
                    cond: other_cond,
                    value: other_value,
                },
            ) => cond == other_cond && value == other_value,
            (
                Self::Constraint { op, left, right },
                Self::Constraint {
                    op: other_op,
                    left: other_left,
                    right: other_right,
                },
            ) => op == other_op && left == other_left && right == other_right,
            _ => false,
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
    use std::collections::BTreeMap;

    use super::*;

    #[test]
    fn simple() {
        let input = include_str!("../test/hashmap.tlb");
        // let input = r##"
        // a$111 {x:#} test:# = WithGuard (2 * x);
        // b$110 {x:#} test:# = WithGuard (2 * x + 1);
        // "##;

        let mut ctx = parser::ParserContext::default();
        let scheme = ast::Scheme::parse(&mut ctx, input).unwrap();

        let mut ctx = Resolver::new(&mut ctx);
        if let Err(e) = ctx.import(&scheme) {
            let span = e.span();
            let text = &input[span.start..span.end];
            panic!("{e:?}, text: {text}");
        }

        let sorted = ctx.global.symbols.into_iter().collect::<BTreeMap<_, _>>();

        for (symbol, ty) in sorted {
            if ty.is_builtin() {
                continue;
            }

            let name = ctx.parser_context.resolve_symbol(symbol).unwrap();
            println!("{name}: {ty:#?}");
        }
    }

    #[test]
    fn full_block() {
        let input = include_str!("../test/block.tlb");

        let mut ctx = parser::ParserContext::default();
        let scheme = ast::Scheme::parse(&mut ctx, input).unwrap();

        let mut ctx = Resolver::new(&mut ctx);
        if let Err(e) = ctx.import(&scheme) {
            let span = e.span();
            let text = &input[span.start..span.end];
            panic!("{e:?}, text: {text}");
        }
    }
}

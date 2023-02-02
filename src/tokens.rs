#[derive(Debug, Clone)]
pub struct Scheme<'a> {
    /// Constructor declarations.
    pub declarations: Vec<Constructor<'a>>,
}

/// Object declaration.
#[derive(Debug, Clone)]
pub struct Constructor<'a> {
    /// Optional constructor name.
    pub name: Option<&'a str>,
    /// Constructor id.
    pub id: Option<ConstructorId>,
    /// Type arguments.
    pub generics: Vec<Generic<'a>>,
    /// Field groups.
    pub fields: Vec<FieldGroupItem<'a>>,
    /// Output type.
    pub output_type: (&'a str, Vec<TypeExpr<'a>>),
}

/// Object constructor id.
#[derive(Debug, Clone)]
pub enum ConstructorId {
    Empty,
    Explicit {
        /// Representation kind.
        radix: ConstructorRadix,
        /// Constructor value.
        value: u32,
        /// Constructor length in bits.
        bits: u8,
    },
}

/// Constructor representation kind.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum ConstructorRadix {
    /// Explicit id in binary base.
    Binary,
    /// Explicit id in hex base.
    Hex,
}

impl From<ConstructorRadix> for u32 {
    fn from(value: ConstructorRadix) -> Self {
        match value {
            ConstructorRadix::Binary => 2,
            ConstructorRadix::Hex => 16,
        }
    }
}

/// Object type argument.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Generic<'a> {
    /// Type argument name.
    pub ident: &'a str,
    /// Argument type.
    pub ty: GenericType,
}

/// Generic argument type.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum GenericType {
    /// Unsigned integer type.
    Nat,
    /// Type-level type.
    Type,
}

/// Object field group item.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum FieldGroupItem<'a> {
    /// Object field.
    Field(Field<'a>),
    /// Type guard used to check field values.
    Guard(GuardExpr<'a>),
    /// A group of fields in the child cell.
    ChildCell(Vec<FieldGroupItem<'a>>),
}

/// Object field.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Field<'a> {
    /// Optional field name.
    pub ident: Option<&'a str>,
    /// Optional field condition.
    pub condition: Option<FieldCondition<'a>>,
    /// Field type.
    pub ty: TypeExpr<'a>,
}

/// Flags bit and identifier for conditional fields.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct FieldCondition<'a> {
    /// Identifier of the numeric field with flags.
    pub ident: &'a str,
    /// Bit number in the flags field.
    pub bit: u16,
}

/// Type expression.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum TypeExpr<'a> {
    /// Integer constant.
    ///
    /// ```text
    /// test field:123 = Test;
    /// ```
    Const(u32),
    /// 32-bit unsigned integer type.
    ///
    /// ```text
    /// test field:# = Test;
    /// ```
    Nat,
    /// Unsigned integer type with bits info.
    ///
    /// ```text
    /// test field:(## 10) = Test;
    /// test field:(#<= 10) = Test;
    /// test field:(#< 10) = Test;
    /// ```
    AltNat(AltNat<'a>),
    /// Expression with integer values.
    ///
    /// ```text
    /// test {n:#} field:(n + 1) = Test;
    /// ```
    NatExpr(NatExpr<'a>),
    /// Type identifier with type parameters.
    ///
    /// ```text
    /// test {X:Type} field:(HashMap 64 X) = Test;
    /// ```
    Ident(&'a str, Vec<TypeExpr<'a>>),
    /// Type serialized into a separate cell.
    ///
    /// ```text
    /// test field:^(## 64) = Test;
    /// ```
    ChildCell(Box<TypeExpr<'a>>),
}

/// Integer with explicit bit representation.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum AltNat<'a> {
    /// Integer with the fixed number of bits, `(## n)`.
    Width(NatValue<'a>),
    /// Integer with at most the specified number of bits, `(#<= n)`.
    Leq(NatValue<'a>),
    /// Integer with less bits than specified, `(#< n)`.
    Less(NatValue<'a>),
}

/// Integer value.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum NatValue<'a> {
    /// Integer constant.
    Const(u32),
    /// Type or field identifier.
    Ident(&'a str),
}

/// Simple expression with integer operands.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct NatExpr<'a> {
    /// Type or field identifier.
    pub left: NatValue<'a>,
    /// Type or field identifier.
    pub right: NatValue<'a>,
    /// Binary operator.
    pub op: NatOperator,
}

/// Binary operator for integers.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum NatOperator {
    /// `+`
    Add,
    /// `-`
    Sub,
    /// `*`
    Mul,
    /// `/`
    Div,
}

/// Guard expression used to add checks to the parsed fields.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct GuardExpr<'a> {
    /// Type or field identifier.
    pub left: NatValue<'a>,
    /// Type or field identifier.
    pub right: NatValue<'a>,
    /// Comparison operator.
    pub op: GuardOperator,
}

/// Comparison operator used in guard expression.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum GuardOperator {
    /// `<`
    Lt,
    /// `<=`
    Le,
    /// `=`
    Eq,
    /// `>=`
    Ge,
    /// `>`
    Gt,
}

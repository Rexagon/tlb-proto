use crate::parser::Symbol;

#[derive(Debug, Clone)]
pub struct Scheme {
    /// Constructor declarations.
    pub declarations: Vec<Constructor>,
}

/// Object declaration.
#[derive(Debug, Clone)]
pub struct Constructor {
    /// Optional constructor name.
    pub name: Option<Symbol>,
    /// Constructor tag.
    pub tag: ConstructorTag,
    /// Type arguments.
    pub generics: Vec<Generic>,
    /// Field groups.
    pub fields: Vec<FieldGroupItem>,
    /// Output type.
    pub output_type: (Symbol, Vec<TypeExpr>),
}

/// Object constructor tag.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum ConstructorTag {
    Empty,
    Explicit {
        /// Constructor value.
        value: u32,
        /// Constructor length in bits.
        bits: u8,
    },
}

/// Object type argument.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Generic {
    /// Type argument name.
    pub ident: Symbol,
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

impl std::fmt::Display for GenericType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Nat => "#",
            Self::Type => "Type",
        })
    }
}

/// Object field group item.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum FieldGroupItem {
    /// Object field.
    Field(Field),
    /// Field constraint used to check field values.
    Constraint(ConstraintExpr),
    /// A group of fields in the child cell.
    ChildCell(Vec<FieldGroupItem>),
}

/// Object field.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Field {
    /// Optional field name.
    pub ident: Option<Symbol>,
    /// Optional field condition.
    pub condition: Option<FieldCondition>,
    /// Field type.
    pub ty: TypeExpr,
}

/// Flags bit and identifier for conditional fields.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct FieldCondition {
    /// Identifier of the numeric field with flags.
    pub ident: Symbol,
    /// Bit number in the flags field.
    pub bit: u16,
}

/// Type expression.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum TypeExpr {
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
    AltNat(AltNat),
    /// Expression with integer values.
    ///
    /// ```text
    /// test {n:#} field:(n + 1) = Test;
    /// ```
    NatExpr(NatExpr),
    /// Type identifier with type parameters.
    ///
    /// ```text
    /// test {X:Type} field:(HashMap 64 X) = Test;
    /// ```
    Ident(Symbol, Vec<TypeExpr>),
    /// Type serialized into a separate cell.
    ///
    /// ```text
    /// test field:^(## 64) = Test;
    /// ```
    ChildCell(Box<TypeExpr>),
}

/// Integer with explicit bit representation.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum AltNat {
    /// Integer with the fixed number of bits, `(## n)`.
    Width(NatValue),
    /// Integer with at most the specified number of bits, `(#<= n)`.
    Leq(NatValue),
    /// Integer with less bits than specified, `(#< n)`.
    Less(NatValue),
}

/// Integer value.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum NatValue {
    /// Integer constant.
    Const(u32),
    /// Type or field identifier.
    Ident(Symbol),
}

impl NatValue {
    /// Returns `true` if the value is constant.
    pub fn is_const(&self) -> bool {
        matches!(self, Self::Const(_))
    }
}

/// Simple expression with integer operands.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct NatExpr {
    /// Type or field identifier.
    pub left: NatValue,
    /// Type or field identifier.
    pub right: NatValue,
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
}

impl std::fmt::Display for NatOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
        })
    }
}

/// Constraint expression used to add checks to the parsed fields.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct ConstraintExpr {
    /// Type or field identifier.
    pub left: NatValue,
    /// Type or field identifier.
    pub right: NatValue,
    /// Comparison operator.
    pub op: ConstraintOperator,
}

/// Comparison operator used in constraint expression.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum ConstraintOperator {
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

impl std::fmt::Display for ConstraintOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Eq => "=",
            Self::Ge => ">=",
            Self::Gt => ">",
        })
    }
}

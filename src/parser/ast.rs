//! ```text
//! constructor = ( ident | _ ) field-list = Ident ( T )* ;
//!
//! T = ( E ) | [ {field-def} ] | id | ~id | num | ^T
//!
//! expr97 = T[.T]
//! expr95 = expr97 ? T
//! expr90 = expr90 * expr90
//! expr20 = expr30 + expr30
//! expr10 = expr20 | expr20 = expr20 | expr20 < expr20 | expr20 <= expr20 | ...
//! E = expr10
//!
//! type-expr = expr95
//!
//! field-list = ( { implicit-param } | { constraint } | param )*
//!
//! constraint = expr
//! implicit-param = ident : # | ident : Type
//! param = [ ( ident | _ ) : ] type-expr
//! ```
use crate::parser::{Span, Symbol};

#[derive(Debug, Clone)]
pub struct Scheme {
    /// Constructor declarations.
    pub constructors: Vec<Constructor>,
}

/// Object declaration.
#[derive(Debug, Clone)]
pub struct Constructor {
    /// Source location.
    pub span: Span,
    /// Optional constructor name.
    pub name: Option<Name>,
    /// Constructor tag.
    pub tag: Option<ConstructorTag>,
    /// Field groups.
    pub fields: Vec<Field>,
    /// Output type.
    pub output_type: Name,
    /// Type arguments for the output type.
    pub output_type_args: Vec<OutputTypeExpr>,
}

/// Object constructor tag.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ConstructorTag {
    /// Source location.
    pub span: Span,
    /// Constructor length in bits.
    pub bits: u8,
    /// Constructor value.
    pub value: u32,
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

/// Object field.
#[derive(Debug, Clone)]
pub enum Field {
    ImplicitParam {
        /// Source location.
        span: Span,
        /// Type argument name.
        ident: Symbol,
        /// Argument type.
        ty: GenericType,
    },
    Constraint {
        /// Source location.
        span: Span,
        /// Constraint expression.
        expr: Box<TypeExpr>,
    },
    Param {
        /// Source location.
        span: Span,
        /// Optional field name.
        name: Option<Name>,
        /// Field type.
        ty: Box<TypeExpr>,
    },
    Invalid {
        /// Source location.
        span: Span,
    },
}

impl Field {
    pub fn name_ident(&self) -> Option<Symbol> {
        match self {
            Self::ImplicitParam { ident, .. } => Some(*ident),
            Self::Constraint { .. } | Self::Invalid { .. } => None,
            Self::Param { name, .. } => name.map(|n| n.ident),
        }
    }

    pub fn span(&self) -> Span {
        match self {
            Self::ImplicitParam { span, .. }
            | Self::Constraint { span, .. }
            | Self::Param { span, .. }
            | Self::Invalid { span } => *span,
        }
    }
}

/// Output type expression.
#[derive(Debug, Clone)]
pub struct OutputTypeExpr {
    pub span: Span,
    pub ty: TypeExpr,
    pub negate: bool,
}

/// Type expression.
#[derive(Debug, Clone)]
pub enum TypeExpr {
    /// Integer constant.
    ///
    /// ```text
    /// test field:123 = Test;
    /// ```
    Const { span: Span, value: u32 },

    /// 32-bit unsigned integer type.
    ///
    /// ```text
    /// test field:# = Test;
    /// ```
    Nat { span: Span },

    /// Unsigned integer type with bits info.
    ///
    /// ```text
    /// test field:(## 10) = Test;
    /// test field:(#<= 10) = Test;
    /// test field:(#< 10) = Test;
    /// ```
    AltNat {
        span: Span,
        kind: AltNat,
        arg: Box<TypeExpr>,
    },

    /// Addition expression with integer values.
    ///
    /// ```text
    /// test {n:#} field:(n + 1) = Test;
    /// ```
    Add {
        span: Span,
        left: Box<TypeExpr>,
        right: Box<TypeExpr>,
    },

    /// Multiplication expression with integer values.
    ///
    /// ```text
    /// test {n:#} field:(n * Bit) = Test;
    /// ```
    Mul {
        span: Span,
        left: Box<TypeExpr>,
        right: Box<TypeExpr>,
    },

    /// A constraint expression.
    ///
    /// ```text
    /// test flags:(## 8) { flags <= 1 } = Test;
    /// ```
    Constraint {
        span: Span,
        op: ConstraintOp,
        left: Box<TypeExpr>,
        right: Box<TypeExpr>,
    },

    /// Conditional field.
    ///
    /// ```text
    /// test cond:(## 1) field:cond?Cell = BlockInfo;
    /// ```
    Cond {
        span: Span,
        cond: Box<TypeExpr>,
        value: Box<TypeExpr>,
    },

    /// Get bit from the field.
    ///
    /// ```text
    /// test flags:(## 8) field:flags.0?Cell = BlockInfo;
    /// ```
    GetBit {
        span: Span,
        value: Box<TypeExpr>,
        bit: Box<TypeExpr>,
    },

    /// Type identifier with type parameters.
    ///
    /// ```text
    /// test {X:Type} field:(HashMap 64 X) = Test;
    /// ```
    Apply {
        span: Span,
        ident: Symbol,
        args: Vec<TypeExpr>,
        negate: bool,
    },

    /// Type serialized into a separate cell.
    ///
    /// ```text
    /// test field:^(## 64) = Test;
    /// ```
    Ref { span: Span, value: Box<TypeExpr> },

    /// Anonymous constructor.
    ///
    /// ```text
    /// test [ field:# ] = Test;
    /// ```
    AnonConstructor { span: Span, fields: Vec<Field> },

    /// Type expression is invalid.
    Invalid { span: Span },
}

impl TypeExpr {
    pub fn span(&self) -> Span {
        match self {
            Self::Const { span, .. }
            | Self::Nat { span, .. }
            | Self::AltNat { span, .. }
            | Self::Add { span, .. }
            | Self::Mul { span, .. }
            | Self::Constraint { span, .. }
            | Self::Cond { span, .. }
            | Self::GetBit { span, .. }
            | Self::Apply { span, .. }
            | Self::Ref { span, .. }
            | Self::AnonConstructor { span, .. }
            | Self::Invalid { span } => *span,
        }
    }
}

/// Integer with explicit bit representation.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum AltNat {
    /// Integer with the fixed number of bits, `(## n)`.
    Width,
    /// Integer with at most the specified number of bits, `(#<= n)`.
    Leq,
    /// Integer with less bits than specified, `(#< n)`.
    Less,
}

impl std::fmt::Display for AltNat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Width => "##",
            Self::Leq => "#<=",
            Self::Less => "#<",
        })
    }
}

/// Comparison operator used in constraint expression.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum ConstraintOp {
    /// `<`
    Lt,
    /// `<=`
    Le,
    /// `=`
    Eq,
}

impl std::fmt::Display for ConstraintOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Eq => "=",
        })
    }
}

/// Identifier with source location.
#[derive(Debug, Clone, Copy)]
pub struct Name {
    pub ident: Symbol,
    pub span: Span,
}

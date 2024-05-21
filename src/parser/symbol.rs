use std::num::NonZeroU32;

/// Copyable reference to a string.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Symbol(NonZeroU32);

impl From<string_interner::symbol::SymbolU32> for Symbol {
    fn from(value: string_interner::symbol::SymbolU32) -> Self {
        use string_interner::Symbol;
        Self(NonZeroU32::new(value.to_usize() as u32 + 1).expect("should not fail"))
    }
}

impl From<Symbol> for string_interner::symbol::SymbolU32 {
    fn from(value: Symbol) -> Self {
        use string_interner::symbol::Symbol;
        Self::try_from_usize((value.0.get() - 1) as usize).expect("should not fail")
    }
}

// TODO: inline small strings

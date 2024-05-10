use bitflags::bitflags;
use std::rc::Rc;

use crate::parser::{self, ast, Symbol};
use crate::util::{BinTrie, BitPfxCollection, FastHashMap, FastHashSet, Recurse, SizeRange};

pub struct Context<'a> {
    parser_context: &'a mut parser::Context,
    types: FastHashMap<Symbol, Rc<Type>>,
}

impl<'a> Context<'a> {
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
                    ast::TypeExpr::Apply { name, .. } => {
                        if !self.constructors_by_output.contains_key(&name.ident)
                            && !self.types.contains_key(&name.ident)
                        {
                            self.unresolved.insert(name.ident);
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
        };
        self.types.insert(name, Rc::new(ty));

        Ok(())
    }
}

pub struct Type {
    pub size: SizeRange,
    pub constructors: Vec<Constructor>,
    pub starts_with: BitPfxCollection,
    pub prefix_trie: BinTrie,
    pub flags: TypeFlags,
    pub produces: TypeKind,
}

bitflags! {
    pub struct TypeFlags: u32 {
        const BUILTIN = 1;
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeKind {
    Unit,
    Bool,
    Int,
    Type,
}

pub struct Constructor {
    pub name: Option<Symbol>,
    pub size: SizeRange,
    pub starts_with: BitPfxCollection,
}

enum TypeExpr {
    Type,
    Param {
        ty: ast::GenericType,
        index: usize,
        negate: bool,
    },
    Apply {
        name: Option<Symbol>,
        applied: Rc<TypeExpr>,
    },
    Add {
        left: Rc<TypeExpr>,
        right: Rc<TypeExpr>,
        negated: bool,
    },
    GetBit {
        field: Rc<TypeExpr>,
        bit: Rc<TypeExpr>,
    },
    MulConst {
        left: Rc<TypeExpr>,
        right: u32,
        negated: bool,
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
        item: Rc<TypeExpr>,
    },
}

#[derive(thiserror::Error, Debug)]
pub enum ImportError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn full_block() {
        let input = include_str!("../test/block.tlb");

        let mut ctx = parser::Context::default();
        let scheme = ast::Scheme::parse(&mut ctx, input).unwrap();

        let mut ctx = Context::new(&mut ctx);
        ctx.import(&scheme.constructors).unwrap();
    }
}

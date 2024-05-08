use std::rc::Rc;

use crate::parser::{self, ast, Symbol};
use crate::util::{BinTrie, BitPfxCollection, FastHashMap, SizeRange};

pub struct Context<'a> {
    parser_context: &'a parser::Context,
    types: FastHashMap<Symbol, Rc<Type>>,
}

impl<'a> Context<'a> {
    pub fn new(parser_context: &'a parser::Context) -> Self {
        Self {
            parser_context,
            types: FastHashMap::default(),
        }
    }

    fn import_builtin_types(&mut self) -> Result<(), ImportError> {
        self.add_builtin_type("#", &[], SizeRange::bits(32..=32))?;
        self.add_builtin_type("##", &["#"], SizeRange::bits(0..=32))?;
        self.add_builtin_type("#<", &["#"], SizeRange::bits(0..=32))?;
        self.add_builtin_type("#<=", &["#"], SizeRange::bits(0..=32))?;

        self.add_builtin_type("Any", &[], SizeRange::any())?;
        self.add_builtin_type("Cell", &[], SizeRange::exact_refs(1))?;

        self.add_builtin_type("int", &["#"], SizeRange::bits(0..=257))?;
        self.add_builtin_type("uint", &["#"], SizeRange::bits(0..=256))?;
        self.add_builtin_type("bits", &["#"], SizeRange::bits(0..=1023))?;

        for i in 0..=257 {
            let name = format!("uint{i}");
            self.add_builtin_type(&name[1..], &[], SizeRange::exact_bits(i))?;
            if i <= 256 {
                self.add_builtin_type(&name, &[], SizeRange::exact_bits(i))?;
            }
        }

        for i in 0..=1023 {
            let name = format!("bits{i}");
            self.add_builtin_type(&name, &[], SizeRange::exact_bits(i))?;
        }

        Ok(())
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
                .entry(constructor.output_type)
                .or_default()
                .push(constructor);
        }

        // Start importing constructors

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

    fn add_builtin_type(
        &mut self,
        name: &str,
        args: &[&str],
        size: SizeRange,
    ) -> Result<(), ImportError> {
        todo!()
    }
}

pub struct Type {
    pub size: SizeRange,
    pub constructors: Vec<Constructor>,
    pub starts_with: BitPfxCollection,
    pub prefix_trie: BinTrie,
}

impl Type {
    fn new(ast: &[ast::Constructor]) -> Result<Self, ImportError> {
        let size = SizeRange::default();
        let mut starts_with: BitPfxCollection = BitPfxCollection::default();
        let prefix_trie = BinTrie::default();

        let mut constructors = Vec::with_capacity(ast.len());
        for ctor in ast {
            let ctor = Constructor::new(ctor)?;
            starts_with.merge(&ctor.starts_with);
            constructors.push(ctor);
        }

        Ok(Self {
            size,
            constructors,
            starts_with,
            prefix_trie,
        })
    }
}

pub struct Constructor {
    pub name: Option<Symbol>,
    pub size: SizeRange,
    pub starts_with: BitPfxCollection,
}

impl Constructor {
    fn new(ast: &ast::Constructor) -> Result<Self, ImportError> {
        let size = SizeRange::default();
        let starts_with = BitPfxCollection::default();

        for field in &ast.fields {
            let ast::FieldGroupItem::Field(_field) = field else {
                continue;
            };

            // TODO
        }

        Ok(Self {
            name: ast.name,
            size,
            starts_with,
        })
    }
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

impl TypeExpr {
    fn new(ast: &ast::TypeExpr) -> Result<Self, ImportError> {
        match ast {
            &ast::TypeExpr::Const(value) => Ok(Self::IntConst { value }),
            _ => unimplemented!(),
        }
    }
}

#[derive(thiserror::Error, Debug)]
pub enum ImportError {}

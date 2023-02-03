// use std::collections::HashMap;

// use crate::parser::ast;

// pub enum Opcode<'a> {
//     PushGeneric(GenericValue<'a>),
// }

// pub enum GenericValue<'a> {
//     Const(u32),
//     Type {
//         ident: &'a str,
//         generics: Vec<GenericValue<'a>>,
//     },
// }

// struct Context<'a> {
//     nat_generics: HashMap<&'a str, u32>,
//     type_generics: HashMap<&'a str, &'a str>,
//     nat_fields: HashMap<&'a str, u32>,
// }

// trait Tlb<'a> {
//     fn begin_type(&self, name: &'a str, generics: Vec<GenericValue<'a>>);
// }

// #[derive(Default)]
// struct ConstructorTrie {
//     root: ConstructorTrieNode,
// }

// // impl ConstructorTrie {
// //     fn new(mut constructors: Vec<ast::Constructor>) -> Result<Self, GeneratorError> {
// //         let mut longest_common_prefix = TagPart {
// //             value: u32::MAX,
// //             bits: u8::MAX,
// //         };
// //     }
// // }

// #[derive(Default)]
// struct ConstructorTrieNode {
//     constructors: Vec<(TagPart, ast::Constructor)>,
//     left: Option<Box<ConstructorTrieNode>>,
//     right: Option<Box<ConstructorTrieNode>>,
// }

// #[derive(Default)]
// struct TagPart {
//     value: u32,
//     bits: u8,
// }

// #[derive(Debug, Clone, thiserror::Error)]
// pub enum GeneratorError {
//     #[error("ambiguous constructor")]
//     AmbiguousConstructor,
// }

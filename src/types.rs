use crate::util::{BinTrie, BitPfxCollection};

pub struct Type {
    pub useful_depth: u32,
    pub begins_with: BitPfxCollection,
    pub constructor_trie: BinTrie,
}

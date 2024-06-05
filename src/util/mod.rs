pub use self::abstract_nat::*;
pub use self::admissibility_info::*;
pub use self::bin_trie::*;
pub use self::bit_pfx_collection::*;
pub use self::conflict_graph::*;
pub use self::size_range::*;

mod abstract_nat;
mod admissibility_info;
mod bin_trie;
mod bit_pfx_collection;
mod conflict_graph;
mod size_range;

pub type FastHashMap<K, V> = std::collections::HashMap<K, V, ahash::RandomState>;
pub type FastHashSet<K> = std::collections::HashSet<K, ahash::RandomState>;

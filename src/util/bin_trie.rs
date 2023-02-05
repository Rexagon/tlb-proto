use super::bit_pfx_collection::{lower_bit, BitPfxCollection};

#[derive(Default)]
pub struct BinTrieBuilder {
    root: BinTrieNode,
}

impl BinTrieBuilder {
    pub fn insert(&mut self, path: u64, tag: u64) {
        self.root.insert(path, tag);
    }

    pub fn insert_multiple(&mut self, paths: &BitPfxCollection, tag: u64) {
        if tag != 0 {
            for &path in paths {
                self.root.insert(path, tag);
            }
        }
    }

    pub fn build(mut self) -> BinTrie {
        self.root.update_useful_depth(0);
        BinTrie { root: self.root }
    }
}

#[derive(Default)]
pub struct BinTrie {
    root: BinTrieNode,
}

impl BinTrie {
    pub fn builder() -> BinTrieBuilder {
        BinTrieBuilder::default()
    }

    pub fn get(&self, path: u64) -> Option<u64> {
        Some(self.get_node(path)?.tag)
    }

    fn get_node(&self, path: u64) -> Option<&BinTrieNode> {
        self.root.get_node(path)
    }
}

impl std::fmt::Debug for BinTrie {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        struct Path(u64);

        impl std::fmt::Debug for Path {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let mut item = self.0;
                let zeros = self.0.trailing_zeros();
                if zeros < 63 {
                    let len = (63 - zeros) as usize;
                    item >>= zeros + 1;
                    f.write_fmt(format_args!("{item:0len$b}"))
                } else {
                    f.write_str("root")
                }
            }
        }

        struct Node<'a>(&'a BinTrieNode);

        impl std::fmt::Debug for Node<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.debug_struct("BinTrieNode")
                    .field("tag", &self.0.tag)
                    .field("down_tag", &self.0.down_tag)
                    .field("useful_depth", &self.0.useful_depth)
                    .finish()
            }
        }

        let mut map = f.debug_map();

        let mut stack = vec![(HIGH_BIT, &self.root, false)];
        while let Some((path, node, visited)) = stack.last_mut() {
            let (path, node, visited) = (*path, *node, std::mem::replace(visited, true));
            let tag = lower_bit(path) >> 1;

            if !visited {
                map.entry(&Path(path), &Node(node));

                if let Some(left) = &node.left {
                    stack.push((path - tag, left, false));
                    continue;
                }
            }

            stack.pop();
            if let Some(right) = &node.right {
                stack.push((path + tag, right, false));
            }
        }

        map.finish()
    }
}

#[derive(Default, Debug)]
struct BinTrieNode {
    tag: u64,
    down_tag: u64,
    useful_depth: u32,
    left: Option<Box<BinTrieNode>>,
    right: Option<Box<BinTrieNode>>,
}

impl BinTrieNode {
    fn insert(&mut self, path: u64, tag: u64) {
        if path == 0 || tag == 0 {
            return;
        }

        if path & PATH_BITS == 0 {
            self.tag |= tag;
            return;
        } else if path & HIGH_BIT == 0 {
            self.left = insert(self.left.take(), path << 1, tag);
        } else {
            self.right = insert(self.right.take(), path << 1, tag);
        }

        if let (Some(left), Some(right)) = (&self.left, &self.right) {
            self.tag |= left.tag & right.tag;
        }
    }

    fn update_useful_depth(&mut self, mut colors: u64) {
        let mut result = 0;

        colors |= self.tag;
        self.tag = colors;
        self.down_tag = colors;

        if let Some(left) = &mut self.left {
            left.update_useful_depth(colors);
            result = left.useful_depth;
            self.down_tag |= left.down_tag;
        }
        if let Some(right) = &mut self.right {
            right.update_useful_depth(colors);
            result = std::cmp::max(result, right.useful_depth);
            self.down_tag |= right.down_tag;
        }

        self.useful_depth = if result > 0 {
            result + 1
        } else {
            match (&self.left, &self.right) {
                (Some(left), Some(right))
                    if (left.down_tag & !right.down_tag != 0)
                        && (right.down_tag & !left.down_tag != 0) =>
                {
                    1
                }
                _ => 0,
            }
        };
    }

    fn get_node(&self, path: u64) -> Option<&BinTrieNode> {
        if path == 0 {
            None
        } else if path & PATH_BITS == 0 {
            Some(self)
        } else if path & HIGH_BIT == 0 {
            self.left.as_ref()?.get_node(path << 1)
        } else {
            self.right.as_ref()?.get_node(path << 1)
        }
    }
}

fn insert(root: Option<Box<BinTrieNode>>, path: u64, tag: u64) -> Option<Box<BinTrieNode>> {
    if path == 0 || tag == 0 {
        return root;
    }

    if let Some(mut root) = root {
        root.insert(path, tag);
        return Some(root);
    }

    let mut result = Box::<BinTrieNode>::default();
    if path & PATH_BITS == 0 {
        result.tag = tag;
    } else if path & HIGH_BIT == 0 {
        result.left = insert(None, path << 1, tag);
    } else {
        result.right = insert(None, path << 1, tag);
    }
    Some(result)
}

const HIGH_BIT: u64 = 1 << 63;
const PATH_BITS: u64 = !HIGH_BIT;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn builder() {
        let trie = {
            let mut t = BinTrie::builder();
            t.insert(0xab80000000000000, 1 << 0);
            t.insert(0xabc8000000000000, 1 << 1);
            t.insert(0x0280000000000000, 1 << 2);
            t.insert(0x2280000000000000, 1 << 3);
            t.build()
        };
        println!("{trie:#?}");

        assert_eq!(trie.root.tag, 0);
        assert_eq!(trie.root.down_tag, 0xf);
        assert!(trie.root.left.is_some() && trie.root.right.is_some());

        assert_eq!(trie.get(0xab80000000000000), Some(1 << 0));
        assert_eq!(trie.get(0xabc8000000000000), Some((1 << 1) | (1 << 0)));
        assert_eq!(trie.get(0x0280000000000000), Some(1 << 2));
        assert_eq!(trie.get(0x2280000000000000), Some(1 << 3));
    }
}

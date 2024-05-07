use std::ops::{Add, AddAssign};

#[derive(Default, Eq, PartialEq)]
pub struct BitPfxCollection {
    items: Vec<u64>,
}

impl BitPfxCollection {
    /// Creates a new prefix collection for any prefix.
    pub fn all() -> Self {
        Self::new(ALL)
    }

    /// Creates a new prefix collection for the specified prefix.
    pub fn new(prefix: u64) -> Self {
        let mut result = Self::default();
        if prefix != 0 {
            result.merge_back(prefix);
        }
        result
    }

    /// Returns `true` if the prefix collection contains no elements.
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// Returns the number of elements in the prefix collection.
    pub fn len(&self) -> usize {
        self.items.len()
    }

    /// Returns `true` if the prefix collection contains any prefix.
    pub fn is_all(&self) -> bool {
        matches!(self.items.first(), Some(&first) if self.items.len() == 1 && first == ALL)
    }

    /// Returns the lowest prefix if not empty.
    pub fn min(&self) -> Option<u64> {
        self.items.first().copied()
    }

    /// Returns an iterator over the elements of the prefix collection.
    pub fn iter(&self) -> std::slice::Iter<'_, u64> {
        self.items.iter()
    }

    /// Prepends the given prefix to all items.
    pub fn prepend(&mut self, mut prefix: u64) {
        // Clear for invalid prefix
        if prefix == 0 {
            return self.items.clear();
        }
        // Do nothing if we append empty prefix
        if prefix == ALL {
            return;
        }

        // Compute prefix length in bits
        let prefix_len = 63 - prefix.trailing_zeros();
        // Remove termination bit
        prefix &= prefix - 1;

        // For each prefix in the collection
        let mut j = 0;
        for i in 0..self.items.len() {
            let mut item = self.items[i];

            // Get tag from the item
            let tag = lower_bit(item);
            // Prepend item with the prefix
            item = prefix | (item >> prefix_len);
            // Make sure that the termination bit is always set
            if tag >> prefix_len == 0 {
                item |= 1;
            }

            // Update the value, with a hack for overflown prefixes
            if j == 0 || self.items[j - 1] != item {
                self.items[j] = item;
                j += 1;
            }
        }

        // Retain only first `j` updated elements
        self.items.truncate(j);
    }

    /// Merges current prefix collection with the provided
    pub fn merge(&mut self, other: Self) {
        struct Interval {
            prefix: u64,
            start: u64,
            end: u64,
        }

        impl Interval {
            fn new(prefix: u64) -> Self {
                Self {
                    prefix,                       // xxx1000...
                    start: prefix & (prefix - 1), // xxx0000...
                    end: prefix | (prefix - 1),   // xxx1111...
                }
            }
        }

        // Get interval for the "lowest" prefix from the other collection
        let mut v = match other.items.first() {
            Some(&item) => Interval::new(item),
            // Merging with empty collection <=> noop
            None => return,
        };
        // Get interval for the "lowest" prefix from the current collection
        let mut u = match self.items.first() {
            Some(&item) => Interval::new(item),
            // Just return other collection if the current is empty
            None => {
                self.items = other.items;
                return;
            }
        };

        // Prepare resulting collection
        let mut result = Self {
            items: Vec::with_capacity(self.items.len() + other.items.len()),
        };

        // Iterate simultaneously through both collections
        let mut i = 0;
        let mut j = 0;
        let m = self.items.len();
        let n = other.items.len();
        while i < m && j < n {
            // Check if other interval contains the current interval for the lowest prefix
            if u.end < v.end || u.end == v.end && u.start >= v.start {
                // `u` is "lower" than `v`

                if u.start < v.start {
                    // Add prefix from the current collection
                    result.merge_back(u.prefix);
                }

                // Try using the next prefix in the current collection
                i += 1;
                if i >= m {
                    break;
                }
                u = Interval::new(self.items[i]);
            } else {
                // `v` is "lower" than `u`

                if v.start < u.start {
                    // Add prefix from the other collection
                    result.merge_back(v.prefix);
                }

                // Try using the next prefix in the other collection
                j += 1;
                if j >= n {
                    break;
                }
                v = Interval::new(other.items[j]);
            }
        }

        // Add remaining prefixes from the current collection
        while i < m {
            result.merge_back(self.items[i]);
            i += 1;
        }

        // Add remaining prefixes from the other collection
        while j < n {
            result.merge_back(other.items[j]);
            j += 1;
        }

        // Update elements of the current collection
        self.items = result.items;
    }

    /// Adds prefix to the end of prefixes list,
    /// or merges it with the last one.
    fn merge_back(&mut self, mut prefix: u64) {
        if self.items.is_empty() {
            self.items.push(prefix);
            return;
        }

        let mut tag = lower_bit(prefix);
        while let Some(last) = self.items.last() {
            let diff = last ^ prefix;

            // Do nothing while merging with an existing prefix
            if diff == 0 {
                return;
            }

            // Check if `prefix` differs not only by tag
            if diff != tag << 1 {
                break;
            }

            // At this point `prefix` is one bit larger than `last`,
            // remove the tag from `prefix` and proceed to the previous item.
            prefix -= tag;
            tag <<= 1;
            self.items.pop();
        }
        self.items.push(prefix);
    }
}

impl std::fmt::Debug for BitPfxCollection {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        struct Item(u64);

        impl std::fmt::Debug for Item {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let mut item = self.0;
                let zeros = item.trailing_zeros();
                if zeros < 63 {
                    let len = (63 - zeros) as usize;
                    item >>= zeros + 1;
                    f.write_fmt(format_args!("{item:0len$b}*"))
                } else {
                    f.write_str("*")
                }
            }
        }

        let mut list = f.debug_list();
        for &item in &self.items {
            list.entry(&Item(item));
        }
        list.finish()
    }
}

impl<'a> IntoIterator for &'a BitPfxCollection {
    type Item = &'a u64;

    type IntoIter = std::slice::Iter<'a, u64>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.items.iter()
    }
}

impl IntoIterator for BitPfxCollection {
    type Item = u64;

    type IntoIter = std::vec::IntoIter<u64>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.items.into_iter()
    }
}

impl Add for BitPfxCollection {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        self.merge(rhs);
        self
    }
}

impl AddAssign for BitPfxCollection {
    fn add_assign(&mut self, rhs: Self) {
        self.merge(rhs);
    }
}

// value  | !tag   | !tag + 1 | tag & (!tag + 1)
// 011000 | 100111 | 101000   | 0001000
pub fn lower_bit(prefix: u64) -> u64 {
    prefix & (!prefix + 1)
}

const ALL: u64 = 1 << 63;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prepend() {
        let mut collection = BitPfxCollection::new(0xca80000000000000);
        collection += BitPfxCollection::new(0xba80000000000000);
        collection.prepend(0x5580000000000000);
        println!("{collection:#?}");
        assert_eq!(collection.items, [0x55ba800000000000, 0x55ca800000000000]);

        let mut collection = BitPfxCollection::new(0xff80000000000000);
        collection.prepend(0xf800000000000000);
        println!("{collection:#?}");
        assert_eq!(collection.items, [0xfff8000000000000]);

        let mut collection = BitPfxCollection::all();
        collection.prepend(0xff80000000000000);
        assert_eq!(collection.items, [0xff80000000000000]);
    }

    #[test]
    fn merge() {
        let mut collection = BitPfxCollection::default();
        collection += BitPfxCollection::new(0xca80000000000000);
        collection += BitPfxCollection::new(0x0af8000000000000);
        println!("{collection:#?}");
        assert_eq!(collection.items, [0x0af8000000000000, 0xca80000000000000]);

        let mut other = BitPfxCollection::default();
        other += BitPfxCollection::new(0xcd80000000000000);
        other += BitPfxCollection::new(0x0bf8000000000000);
        println!("{other:#?}");

        collection += other;
        println!("{collection:#?}");
        assert_eq!(
            collection.items,
            [
                0x0af8000000000000,
                0x0bf8000000000000,
                0xca80000000000000,
                0xcd80000000000000
            ]
        );

        collection += BitPfxCollection::all();
        assert!(collection.is_all());
    }
}

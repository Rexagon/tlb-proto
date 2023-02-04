use std::ops::{Add, AddAssign};

#[derive(Default, Eq, PartialEq)]
pub struct BitPfxCollection {
    items: Vec<u64>,
}

impl BitPfxCollection {
    pub fn all() -> Self {
        Self::new(ALL)
    }

    pub fn new(prefix: u64) -> Self {
        let mut result = Self::default();
        if prefix != 0 {
            result.merge_back(prefix);
        }
        result
    }

    pub fn clear(&mut self) {
        self.items.clear();
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    pub fn is_all(&self) -> bool {
        matches!(self.items.first(), Some(&first) if self.items.len() == 1 && first == ALL)
    }

    pub fn min(&self) -> Option<u64> {
        self.items.first().copied()
    }

    pub fn prepend(&mut self, mut prefix: u64) {
        if prefix == 0 {
            return self.clear();
        }
        if prefix == ALL {
            return;
        }

        let prefix_len = 63 - prefix.trailing_zeros();
        prefix &= prefix - 1; // remove termination bit

        let mut j = 0;
        for i in 0..self.items.len() {
            let mut item = self.items[i];

            let mask = lower_bit(item);
            item = prefix | (item >> prefix_len);
            if mask >> prefix_len == 0 {
                item |= 1;
            }

            if j == 0 || self.items[j - 1] != item {
                self.items[j] = item;
                j += 1;
            }
        }

        self.items.truncate(j);
    }

    pub fn merge(&mut self, other: Self) {
        struct Interval {
            prefix: u64,
            start: u64,
            end: u64,
        }

        impl Interval {
            fn new(prefix: u64) -> Self {
                Self {
                    prefix,
                    start: prefix & (prefix - 1),
                    end: prefix | (prefix - 1),
                }
            }
        }

        let mut v = match other.items.first() {
            Some(&item) => Interval::new(item),
            None => return,
        };
        let mut u = match self.items.first() {
            Some(&item) => Interval::new(item),
            None => {
                self.items = other.items;
                return;
            }
        };

        let mut result = Self {
            items: Vec::with_capacity(self.items.len() + other.items.len()),
        };

        let mut i = 0;
        let mut j = 0;
        let m = self.items.len();
        let n = other.items.len();
        while i < m && j < n {
            if u.end < v.end || u.end == v.end && u.start >= v.start {
                if u.start < v.start {
                    result.merge_back(u.prefix);
                }
                i += 1;
                if i >= m {
                    break;
                }
                u = Interval::new(self.items[i]);
            } else {
                if v.start < u.start {
                    result.merge_back(v.prefix);
                }
                j += 1;
                if j >= n {
                    break;
                }
                v = Interval::new(other.items[j]);
            }
        }

        while i < m {
            result.merge_back(self.items[i]);
            i += 1;
        }

        while j < n {
            result.merge_back(other.items[j]);
            j += 1;
        }

        self.items = result.items;
    }

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

            // Merged tag differs not only by the mask bit => insert new prefix
            if diff != tag << 1 {
                break;
            }

            // Extend an existing prefix otherwise
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
fn lower_bit(tag: u64) -> u64 {
    tag & (!tag + 1)
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

#[derive(Debug, Clone)]
pub struct ConflictGraph {
    items: [ConflictSet; 64],
}

impl ConflictGraph {
    pub fn add(&mut self, set: ConflictSet) {
        if !set.is_empty() {
            for i in 0..64 {
                if set.contains(i) {
                    self.items[i as usize] |= set;
                }
            }
        }
    }

    pub fn check(&self, row: u64, col: u64) -> bool {
        row < 64 && self.items[row as usize].contains(col)
    }

    pub fn row(&self, tag: u64) -> Option<&ConflictSet> {
        self.items.get(tag as usize)
    }

    pub fn row_mut(&mut self, tag: u64) -> Option<&mut ConflictSet> {
        self.items.get_mut(tag as usize)
    }
}

impl Default for ConflictGraph {
    fn default() -> Self {
        Self {
            items: [ConflictSet(0); 64],
        }
    }
}

#[derive(Default, Clone, Copy, Eq, PartialEq)]
#[repr(transparent)]
pub struct ConflictSet(u64);

impl ConflictSet {
    pub fn new(value: u64) -> Self {
        Self(value)
    }

    pub fn is_empty(&self) -> bool {
        self.0 == 0
    }

    pub fn len(&self) -> usize {
        self.0.count_ones() as usize
    }

    pub fn insert(&mut self, tag: u64) {
        if tag < 64 {
            self.0 |= 1 << tag;
        }
    }

    pub fn remove(&mut self, tag: u64) {
        if tag < 64 {
            self.0 &= !(1 << tag);
        }
    }

    pub fn contains(&self, tag: u64) -> bool {
        tag < 64 && (self.0 >> tag) & 1 != 0
    }
}

impl std::fmt::Debug for ConflictSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:064b}", self.0))
    }
}

impl From<u64> for ConflictSet {
    #[inline]
    fn from(value: u64) -> Self {
        Self(value)
    }
}

impl std::ops::BitOr for ConflictSet {
    type Output = Self;

    #[inline]
    fn bitor(mut self, rhs: Self) -> Self::Output {
        self.0 |= rhs.0;
        self
    }
}

impl std::ops::BitOrAssign for ConflictSet {
    #[inline]
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

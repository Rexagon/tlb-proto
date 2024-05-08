#[derive(Debug, Default, Clone, Copy, Eq, PartialEq)]
pub struct SizeRange {
    /// Minimal possible size.
    pub min: Option<TypeSize>,
    /// Maximum possible size.
    pub max: Option<TypeSize>,
}

impl SizeRange {
    pub fn any() -> Self {
        Self {
            min: None,
            max: None,
        }
    }

    pub fn zero() -> Self {
        Self {
            min: Some(TypeSize::ZERO),
            max: Some(TypeSize::ZERO),
        }
    }

    pub fn exact_bits(bits: u16) -> Self {
        Self {
            min: Some(TypeSize { bits, refs: 0 }),
            max: Some(TypeSize { bits, refs: 0 }),
        }
    }

    pub fn bits(bits: impl std::ops::RangeBounds<u16>) -> Self {
        Self {
            min: {
                let bits = match bits.start_bound() {
                    std::ops::Bound::Included(&start) => start,
                    std::ops::Bound::Excluded(&start) => start + 1,
                    std::ops::Bound::Unbounded => 0,
                };
                Some(TypeSize { bits, refs: 0 })
            },
            max: {
                let bits = match bits.end_bound() {
                    std::ops::Bound::Included(&end) => Some(end),
                    std::ops::Bound::Excluded(&end) => Some(end - 1),
                    std::ops::Bound::Unbounded => None,
                };
                bits.map(|bits| TypeSize { bits, refs: 0 })
            },
        }
    }

    pub fn exact_refs(refs: u8) -> Self {
        Self {
            min: Some(TypeSize { bits: 0, refs }),
            max: Some(TypeSize { bits: 0, refs }),
        }
    }

    pub fn refs(refs: impl std::ops::RangeBounds<u8>) -> Self {
        Self {
            min: {
                let refs = match refs.start_bound() {
                    std::ops::Bound::Included(&start) => start,
                    std::ops::Bound::Excluded(&start) => start + 1,
                    std::ops::Bound::Unbounded => 0,
                };
                Some(TypeSize { bits: 0, refs })
            },
            max: {
                let refs = match refs.end_bound() {
                    std::ops::Bound::Included(&end) => Some(end),
                    std::ops::Bound::Excluded(&end) => Some(end - 1),
                    std::ops::Bound::Unbounded => None,
                };
                refs.map(|refs| TypeSize { bits: 0, refs })
            },
        }
    }

    pub fn is_fixed(&self) -> bool {
        self.min == self.max
    }

    pub fn fixed_bit_size(&self) -> Option<u16> {
        if self.min == self.max {
            if let Some(size) = self.min {
                return Some(size.bits);
            }
        }
        None
    }

    pub fn is_possible(&self) -> bool {
        if let (Some(min), Some(max)) = (&self.min, &self.max) {
            min <= max
        } else {
            true
        }
    }
}

impl std::ops::Add for SizeRange {
    type Output = Self;

    #[inline]
    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl std::ops::AddAssign for SizeRange {
    fn add_assign(&mut self, rhs: Self) {
        match (&mut self.min, rhs.min) {
            (None, min) => self.min = min,
            (Some(this), Some(min)) => *this += min,
            (Some(_), None) => {}
        }

        match (&mut self.max, rhs.max) {
            (None, max) => self.max = max,
            (Some(this), Some(max)) => *this += max,
            (Some(_), None) => {}
        }
    }
}

impl std::ops::BitOr for SizeRange {
    type Output = Self;

    #[inline]
    fn bitor(mut self, rhs: Self) -> Self::Output {
        self |= rhs;
        self
    }
}

impl std::ops::BitOrAssign for SizeRange {
    fn bitor_assign(&mut self, rhs: Self) {
        match (&mut self.max, rhs.max) {
            (None, max) => self.max = max,
            (Some(this), Some(min)) => {
                this.bits = this.bits.max(min.bits);
                this.refs = this.refs.max(min.refs);
            }
            (Some(_), None) => {}
        }
    }
}

#[derive(Debug, Default, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub struct TypeSize {
    /// Type size in bits.
    pub bits: u16,
    /// Type size in refs.
    pub refs: u8,
}

impl TypeSize {
    /// Additive identity.
    pub const ZERO: Self = Self { bits: 0, refs: 0 };

    /// Max possible size.
    pub const CELL_MAX: Self = Self {
        bits: 1023,
        refs: 4,
    };
}

impl std::ops::Add for TypeSize {
    type Output = Self;

    #[inline]
    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl std::ops::AddAssign for TypeSize {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.bits += rhs.bits;
        self.refs += rhs.refs;
    }
}

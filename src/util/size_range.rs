#[derive(Debug, Default, Clone, Copy, Eq, PartialEq)]
pub struct SizeRange {
    /// Minimal possible size.
    pub min: Option<TypeSize>,
    /// Maximum possible size.
    pub max: Option<TypeSize>,
}

impl SizeRange {
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

/// Abstract integer that only describes properties.
///
/// ```text
/// |bit 0 | bit 1 | bit 2 | bit 3 |
/// |------|-------|-------|-------|
/// |zero  | one   | even  | odd   |
/// ```
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[repr(transparent)]
pub struct AbstractNat(u8);

impl AbstractNat {
    pub const NAN: Self = Self(0);
    pub const ZERO: Self = Self(1 << 0);
    pub const ONE: Self = Self(1 << 1);
    pub const ANY: Self = Self(0b1111);

    /// Converts the number to an abstract value.
    pub const fn new(value: u32) -> Self {
        Self(1 << ((value & 1) + if value >= 2 { 2 } else { 0 }))
    }

    pub const fn inner(self) -> u8 {
        self.0
    }

    pub const fn get_bit(self, bit: AbstractNat) -> Self {
        Self(GET_BIT_TABLE[self.0 as usize][bit.0 as usize])
    }

    pub const fn is_nan(self) -> bool {
        self.0 == 0
    }

    pub const fn is_zero(self) -> bool {
        self.0 == Self::ZERO.0
    }

    pub const fn is_one(self) -> bool {
        self.0 == Self::ONE.0
    }

    pub const fn is_any(self) -> bool {
        self.0 == Self::ANY.0
    }
}

impl std::ops::Add for AbstractNat {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self(ADD_TABLE[self.0 as usize][rhs.0 as usize])
    }
}

impl std::ops::AddAssign for AbstractNat {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl std::ops::Mul for AbstractNat {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        Self(MUL_TABLE[self.0 as usize][rhs.0 as usize])
    }
}

impl std::ops::MulAssign for AbstractNat {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

// 0 = 0
// 1 = 1
// 2 = 2n (n >= 1)
// 3 = 2n+1 (n >= 1)

// x + y
// x \ y| zero | one  | even | odd  |
// -----|------|------|------|------|
// zero | zero | one  | even | odd  |
// one  | one  | even | odd  | even |
// even | even | odd  | even | odd  |
// odd  | odd  | even | odd  | even |
const ADD_BASE_TABLE: [[u8; 4]; 4] = [[0, 1, 2, 3], [1, 2, 3, 2], [2, 3, 2, 3], [3, 2, 3, 2]];

// x * y
// x \ y| zero | one  | even | odd  |
// -----|------|------|------|------|
// zero | zero | zero | zero | zero |
// one  | zero | one  | even | odd  |
// even | zero | even | even | even |
// odd  | zero | odd  | even | odd  |
const MUL_BASE_TABLE: [[u8; 4]; 4] = [[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 2, 2], [0, 3, 2, 3]];

// NOTE: Each item has two flags: `is_one << 1 | is_zero`
//
// x \ y| zero | one  | even | odd  |
// -----|------|------|------|------|
// zero | 0    | 0    | 0    | 0    |
// one  | 1    | 0    | 0    | 0    |
// even | 0    | 0/1  | 0/1  | 0/1  |
// odd  | 1    | 0/1  | 0/1  | 0/1  |
const GET_BIT_BASE_TABLE: [[u8; 4]; 4] = [[1, 1, 1, 1], [2, 1, 1, 1], [1, 3, 3, 3], [2, 3, 3, 3]];

const ADD_TABLE: [[u8; 16]; 16] = compute_table::<true>(&ADD_BASE_TABLE);
const MUL_TABLE: [[u8; 16]; 16] = compute_table::<true>(&MUL_BASE_TABLE);
const GET_BIT_TABLE: [[u8; 16]; 16] = compute_table::<false>(&GET_BIT_BASE_TABLE);

const fn compute_table<const SHIFT: bool>(base_table: &[[u8; 4]; 4]) -> [[u8; 16]; 16] {
    let mut result = [[0; 16]; 16];

    let mut x = 0;
    while x < 16 {
        let mut y = 0;
        while y < 16 {
            let mut res = 0;

            let mut i = 0;
            while i < 4 {
                if x >> i & 1 != 0 {
                    let mut j = 0;
                    while j < 4 {
                        if y >> j & 1 != 0 {
                            if SHIFT {
                                res |= 1 << base_table[i][j];
                            } else {
                                res |= base_table[i][j];
                            }
                        }
                        j += 1;
                    }
                }
                i += 1;
            }

            result[x][y] = res;
            y += 1;
        }
        x += 1;
    }

    result
}

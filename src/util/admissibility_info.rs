use crate::util::AbstractNat;

pub struct AdmissibilityInfo {
    dimension: usize,
    matrix: Vec<bool>,
}

impl std::fmt::Debug for AdmissibilityInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str("[")?;
        for &flag in &self.matrix {
            std::fmt::Display::fmt(&(flag as u8), f)?;
        }
        f.write_str("]")
    }
}

impl Default for AdmissibilityInfo {
    fn default() -> Self {
        Self {
            dimension: 0,
            matrix: vec![false],
        }
    }
}

impl AdmissibilityInfo {
    pub fn get(&self, i: usize) -> bool {
        // dimension = 0, matrix = 1, i & 0
        // dimension = 1, matrix = 4, i & 3
        // dimension = 2, matrix = 16, i & 15
        // dimension = 3, matrix = 64, i & 63
        self.matrix[i & (self.matrix.len() - 1)]
    }

    pub fn conflicts_at(&self, other: &AdmissibilityInfo) -> Option<usize> {
        let n1 = self.matrix.len();
        let n2 = other.matrix.len();
        for i in 0..std::cmp::max(n1, n2) {
            if self.matrix[i & (n1 - 1)] && other.matrix[i & (n2 - 1)] {
                return Some(i);
            }
        }
        None
    }

    pub fn set_by_pattern(&mut self, pattern: &[AbstractNat]) {
        self.extend(pattern.len());

        let n = self.matrix.len();

        // For each dimension
        for x in 0..n {
            let mut y = x;
            let mut f = true;

            // For each parameter in pattern
            for param in pattern {
                // Check if matrix has corresponding property
                if (param.inner() >> (y & 0b11)) & 1 == 0 {
                    f = false;
                    break;
                }
                y >>= 2;
            }

            if f {
                self.matrix[x] = true;
            }
        }
    }

    pub fn set_all(&mut self, value: bool) {
        self.dimension = 0;
        self.matrix.resize(1, value);
    }

    pub fn is_set_all(&self) -> bool {
        self.dimension == 0 && self.matrix[0]
    }

    pub fn extend(&mut self, new_dimension: usize) {
        // dimension = 0, matrix = 1
        // dimension = 1, matrix = 4
        // dimension = 2, matrix = 16
        // dimension = 3, matrix = 64
        if new_dimension <= self.dimension {
            return;
        }

        let n = self.matrix.len();
        let new_n = 1 << (2 * new_dimension);
        self.matrix.resize(new_n, false);

        for i in n..new_n {
            self.matrix[i] = self.matrix[i - n];
        }

        self.dimension = new_dimension;
    }

    pub fn combine(&mut self, other: &AdmissibilityInfo) {
        self.extend(other.dimension);

        let n = self.matrix.len();
        let other_n = other.matrix.len();
        assert!(other_n != 0 && other_n.is_power_of_two());

        let mut j = 0;
        for i in 0..n {
            self.matrix[i] |= other.matrix[j];
            j = (j + 1) & (other_n - 1);
        }
    }
}

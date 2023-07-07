use std::{error, fmt, ops};

#[cfg(feature = "random")]
use {crate::Permutations, rand::Rng};

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct TryFromError;
impl fmt::Display for TryFromError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ill-formed slice to permutation conversion attempted",)
    }
}
impl error::Error for TryFromError {}

/// Returns true if a slice is a permutation.
///
/// That is, all the elements in `0..len` occur exactly once in the slice.
fn is_permutation(v: &[usize]) -> bool {
    let n = v.len();
    let mut seen = vec![false; n];
    for &e in v {
        if (0..n).contains(&e) {
            seen[e] = true;
        }
    }
    seen.into_iter().all(|b| b)
}

#[inline]
pub(crate) fn validate(v: &[usize]) -> Result<(), TryFromError> {
    if !is_permutation(v) {
        return Err(TryFromError);
    }
    Ok(())
}

/// A permutation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Permutation(Box<[usize]>);

impl Permutation {
    /// Returns the identity permutation of n elements.
    pub fn identity(n: usize) -> Self {
        Self((0..n).collect())
    }

    /// Checks if permutation is identity
    pub fn is_identity(&self) -> bool {
        (0..self.len()).eq(self.0.iter().cloned())
    }

    /// Returns the permutation of n elements which rotates r steps to the left.
    pub fn rotation_left(n: usize, r: usize) -> Self {
        Self((0..n).map(|i| (i + r) % n).collect())
    }
    /// Returns the permutation of n elements which rotates r steps to the right.
    pub fn rotation_right(n: usize, r: usize) -> Self {
        Self::rotation_left(n, n - (r % n))
    }
    /// Returns the permutation of n elements which exchanges the elements at i and j.
    pub fn transposition(n: usize, i: usize, j: usize) -> Self {
        assert!(i < n && j < n);
        Self(
            (0..n)
                .map(|k| {
                    if k == i {
                        j
                    } else if k == j {
                        i
                    } else {
                        k
                    }
                })
                .collect(),
        )
    }

    /// Returns a random permutation.
    ///
    /// Uses a uniform distribution.
    #[cfg(feature = "random")]
    pub fn random<R>(rng: &mut R, n: usize) -> Self
    where
        R: Rng,
    {
        let ps = Self::new(n);
        let i = rng.gen_range(0..ps.len());
        ps.get(i).expect("random index out of range")
    }
    /// Applies the permutation to an element.
    pub fn apply(&self, i: usize) -> usize {
        self.0[i]
    }
    /// Returns a vector permuted by this permutation.
    pub fn permute<T: Clone>(&self, v: &[T]) -> Vec<T> {
        assert_eq!(self.len(), v.len());
        (0..self.len()).map(|i| v[self.apply(i)].clone()).collect()
    }
    /// Returns the composition of the permutation with itself.
    pub fn square(&self) -> Self {
        self * self
    }
    /// Returns the composition of the permutation with itself `exp` number of times.
    pub fn pow(&self, exp: u32) -> Self {
        if exp == 0 {
            Self::identity(self.len())
        } else if exp == 1 {
            self.clone()
        } else if exp % 2 == 0 {
            self.square().pow(exp / 2)
        } else {
            self * self.pow(exp - 1)
        }
    }
    /// Returns the inverse permutation.
    pub fn inv(&self) -> Self {
        let len = self.len();
        let mut map = vec![0; len];
        for (i, j) in self.0.iter().enumerate() {
            map[*j] = i;
        }
        Self(map.into())
    }
    /// The length of the permutation.
    ///
    /// That is, the length of its domain and range.
    pub fn len(&self) -> usize {
        self.0.len()
    }
    /// Returns true if this is the empty permutation.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    /// Returns true if the permutation is even.
    pub fn is_even(&self) -> bool {
        let mut even = true;
        let mut seen = vec![false; self.len()];
        for i in 0..self.len() {
            if !seen[i] {
                seen[i] = true;
                let mut j = self.apply(i);
                while j != i {
                    seen[j] = true;
                    j = self.apply(j);
                    even = !even;
                }
            }
        }
        even
    }
    /// Returns true if the permutation is odd.
    pub fn is_odd(&self) -> bool {
        !self.is_even()
    }
    /// Returns the sign of a permutation.
    pub fn sign(&self) -> isize {
        if self.is_even() {
            1
        } else {
            -1
        }
    }
}

impl ops::Mul for Permutation {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        &self * &other
    }
}

impl ops::Mul<Permutation> for &Permutation {
    type Output = Permutation;
    fn mul(self, other: Permutation) -> Self::Output {
        self * &other
    }
}

impl ops::Mul<&Self> for Permutation {
    type Output = Self;
    fn mul(self, other: &Self) -> Self {
        &self * other
    }
}

impl ops::Mul for &Permutation {
    type Output = Permutation;
    fn mul(self, other: &Permutation) -> Self::Output {
        assert_eq!(self.len(), other.len());
        Permutation(
            (0..self.len())
                .map(|i| other.apply(self.apply(i)))
                .collect(),
        )
    }
}

impl TryFrom<Vec<usize>> for Permutation {
    type Error = TryFromError;
    fn try_from(v: Vec<usize>) -> Result<Self, TryFromError> {
        let _ = validate(&v)?;
        Ok(Self(v.into()))
    }
}

impl<'a> TryFrom<&'a Vec<usize>> for Permutation {
    type Error = TryFromError;
    fn try_from(v: &'a Vec<usize>) -> Result<Self, TryFromError> {
        let _ = validate(&v)?;
        Ok(Self(v[..].into()))
    }
}

impl TryFrom<&[usize]> for Permutation {
    type Error = TryFromError;
    fn try_from(a: &[usize]) -> Result<Self, TryFromError> {
        let _ = validate(&a)?;
        Ok(Self(a.into()))
    }
}

impl<const N: usize> TryFrom<&[usize; N]> for Permutation {
    type Error = TryFromError;
    fn try_from(a: &[usize; N]) -> Result<Self, TryFromError> {
        let _ = validate(a.as_slice())?;
        Ok(Self(a[..].into()))
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "random")]
    use rand::rngs::StdRng;
    #[cfg(feature = "random")]
    use rand::SeedableRng;

    use super::is_permutation;
    use super::Permutation;
    use super::TryFromError;

    #[test]
    fn test_is_permutation_true() {
        assert_eq!(true, is_permutation(&vec![2, 1, 0]));
    }
    #[test]
    fn test_is_permutation_false_missing_element() {
        assert_eq!(false, is_permutation(&vec![0, 1, 1]));
    }
    #[test]
    fn test_is_permutation_false_out_of_range() {
        assert_eq!(false, is_permutation(&vec![2, 7, 1]));
    }

    #[test]
    fn test_identity() {
        let id = Permutation::identity(3);
        assert_eq!(Permutation(Box::new([0, 1, 2])), id);
        assert!(id.is_identity());
    }

    #[test]
    fn test_rotation_left() {
        let p = Permutation::rotation_left(3, 1);
        assert_eq!(Permutation(Box::new([1, 2, 0])), p);
    }

    #[test]
    fn test_rotation_right() {
        let p = Permutation::rotation_right(3, 1);
        assert_eq!(Permutation(Box::new([2, 0, 1])), p);
    }

    #[test]
    fn test_transposition() {
        let p = Permutation::transposition(3, 1, 2);
        assert_eq!(Permutation(Box::new([0, 2, 1])), p);
    }

    #[test]
    fn test_apply() {
        let p = Permutation(Box::new([0, 2, 1]));
        assert_eq!(2, p.apply(1));
    }

    #[test]
    fn test_permute() {
        let p = Permutation(Box::new([0, 2, 1]));
        assert_eq!(vec!['a', 'c', 'b'], p.permute(&vec!['a', 'b', 'c']));
    }

    #[test]
    fn test_square() {
        let p = Permutation::rotation_left(3, 1);
        assert_eq!(Permutation(Box::new([2, 0, 1])), p.square());
    }

    #[test]
    fn test_pow() {
        let p = Permutation::rotation_left(3, 1);
        assert_eq!(Permutation::identity(3), p.pow(3));
    }

    #[test]
    fn test_inv() {
        let p = Permutation::rotation_left(3, 1);
        assert_eq!(Permutation::rotation_right(3, 1), p.inv());
    }
    #[test]
    fn test_inv_identity() {
        let id = Permutation::identity(3);
        assert_eq!(id, id.inv());
    }

    #[test]
    fn test_len() {
        let id = Permutation::identity(3);
        assert_eq!(3, id.len());
    }

    #[test]
    fn test_is_empty_true() {
        let id = Permutation::identity(0);
        assert_eq!(true, id.is_empty());
    }
    #[test]
    fn test_is_empty_false() {
        let id = Permutation::identity(3);
        assert_eq!(false, id.is_empty());
    }

    #[test]
    fn test_is_even_identity() {
        let id = Permutation::identity(3);
        assert_eq!(true, id.is_even());
    }
    #[test]
    fn test_is_even_rotation() {
        let p = Permutation::rotation_left(3, 1);
        assert_eq!(true, p.is_even());
    }
    #[test]
    fn test_is_even_transposition() {
        let p = Permutation::transposition(3, 0, 1);
        assert_eq!(false, p.is_even());
    }

    #[test]
    fn test_is_odd_identity() {
        let id = Permutation::identity(3);
        assert_eq!(false, id.is_odd());
    }
    #[test]
    fn test_is_odd_rotation() {
        let p = Permutation::rotation_left(3, 1);
        assert_eq!(false, p.is_odd());
    }
    #[test]
    fn test_is_odd_transposition() {
        let p = Permutation::transposition(3, 0, 1);
        assert_eq!(true, p.is_odd());
    }

    #[test]
    fn test_sign_identity() {
        let id = Permutation::identity(3);
        assert_eq!(1, id.sign());
    }
    #[test]
    fn test_sign_rotation() {
        let p = Permutation::rotation_left(3, 1);
        assert_eq!(1, p.sign());
    }
    #[test]
    fn test_sign_transposition() {
        let p = Permutation::transposition(3, 0, 1);
        assert_eq!(-1, p.sign());
    }

    #[cfg(feature = "random")]
    #[test]
    fn test_random() {
        let mut rng = StdRng::seed_from_u64(42);
        let p = Permutation(Box::new([2, 3, 1, 4, 0]));
        assert_eq!(p, Permutation::random(&mut rng, 5));
    }

    #[test]
    fn test_mul_mm() {
        let p0 = Permutation::rotation_left(3, 1);
        let p1 = Permutation::rotation_right(3, 1);
        assert_eq!(Permutation::identity(3), p0 * p1);
    }
    #[test]
    fn test_mul_mr() {
        let p0 = Permutation::rotation_left(3, 1);
        let p1 = Permutation::rotation_right(3, 1);
        assert_eq!(Permutation::identity(3), p0 * &p1);
    }
    #[test]
    fn test_mul_rm() {
        let p0 = Permutation::rotation_left(3, 1);
        let p1 = Permutation::rotation_right(3, 1);
        assert_eq!(Permutation::identity(3), &p0 * p1);
    }
    #[test]
    fn test_mul_rr() {
        let p0 = Permutation::rotation_left(3, 1);
        let p1 = Permutation::rotation_right(3, 1);
        assert_eq!(Permutation::identity(3), &p0 * &p1);
    }

    #[test]
    fn test_try_from_ok_owned() {
        let v = vec![2, 1, 0];
        let result = Ok(Permutation(v.clone().into()));
        assert_eq!(result, Permutation::try_from(v));
    }
    #[test]
    fn test_try_from_ok_vec_ref() {
        let v = vec![2, 1, 0];
        let result = Ok(Permutation(v.clone().into()));
        assert_eq!(result, Permutation::try_from(&v));
    }
    #[test]
    fn test_try_from_ok_slice_ref() {
        let v = vec![2, 1, 0];
        let result = Ok(Permutation(v.clone().into()));
        assert_eq!(result, Permutation::try_from(&v[..]));
    }
    #[test]
    fn test_try_from_err_missing_element_owned() {
        assert_eq!(Err(TryFromError), Permutation::try_from(vec![0, 1, 1]));
    }
    #[test]
    fn test_try_from_err_out_of_range_ref() {
        assert_eq!(Err(TryFromError), Permutation::try_from(&[2, 7, 1]));
    }
}

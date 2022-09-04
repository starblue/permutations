use core::fmt::Debug;

use std::ops;

#[cfg(feature = "random")]
use rand::Rng;

use crate::util::is_permutation;
#[cfg(feature = "random")]
use crate::Permutations;
use crate::TryFromError;

/// A permutation with a constant length fixed at compile time.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstPermutation<const N: usize>([usize; N]);
impl<const N: usize> ConstPermutation<N> {
    /// Returns the identity permutation.
    pub fn identity() -> Self {
        ConstPermutation((0..N).collect::<Vec<_>>().try_into().unwrap())
    }
    /// Returns the permutation which rotates r steps to the left.
    pub fn rotation_left(r: usize) -> Self {
        ConstPermutation(
            (0..N)
                .map(|i| (i + r) % N)
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        )
    }
    /// Returns the permutation which rotates r steps to the right.
    pub fn rotation_right(r: usize) -> Self {
        ConstPermutation::rotation_left(N - (r % N))
    }
    /// Returns the permutation which exchanges the elements at i and j.
    pub fn transposition(i: usize, j: usize) -> Self {
        assert!(i < N && j < N);
        ConstPermutation(
            (0..N)
                .map(|k| {
                    if k == i {
                        j
                    } else if k == j {
                        i
                    } else {
                        k
                    }
                })
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        )
    }

    /// Returns a random permutation.
    ///
    /// Uses a uniform distribution.
    #[cfg(feature = "random")]
    pub fn random<R>(rng: &mut R) -> Self
    where
        R: Rng,
    {
        let ps = Permutations::new(N);
        let i = rng.gen_range(0..ps.len());
        ps.get(i).expect("random index out of range")
    }
    /// Applies the permutation to an element.
    pub fn apply(&self, i: usize) -> usize {
        self.0[i]
    }
    /// Returns an array permuted by this permutation.
    pub fn permute<T>(&self, a: &[T; N]) -> [T; N]
    where
        T: Clone + Debug,
    {
        (0..N)
            .map(|i| a[self.apply(i)].clone())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }
    /// Returns the composition of the permutation with itself.
    pub fn square(&self) -> Self {
        self * self
    }
    /// Returns the composition of the permutation with itself `exp` number of times.
    pub fn pow(&self, exp: u32) -> Self {
        if exp == 0 {
            ConstPermutation::identity()
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
        let mut map = [0; N];
        for i in 0..N {
            let j = self.0[i];
            map[j] = i;
        }
        ConstPermutation(map)
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
impl<const N: usize> ops::Mul<ConstPermutation<N>> for ConstPermutation<N> {
    type Output = ConstPermutation<N>;
    fn mul(self, other: ConstPermutation<N>) -> Self::Output {
        let mut map = [0; N];
        for i in 0..N {
            map[i] = other.apply(self.apply(i));
        }
        ConstPermutation(map)
    }
}
impl<const N: usize> ops::Mul<ConstPermutation<N>> for &ConstPermutation<N> {
    type Output = ConstPermutation<N>;
    fn mul(self, other: ConstPermutation<N>) -> Self::Output {
        let mut map = [0; N];
        for i in 0..N {
            map[i] = other.apply(self.apply(i));
        }
        ConstPermutation(map)
    }
}
impl<const N: usize> ops::Mul<&ConstPermutation<N>> for ConstPermutation<N> {
    type Output = ConstPermutation<N>;
    fn mul(self, other: &ConstPermutation<N>) -> Self::Output {
        let mut map = [0; N];
        for i in 0..N {
            map[i] = other.apply(self.apply(i));
        }
        ConstPermutation(map)
    }
}
impl<const N: usize> ops::Mul<&ConstPermutation<N>> for &ConstPermutation<N> {
    type Output = ConstPermutation<N>;
    fn mul(self, other: &ConstPermutation<N>) -> Self::Output {
        let mut map = [0; N];
        for i in 0..N {
            map[i] = other.apply(self.apply(i));
        }
        ConstPermutation(map)
    }
}
impl<const N: usize> TryFrom<Vec<usize>> for ConstPermutation<N> {
    type Error = TryFromError;
    fn try_from(v: Vec<usize>) -> Result<ConstPermutation<N>, TryFromError> {
        ConstPermutation::<N>::try_from(&v[..])
    }
}
impl<'a, const N: usize> TryFrom<&'a Vec<usize>> for ConstPermutation<N> {
    type Error = TryFromError;
    fn try_from(v: &'a Vec<usize>) -> Result<ConstPermutation<N>, TryFromError> {
        ConstPermutation::<N>::try_from(&v[..])
    }
}
impl<const N: usize> TryFrom<&[usize]> for ConstPermutation<N> {
    type Error = TryFromError;
    fn try_from(a: &[usize]) -> Result<ConstPermutation<N>, TryFromError> {
        if a.len() == N && is_permutation(a) {
            Ok(ConstPermutation(a.try_into().unwrap()))
        } else {
            Err(TryFromError)
        }
    }
}
impl<const N: usize> TryFrom<&[usize; N]> for ConstPermutation<N> {
    type Error = TryFromError;
    fn try_from(a: &[usize; N]) -> Result<ConstPermutation<N>, TryFromError> {
        if is_permutation(a) {
            Ok(ConstPermutation(*a))
        } else {
            Err(TryFromError)
        }
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "random")]
    use rand::rngs::StdRng;
    #[cfg(feature = "random")]
    use rand::SeedableRng;

    use super::is_permutation;
    use super::ConstPermutation;
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
        let id = ConstPermutation::<3>::identity();
        assert_eq!(ConstPermutation([0, 1, 2]), id);
    }

    #[test]
    fn test_rotation_left() {
        let p = ConstPermutation::<3>::rotation_left(1);
        assert_eq!(ConstPermutation([1, 2, 0]), p);
    }

    #[test]
    fn test_rotation_right() {
        let p = ConstPermutation::<3>::rotation_right(1);
        assert_eq!(ConstPermutation([2, 0, 1]), p);
    }

    #[test]
    fn test_transposition() {
        let p = ConstPermutation::<3>::transposition(1, 2);
        assert_eq!(ConstPermutation([0, 2, 1]), p);
    }

    #[test]
    fn test_apply() {
        let p = ConstPermutation([0, 2, 1]);
        assert_eq!(2, p.apply(1));
    }

    #[test]
    fn test_permute() {
        let p = ConstPermutation([0, 2, 1]);
        assert_eq!(['a', 'c', 'b'], p.permute(&['a', 'b', 'c']));
    }

    #[test]
    fn test_square() {
        let p = ConstPermutation::<3>::rotation_left(1);
        assert_eq!(ConstPermutation([2, 0, 1]), p.square());
    }

    #[test]
    fn test_pow() {
        let p = ConstPermutation::<3>::rotation_left(1);
        assert_eq!(ConstPermutation::<3>::identity(), p.pow(3));
    }

    #[test]
    fn test_inv() {
        let p = ConstPermutation::<3>::rotation_left(1);
        assert_eq!(ConstPermutation::<3>::rotation_right(1), p.inv());
    }
    #[test]
    fn test_inv_identity() {
        let id = ConstPermutation::<3>::identity();
        assert_eq!(id, id.inv());
    }

    #[test]
    fn test_len() {
        let id = ConstPermutation::<3>::identity();
        assert_eq!(3, id.len());
    }

    #[test]
    fn test_is_empty_true() {
        let id = ConstPermutation::<0>::identity();
        assert_eq!(true, id.is_empty());
    }
    #[test]
    fn test_is_empty_false() {
        let id = ConstPermutation::<3>::identity();
        assert_eq!(false, id.is_empty());
    }

    #[test]
    fn test_is_even_identity() {
        let id = ConstPermutation::<3>::identity();
        assert_eq!(true, id.is_even());
    }
    #[test]
    fn test_is_even_rotation() {
        let p = ConstPermutation::<3>::rotation_left(1);
        assert_eq!(true, p.is_even());
    }
    #[test]
    fn test_is_even_transposition() {
        let p = ConstPermutation::<3>::transposition(0, 1);
        assert_eq!(false, p.is_even());
    }

    #[test]
    fn test_is_odd_identity() {
        let id = ConstPermutation::<3>::identity();
        assert_eq!(false, id.is_odd());
    }
    #[test]
    fn test_is_odd_rotation() {
        let p = ConstPermutation::<3>::rotation_left(1);
        assert_eq!(false, p.is_odd());
    }
    #[test]
    fn test_is_odd_transposition() {
        let p = ConstPermutation::<3>::transposition(0, 1);
        assert_eq!(true, p.is_odd());
    }

    #[test]
    fn test_sign_identity() {
        let id = ConstPermutation::<3>::identity();
        assert_eq!(1, id.sign());
    }
    #[test]
    fn test_sign_rotation() {
        let p = ConstPermutation::<3>::rotation_left(1);
        assert_eq!(1, p.sign());
    }
    #[test]
    fn test_sign_transposition() {
        let p = ConstPermutation::<3>::transposition(0, 1);
        assert_eq!(-1, p.sign());
    }

    #[cfg(feature = "random")]
    #[test]
    fn test_random() {
        let mut rng = StdRng::seed_from_u64(42);
        let p = ConstPermutation([2, 3, 1, 4, 0]);
        assert_eq!(p, ConstPermutation::<5>::random(&mut rng));
    }

    #[test]
    fn test_mul_mm() {
        let p0 = ConstPermutation::<3>::rotation_left(1);
        let p1 = ConstPermutation::<3>::rotation_right(1);
        assert_eq!(ConstPermutation::<3>::identity(), p0 * p1);
    }
    #[test]
    fn test_mul_mr() {
        let p0 = ConstPermutation::<3>::rotation_left(1);
        let p1 = ConstPermutation::<3>::rotation_right(1);
        assert_eq!(ConstPermutation::<3>::identity(), p0 * &p1);
    }
    #[test]
    fn test_mul_rm() {
        let p0 = ConstPermutation::<3>::rotation_left(1);
        let p1 = ConstPermutation::<3>::rotation_right(1);
        assert_eq!(ConstPermutation::<3>::identity(), &p0 * p1);
    }
    #[test]
    fn test_mul_rr() {
        let p0 = ConstPermutation::<3>::rotation_left(1);
        let p1 = ConstPermutation::<3>::rotation_right(1);
        assert_eq!(ConstPermutation::<3>::identity(), &p0 * &p1);
    }

    #[test]
    fn test_try_from_ok_owned() {
        let v = vec![2, 1, 0];
        let result = Ok(ConstPermutation([2, 1, 0]));
        assert_eq!(result, ConstPermutation::try_from(v));
    }
    // #[test]
    // fn test_try_from_ok_vec_ref() {
    //     let v = vec![2, 1, 0];
    //     let result = Ok(ConstPermutation([2, 1, 0]));
    //     assert_eq!(result, ConstPermutation::try_from(&v));
    // }
    #[test]
    fn test_try_from_ok_slice_ref() {
        let v = vec![2, 1, 0];
        let result = Ok(ConstPermutation([2, 1, 0]));
        assert_eq!(result, ConstPermutation::try_from(&v[..]));
    }
    #[test]
    fn test_try_from_err_missing_element_owned() {
        assert_eq!(
            Err(TryFromError),
            ConstPermutation::<3>::try_from(vec![0, 1, 1])
        );
    }
    #[test]
    fn test_try_from_err_out_of_range_ref() {
        assert_eq!(
            Err(TryFromError),
            ConstPermutation::<3>::try_from(&[2, 7, 1])
        );
    }
    #[test]
    fn test_try_from_err_wrong_length() {
        assert_eq!(
            Err(TryFromError),
            ConstPermutation::<3>::try_from(vec![0, 1])
        );
    }
}

//! Iterators and indexed access to permutations.

use core::fmt::Debug;
use core::marker::PhantomData;

/// The sequence of all permutations of `n` elements in lexicographic order.
#[derive(Clone, Debug)]
pub struct Permutations<P>
where
    P: Clone,
    P: TryFrom<Vec<usize>>,
{
    n: usize,
    len: usize,
    _phantom_data: PhantomData<P>,
}
impl<P> Permutations<P>
where
    P: Clone,
    P: TryFrom<Vec<usize>>,
{
    /// Constructs the sequence of permutations of `n` elements.
    pub fn new(n: usize) -> Self {
        let len = (2..=n).product::<usize>();
        Permutations {
            n,
            len,
            _phantom_data: PhantomData,
        }
    }
    /// Returns the permutation at a given index.
    pub fn get(&self, index: usize) -> Option<P>
    where
        <P as TryFrom<Vec<usize>>>::Error: Debug,
    {
        if index < self.len {
            let mut v = Vec::new();
            let mut es = (0..self.n).collect::<Vec<_>>();
            let mut divisor = self.len;
            let mut k = self.n;
            let mut i = index;
            while k > 0 {
                divisor /= k;
                let j = i / divisor;
                v.push(es.remove(j));
                i %= divisor;
                k -= 1;
            }
            Some(P::try_from(v).unwrap())
        } else {
            None
        }
    }
    /// Returns the number of permutations in the sequence.
    ///
    /// The sequence is never empty.
    /// Even for `n = 0` it contains the empty permutation.
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.len
    }
    /// Returns an iterator over the permutations.
    pub fn iter(&self) -> Iter<P> {
        Iter::new(self.clone())
    }
}
impl<P> IntoIterator for Permutations<P>
where
    P: Clone,
    P: TryFrom<Vec<usize>>,
    <P as TryFrom<Vec<usize>>>::Error: Debug,
{
    type Item = P;
    type IntoIter = Iter<P>;
    fn into_iter(self) -> Iter<P> {
        Iter::new(self)
    }
}
impl<'a, P> IntoIterator for &'a Permutations<P>
where
    P: Clone,
    P: TryFrom<Vec<usize>>,
    <P as TryFrom<Vec<usize>>>::Error: Debug,
{
    type Item = P;
    type IntoIter = Iter<P>;
    fn into_iter(self) -> Iter<P> {
        self.iter()
    }
}

#[derive(Clone, Debug)]
pub struct Iter<P>
where
    P: Clone,
    P: TryFrom<Vec<usize>>,
{
    permutations: Permutations<P>,
    next_index: usize,
}
impl<P> Iter<P>
where
    P: Clone,
    P: TryFrom<Vec<usize>>,
{
    fn new(permutations: Permutations<P>) -> Iter<P> {
        let next_index = 0;
        Iter {
            permutations,
            next_index,
        }
    }
}
impl<P> Iterator for Iter<P>
where
    P: Clone,
    P: TryFrom<Vec<usize>>,
    <P as TryFrom<Vec<usize>>>::Error: Debug,
{
    type Item = P;
    fn next(&mut self) -> Option<P> {
        if let Some(result) = self.permutations.get(self.next_index) {
            self.next_index += 1;
            Some(result)
        } else {
            None
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.permutations.len() - self.next_index;
        (len, Some(len))
    }
}
impl<P> ExactSizeIterator for Iter<P>
where
    P: Clone,
    P: TryFrom<Vec<usize>>,
    <P as TryFrom<Vec<usize>>>::Error: Debug,
{
}

#[cfg(test)]
mod tests {
    use crate::ConstPermutation;
    use crate::Permutation;
    use crate::Permutations;

    #[test]
    fn test_len_0() {
        let ps = Permutations::<Permutation>::new(0);
        assert_eq!(1, ps.len());
    }
    #[test]
    fn test_len_1() {
        let ps = Permutations::<Permutation>::new(1);
        assert_eq!(1, ps.len());
    }
    #[test]
    fn test_len_2() {
        let ps = Permutations::<Permutation>::new(2);
        assert_eq!(2, ps.len());
    }
    #[test]
    fn test_len_3() {
        let ps = Permutations::<Permutation>::new(3);
        assert_eq!(6, ps.len());
    }

    #[test]
    fn test_get() {
        let ps = Permutations::new(3);
        assert_eq!(Some(Permutation::try_from(&[0, 1, 2]).unwrap()), ps.get(0));
        assert_eq!(Some(Permutation::try_from(&[0, 2, 1]).unwrap()), ps.get(1));
        assert_eq!(Some(Permutation::try_from(&[1, 0, 2]).unwrap()), ps.get(2));
        assert_eq!(Some(Permutation::try_from(&[1, 2, 0]).unwrap()), ps.get(3));
        assert_eq!(Some(Permutation::try_from(&[2, 0, 1]).unwrap()), ps.get(4));
        assert_eq!(Some(Permutation::try_from(&[2, 1, 0]).unwrap()), ps.get(5));
        assert_eq!(None, ps.get(6));
    }

    #[test]
    fn test_iter() {
        let ps = Permutations::new(3);
        let mut iter = ps.iter();
        assert_eq!(
            Some(Permutation::try_from(&[0, 1, 2]).unwrap()),
            iter.next()
        );
        assert_eq!(
            Some(Permutation::try_from(&[0, 2, 1]).unwrap()),
            iter.next()
        );
        assert_eq!(
            Some(Permutation::try_from(&[1, 0, 2]).unwrap()),
            iter.next()
        );
        assert_eq!(
            Some(Permutation::try_from(&[1, 2, 0]).unwrap()),
            iter.next()
        );
        assert_eq!(
            Some(Permutation::try_from(&[2, 0, 1]).unwrap()),
            iter.next()
        );
        assert_eq!(
            Some(Permutation::try_from(&[2, 1, 0]).unwrap()),
            iter.next()
        );
        assert_eq!(None, iter.next());
    }

    #[test]
    fn test_into_iter_owned() {
        let ps = Permutations::new(3);
        let mut iter = ps.into_iter();
        assert_eq!(
            Some(Permutation::try_from(&[0, 1, 2]).unwrap()),
            iter.next()
        );
        assert_eq!(
            Some(Permutation::try_from(&[0, 2, 1]).unwrap()),
            iter.next()
        );
        assert_eq!(
            Some(Permutation::try_from(&[1, 0, 2]).unwrap()),
            iter.next()
        );
        assert_eq!(
            Some(Permutation::try_from(&[1, 2, 0]).unwrap()),
            iter.next()
        );
        assert_eq!(
            Some(Permutation::try_from(&[2, 0, 1]).unwrap()),
            iter.next()
        );
        assert_eq!(
            Some(Permutation::try_from(&[2, 1, 0]).unwrap()),
            iter.next()
        );
        assert_eq!(None, iter.next());
    }

    #[test]
    fn test_into_iter_ref() {
        let ps = &Permutations::new(3);
        let mut iter = ps.into_iter();
        assert_eq!(
            Some(Permutation::try_from(&[0, 1, 2]).unwrap()),
            iter.next()
        );
        assert_eq!(
            Some(Permutation::try_from(&[0, 2, 1]).unwrap()),
            iter.next()
        );
        assert_eq!(
            Some(Permutation::try_from(&[1, 0, 2]).unwrap()),
            iter.next()
        );
        assert_eq!(
            Some(Permutation::try_from(&[1, 2, 0]).unwrap()),
            iter.next()
        );
        assert_eq!(
            Some(Permutation::try_from(&[2, 0, 1]).unwrap()),
            iter.next()
        );
        assert_eq!(
            Some(Permutation::try_from(&[2, 1, 0]).unwrap()),
            iter.next()
        );
        assert_eq!(None, iter.next());
    }

    #[test]
    fn test_iter_exact_size_iterator_len() {
        let ps = &Permutations::<Permutation>::new(3);
        let mut iter = ps.into_iter();
        assert_eq!(6, iter.len());
        iter.next();
        assert_eq!(5, iter.len());
    }

    #[test]
    fn test_len_0_const() {
        let ps = Permutations::<ConstPermutation<0>>::new(0);
        assert_eq!(1, ps.len());
    }

    #[test]
    fn test_get_const() {
        let ps = Permutations::<ConstPermutation<3>>::new(3);
        assert_eq!(
            Some(ConstPermutation::<3>::try_from(&[0, 1, 2]).unwrap()),
            ps.get(0)
        );
        assert_eq!(
            Some(ConstPermutation::<3>::try_from(&[0, 2, 1]).unwrap()),
            ps.get(1)
        );
        assert_eq!(
            Some(ConstPermutation::<3>::try_from(&[1, 0, 2]).unwrap()),
            ps.get(2)
        );
        assert_eq!(
            Some(ConstPermutation::<3>::try_from(&[1, 2, 0]).unwrap()),
            ps.get(3)
        );
        assert_eq!(
            Some(ConstPermutation::<3>::try_from(&[2, 0, 1]).unwrap()),
            ps.get(4)
        );
        assert_eq!(
            Some(ConstPermutation::<3>::try_from(&[2, 1, 0]).unwrap()),
            ps.get(5)
        );
        assert_eq!(None, ps.get(6));
    }

    #[test]
    fn test_iter_const() {
        let ps = Permutations::<ConstPermutation<3>>::new(3);
        let mut iter = ps.iter();
        assert_eq!(
            Some(ConstPermutation::<3>::try_from(&[0, 1, 2]).unwrap()),
            iter.next()
        );
        assert_eq!(
            Some(ConstPermutation::<3>::try_from(&[0, 2, 1]).unwrap()),
            iter.next()
        );
        assert_eq!(
            Some(ConstPermutation::<3>::try_from(&[1, 0, 2]).unwrap()),
            iter.next()
        );
        assert_eq!(
            Some(ConstPermutation::<3>::try_from(&[1, 2, 0]).unwrap()),
            iter.next()
        );
        assert_eq!(
            Some(ConstPermutation::<3>::try_from(&[2, 0, 1]).unwrap()),
            iter.next()
        );
        assert_eq!(
            Some(ConstPermutation::<3>::try_from(&[2, 1, 0]).unwrap()),
            iter.next()
        );
        assert_eq!(None, ps.get(6));
    }
}

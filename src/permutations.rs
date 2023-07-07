//! Iterators and indexed access to permutations.

use crate::Permutation;

/// The sequence of all permutations of `n` elements in lexicographic order.
#[derive(Clone, Debug)]
pub struct Permutations {
    n: usize,
    len: usize,
}

impl Permutations {
    /// Constructs the sequence of permutations of `n` elements.
    pub fn new(n: usize) -> Self {
        let len = (2..=n).product::<usize>();
        Self { n, len }
    }

    /// Returns the permutation at a given index.
    pub fn get(&self, index: usize) -> Option<Permutation> {
        if index >= self.len {
            return None;
        }
        let mut v = vec![];
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
        Some(Permutation::try_from(v).unwrap())
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
    pub fn iter(&self) -> Iter {
        Iter::new(self.clone())
    }
}

impl IntoIterator for Permutations {
    type Item = Permutation;
    type IntoIter = Iter;
    fn into_iter(self) -> Iter {
        Iter::new(self)
    }
}

impl<'a> IntoIterator for &'a Permutations {
    type Item = Permutation;
    type IntoIter = Iter;
    fn into_iter(self) -> Iter {
        self.iter()
    }
}

#[derive(Clone, Debug)]
pub struct Iter {
    permutations: Permutations,
    next_index: usize,
}

impl Iter {
    fn new(permutations: Permutations) -> Self {
        Self {
            permutations,
            next_index: 0,
        }
    }
}

impl Iterator for Iter {
    type Item = Permutation;
    fn next(&mut self) -> Option<Permutation> {
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

impl ExactSizeIterator for Iter {}

#[cfg(test)]
mod tests {
    use crate::Permutation;
    use crate::Permutations;

    #[test]
    fn test_len_0() {
        let ps = Permutations::new(0);
        assert_eq!(1, ps.len());
    }
    #[test]
    fn test_len_1() {
        let ps = Permutations::new(1);
        assert_eq!(1, ps.len());
    }
    #[test]
    fn test_len_2() {
        let ps = Permutations::new(2);
        assert_eq!(2, ps.len());
    }
    #[test]
    fn test_len_3() {
        let ps = Permutations::new(3);
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
        let ps = &Permutations::new(3);
        let mut iter = ps.into_iter();
        assert_eq!(6, iter.len());
        iter.next();
        assert_eq!(5, iter.len());
    }
}

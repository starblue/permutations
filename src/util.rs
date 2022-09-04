/// Utility functions.

/// Returns true if a slice is a permutation.
///
/// That is, all the elements in `0..len` occur exactly once in the slice.
pub fn is_permutation(v: &[usize]) -> bool {
    let n = v.len();
    let mut seen = (0..n).map(|_| false).collect::<Vec<_>>();
    for &e in v {
        if (0..n).contains(&e) {
            seen[e] = true;
        }
    }
    seen.into_iter().all(|b| b)
}

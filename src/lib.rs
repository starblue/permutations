//! Permutations.
//!
//! Constructs single permutations and provides operations
//! such as composition, inverse and exponentiation.
//! Allows iterate over permutations in lexicographic order and alos
//! to access them by index.
//!
//! ## Crate Status
//!
//! Experimental
//!
//! ### Limitations
//! - Depending on the number of bits in `usize` you can iterate over
//!   permutations of at most 20 elements for 64 bits, 12 elements for 32 bits,
//!   or 8 elements for 16 bits.  The same applies to indexed access.
//!
//! ## Crate Feature Flags
//! - `random`
//!   - Off by default.
//!   - Adds a dependency to the `rand` crate.
//!   - Adds the method [`random`](Permutation::random)
//!     to generate a random permutation of `n` elements.

#![warn(missing_docs)]

mod permutation;
#[doc(inline)]
pub use crate::permutation::Permutation;

mod permutations;
#[doc(inline)]
pub use crate::permutations::Permutations;

#[cfg(test)]
mod tests {
    fn factorial(n: u128) -> u128 {
        (1..=n).product::<u128>()
    }

    #[test]
    fn test_limits() {
        assert!(factorial(8) < 2_u128.pow(16));
        assert!(factorial(9) >= 2_u128.pow(16));
        assert!(factorial(12) < 2_u128.pow(32));
        assert!(factorial(13) >= 2_u128.pow(32));
        assert!(factorial(20) < 2_u128.pow(64));
        assert!(factorial(21) >= 2_u128.pow(64));
    }
}

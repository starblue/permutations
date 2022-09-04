//! Errors returned by this library.

use std::error;
use std::fmt;

/// The error returned when a slice cannot be converted to a permutation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TryFromError;
impl fmt::Display for TryFromError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ill-formed slice to permutation conversion attempted",)
    }
}
impl error::Error for TryFromError {}

//! Compatibility wrapper around function pointers to support <=1.69.0 versions of Rust

use core::fmt;
use core::ops::Deref;

/// Compatibility wrapper around function pointers to support <=1.69.0 versions of Rust
pub struct CompatFnWrapper<F>(pub(crate) F);

impl<F> fmt::Debug for CompatFnWrapper<F> {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<fn>")
    }
}

impl<F> Deref for CompatFnWrapper<F> {
    type Target = F;
    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

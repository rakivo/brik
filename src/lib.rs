// TODO(#1): Implement tests
// TODO(#7): "no_std" feature
// TODO(#2): Implement F/D-extension: (single/double precision)
// TODO(#4): Implement C-extension: (compressed instructions (16-bit))

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
pub(crate) extern crate alloc as std;

#[macro_use]
pub mod util;

pub mod asm;
pub mod rv64;
pub mod reloc;

pub use rv32;
pub use object;

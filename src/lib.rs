// TODO(#1): Implement tests
// TODO(#6): Add a feature to strip `miette` dependency
// TODO(#2): Implement F/D-extension: (single/double precision)
// TODO(#4): Implement C-extension: (compressed instructions (16-bit))

#[macro_use]
pub mod util;

pub mod asm;
pub mod rv64;
pub mod reloc;

pub use object;
pub use asm_riscv as rv32;

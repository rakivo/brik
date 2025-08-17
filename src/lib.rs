// TODO(#1): Implement tests
// TODO(#30): API to get current label
// TODO(#27): Generate `new_symbol_*` functions
// TODO(#22): Support variable word-sizes
// TODO(#13): Support for `GOT` and `TLS` relocations
//   e.g. R_RISCV_GOT_HI20 and R_RISCV_TLS_GD_HI20.
//   For example, an instruction loading a 32‑bit address will generate an
//   R_RISCV_HI20 for the AUIPC's immediate and an R_RISCV_LO12_I for the following ADDI.
//   The assembler should provide APIs like `add_reloc(section_id, offset, RelocKind::Hi20, symbol_id)`
//   and correctly pair them
// TODO(#14): Support for Section attributes
// TODO(#15): Support MACH-O/COFF relocation kinds
// TODO(#17): Implement API for emission of `pic/nopic`, `relax/norelax`
// TODO(#9): `Imm` enum for convenient im usage
// TODO(#2): Implement F/D-extension: (single/double precision)
// TODO(#4): Implement C-extension: (compressed instructions (16-bit))

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
pub(crate) extern crate alloc as std;

#[macro_use]
pub mod util;

pub mod asm;
pub mod misc_enc;

pub use object;
pub use brik_rv32 as rv32;
pub use brik_rv64 as rv64;

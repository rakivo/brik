// TODO(#1): Implement tests
// TODO(#10): Implement API for emission of COMDAT sections
//   Support COMDAT grouping so that identically‑named sections (or data items) can be folded at link time.
//   .e.g. template or inline function instantiations often require sections marked "any" or "same_size" COMDAT.
//   The object API already has a `add_comdat(Comdat { name, kind }) -> ComdatId` and ability to associate sections with it.
//   Expose this via the assembler: e.g. a directive or API `assembler.add_comdat(name, kind)`
//   and then allow assigning a section to that COMDAT.
//   On Mach-O/COFF this uses special auxiliary symbols under the hood, but on ELF it uses SHT_GROUP
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
pub mod rv64;
pub mod reloc;
pub mod misc_enc;

pub use object;
pub use brik_rv32 as rv32;

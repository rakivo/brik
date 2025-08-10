//! Abstraction over RISC-V relocation kinds

use crate::object::write::SymbolId;

#[derive(Eq, Copy, Clone, Debug, PartialEq)]
pub enum PcrelPart {
    Hi20,
    Lo12I,
    Lo12S,
}

#[derive(Debug)]
pub struct Reloc {
    pub offset: u64,
    pub symbol: SymbolId,
    pub rtype: RelocKind,
    pub addend: i64,
}

#[derive(Eq, Copy, Clone, Debug, PartialEq)]
pub enum RelocKind {
    Branch     = 16, // R_RISCV_BRANCH
    PcrelHi20  = 23, // R_RISCV_PCREL_HI20
    PcrelLo12I = 24, // R_RISCV_PCREL_LO12_I
    CallPlt    = 19, // R_RISCV_CALL_PLT
    Call       = 2   // R_RISCV_CALL
}

impl RelocKind {
    #[inline(always)]
    pub const fn code(self) -> u32 {
        self as _
    }
}


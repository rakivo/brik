//! Abstraction over RISC-V relocation kinds

#[derive(Eq, Copy, Clone, Debug, PartialEq)]
pub enum RiscvReloc {
    Branch,      // R_RISCV_BRANCH (16)
    PcrelHi20,   // R_RISCV_PCREL_HI20 (23)
    PcrelLo12I,  // R_RISCV_PCREL_LO12_I (24)
    CallPlt,     // R_RISCV_CALL_PLT (19)
    Call         // R_RISCV_CALL (2)
}

impl RiscvReloc {
    #[inline(always)]
    pub const fn code(self) -> u32 {
        match self {
            Self::Branch => 16,
            Self::PcrelHi20 => 23,
            Self::PcrelLo12I => 24,
            Self::CallPlt => 19,
            Self::Call => 2
        }
    }
}


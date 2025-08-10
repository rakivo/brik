//! Abstraction over RISC-V relocation kinds

#[derive(Eq, Copy, Clone, PartialEq)]
pub enum RiscvReloc {
    Branch,
    PcrelHi20,
    PcrelLo12I,
    CallPlt,
    // ...
}

impl RiscvReloc {
    #[inline(always)]
    pub const fn code(self) -> u32 {
        match self {
            Self::Branch => 16,
            Self::PcrelHi20 => 23,
            Self::PcrelLo12I => 24,
            Self::CallPlt => 19,
        }
    }
}


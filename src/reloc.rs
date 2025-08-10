#[derive(Clone, Copy, PartialEq, Eq)]
pub enum RiscvReloc {
    PcrelHi20,
    PcrelLo12I,
    CallPlt,
    // ...
}

impl RiscvReloc {
    #[inline(always)]
    pub const fn code(self) -> u32 {
        match self {
            Self::PcrelHi20 => 23,
            Self::PcrelLo12I => 24,
            Self::CallPlt => 19,
        }
    }
}


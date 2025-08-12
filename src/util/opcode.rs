/// RISC-V RV64I and M-extension opcodes for instruction encoding.
#[repr(u32)]
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum RV64Opcode {
    /// LOAD        opcode (`0x03`, binary `0000011`) for load instructions (e.g., LD, LWU).
    Load    = 0x03,

    /// STORE       opcode (`0x23`, binary `1000011`) for store instructions (e.g., SD).
    Store   = 0x23,

    /// OP          opcode (`0x33`, binary `0110011`) for register-register operations (e.g., MUL, ADD).
    Op      = 0x33,

    /// OP-32       opcode (`0x3B`, binary `0111011`) for 32-bit register-register operations (e.g., ADDW, SUBW, SLLW, SRLW, SRAW).
    Op32    = 0x3B,

    /// OP-IMM-32   opcode (`0x1B`, binary `0011011`) for 32-bit immediate operations (e.g., ADDIW, SLLIW, SRLIW, SRAIW).
    OpImm32 = 0x1B,

    /// OP-IMM      opcode (`0x13`, binary `0010011`) for immediate operations (e.g., ADDI).
    OpImm   = 0x13,

    /// LUI         opcode (`0x37`, binary `0110111`) for Load Upper Immediate.
    Lui     = 0x37,

    /// AMO         opcode (`0x2F`, binary `0101111`) for atomic operations (e.g., LR.W, AMOADD.D).
    Amo     = 0x2F
}

impl RV64Opcode {
    /// Returns the 7-bit opcode value as a `u32` for instruction encoding.
    #[inline(always)]
    pub const fn as_u32(self) -> u32 {
        self as _
    }
}

/// Memory ordering bits for A-extension instructions (aq: acquire, rl: release).
#[repr(u8)]
#[derive(Eq, Copy, Clone, Debug, PartialEq)]
pub enum AqRl {
    /// No ordering constraints       (aq=0, rl=0).
    None           = 0b00,
    /// Release semantics             (aq=0, rl=1).
    Release        = 0b01,
    /// Acquire semantics             (aq=1, rl=0).
    Acquire        = 0b10,
    /// Acquire and release semantics (aq=1, rl=1).
    AcquireRelease = 0b11,
}

impl AqRl {
    /// Returns the 2-bit aq/rl value as a `u32` for instruction encoding.
    #[inline(always)]
    pub const fn as_u32(self) -> u32 {
        self as u8 as u32
    }
}



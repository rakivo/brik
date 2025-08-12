//! RV64 extension for asm_riscv (RV32)

use crate::util::misc;
use crate::asm_riscv::{I, Reg};
use crate::util::into_bytes::IntoBytes;

use std::mem;

use smallvec::SmallVec;

pub type RV64Inst = SmallVec<[u8; mem::size_of::<u32>() * 6]>;

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
}

use RV64Opcode::*;

impl RV64Opcode {
    /// Returns the 7-bit opcode value as a `u32` for instruction encoding.
    #[inline(always)]
    pub const fn as_u32(self) -> u32 {
        self as _
    }
}

/// Encode RISC-V LD (Load Doubleword) instruction.
/// imm is a signed 12-bit offset.
///
/// # Example
///
/// Runnable check for an LD with offset 0:
/// ```
/// use brik::asm_riscv::Reg;
/// use brik::util::rv64::encode_ld;
/// let inst = encode_ld(Reg::S1, Reg::S2, 0);
/// assert_eq!(inst, 0x093483); // LD a0, 0(sp)
/// ```
#[inline(always)]
pub const fn encode_ld(rd: Reg, rs1: Reg, imm: i16) -> u32 {
    // For I-type instructions, immediate is stored directly in bits [31:20]
    // The sign extension is handled automatically by the hardware
    let imm12 = (imm as u32) & 0xfff;
    (imm12 << 20)              // imm[11:0]
        | ((rs1 as u32) << 15) // rs1 (base)
        | (3 << 12)            // funct3 (width) = 3 for LD (64-bit load)
        | ((rd as u32) << 7)   // rd (dest)
        | Load.as_u32()
}

/// Encode RISC-V SD (Store Doubleword) instruction.
/// imm is a signed 12-bit offset.
///
/// # Example
/// ```
/// use brik::asm_riscv::Reg;
/// use brik::util::rv64::encode_sd;
/// let inst = encode_sd(Reg::A0, Reg::SP, 0);
/// assert_eq!(inst, 0xa13023); // sd a0, 0(sp)
/// ```
#[inline(always)]
pub const fn encode_sd(rs2: Reg, rs1: Reg, imm: i16) -> u32 {
    // For S-type instructions, immediate is split: [11:5] and [4:0]
    let imm12    = (imm as u32) & 0xfff;
    let imm_low  = imm12 & 0x1f;        // imm[4:0]
    let imm_high = (imm12 >> 5) & 0x7f; // imm[11:5]

    (imm_high << 25)           // imm[11:5]
        | ((rs2 as u32) << 20) // rs2 (source register)
        | ((rs1 as u32) << 15) // rs1 (base register)
        | (3 << 12)            // funct3 (width) = 3 for SD (64-bit store)
        | (imm_low << 7)       // imm[4:0]
        | Store.as_u32()
}

/// Encode RISC-V MUL (M-extension) instruction.
///
/// # Example
/// ```
/// use brik::asm_riscv::Reg;
/// use brik::util::rv64::encode_mul;
/// let inst = encode_mul(Reg::A0, Reg::A1, Reg::A2);
/// assert_eq!(inst, 0x02c58533); // mul a0, a1, a2
/// ```
#[inline(always)]
pub const fn encode_mul(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    (0x01 << 25)               // funct7 = 0x01
        | ((rs2 as u32) << 20) // multiplier
        | ((rs1 as u32) << 15) // multiplicand
        | (0x0 << 12)          // funct3 = 0x0 for mul
        | ((rd as u32) << 7)   // dest
        | Op.as_u32()
}

/// Expand `li rd, imm` for RV64 and return its encoding as little-endian bytes.
///
/// # Example
/// ```
/// use brik::asm_riscv::Reg;
/// use brik::util::rv64::encode_li_rv64_little;
///
/// // imm fits into 12 bits
/// let bytes = encode_li_rv64_little(Reg::A0, 42);
///
/// assert_eq!{
///     bytes.as_slice(),
///     [0x13, 0x05, 0xa0, 0x02] // addi a0, zero, 42
/// };
///
/// // imm doesn't fit into 12 bits
/// let bytes = encode_li_rv64_little(Reg::A1, 0x12345);
/// assert_eq!{
///     bytes.as_slice(),
///     [
///         0xb7, 0x25, 0x01, 0x00, // lui  a1, 0x12
///         0x93, 0x85, 0x55, 0x34  // addi a1, a1, 0x345
///     ]
/// };
/// ```
pub fn encode_li_rv64_little(rd: Reg, imm: i64) -> RV64Inst {
    let mut bytes = RV64Inst::new();

    if misc::fits_into_12_bits(imm) {
        let inst = I::ADDI { d: rd, s: Reg::ZERO, im: imm as i16 };
        bytes.extend_from_slice(&inst.into_bytes());
        return bytes
    }

    let upper12 = ((imm + 0x800) >> 12) as i32;
    let hi_inst = I::LUI { d: rd, im: upper12 };
    bytes.extend_from_slice(&hi_inst.into_bytes());

    let lower12 = imm - ((upper12 as i64) << 12);
    debug_assert!{
        misc::fits_into_12_bits(lower12),
        "lower12 bits of `li` rv64 little-endian don't fit into 12 bits: {lower12}"
    };

    let lo_inst = I::ADDI { d: rd, s: rd, im: lower12 as i16 };
    bytes.extend_from_slice(&lo_inst.into_bytes());

    bytes
}

// =============================================================================
// RV64I-specific instructions (Version 2.1) (32-bit operations with sign extension)
// =============================================================================

/// Encode RISC-V ADDW (Add Word) instruction - RV64 only.
/// Performs 32-bit addition and sign-extends the result to 64 bits.
///
/// # Example
/// ```
/// use brik::asm_riscv::Reg;
/// use brik::util::rv64::encode_addw;
/// let inst = encode_addw(Reg::A0, Reg::A1, Reg::A2);
/// assert_eq!(inst, 0xc5853b);
/// // addw a0, a1, a2
/// ```
#[inline(always)]
pub const fn encode_addw(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    // opcode 0x3B, funct3 = 0, funct7 = 0
    ((rs2 as u32) << 20)
        | ((rs1 as u32) << 15)
        | (0 << 12)            // funct3 = 0
        | ((rd as u32) << 7)
        | (0 << 25)            // funct7 = 0
        | Op32.as_u32()
}

/// Encode RISC-V SUBW (Subtract Word) instruction - RV64 only.
/// Performs 32-bit subtraction and sign-extends the result to 64 bits.
///
/// # Example
///
/// ```rust
/// use brik::asm_riscv::Reg;
/// use brik::util::rv64::encode_subw;
/// assert_eq!(encode_subw(Reg::A0, Reg::A1, Reg::A2), 0x40c5853b);
/// ```
#[inline(always)]
pub const fn encode_subw(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    // opcode 0x3B, funct3 = 0, funct7 = 0x20
    ((rs2 as u32) << 20)       // src2
        | ((rs1 as u32) << 15) // src1
        | (0 << 12)
        | ((rd as u32) << 7)   // dest
        | (0x20 << 25)         // funct7 = 0b0100000
        | Op32.as_u32()
}

/// Encode RISC-V ADDIW (Add Immediate Word) instruction - RV64 only.
/// Performs 32-bit addition with immediate and sign-extends the result.
///
/// # Example
/// ```
/// use brik::asm_riscv::Reg;
/// use brik::util::rv64::encode_addiw;
/// let inst = encode_addiw(Reg::A0, Reg::A1, 42);
/// assert_eq!(inst, 0x2a5851b);
/// // addiw a0, a1, 42
/// ```
#[inline(always)]
pub const fn encode_addiw(rd: Reg, rs1: Reg, imm: i16) -> u32 {
    let imm12 = (imm as u32) & 0xfff;
    (imm12 << 20)              // [11:0] I-imm
        | ((rs1 as u32) << 15) // src
        | (0 << 12)            // funct3 = 0 (ADDIW)
        | ((rd as u32) << 7)   // dest
        | OpImm32.as_u32()
}

/// Encode RISC-V SLLW (Shift Left Logical Word) instruction - RV64 only.
/// Performs 32-bit left shift and sign-extends the result.
///
/// # Example
///
/// ```rust
/// use brik::asm_riscv::Reg;
/// use brik::util::rv64::encode_sllw;
/// assert_eq!(encode_sllw(Reg::A0, Reg::A1, Reg::A2), 0xc5953b);
/// ```
#[inline(always)]
pub const fn encode_sllw(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    ((rs2 as u32) << 20)       // rs2 (shift amount in lower 5 bits) (src2)
        | ((rs1 as u32) << 15) // rs1 (src1)
        | (1 << 12)            // funct3 = 1 for SLLW
        | ((rd as u32) << 7)   // rd
        | (0 << 25)            // funct7 = 0000000 for SLLW
        | 0x3B                 // opcode = 0x3B for OP-32
}

/// Encode RISC-V SRLW (Shift Right Logical Word) instruction - RV64 only.
/// Performs 32-bit logical right shift and sign-extends the result.
///
/// # Example
///
/// ```rust
/// use brik::asm_riscv::Reg;
/// use brik::util::rv64::encode_srlw;
/// assert_eq!(encode_srlw(Reg::A0, Reg::A1, Reg::A2), 0xc5d53b);
/// ```
#[inline(always)]
pub const fn encode_srlw(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    ((rs2 as u32) << 20)       // rs2 (shift amount in lower 5 bits)
        | ((rs1 as u32) << 15) // rs1
        | (5 << 12)            // funct3 = 5 for SRLW
        | ((rd as u32) << 7)   // rd
        | (0 << 25)            // funct7 = 0000000 for SRLW
        | 0x3B                 // opcode = 0x3B for OP-32
}

/// Encode RISC-V SRAW (Shift Right Arithmetic Word) instruction - RV64 only.
/// Performs 32-bit arithmetic right shift and sign-extends the result.
///
/// # Example
///
/// ```rust
/// use brik::asm_riscv::Reg;
/// use brik::util::rv64::encode_sraw;
/// assert_eq!(encode_sraw(Reg::A0, Reg::A1, Reg::A2), 0x40c5d53b);
/// ```
#[inline(always)]
pub const fn encode_sraw(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    ((rs2 as u32) << 20)       // rs2 (shift amount in lower 5 bits)
        | ((rs1 as u32) << 15) // rs1
        | (5 << 12)            // funct3 = 5 for SRAW
        | ((rd as u32) << 7)   // rd
        | (0x20 << 25)         // funct7 = 0100000 for SRAW
        | 0x3B                 // opcode = 0x3B for OP-32
}

#[inline(always)]
const fn const_32_contains_shamt_(shamt: i8) -> bool {
    shamt > 0 && shamt < 32
}

/// # Example
///
/// ```rust
/// use brik::asm_riscv::Reg;
/// use brik::util::rv64::encode_slliw;
/// assert_eq!(encode_slliw(Reg::A0, Reg::A1, 4), 0x45951b);
/// ```
#[inline(always)]
pub const fn encode_slliw(rd: Reg, rs1: Reg, shamt: i8) -> u32 {
    debug_assert!(const_32_contains_shamt_(shamt), "slliw shamt must be <32");
    let sh = (shamt as u32) & 0x1f;
    // imm[11:0] carries funct7 in [11:5] and shamt in [4:0] but for SLLIW funct7=0
    (sh << 20)                 // shamt -> bits 24:20
        | ((rs1 as u32) << 15) // src1
        | (1 << 12)            // funct3 = 1
        | ((rd as u32) << 7)   // dest
        | 0x1B                 // opcode = OP-IMM-32
}

/// # Example
///
/// ```rust
/// use brik::asm_riscv::Reg;
/// use brik::util::rv64::encode_srliw;
/// assert_eq!(encode_srliw(Reg::A0, Reg::A1, 4), 0x45d51b);
/// ```
#[inline(always)]
pub const fn encode_srliw(rd: Reg, rs1: Reg, shamt: i8) -> u32 {
    debug_assert!(const_32_contains_shamt_(shamt), "srliw shamt must be <32");
    let sh = (shamt as u32) & 0x1f;
    (sh << 20)                 // shamt -> bits 24:20, funct7=0 for SRLIW
        | ((rs1 as u32) << 15) // src1
        | (5 << 12)            // funct3 = 5
        | ((rd as u32) << 7)   // dest
        | 0x1B                 // opcode = OP-IMM-32
}

/// # Example
///
/// ```rust
/// use brik::asm_riscv::Reg;
/// use brik::util::rv64::encode_sraiw;
/// assert_eq!(encode_sraiw(Reg::A0, Reg::A1, 4), 0x4045d51b);
/// ```
#[inline(always)]
pub const fn encode_sraiw(rd: Reg, rs1: Reg, shamt: i8) -> u32 {
    debug_assert!(const_32_contains_shamt_(shamt), "sraiw shamt must be <32");
    let sh = (shamt as u32) & 0x1f;
    // funct7=0x20 in bits 31:25 and shamt in 24:20
    ((0x20 << 5 | sh) << 20)   // combine funct7 <<5 | shamt -> then <<20 places into bits 31:20
        | ((rs1 as u32) << 15) // src1
        | (5 << 12)            // funct3 = 5
        | ((rd as u32) << 7)   // dest
        | 0x1B                 // opcode = OP-IMM-32
}

// ---------------- Loads (unsigned variants) ----------------

/// # Example
///
/// ```rust
/// use brik::asm_riscv::Reg;
/// use brik::util::rv64::encode_lwu;
/// assert_eq!(encode_lwu(Reg::A0, Reg::SP, 0), 0x16503);
/// ```
#[inline(always)]
pub const fn encode_lwu(rd: Reg, rs1: Reg, imm: i16) -> u32 {
    let imm12 = (imm as u32) & 0xfff;
    (imm12 << 20)              // [11:0] imm
        | ((rs1 as u32) << 15) // src1
        | (6 << 12)            // funct3 = 6 for LWU
        | ((rd as u32) << 7)   // dest
        | 0x03                 // opcode = LOAD
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_negative_immediate_ld() {
        // test that negative immediates work correctly
        let inst = encode_ld(Reg::A0, Reg::SP, -8);
        // should encode -8 correctly in the immediate field
        assert_eq!(inst & 0xfff00000, 0xff800000); // upper bits should be set for -8
    }

    #[test]
    fn test_negative_immediate_sd() {
        // test that negative immediates work correctly for SD too
        let inst = encode_sd(Reg::A0, Reg::SP, -8);
        // for S-type, immediate is split but should still represent -8
        let imm_high = (inst >> 25) & 0x7f;
        let imm_low  = (inst >>  7) & 0x1f;
        let reconstructed_imm = ((imm_high << 5) | imm_low) as i16;
        // due to 2's complement, this should reconstruct to -8
        assert_eq!((reconstructed_imm << 4) >> 4, -8); // sext from 12-bit
    }
}

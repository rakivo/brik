//! RV64 extension for asm_riscv (RV32)

use crate::asm_riscv::{I, Reg};
use crate::util::into_bytes::IntoBytes;

use std::mem;

use smallvec::SmallVec;

pub type RV64Bytes = SmallVec<[u8; mem::size_of::<u32>() * 3]>;

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
        | ((rs1 as u32) << 15) // rs1
        | (3 << 12)            // funct3 = 3 for LD (64-bit load)
        | ((rd as u32) << 7)   // rd
        | 0x03                 // opcode = 0x03 for LOAD
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
        | (3 << 12)            // funct3 = 3 for SD (64-bit store)
        | (imm_low << 7)       // imm[4:0]
        | 0x23                 // opcode = 0x23 for STORE
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
      (0x01 << 25)         // funct7 = 0x01
    | ((rs2 as u32) << 20)
    | ((rs1 as u32) << 15)
    | (0x0 << 12)          // funct3 = 0x0 for mul
    | ((rd as u32) << 7)
    | 0x33                 // opcode = 0x33 (OP)
}

/// Expand `li rd, imm` for RV64 and return its encoding as little-endian bytes.
///
/// # Example
/// ```
/// use brik::asm_riscv::Reg;
/// use brik::util::rv64::encode_li_rv64_little;
/// let bytes = encode_li_rv64_little(Reg::A0, 42);
/// assert_eq!(bytes.as_slice(), [0x13, 0x05, 0xa0, 0x02]); // addi a0, zero, 42
/// ```
pub fn encode_li_rv64_little(rd: Reg, imm: i64) -> RV64Bytes {
    let mut bytes = RV64Bytes::new();

    if (-2048..=2047).contains(&imm) {
        // fits into 12 bytes
        let inst = I::ADDI { d: rd, s: Reg::ZERO, im: imm as i16 };
        let word = u32::from(inst);
        bytes.extend_from_slice(&word.into_bytes());
        return bytes
    }

    let upper = ((imm + 0x800) >> 12) as i32;
    let hi_inst = I::LUI { d: rd, im: upper };
    let hi_word = u32::from(hi_inst);
    bytes.extend_from_slice(&hi_word.into_bytes());

    let low12 = imm - ((upper as i64) << 12);
    debug_assert!((-2048..=2047).contains(&low12));

    let lo_inst = I::ADDI { d: rd, s: rd, im: low12 as i16 };
    let lo_word = u32::from(lo_inst);
    bytes.extend_from_slice(&lo_word.into_bytes());

    bytes
}

// =============================================================================
// RV64I-specific instructions (32-bit operations with sign extension)
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
        | 0x3B                 // opcode
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
    ((rs2 as u32) << 20)
        | ((rs1 as u32) << 15)
        | (0 << 12)
        | ((rd as u32) << 7)
        | (0x20 << 25)         // funct7 = 0b0100000
        | 0x3B
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
    (imm12 << 20)
        | ((rs1 as u32) << 15)
        | (0 << 12)            // funct3 = 0
        | ((rd as u32) << 7)
        | 0x1B                 // opcode = 0x1B
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
    ((rs2 as u32) << 20)       // rs2 (shift amount in lower 5 bits)
        | ((rs1 as u32) << 15) // rs1
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
const fn const_32_shamt_constains_(shamt: i8) -> bool {
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
    debug_assert!(const_32_shamt_constains_(shamt), "slliw shamt must be <32");
    let sh = (shamt as u32) & 0x1f;
    // imm[11:0] carries funct7 in [11:5] and shamt in [4:0] but for SLLIW funct7=0
    ((sh) << 20)             // shamt -> bits 24:20
        | ((rs1 as u32) << 15)
        | (1 << 12)          // funct3 = 1
        | ((rd as u32) << 7)
        | 0x1B
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
    debug_assert!(const_32_shamt_constains_(shamt), "srliw shamt must be <32");
    let sh = (shamt as u32) & 0x1f;
    ((sh) << 20)             // shamt -> bits 24:20, funct7=0 for SRLIW
        | ((rs1 as u32) << 15)
        | (5 << 12)          // funct3 = 5
        | ((rd as u32) << 7)
        | 0x1B
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
    debug_assert!(const_32_shamt_constains_(shamt), "sraiw shamt must be <32");
    let sh = (shamt as u32) & 0x1f;
    // funct7=0x20 in bits 31:25 and shamt in 24:20
    ((0x20 << 5 | sh) << 20) // combine funct7 <<5 | shamt -> then <<20 places into bits 31:20
        | ((rs1 as u32) << 15)
        | (5 << 12)          // funct3 = 5
        | ((rd as u32) << 7)
        | 0x1B
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
    (imm12 << 20)
        | ((rs1 as u32) << 15)
        | (6 << 12)            // funct3 = 6 for LWU
        | ((rd as u32) << 7)
        | 0x03
}

/// # Example
///
/// ```rust
/// use brik::asm_riscv::Reg;
/// use brik::util::rv64::encode_lhu;
/// assert_eq!(encode_lhu(Reg::A0, Reg::SP, 0), 0x15503);
/// ```
#[inline(always)]
pub const fn encode_lhu(rd: Reg, rs1: Reg, imm: i16) -> u32 {
    let imm12 = (imm as u32) & 0xfff;
    (imm12 << 20)
        | ((rs1 as u32) << 15)
        | (5 << 12)            // funct3 = 5 for LHU
        | ((rd as u32) << 7)
        | 0x03
}

/// # Example
///
/// ```rust
/// use brik::asm_riscv::Reg;
/// use brik::util::rv64::encode_lbu;
/// assert_eq!(encode_lbu(Reg::A0, Reg::SP, 0), 0x14503);
/// ```
#[inline(always)]
pub const fn encode_lbu(rd: Reg, rs1: Reg, imm: i16) -> u32 {
    let imm12 = (imm as u32) & 0xfff;
    (imm12 << 20)
        | ((rs1 as u32) << 15)
        | (4 << 12)            // funct3 = 4 for LBU
        | ((rd as u32) << 7)
        | 0x03
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

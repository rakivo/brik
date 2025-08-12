//! RV64 extension for asm_riscv (RV32)

use std::mem;

use crate::util::into_bytes::IntoBytes;

use smallvec::SmallVec;
use asm_riscv::{I, Reg};

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

/// Encode RISC-V MUL (Multiplication) instruction.
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
/// // addw a0, a1, a2
/// ```
#[inline(always)]
pub const fn encode_addw(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    ((rs2 as u32) << 20)       // rs2
        | ((rs1 as u32) << 15) // rs1
        | (0 << 12)            // funct3 = 0 for ADDW
        | ((rd as u32) << 7)   // rd
        | (0 << 25)            // funct7 = 0000000 for ADDW
        | 0x3B                 // opcode = 0x3B for OP-32
}

/// Encode RISC-V SUBW (Subtract Word) instruction - RV64 only.
/// Performs 32-bit subtraction and sign-extends the result to 64 bits.
#[inline(always)]
pub const fn encode_subw(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    ((rs2 as u32) << 20)       // rs2
        | ((rs1 as u32) << 15) // rs1
        | (0 << 12)            // funct3 = 0 for SUBW
        | ((rd as u32) << 7)   // rd
        | (0x20 << 25)         // funct7 = 0100000 for SUBW
        | 0x3B                 // opcode = 0x3B for OP-32
}

/// Encode RISC-V ADDIW (Add Immediate Word) instruction - RV64 only.
/// Performs 32-bit addition with immediate and sign-extends the result.
///
/// # Example
/// ```
/// use brik::asm_riscv::Reg;
/// use brik::util::rv64::encode_addiw;
/// let inst = encode_addiw(Reg::A0, Reg::A1, 42);
/// // addiw a0, a1, 42
/// ```
#[inline(always)]
pub const fn encode_addiw(rd: Reg, rs1: Reg, imm: i16) -> u32 {
    let imm12 = (imm as u32) & 0xfff;
    (imm12 << 20)              // imm[11:0]
        | ((rs1 as u32) << 15) // rs1
        | (0 << 12)            // funct3 = 0 for ADDIW
        | ((rd as u32) << 7)   // rd
        | 0x1B                 // opcode = 0x1B for OP-IMM-32
}

/// Encode RISC-V SLLW (Shift Left Logical Word) instruction - RV64 only.
/// Performs 32-bit left shift and sign-extends the result.
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
#[inline(always)]
pub const fn encode_sraw(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    ((rs2 as u32) << 20)       // rs2 (shift amount in lower 5 bits)
        | ((rs1 as u32) << 15) // rs1
        | (5 << 12)            // funct3 = 5 for SRAW
        | ((rd as u32) << 7)   // rd
        | (0x20 << 25)         // funct7 = 0100000 for SRAW
        | 0x3B                 // opcode = 0x3B for OP-32
}

/// Encode RISC-V SLLIW (Shift Left Logical Immediate Word) instruction - RV64 only.
/// Performs 32-bit left shift by immediate and sign-extends the result.
///
/// # Example
/// ```
/// use brik::asm_riscv::Reg;
/// use brik::util::rv64::encode_slliw;
/// let inst = encode_slliw(Reg::A0, Reg::A1, 4);
/// // slliw a0, a1, 4
/// ```
#[inline(always)]
pub const fn encode_slliw(rd: Reg, rs1: Reg, shamt: i8) -> u32 {
    debug_assert!(shamt < 32, "SLLIW shift amount must be < 32");
    ((shamt as u32) << 20)     // shamt[4:0] in imm[11:0] field
        | ((rs1 as u32) << 15) // rs1
        | (1 << 12)            // funct3 = 1 for SLLIW
        | ((rd as u32) << 7)   // rd
        | 0x1B                 // opcode = 0x1B for OP-IMM-32
}

/// Encode RISC-V SRLIW (Shift Right Logical Immediate Word) instruction - RV64 only.
/// Performs 32-bit logical right shift by immediate and sign-extends the result.
#[inline(always)]
pub const fn encode_srliw(rd: Reg, rs1: Reg, shamt: i8) -> u32 {
    debug_assert!(shamt < 32, "SRLIW shift amount must be < 32");
    ((shamt as u32) << 20)     // shamt[4:0] in imm[11:0] field
        | ((rs1 as u32) << 15) // rs1
        | (5 << 12)            // funct3 = 5 for SRLIW
        | ((rd as u32) << 7)   // rd
        | 0x1B                 // opcode = 0x1B for OP-IMM-32
}

/// Encode RISC-V SRAIW (Shift Right Arithmetic Immediate Word) instruction - RV64 only.
/// Performs 32-bit arithmetic right shift by immediate and sign-extends the result.
#[inline(always)]
pub const fn encode_sraiw(rd: Reg, rs1: Reg, shamt: i8) -> u32 {
    debug_assert!(shamt < 32, "SRAIW shift amount must be < 32");
    ((0x20 << 5) | (shamt as u32)) << 20  // funct7=0100000, shamt[4:0]
        | ((rs1 as u32) << 15) // rs1
        | (5 << 12)            // funct3 = 5 for SRAIW
        | ((rd as u32) << 7)   // rd
        | 0x1B                 // opcode = 0x1B for OP-IMM-32
}

// =============================================================================
// Additional useful 64-bit operations
// =============================================================================

/// Encode RISC-V LWU (Load Word Unsigned) instruction - RV64 only.
/// Loads 32 bits and zero-extends to 64 bits (no sign extension).
#[inline(always)]
pub const fn encode_lwu(rd: Reg, rs1: Reg, imm: i16) -> u32 {
    let imm12 = (imm as u32) & 0xfff;
    (imm12 << 20)              // imm[11:0]
        | ((rs1 as u32) << 15) // rs1
        | (6 << 12)            // funct3 = 6 for LWU (32-bit unsigned load)
        | ((rd as u32) << 7)   // rd
        | 0x03                 // opcode = 0x03 for LOAD
}

/// Encode RISC-V LHU (Load Halfword Unsigned) instruction.
/// Loads 16 bits and zero-extends to register width.
#[inline(always)]
pub const fn encode_lhu(rd: Reg, rs1: Reg, imm: i16) -> u32 {
    let imm12 = (imm as u32) & 0xfff;
    (imm12 << 20)              // imm[11:0]
        | ((rs1 as u32) << 15) // rs1
        | (5 << 12)            // funct3 = 5 for LHU (16-bit unsigned load)
        | ((rd as u32) << 7)   // rd
        | 0x03                 // opcode = 0x03 for LOAD
}

/// Encode RISC-V LBU (Load Byte Unsigned) instruction.
/// Loads 8 bits and zero-extends to register width.
#[inline(always)]
pub const fn encode_lbu(rd: Reg, rs1: Reg, imm: i16) -> u32 {
    let imm12 = (imm as u32) & 0xfff;
    (imm12 << 20)              // imm[11:0]
        | ((rs1 as u32) << 15) // rs1
        | (4 << 12)            // funct3 = 4 for LBU (8-bit unsigned load)
        | ((rd as u32) << 7)   // rd
        | 0x03                 // opcode = 0x03 for LOAD
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_negative_immediate_ld() {
        // Test that negative immediates work correctly
        let inst = encode_ld(Reg::A0, Reg::SP, -8);
        // Should encode -8 correctly in the immediate field
        assert_eq!(inst & 0xfff00000, 0xff800000); // Upper bits should be set for -8
    }

    #[test]
    fn test_negative_immediate_sd() {
        // Test that negative immediates work correctly for SD too
        let inst = encode_sd(Reg::A0, Reg::SP, -8);
        // For S-type, immediate is split but should still represent -8
        let imm_high = (inst >> 25) & 0x7f;
        let imm_low = (inst >> 7) & 0x1f;
        let reconstructed_imm = ((imm_high << 5) | imm_low) as i16;
        // Due to 2's complement, this should reconstruct to -8
        assert_eq!((reconstructed_imm << 4) >> 4, -8); // Sign extend from 12-bit
    }

    #[test]
    fn test_addw_encoding() {
        let inst = encode_addw(Reg::A0, Reg::A1, Reg::A2);
        // Check opcode is 0x3B
        assert_eq!(inst & 0x7f, 0x3b);
        // Check funct3 is 0
        assert_eq!((inst >> 12) & 0x7, 0);
        // Check funct7 is 0
        assert_eq!((inst >> 25) & 0x7f, 0);
    }
}

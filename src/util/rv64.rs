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
    let imm12 = (imm as u32) & 0xfff;
    (imm12 << 20)              // imm[11:0]
        | ((rs1 as u32) << 15) // rs1
        | (3 << 12)            // funct3 = 3 for LD
        | ((rd as u32) << 7)   // rd
        | 0x03                 // opcode = 0x03 for LOAD
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
    let imm12    = (imm as u32) & 0xfff;
    let imm_low  = imm12 & 0x1f;        // imm[4:0]
    let imm_high = (imm12 >> 5) & 0x7f; // imm[11:5]

    (imm_high << 25)           // imm[11:5]
        | ((rs2 as u32) << 20) // rs2
        | ((rs1 as u32) << 15) // rs1
        | (3 << 12)            // funct3 = 3 for SD
        | (imm_low << 7)       // imm[4:0]
        | 0x23                 // opcode = 0x23 for STORE
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



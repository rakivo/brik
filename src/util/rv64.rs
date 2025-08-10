use std::mem;

use crate::util::into_bytes::IntoBytes;

use smallvec::SmallVec;
use asm_riscv::{I, Reg};

pub type RV64Bytes = SmallVec<[u8; mem::size_of::<u32>() * 3]>;

/// Encode RISC-V LD (Load Doubleword) instruction.
/// imm is a signed 12-bit offset.
#[inline(always)]
pub const fn encode_ld(rd: Reg, rs1: Reg, imm: i16) -> u32 {
    let imm12 = (imm as u32) & 0xfff;
    (imm12 << 20)              // imm[11:0]
        | ((rs1 as u32) << 15) // rs1
        | (3 << 12)            // funct3 = 3 for LD
        | ((rd as u32) << 7)   // rd
        | 0x03                 // opcode = 0x03 for LOAD
}

/// Encode RISC-V SD (Store Doubleword) instruction.
/// imm is a signed 12-bit offset.
#[inline(always)]
pub const fn encode_sd(rs2: Reg, rs1: Reg, imm: i16) -> u32 {
    let imm12 = (imm as u32) & 0xfff;
    let imm_low = imm12 & 0x1f;         // imm[4:0]
    let imm_high = (imm12 >> 5) & 0x7f; // imm[11:5]

    (imm_high << 25)           // imm[11:5]
        | ((rs2 as u32) << 20) // rs2
        | ((rs1 as u32) << 15) // rs1
        | (3 << 12)            // funct3 = 3 for SD
        | (imm_low << 7)       // imm[4:0]
        | 0x23                 // opcode = 0x23 for STORE
}

/// Expand `li rd, imm` for RV64 and return its encoding as little-endian bytes.
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



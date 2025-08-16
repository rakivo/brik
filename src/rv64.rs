//! RV64 extension for asm_riscv (RV32)

use crate::util::misc;
use crate::opcode::AqRl;
use crate::rv32::{I, Reg};
use crate::opcode::RV64Opcode::*;
use crate::util::into_bytes::IntoBytes;

use core::mem;

use smallvec::SmallVec;

pub type RV64Inst = SmallVec<[u8; mem::size_of::<u32>() * 6]>;

/// Encode RISC-V LD (Load Doubleword) instruction.
/// imm is a signed 12-bit offset.
///
/// # Example
///
/// Runnable check for an LD with offset 0:
/// ```
/// use brik::rv32::Reg;
/// use brik::rv64::encode_ld;
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
/// use brik::rv32::Reg;
/// use brik::rv64::encode_sd;
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

/// Expand `li rd, imm` for RV64 and return its encoding as little-endian bytes.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::rv64::encode_li_rv64_little;
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
// (M-extension) instructions (Version 2.1)
// =============================================================================

/// Encode RISC-V DIV (M-extension) instruction.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::rv64::encode_div;
/// let inst = encode_div(Reg::A0, Reg::A1, Reg::A2);
/// assert_eq!(inst, 0x02c5c533); // div a0, a1, a2
/// ```
#[inline(always)]
pub const fn encode_div(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    (0x01 << 25)               // funct7 = 0x01
        | ((rs2 as u32) << 20) // divisor
        | ((rs1 as u32) << 15) // dividend
        | (0x4 << 12)          // funct3 = 0x4 for div
        | ((rd as u32) << 7)   // dest
        | Op.as_u32()
}

// Encode RISC-V DIVW (M-extension) instruction.
/// Performs 32-bit signed division, sign-extends quotient to 64 bits.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::rv64::encode_divw;
/// let inst = encode_divw(Reg::A0, Reg::A1, Reg::A2);
/// assert_eq!(inst, 0x02C5C53B); // divw a0, a1, a2
/// ```
#[inline(always)]
pub const fn encode_divw(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    (0x01 << 25)               // funct7 = 0000001
        | ((rs2 as u32) << 20) // rs2 (divisor)
        | ((rs1 as u32) << 15) // rs1 (dividend)
        | (0x4 << 12)          // funct3 = 100 for DIVW
        | ((rd as u32) << 7)   // rd (destination, quotient)
        | Op32.as_u32()        // opcode = 0x3B for OP-32
}

/// Encode RISC-V DIVU (M-extension) instruction.
/// Performs 64-bit unsigned division and stores the quotient in rd.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::rv64::encode_divu;
/// let inst = encode_divu(Reg::A0, Reg::A1, Reg::A2);
/// assert_eq!(inst, 0x02C5D533); // divu a0, a1, a2
/// ```
#[inline(always)]
pub const fn encode_divu(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    (0x01 << 25)               // funct7 = 0000001 for M-extension
        | ((rs2 as u32) << 20) // rs2 (divisor)
        | ((rs1 as u32) << 15) // rs1 (dividend)
        | (0x5 << 12)          // funct3 = 101 for DIVU
        | ((rd as u32) << 7)   // rd (destination, quotient)
        | Op.as_u32()          // opcode = 0x33 for OP
}

/// Encode RISC-V DIVUW (M-extension) instruction.
/// Performs 32-bit unsigned division and sign-extends the quotient to 64 bits (RV64 only).
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::rv64::encode_divuw;
/// let inst = encode_divuw(Reg::A0, Reg::A1, Reg::A2);
/// assert_eq!(inst, 0x02C5D53B); // divuw a0, a1, a2
/// ```
#[inline(always)]
pub const fn encode_divuw(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    (0x01 << 25)               // funct7 = 0000001 for M-extension
        | ((rs2 as u32) << 20) // rs2 (divisor)
        | ((rs1 as u32) << 15) // rs1 (dividend)
        | (0x5 << 12)          // funct3 = 101 for DIVUW
        | ((rd as u32) << 7)   // rd (destination, quotient)
        | Op32.as_u32()        // opcode = 0x3B for OP-32
}

/// Encode RISC-V REM (M-extension) instruction.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::rv64::encode_rem;
/// let inst = encode_rem(Reg::A0, Reg::A1, Reg::A2);
/// assert_eq!(inst, 0x02c5e533); // rem a0, a1, a2
/// ```
#[inline(always)]
pub const fn encode_rem(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    (0x01 << 25)               // funct7 = 0x01
        | ((rs2 as u32) << 20) // divisor
        | ((rs1 as u32) << 15) // dividend
        | (0x6 << 12)          // funct3 = 0x6 for rem
        | ((rd as u32) << 7)   // dest
        | Op.as_u32()
}

/// Encode RISC-V REMW (M-extension) instruction.
/// Performs 32-bit signed division, sign-extends remainder to 64 bits.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::rv64::encode_remw;
/// let inst = encode_remw(Reg::A0, Reg::A1, Reg::A2);
/// assert_eq!(inst, 0x02C5E53B); // remw a0, a1, a2
/// ```
#[inline(always)]
pub const fn encode_remw(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    (0x01 << 25)               // funct7 = 0000001
        | ((rs2 as u32) << 20) // rs2 (divisor)
        | ((rs1 as u32) << 15) // rs1 (dividend)
        | (0x6 << 12)          // funct3 = 110 for REMW
        | ((rd as u32) << 7)   // rd (destination, remainder)
        | Op32.as_u32()        // opcode = 0x3B for OP-32
}

/// Encode RISC-V REMU (M-extension) instruction.
/// Performs 64-bit unsigned division and stores the remainder in rd.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::rv64::encode_remu;
/// let inst = encode_remu(Reg::A0, Reg::A1, Reg::A2);
/// assert_eq!(inst, 0x02C5F533); // remu a0, a1, a2
/// ```
#[inline(always)]
pub const fn encode_remu(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    (0x01 << 25)               // funct7 = 0000001 for M-extension
        | ((rs2 as u32) << 20) // rs2 (divisor)
        | ((rs1 as u32) << 15) // rs1 (dividend)
        | (0x7 << 12)          // funct3 = 111 for REMU
        | ((rd as u32) << 7)   // rd (destination, remainder)
        | Op.as_u32()          // opcode = 0x33 for OP
}

/// Encode RISC-V REMUW (M-extension) instruction.
/// Performs 32-bit unsigned division and sign-extends the remainder to 64 bits (RV64 only).
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::rv64::encode_remuw;
/// let inst = encode_remuw(Reg::A0, Reg::A1, Reg::A2);
/// assert_eq!(inst, 0x02C5F53B); // remuw a0, a1, a2
/// ```
#[inline(always)]
pub const fn encode_remuw(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    (0x01 << 25)               // funct7 = 0000001 for M-extension
        | ((rs2 as u32) << 20) // rs2 (divisor)
        | ((rs1 as u32) << 15) // rs1 (dividend)
        | (0x7 << 12)          // funct3 = 111 for REMUW
        | ((rd as u32) << 7)   // rd (destination, remainder)
        | Op32.as_u32()        // opcode = 0x3B for OP-32
}

/// Encode RISC-V MUL (M-extension) instruction.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::rv64::encode_mul;
/// let inst = encode_mul(Reg::A0, Reg::A1, Reg::A2);
/// assert_eq!(inst, 0x02c58533); // mul a0, a1, a2
/// ```
#[inline(always)]
#[allow(clippy::identity_op)]
pub const fn encode_mul(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    (0x01 << 25)               // funct7 = 0x01
        | ((rs2 as u32) << 20) // multiplier
        | ((rs1 as u32) << 15) // multiplicand
        | (0x0 << 12)          // funct3 = 0x0 for mul
        | ((rd as u32) << 7)   // dest
        | Op.as_u32()
}

/// Encode RISC-V MULW (M-extension) instruction.
/// Performs 32-bit signed multiplication and sign-extends the result to 64 bits (RV64 only).
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::rv64::encode_mulw;
/// let inst = encode_mulw(Reg::A0, Reg::A1, Reg::A2);
/// assert_eq!(inst, 0x02C5853B); // mulw a0, a1, a2
/// ```
#[inline(always)]
#[allow(clippy::identity_op)]
pub const fn encode_mulw(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    (0x01 << 25)               // funct7 = 0000001 for M-extension
        | ((rs2 as u32) << 20) // rs2 (multiplier)
        | ((rs1 as u32) << 15) // rs1 (multiplicand)
        | (0x0 << 12)          // funct3 = 000 for MULW
        | ((rd as u32) << 7)   // rd (destination, product)
        | Op32.as_u32()        // opcode = 0x3B for OP-32
}

/// Encode RISC-V MULHW (M-extension) instruction.
/// Performs 32-bit signed × signed multiplication, sign-extends upper 32 bits to 64 bits.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::rv64::encode_mulhw;
/// let inst = encode_mulhw(Reg::A0, Reg::A1, Reg::A2);
/// assert_eq!(inst, 0x02C5953B); // mulhw a0, a1, a2
/// ```
#[inline(always)]
pub const fn encode_mulhw(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    (0x01 << 25)               // funct7 = 0000001
        | ((rs2 as u32) << 20) // rs2 (multiplier)
        | ((rs1 as u32) << 15) // rs1 (multiplicand)
        | (0x1 << 12)          // funct3 = 001 for MULHW
        | ((rd as u32) << 7)   // rd (destination, upper product)
        | Op32.as_u32()        // opcode = 0x3B for OP-32
}

/// Encode RISC-V MULHSUW (M-extension) instruction.
/// Performs 32-bit signed × unsigned multiplication, sign-extends upper 32 bits to 64 bits.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::rv64::encode_mulhsuw;
/// let inst = encode_mulhsuw(Reg::A0, Reg::A1, Reg::A2);
/// assert_eq!(inst, 0x02C5A53B); // mulhsuw a0, a1, a2
/// ```
#[inline(always)]
pub const fn encode_mulhsuw(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    (0x01 << 25)               // funct7 = 0000001
        | ((rs2 as u32) << 20) // rs2 (unsigned multiplier)
        | ((rs1 as u32) << 15) // rs1 (signed multiplicand)
        | (0x2 << 12)          // funct3 = 010 for MULHSUW
        | ((rd as u32) << 7)   // rd (destination, upper product)
        | Op32.as_u32()        // opcode = 0x3B for OP-32
}

/// Encode RISC-V MULHUW (M-extension) instruction.
/// Performs 32-bit unsigned × unsigned multiplication, sign-extends upper 32 bits to 64 bits.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::rv64::encode_mulhuw;
/// let inst = encode_mulhuw(Reg::A0, Reg::A1, Reg::A2);
/// assert_eq!(inst, 0x02C5B53B); // mulhuw a0, a1, a2
/// ```
#[inline(always)]
pub const fn encode_mulhuw(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    (0x01 << 25)               // funct7 = 0000001
        | ((rs2 as u32) << 20) // rs2 (unsigned multiplier)
        | ((rs1 as u32) << 15) // rs1 (unsigned multiplicand)
        | (0x3 << 12)          // funct3 = 011 for MULHUW
        | ((rd as u32) << 7)   // rd (destination, upper product)
        | Op32.as_u32()        // opcode = 0x3B for OP-32
}

/// Encode RISC-V MULH (M-extension) instruction.
/// Performs 64-bit signed × signed multiplication, stores upper 64 bits in rd.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::rv64::encode_mulh;
/// let inst = encode_mulh(Reg::A0, Reg::A1, Reg::A2);
/// assert_eq!(inst, 0x02C59533); // mulh a0, a1, a2
/// ```
#[inline(always)]
pub const fn encode_mulh(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    (0x01 << 25)               // funct7 = 0000001
        | ((rs2 as u32) << 20) // rs2 (multiplier)
        | ((rs1 as u32) << 15) // rs1 (multiplicand)
        | (0x1 << 12)          // funct3 = 001 for MULH
        | ((rd as u32) << 7)   // rd (destination, upper product)
        | Op.as_u32()          // opcode = 0x33 for OP
}

/// Encode RISC-V MULHSU (M-extension) instruction.
/// Performs 64-bit signed × unsigned multiplication, stores upper 64 bits in rd.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::rv64::encode_mulhsu;
/// let inst = encode_mulhsu(Reg::A0, Reg::A1, Reg::A2);
/// assert_eq!(inst, 0x02C5A533); // mulhsu a0, a1, a2
/// ```
#[inline(always)]
pub const fn encode_mulhsu(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    (0x01 << 25)               // funct7 = 0000001
        | ((rs2 as u32) << 20) // rs2 (unsigned multiplier)
        | ((rs1 as u32) << 15) // rs1 (signed multiplicand)
        | (0x2 << 12)          // funct3 = 010 for MULHSU
        | ((rd as u32) << 7)   // rd (destination, upper product)
        | Op.as_u32()          // opcode = 0x33 for OP
}

/// Encode RISC-V MULHU (M-extension) instruction.
/// Performs 64-bit unsigned × unsigned multiplication, stores upper 64 bits in rd.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::rv64::encode_mulhu;
/// let inst = encode_mulhu(Reg::A0, Reg::A1, Reg::A2);
/// assert_eq!(inst, 0x02C5B533); // mulhu a0, a1, a2
/// ```
#[inline(always)]
pub const fn encode_mulhu(rd: Reg, rs1: Reg, rs2: Reg) -> u32 {
    (0x01 << 25)               // funct7 = 0000001
        | ((rs2 as u32) << 20) // rs2 (unsigned multiplier)
        | ((rs1 as u32) << 15) // rs1 (unsigned multiplicand)
        | (0x3 << 12)          // funct3 = 011 for MULHU
        | ((rd as u32) << 7)   // rd (destination, upper product)
        | Op.as_u32()          // opcode = 0x33 for OP
}

// =============================================================================
// RV64I-specific instructions (Version 2.1) (32-bit operations with sign extension)
// =============================================================================

/// Encode RISC-V ADDW (Add Word) instruction - RV64 only.
/// Performs 32-bit addition and sign-extends the result to 64 bits.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::rv64::encode_addw;
/// let inst = encode_addw(Reg::A0, Reg::A1, Reg::A2);
/// assert_eq!(inst, 0xc5853b);
/// // addw a0, a1, a2
/// ```
#[inline(always)]
#[allow(clippy::identity_op)]
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
/// use brik::rv32::Reg;
/// use brik::rv64::encode_subw;
/// assert_eq!(encode_subw(Reg::A0, Reg::A1, Reg::A2), 0x40c5853b);
/// ```
#[inline(always)]
#[allow(clippy::identity_op)]
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
/// use brik::rv32::Reg;
/// use brik::rv64::encode_addiw;
/// let inst = encode_addiw(Reg::A0, Reg::A1, 42);
/// assert_eq!(inst, 0x2a5851b);
/// // addiw a0, a1, 42
/// ```
#[inline(always)]
#[allow(clippy::identity_op)]
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
/// use brik::rv32::Reg;
/// use brik::rv64::encode_sllw;
/// assert_eq!(encode_sllw(Reg::A0, Reg::A1, Reg::A2), 0xc5953b);
/// ```
#[inline(always)]
#[allow(clippy::identity_op)]
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
/// use brik::rv32::Reg;
/// use brik::rv64::encode_srlw;
/// assert_eq!(encode_srlw(Reg::A0, Reg::A1, Reg::A2), 0xc5d53b);
/// ```
#[inline(always)]
#[allow(clippy::identity_op)]
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
/// use brik::rv32::Reg;
/// use brik::rv64::encode_sraw;
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
/// use brik::rv32::Reg;
/// use brik::rv64::encode_slliw;
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
/// use brik::rv32::Reg;
/// use brik::rv64::encode_srliw;
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
/// use brik::rv32::Reg;
/// use brik::rv64::encode_sraiw;
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
/// use brik::rv32::Reg;
/// use brik::rv64::encode_lwu;
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

// === A-extension Load-Reserved/Store-Conditional Instructions ===

/// Encode RISC-V LR.W (A-extension) instruction.
/// Loads a 32-bit word from address in rs1, places it in rd (sign-extended).
/// rs2 must be 0. Supports acquire/release ordering.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::opcode::AqRl;
/// use brik::rv64::encode_lr_w;
/// let inst = encode_lr_w(Reg::A0, Reg::A1, AqRl::None);
/// assert_eq!(inst, 0x1005A52F); // lr.w a0, (a1)
/// ```
#[inline(always)]
#[allow(clippy::identity_op)]
pub const fn encode_lr_w(rd: Reg, rs1: Reg, aqrl: AqRl) -> u32 {
    (0x02 << 27)               // funct5 = 00010 for LR
        | (aqrl.as_u32() << 25)// aq/rl bits
        | (0 << 20)            // rs2 = 0 for LR
        | ((rs1 as u32) << 15) // rs1 (address)
        | (0x2 << 12)          // funct3 = 010 for .W
        | ((rd as u32) << 7)   // rd (destination)
        | Amo.as_u32()         // opcode = 0x2F for AMO
}

/// Encode RISC-V SC.W (A-extension) instruction.
/// Conditionally stores a 32-bit word from rs2 to address in rs1, sets rd to 0 on success, 1 on failure.
/// Supports acquire/release ordering.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::opcode::AqRl;
/// use brik::rv64::encode_sc_w;
/// let inst = encode_sc_w(Reg::A0, Reg::A1, Reg::A2, AqRl::None);
/// assert_eq!(inst, 0x18C5A52F); // sc.w a0, a2, (a1)
/// ```
#[inline(always)]
pub const fn encode_sc_w(rd: Reg, rs1: Reg, rs2: Reg, aqrl: AqRl) -> u32 {
    (0x03 << 27)               // funct5 = 00011 for SC
        | (aqrl.as_u32() << 25)// aq/rl bits
        | ((rs2 as u32) << 20) // rs2 (value to store)
        | ((rs1 as u32) << 15) // rs1 (address)
        | (0x2 << 12)          // funct3 = 010 for .W
        | ((rd as u32) << 7)   // rd (destination, status)
        | Amo.as_u32()         // opcode = 0x2F for AMO
}

/// Encode RISC-V LR.D (A-extension) instruction.
/// Loads a 64-bit doubleword from address in rs1, places it in rd.
/// rs2 must be 0. Supports acquire/release ordering.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::opcode::AqRl;
/// use brik::rv64::encode_lr_d;
/// let inst = encode_lr_d(Reg::A0, Reg::A1, AqRl::None);
/// assert_eq!(inst, 0x1005B52F); // lr.d a0, (a1)
/// ```
#[inline(always)]
#[allow(clippy::identity_op)]
pub const fn encode_lr_d(rd: Reg, rs1: Reg, aqrl: AqRl) -> u32 {
    (0x02 << 27)               // funct5 = 00010 for LR
        | (aqrl.as_u32() << 25)// aq/rl bits
        | (0 << 20)            // rs2 = 0 for LR
        | ((rs1 as u32) << 15) // rs1 (address)
        | (0x3 << 12)          // funct3 = 011 for .D
        | ((rd as u32) << 7)   // rd (destination)
        | Amo.as_u32()         // opcode = 0x2F for AMO
}

/// Encode RISC-V SC.D (A-extension) instruction.
/// Conditionally stores a 64-bit doubleword from rs2 to address in rs1, sets rd to 0 on success, 1 on failure.
/// Supports acquire/release ordering.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::opcode::AqRl;
/// use brik::rv64::encode_sc_d;
/// let inst = encode_sc_d(Reg::A0, Reg::A1, Reg::A2, AqRl::None);
/// assert_eq!(inst, 0x18C5B52F); // sc.d a0, a2, (a1)
/// ```
#[inline(always)]
pub const fn encode_sc_d(rd: Reg, rs1: Reg, rs2: Reg, aqrl: AqRl) -> u32 {
    (0x03 << 27)               // funct5 = 00011 for SC
        | (aqrl.as_u32() << 25)// aq/rl bits
        | ((rs2 as u32) << 20) // rs2 (value to store)
        | ((rs1 as u32) << 15) // rs1 (address)
        | (0x3 << 12)          // funct3 = 011 for .D
        | ((rd as u32) << 7)   // rd (destination, status)
        | Amo.as_u32()         // opcode = 0x2F for AMO
}

// === A-extension Atomic Memory Operations (32-bit) ===

/// Encode RISC-V AMOADD.W (A-extension) instruction.
/// Atomically adds rs2 to 32-bit word at address in rs1, stores original value in rd (sign-extended).
/// Supports acquire/release ordering.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::opcode::AqRl;
/// use brik::rv64::encode_amoadd_w;
/// let inst = encode_amoadd_w(Reg::A0, Reg::A1, Reg::A2, AqRl::None);
/// assert_eq!(inst, 0x00C5A52F); // amoadd.w a0, a2, (a1)
/// ```
#[inline(always)]
#[allow(clippy::identity_op)]
pub const fn encode_amoadd_w(rd: Reg, rs1: Reg, rs2: Reg, aqrl: AqRl) -> u32 {
    (0x00 << 27)               // funct5 = 00000 for AMOADD
        | (aqrl.as_u32() << 25)// aq/rl bits
        | ((rs2 as u32) << 20) // rs2 (value to add)
        | ((rs1 as u32) << 15) // rs1 (address)
        | (0x2 << 12)          // funct3 = 010 for .W
        | ((rd as u32) << 7)   // rd (destination, original value)
        | Amo.as_u32()         // opcode = 0x2F for AMO
}

/// Encode RISC-V AMOSWAP.W (A-extension) instruction.
/// Atomically swaps 32-bit word in rs2 with word at address in rs1, stores original value in rd (sign-extended).
/// Supports acquire/release ordering.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::opcode::AqRl;
/// use brik::rv64::encode_amoswap_w;
/// let inst = encode_amoswap_w(Reg::A0, Reg::A1, Reg::A2, AqRl::None);
/// assert_eq!(inst, 0x08C5A52F); // amoswap.w a0, a2, (a1)
/// ```
#[inline(always)]
pub const fn encode_amoswap_w(rd: Reg, rs1: Reg, rs2: Reg, aqrl: AqRl) -> u32 {
    (0x01 << 27)               // funct5 = 00001 for AMOSWAP
        | (aqrl.as_u32() << 25)// aq/rl bits
        | ((rs2 as u32) << 20) // rs2 (value to swap)
        | ((rs1 as u32) << 15) // rs1 (address)
        | (0x2 << 12)          // funct3 = 010 for .W
        | ((rd as u32) << 7)   // rd (destination, original value)
        | Amo.as_u32()         // opcode = 0x2F for AMO
}

/// Encode RISC-V AMOAND.W (A-extension) instruction.
/// Atomically ANDs rs2 with 32-bit word at address in rs1, stores original value in rd (sign-extended).
/// Supports acquire/release ordering.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::opcode::AqRl;
/// use brik::rv64::encode_amoand_w;
/// let inst = encode_amoand_w(Reg::A0, Reg::A1, Reg::A2, AqRl::None);
/// assert_eq!(inst, 0x60C5A52F); // amoand.w a0, a2, (a1)
/// ```
#[inline(always)]
pub const fn encode_amoand_w(rd: Reg, rs1: Reg, rs2: Reg, aqrl: AqRl) -> u32 {
    (0x0C << 27)               // funct5 = 01100 for AMOAND
        | (aqrl.as_u32() << 25)// aq/rl bits
        | ((rs2 as u32) << 20) // rs2 (value to AND)
        | ((rs1 as u32) << 15) // rs1 (address)
        | (0x2 << 12)          // funct3 = 010 for .W
        | ((rd as u32) << 7)   // rd (destination, original value)
        | Amo.as_u32()         // opcode = 0x2F for AMO
}

/// Encode RISC-V AMOOR.W (A-extension) instruction.
/// Atomically ORs rs2 with 32-bit word at address in rs1, stores original value in rd (sign-extended).
/// Supports acquire/release ordering.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::opcode::AqRl;
/// use brik::rv64::encode_amoor_w;
/// let inst = encode_amoor_w(Reg::A0, Reg::A1, Reg::A2, AqRl::None);
/// assert_eq!(inst, 0x40C5A52F); // amoor.w a0, a2, (a1)
/// ```
#[inline(always)]
pub const fn encode_amoor_w(rd: Reg, rs1: Reg, rs2: Reg, aqrl: AqRl) -> u32 {
    (0x08 << 27)               // funct5 = 01000 for AMOOR
        | (aqrl.as_u32() << 25)// aq/rl bits
        | ((rs2 as u32) << 20) // rs2 (value to OR)
        | ((rs1 as u32) << 15) // rs1 (address)
        | (0x2 << 12)          // funct3 = 010 for .W
        | ((rd as u32) << 7)   // rd (destination, original value)
        | Amo.as_u32()         // opcode = 0x2F for AMO
}

/// Encode RISC-V AMOXOR.W (A-extension) instruction.
/// Atomically XORs rs2 with 32-bit word at address in rs1, stores original value in rd (sign-extended).
/// Supports acquire/release ordering.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::opcode::AqRl;
/// use brik::rv64::encode_amoxor_w;
/// let inst = encode_amoxor_w(Reg::A0, Reg::A1, Reg::A2, AqRl::None);
/// assert_eq!(inst, 0x20C5A52F); // amoxor.w a0, a2, (a1)
/// ```
#[inline(always)]
pub const fn encode_amoxor_w(rd: Reg, rs1: Reg, rs2: Reg, aqrl: AqRl) -> u32 {
    (0x04 << 27)               // funct5 = 00100 for AMOXOR
        | (aqrl.as_u32() << 25)// aq/rl bits
        | ((rs2 as u32) << 20) // rs2 (value to XOR)
        | ((rs1 as u32) << 15) // rs1 (address)
        | (0x2 << 12)          // funct3 = 010 for .W
        | ((rd as u32) << 7)   // rd (destination, original value)
        | Amo.as_u32()         // opcode = 0x2F for AMO
}

/// Encode RISC-V AMOMAX.W (A-extension) instruction.
/// Atomically stores max of rs2 and signed 32-bit word at address in rs1, stores original value in rd (sign-extended).
/// Supports acquire/release ordering.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::opcode::AqRl;
/// use brik::rv64::encode_amomax_w;
/// let inst = encode_amomax_w(Reg::A0, Reg::A1, Reg::A2, AqRl::None);
/// assert_eq!(inst, 0xA0C5A52F); // amomax.w a0, a2, (a1)
/// ```
#[inline(always)]
pub const fn encode_amomax_w(rd: Reg, rs1: Reg, rs2: Reg, aqrl: AqRl) -> u32 {
    (0x14 << 27)               // funct5 = 10100 for AMOMAX
        | (aqrl.as_u32() << 25)// aq/rl bits
        | ((rs2 as u32) << 20) // rs2 (value to compare)
        | ((rs1 as u32) << 15) // rs1 (address)
        | (0x2 << 12)          // funct3 = 010 for .W
        | ((rd as u32) << 7)   // rd (destination, original value)
        | Amo.as_u32()         // opcode = 0x2F for AMO
}

/// Encode RISC-V AMOMIN.W (A-extension) instruction.
/// Atomically stores min of rs2 and signed 32-bit word at address in rs1, stores original value in rd (sign-extended).
/// Supports acquire/release ordering.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::opcode::AqRl;
/// use brik::rv64::encode_amomin_w;
/// let inst = encode_amomin_w(Reg::A0, Reg::A1, Reg::A2, AqRl::None);
/// assert_eq!(inst, 0x80C5A52F); // amomin.w a0, a2, (a1)
/// ```
#[inline(always)]
pub const fn encode_amomin_w(rd: Reg, rs1: Reg, rs2: Reg, aqrl: AqRl) -> u32 {
    (0x10 << 27)               // funct5 = 10000 for AMOMIN
        | (aqrl.as_u32() << 25)// aq/rl bits
        | ((rs2 as u32) << 20) // rs2 (value to compare)
        | ((rs1 as u32) << 15) // rs1 (address)
        | (0x2 << 12)          // funct3 = 010 for .W
        | ((rd as u32) << 7)   // rd (destination, original value)
        | Amo.as_u32()         // opcode = 0x2F for AMO
}

/// Encode RISC-V AMOMAXU.W (A-extension) instruction.
/// Atomically stores max of rs2 and unsigned 32-bit word at address in rs1, stores original value in rd (sign-extended).
/// Supports acquire/release ordering.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::opcode::AqRl;
/// use brik::rv64::encode_amomaxu_w;
/// let inst = encode_amomaxu_w(Reg::A0, Reg::A1, Reg::A2, AqRl::None);
/// assert_eq!(inst, 0xE0C5A52F); // amomaxu.w a0, a2, (a1)
/// ```
#[inline(always)]
pub const fn encode_amomaxu_w(rd: Reg, rs1: Reg, rs2: Reg, aqrl: AqRl) -> u32 {
    (0x1C << 27)               // funct5 = 11100 for AMOMAXU
        | (aqrl.as_u32() << 25)// aq/rl bits
        | ((rs2 as u32) << 20) // rs2 (value to compare)
        | ((rs1 as u32) << 15) // rs1 (address)
        | (0x2 << 12)          // funct3 = 010 for .W
        | ((rd as u32) << 7)   // rd (destination, original value)
        | Amo.as_u32()         // opcode = 0x2F for AMO
}

/// Encode RISC-V AMOMINU.W (A-extension) instruction.
/// Atomically stores min of rs2 and unsigned 32-bit word at address in rs1, stores original value in rd (sign-extended).
/// Supports acquire/release ordering.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::opcode::AqRl;
/// use brik::rv64::encode_amominu_w;
/// let inst = encode_amominu_w(Reg::A0, Reg::A1, Reg::A2, AqRl::None);
/// assert_eq!(inst, 0xC0C5A52F); // amominu.w a0, a2, (a1)
/// ```
#[inline(always)]
pub const fn encode_amominu_w(rd: Reg, rs1: Reg, rs2: Reg, aqrl: AqRl) -> u32 {
    (0x18 << 27)               // funct5 = 11000 for AMOMINU
        | (aqrl.as_u32() << 25)// aq/rl bits
        | ((rs2 as u32) << 20) // rs2 (value to compare)
        | ((rs1 as u32) << 15) // rs1 (address)
        | (0x2 << 12)          // funct3 = 010 for .W
        | ((rd as u32) << 7)   // rd (destination, original value)
        | Amo.as_u32()         // opcode = 0x2F for AMO
}

// === A-extension Atomic Memory Operations (64-bit) ===

/// Encode RISC-V AMOADD.D (A-extension) instruction.
/// Atomically adds rs2 to 64-bit doubleword at address in rs1, stores original value in rd.
/// Supports acquire/release ordering.
///
/// # Example
///
/// ```
/// use brik::rv32::Reg;
/// use brik::opcode::AqRl;
/// use brik::rv64::encode_amoadd_d;
/// let inst = encode_amoadd_d(Reg::A0, Reg::A1, Reg::A2, AqRl::None);
/// assert_eq!(inst, 0x00C5B52F); // amoadd.d a0, a2, (a1)
/// ```
#[inline(always)]
#[allow(clippy::identity_op)]
pub const fn encode_amoadd_d(rd: Reg, rs1: Reg, rs2: Reg, aqrl: AqRl) -> u32 {
    (0x00 << 27)                // funct5 = 00000 for AMOADD
        | (aqrl.as_u32() << 25) // aq/rl bits
        | ((rs2 as u32) << 20)  // rs2 (value to add)
        | ((rs1 as u32) << 15)  // rs1 (address)
        | (0x3 << 12)           // funct3 = 011 for .D
        | ((rd as u32) << 7)    // rd (destination, original value)
        | Amo.as_u32()          // opcode = 0x2F for AMO
}

/// Encode RISC-V AMOSWAP.D (A-extension) instruction.
/// Atomically swaps 64-bit doubleword in rs2 with doubleword at address in rs1, stores original value in rd.
/// Supports acquire/release ordering.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::opcode::AqRl;
/// use brik::rv64::encode_amoswap_d;
/// let inst = encode_amoswap_d(Reg::A0, Reg::A1, Reg::A2, AqRl::None);
/// assert_eq!(inst, 0x08C5B52F); // amoswap.d a0, a2, (a1)
/// ```
#[inline(always)]
pub const fn encode_amoswap_d(rd: Reg, rs1: Reg, rs2: Reg, aqrl: AqRl) -> u32 {
    (0x01 << 27)               // funct5 = 00001 for AMOSWAP
        | (aqrl.as_u32() << 25)// aq/rl bits
        | ((rs2 as u32) << 20) // rs2 (value to swap)
        | ((rs1 as u32) << 15) // rs1 (address)
        | (0x3 << 12)          // funct3 = 011 for .D
        | ((rd as u32) << 7)   // rd (destination, original value)
        | Amo.as_u32()         // opcode = 0x2F for AMO
}

/// Encode RISC-V AMOAND.D (A-extension) instruction.
/// Atomically ANDs rs2 with 64-bit doubleword at address in rs1, stores original value in rd.
/// Supports acquire/release ordering.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::opcode::AqRl;
/// use brik::rv64::encode_amoand_d;
/// let inst = encode_amoand_d(Reg::A0, Reg::A1, Reg::A2, AqRl::None);
/// assert_eq!(inst, 0x60C5B52F); // amoand.d a0, a2, (a1)
/// ```
#[inline(always)]
pub const fn encode_amoand_d(rd: Reg, rs1: Reg, rs2: Reg, aqrl: AqRl) -> u32 {
    (0x0C << 27)               // funct5 = 01100 for AMOAND
        | (aqrl.as_u32() << 25)// aq/rl bits
        | ((rs2 as u32) << 20) // rs2 (value to AND)
        | ((rs1 as u32) << 15) // rs1 (address)
        | (0x3 << 12)          // funct3 = 011 for .D
        | ((rd as u32) << 7)   // rd (destination, original value)
        | Amo.as_u32()         // opcode = 0x2F for AMO
}

/// Encode RISC-V AMOOR.D (A-extension) instruction.
/// Atomically ORs rs2 with 64-bit doubleword at address in rs1, stores original value in rd.
/// Supports acquire/release ordering.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::opcode::AqRl;
/// use brik::rv64::encode_amoor_d;
/// let inst = encode_amoor_d(Reg::A0, Reg::A1, Reg::A2, AqRl::None);
/// assert_eq!(inst, 0x40C5B52F); // amoor.d a0, a2, (a1)
/// ```
#[inline(always)]
pub const fn encode_amoor_d(rd: Reg, rs1: Reg, rs2: Reg, aqrl: AqRl) -> u32 {
    (0x08 << 27)               // funct5 = 01000 for AMOOR
        | (aqrl.as_u32() << 25)// aq/rl bits
        | ((rs2 as u32) << 20) // rs2 (value to OR)
        | ((rs1 as u32) << 15) // rs1 (address)
        | (0x3 << 12)          // funct3 = 011 for .D
        | ((rd as u32) << 7)   // rd (destination, original value)
        | Amo.as_u32()         // opcode = 0x2F for AMO
}

/// Encode RISC-V AMOXOR.D (A-extension) instruction.
/// Atomically XORs rs2 with 64-bit doubleword at address in rs1, stores original value in rd.
/// Supports acquire/release ordering.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::opcode::AqRl;
/// use brik::rv64::encode_amoxor_d;
/// let inst = encode_amoxor_d(Reg::A0, Reg::A1, Reg::A2, AqRl::None);
/// assert_eq!(inst, 0x20C5B52F); // amoxor.d a0, a2, (a1)
/// ```
#[inline(always)]
pub const fn encode_amoxor_d(rd: Reg, rs1: Reg, rs2: Reg, aqrl: AqRl) -> u32 {
    (0x04 << 27)               // funct5 = 00100 for AMOXOR
        | (aqrl.as_u32() << 25)// aq/rl bits
        | ((rs2 as u32) << 20) // rs2 (value to XOR)
        | ((rs1 as u32) << 15) // rs1 (address)
        | (0x3 << 12)          // funct3 = 011 for .D
        | ((rd as u32) << 7)   // rd (destination, original value)
        | Amo.as_u32()         // opcode = 0x2F for AMO
}

/// Encode RISC-V AMOMAX.D (A-extension) instruction.
/// Atomically stores max of rs2 and signed 64-bit doubleword at address in rs1, stores original value in rd.
/// Supports acquire/release ordering.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::opcode::AqRl;
/// use brik::rv64::encode_amomax_d;
/// let inst = encode_amomax_d(Reg::A0, Reg::A1, Reg::A2, AqRl::None);
/// assert_eq!(inst, 0xA0C5B52F); // amomax.d a0, a2, (a1)
/// ```
#[inline(always)]
pub const fn encode_amomax_d(rd: Reg, rs1: Reg, rs2: Reg, aqrl: AqRl) -> u32 {
    (0x14 << 27)               // funct5 = 10100 for AMOMAX
        | (aqrl.as_u32() << 25)// aq/rl bits
        | ((rs2 as u32) << 20) // rs2 (value to compare)
        | ((rs1 as u32) << 15) // rs1 (address)
        | (0x3 << 12)          // funct3 = 011 for .D
        | ((rd as u32) << 7)   // rd (destination, original value)
        | Amo.as_u32()         // opcode = 0x2F for AMO
}

/// Encode RISC-V AMOMIN.D (A-extension) instruction.
/// Atomically stores min of rs2 and signed 64-bit doubleword at address in rs1, stores original value in rd.
/// Supports acquire/release ordering.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::opcode::AqRl;
/// use brik::rv64::encode_amomin_d;
/// let inst = encode_amomin_d(Reg::A0, Reg::A1, Reg::A2, AqRl::None);
/// assert_eq!(inst, 0x80C5B52F); // amomin.d a0, a2, (a1)
/// ```
#[inline(always)]
pub const fn encode_amomin_d(rd: Reg, rs1: Reg, rs2: Reg, aqrl: AqRl) -> u32 {
    (0x10 << 27)               // funct5 = 10000 for AMOMIN
        | (aqrl.as_u32() << 25)// aq/rl bits
        | ((rs2 as u32) << 20) // rs2 (value to compare)
        | ((rs1 as u32) << 15) // rs1 (address)
        | (0x3 << 12)          // funct3 = 011 for .D
        | ((rd as u32) << 7)   // rd (destination, original value)
        | Amo.as_u32()         // opcode = 0x2F for AMO
}

/// Encode RISC-V AMOMAXU.D (A-extension) instruction.
/// Atomically stores max of rs2 and unsigned 64-bit doubleword at address in rs1, stores original value in rd.
/// Supports acquire/release ordering.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::opcode::AqRl;
/// use brik::rv64::encode_amomaxu_d;
/// let inst = encode_amomaxu_d(Reg::A0, Reg::A1, Reg::A2, AqRl::None);
/// assert_eq!(inst, 0xE0C5B52F); // amomaxu.d a0, a2, (a1)
/// ```
#[inline(always)]
pub const fn encode_amomaxu_d(rd: Reg, rs1: Reg, rs2: Reg, aqrl: AqRl) -> u32 {
    (0x1C << 27)               // funct5 = 11100 for AMOMAXU
        | (aqrl.as_u32() << 25)// aq/rl bits
        | ((rs2 as u32) << 20) // rs2 (value to compare)
        | ((rs1 as u32) << 15) // rs1 (address)
        | (0x3 << 12)          // funct3 = 011 for .D
        | ((rd as u32) << 7)   // rd (destination, original value)
        | Amo.as_u32()         // opcode = 0x2F for AMO
}

/// Encode RISC-V AMOMINU.D (A-extension) instruction.
/// Atomically stores min of rs2 and unsigned 64-bit doubleword at address in rs1, stores original value in rd.
/// Supports acquire/release ordering.
///
/// # Example
/// ```
/// use brik::rv32::Reg;
/// use brik::opcode::AqRl;
/// use brik::rv64::encode_amominu_d;
/// let inst = encode_amominu_d(Reg::A0, Reg::A1, Reg::A2, AqRl::None);
/// assert_eq!(inst, 0xC0C5B52F); // amominu.d a0, a2, (a1)
/// ```
#[inline(always)]
pub const fn encode_amominu_d(rd: Reg, rs1: Reg, rs2: Reg, aqrl: AqRl) -> u32 {
    (0x18 << 27)               // funct5 = 11000 for AMOMINU
        | (aqrl.as_u32() << 25)// aq/rl bits
        | ((rs2 as u32) << 20) // rs2 (value to compare)
        | ((rs1 as u32) << 15) // rs1 (address)
        | (0x3 << 12)          // funct3 = 011 for .D
        | ((rd as u32) << 7)   // rd (destination, original value)
        | Amo.as_u32()         // opcode = 0x2F for AMO
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

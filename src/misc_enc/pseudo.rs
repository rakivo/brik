use crate::util::misc;
use crate::rv32::I32::*;
use crate::rv32::Reg::{self, *};
use crate::util::into_bytes::IntoBytes;

use std::vec::Vec;

use core::mem;

use smallvec::SmallVec;

pub const MAX_I32_SIZE: usize = mem::size_of::<u32>() * 2;
pub const MAX_I64_SIZE: usize = mem::size_of::<u32>() * 6;

pub type RV32Inst = SmallVec<[u8; MAX_I32_SIZE]>;
pub type RV64Inst = SmallVec<[u8; MAX_I64_SIZE]>;

/// Expand `li rd, imm` for RV64 and return its encoding as little-endian bytes.
///
/// # Example
/// ```
/// use brik::rv32::Reg::*;
/// use brik::rv32::I32::{self, *};
/// use brik::util::misc::decode_li64_little;
/// use brik::misc_enc::pseudo::encode_li64_little;
/// use brik::util::misc::le_bytes_into_int as lint;
///
/// // small imm
/// let imm64: i64 = 42;
/// let bytes = encode_li64_little(A0, imm64);
/// assert_eq!(decode_li64_little(&bytes, A0), imm64);
///
/// // medium 32-bit imm
/// let imm64: i64 = 0x12345;
/// let bytes = encode_li64_little(A1, imm64);
/// assert_eq!(decode_li64_little(&bytes, A1), imm64);
///
/// // large 64-bit imm
/// let imm64: i64 = 0x1234_5678_9ABC_DEF0;
/// let bytes = encode_li64_little(A2, imm64);
/// assert_eq!(decode_li64_little(&bytes, A2), imm64);
///
/// // negative 64-bit imm
/// let imm64: i64 = -0x1234_5678_9ABC_DEF0;
/// let bytes = encode_li64_little(A3, imm64);
/// assert_eq!(decode_li64_little(&bytes, A3), imm64);
/// ```
pub fn encode_li64_little(rd: Reg, imm: i64) -> RV64Inst {
    let mut bytes = RV64Inst::with_capacity(MAX_I64_SIZE);

    // -------------- case 1: fits into 12 bits
    if misc::int_fits_into_12_bits(imm) {
        let inst = ADDI { d: rd, s: ZERO, im: imm as i16 };
        bytes.extend_from_slice(&inst.into_bytes());
        return bytes
    }

    // -------------- case 2: fits into 32 bits
    if misc::int_fits_into_32_bits(imm) {
        let hi = ((imm + 0x800) >> 12) as i32;
        let lo = imm - ((hi as i64) << 12);

        let hi_inst = LUI { d: rd, im: hi };
        bytes.extend_from_slice(&hi_inst.into_bytes());

        if lo != 0 {
            debug_assert!{
                misc::int_fits_into_12_bits(lo),
                "lower12 bits of `li` rv64 little-endian don't fit into 12 bits: {lo}"
            };

            let lo_inst = ADDI { d: rd, s: rd, im: lo as i16 };
            bytes.extend_from_slice(&lo_inst.into_bytes());
        }

        return bytes
    }

    // -------------- case 3: does not fit into 32 bits
    let remaining = imm as u64;
    let mut shifts = Vec::with_capacity(6);

    // (shamt, 11-bit chunk)
    for shift in (0..64).step_by(11).rev() {
        let ck = ((remaining >> shift) & 0x7FF) as i16;
        if ck != 0 {
            shifts.push((shift, ck));
        }
    }

    debug_assert!(!shifts.is_empty());

    // emit first chunk using addi from x0 or lui if high chunk
    let (first_shift, first_ck) = shifts[0];
    if first_shift >= 12 {
        let rounding_add = (1u64 << (first_shift - 12)) >> 1;
        let hi20 = (((first_ck as u64) + rounding_add) >> (first_shift - 12)) as i32;
        let remainder = first_ck - (((hi20 as u64) << (first_shift - 12)) as i16);

        let hi_inst = LUI { d: rd, im: hi20 };
        bytes.extend_from_slice(&hi_inst.into_bytes());

        if remainder != 0 {
            debug_assert!{
                misc::int_fits_into_12_bits(remainder as i64),
                "remainder of `li` rv64 little-endian don't fit into 12 bits: {remainder}"
            };

            let lo_inst = ADDI { d: rd, s: rd, im: remainder as _ };
            bytes.extend_from_slice(&lo_inst.into_bytes());
        }
    } else {
        let inst = ADDI { d: rd, s: Reg::ZERO, im: first_ck as _ };
        bytes.extend_from_slice(&inst.into_bytes());
    }

    // emit remaining chunks
    let mut prev_shift = first_shift;
    for &(shift, ck) in &shifts[1..] {
        let dshift = prev_shift - shift;
        if dshift > 0 {
            let inst = SLLI { d: rd, s: rd, shamt: dshift as _ };
            bytes.extend_from_slice(&inst.into_bytes());
        }

        let inst = ORI { d: rd, s: rd, im: ck as _ };
        bytes.extend_from_slice(&inst.into_bytes());
        prev_shift = shift;
    }

    bytes
}

/// ```
/// use brik::rv32::Reg::*;
/// use brik::rv32::I32::{self, *};
/// use brik::util::misc::decode_li32_little;
/// use brik::misc_enc::pseudo::encode_li32_little;
/// use brik::util::misc::le_bytes_into_int as lint;
///
/// // small imm
/// let imm32: i32 = 42;
/// let bytes = encode_li32_little(A0, imm32);
/// assert_eq!(decode_li32_little(&bytes, A0), imm32);
///
/// // large 32-bit imm
/// let imm32 = i32::MAX;
/// let bytes = encode_li32_little(A1, imm32);
/// assert_eq!(decode_li32_little(&bytes, A1), imm32);
///
/// // negative 32-bit imm
/// let imm32 = i32::MIN;
/// let bytes = encode_li32_little(A2, imm32);
/// assert_eq!(decode_li32_little(&bytes, A2), imm32);
/// // ```
pub fn encode_li32_little(rd: Reg, imm: i32) -> RV32Inst {
    let mut bytes = RV32Inst::with_capacity(MAX_I32_SIZE);

    // -------------- case 1: fits into 12 bits
    if misc::int_fits_into_12_bits(imm) {
        let inst = ADDI { d: rd, s: ZERO, im: imm as i16 };
        bytes.extend_from_slice(&inst.into_bytes());
        return bytes
    }

    // -------------- case 1: doesn't fit into 12 bits
    let mut hi = imm >> 12;
    let mut lo = imm - (hi << 12);

    // adjust to ensure lo is in -2048 to 2047
    if lo > 2047 {
        hi += 1;
        lo -= 0x1000;
    } else if lo < -2048 {
        hi -= 1;
        lo += 0x1000;
    }

    let hi_inst = LUI { d: rd, im: hi };
    bytes.extend_from_slice(&hi_inst.into_bytes());

    if lo != 0 {
        debug_assert!{
            misc::int_fits_into_12_bits(lo),
            "lower 12 bits of `li` rv32 little-endian don't fit into 12 bits: {lo}"
        };
        let lo_inst = ADDI { d: rd, s: rd, im: lo as i16 };
        bytes.extend_from_slice(&lo_inst.into_bytes());
    }

    bytes
}

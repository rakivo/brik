use crate::util::misc;
use crate::rv32::I32::*;
use crate::rv32::Reg::{self, *};
use crate::util::into_bytes::IntoBytes;

use core::mem;

use smallvec::SmallVec;

pub type RV32Inst = SmallVec<[u8; mem::size_of::<u32>() * 2]>;
pub type RV64Inst = SmallVec<[u8; mem::size_of::<u32>() * 6]>;

// TODO(#24): Make encode_li64_little support full range of 64-bit immediates
// TODO(#25): Make encode_li32_little support full range of 32-bit immediates

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
/// // skip for now
/// // // large 64-bit imm
/// // let imm64: i64 = 0x1234_5678_9ABC_DEF0;
/// // let bytes = encode_li64_little(A2, imm64);
/// // assert_eq!(decode_li64_little(&bytes, A2), imm64);
///
/// // // negative 64-bit imm
/// // let imm64: i64 = -0x1234_5678_9ABC_DEF0;
/// // let bytes = encode_li64_little(A3, imm64);
/// // assert_eq!(decode_li64_little(&bytes, A3), imm64);
/// ```
pub fn encode_li64_little(rd: Reg, imm: i64) -> RV64Inst {
    let mut bytes = RV64Inst::new();

    if misc::fits_into_12_bits(imm) {
        let inst = ADDI { d: rd, s: ZERO, im: imm as i16 };
        bytes.extend_from_slice(&inst.into_bytes());
        return bytes
    }

    let upper12 = ((imm + 0x800) >> 12) as i32;
    let hi_inst = LUI { d: rd, im: upper12 };
    bytes.extend_from_slice(&hi_inst.into_bytes());

    let lower12 = imm - ((upper12 as i64) << 12);
    if lower12 != 0 {
        debug_assert!{
            misc::fits_into_12_bits(lower12),
            "lower12 bits of `li` rv64 little-endian don't fit into 12 bits: {lower12}"
        };

        let lo_inst = ADDI { d: rd, s: rd, im: lower12 as i16 };
        bytes.extend_from_slice(&lo_inst.into_bytes());
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
/// assert_eq!(decode_li32_little(&bytes, A0), imm32 as i64);
///
/// // skip for now
/// // // large 32-bit imm
/// // let imm32 = i32::MAX;
/// // let bytes = encode_li32_little(A1, imm32);
/// // assert_eq!(decode_li32_little(&bytes, A1), imm32 as i64);
///
/// // // negative 32-bit imm
/// // let imm32 = i32::MIN;
/// // let bytes = encode_li32_little(A2, imm32);
/// // assert_eq!(decode_li32_little(&bytes, A2), imm32 as i64);
/// // ```
pub fn encode_li32_little(rd: Reg, imm: i32) -> RV32Inst {
    let mut bytes = RV32Inst::new();

    if misc::fits_into_12_bits(imm) {
        let inst = ADDI { d: rd, s: ZERO, im: imm as i16 };
        bytes.extend_from_slice(&inst.into_bytes());
        return bytes
    }

    let upper12 = (imm + 0x800) >> 12;
    let hi_inst = LUI { d: rd, im: upper12 };
    bytes.extend_from_slice(&hi_inst.into_bytes());

    let lower12 = imm - (upper12 << 12);
    if lower12 != 0 {
        debug_assert!{
            misc::fits_into_12_bits(lower12),
            "lower12 bits of `li` rv32 little-endian don't fit into 12 bits: {lower12}"
        };

        let lo_inst = ADDI { d: rd, s: rd, im: lower12 as i16 };
        bytes.extend_from_slice(&lo_inst.into_bytes());
    }

    bytes
}

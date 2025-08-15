pub use brik_rv32::*;

use crate::util::misc;
use crate::util::into_bytes::IntoBytes;

use core::mem;

use smallvec::SmallVec;

pub type RV32Inst = SmallVec<[u8; mem::size_of::<u32>() * 2]>;

/// ```
/// use brik::rv32::{I, Reg};
/// use brik::rv32::encode_li_rv32_little;
/// use brik::util::misc::le_bytes_into_int as lint;
///
/// // imm fits into 12 bits
/// let bytes = encode_li_rv32_little(Reg::A0, 42);
/// assert_eq!{
///     I::try_from_u32(lint(&bytes)).unwrap(),
///     I::ADDI { d: Reg::A0, s: Reg::ZERO, im: 42 }
/// };
///
/// // imm doesn't fit into 12 bits
/// let bytes = encode_li_rv32_little(Reg::A1, 0x12345);
/// assert_eq!{
///     I::try_from_u32(lint(&bytes[..4])).unwrap(),
///     I::LUI { d: Reg::A1, im: 0x12 }
/// };
///
/// assert_eq!{
///     I::try_from_u32(lint(&bytes[4..])).unwrap(),
///     I::ADDI { d: Reg::A1, s: Reg::A1, im: 0x345 }
/// };
/// ```
pub fn encode_li_rv32_little(rd: Reg, imm: i32) -> RV32Inst {
    let mut bytes = RV32Inst::new();

    if misc::fits_into_12_bits(imm) {
        let inst = I::ADDI { d: rd, s: Reg::ZERO, im: imm as i16 };
        bytes.extend_from_slice(&inst.into_bytes());
        return bytes
    }

    let upper12 = (imm + 0x800) >> 12;
    let hi_inst = I::LUI { d: rd, im: upper12 };
    bytes.extend_from_slice(&hi_inst.into_bytes());

    let lower12 = imm - (upper12 << 12);

    if lower12 != 0 {
        debug_assert!{
            misc::fits_into_12_bits(lower12),
            "lower12 bits of `li` rv64 little-endian don't fit into 12 bits: {lower12}"
        };

        let lo_inst = I::ADDI { d: rd, s: rd, im: lower12 as i16 };
        bytes.extend_from_slice(&lo_inst.into_bytes());
    }

    bytes
}

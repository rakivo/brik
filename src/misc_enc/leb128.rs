//! LEB128 encoding/decoding for unsigned (ULEB128) and signed (SLEB128) integers.
//!
//! Variable-length encoding, 7 bits per byte, little-endian base-128.

use std::mem;

use smallvec::SmallVec;
use num_traits::{PrimInt, Signed, Unsigned, FromPrimitive, ToPrimitive};

/// Max number of bytes needed to encode a u128 or i128 in LEB128 format.
pub const MAX_LEB128_BYTES: usize = 128_u8.div_ceil(7) as _;

/// Return type of encoding LEB128
pub type LebBytes = SmallVec<[u8; MAX_LEB128_BYTES]>;

/// Encode unsigned integer as ULEB128.
///
/// Returns a `SmallVec` containing the encoded bytes.
///
/// # Examples
///
/// ```
/// use brik::misc_enc::leb128::{encode_uleb128, decode_uleb128};
///
/// let buf = encode_uleb128(624485u32);
/// assert_eq!(&buf[..], &[0xE5, 0x8E, 0x26]);
///
/// let (val, used) = decode_uleb128::<u32>(&buf).unwrap();
/// assert_eq!(val, 624485);
/// assert_eq!(used, buf.len());
/// ```
pub fn encode_uleb128<T>(mut value: T) -> LebBytes
where
    T: PrimInt + Unsigned + FromPrimitive + ToPrimitive
{
    let mask = T::from_u8(0x7F).expect("couldn't construct u8 from T");
    let mut buf = LebBytes::with_capacity(MAX_LEB128_BYTES);
    loop {
        let mut byte = (value & mask).to_u8().unwrap();

        value = value >> 7;
        if !value.is_zero() { byte |= 0x80 }

        buf.push(byte);
        if value.is_zero() { break }
    }

    buf
}

/// Decode ULEB128 into an unsigned integer.
/// Returns `(value, bytes_used)`.
pub fn decode_uleb128<T>(bytes: &[u8]) -> anyhow::Result<(T, usize)>
where
    T: PrimInt + Unsigned + FromPrimitive,
{
    let mut ret = T::zero();
    let mut shift = 0;
    for (i, &byte) in bytes.iter().enumerate() {
        let chunk = T::from_u8(byte & 0x7F).unwrap();
        ret = ret | (chunk << shift);
        if (byte & 0x80) == 0 {
            return Ok((ret, i + 1))
        }

        shift += 7;
    }

    Err(anyhow::anyhow!("incomplete SLEB128 sequence"))
}

/// Encode signed integer as SLEB128.
///
/// Returns a `SmallVec` containing the encoded bytes.
///
/// # Examples
///
/// ```
/// use brik::misc_enc::leb128::{encode_sleb128, decode_sleb128};
///
/// let buf = encode_sleb128(-12345i32);
/// let (val, used) = decode_sleb128::<i32>(&buf).unwrap();
/// assert_eq!(val, -12345);
/// assert_eq!(used, buf.len());
/// ```
pub fn encode_sleb128<T>(mut value: T) -> LebBytes
where
    T: PrimInt + Signed + FromPrimitive + ToPrimitive,
{
    let mask = T::from_u8(0x7F).expect("couldn't construct u8 from T");
    let i8_neg1 = unsafe { T::from_i8(-1).unwrap_unchecked() };

    let mut buf = LebBytes::with_capacity(MAX_LEB128_BYTES);
    loop {
        let byte_val = (value & mask).to_u8().unwrap();
        let sign_bit_set = (byte_val & 0x40) != 0;
        value = value >> 7;

        let done = (value == T::zero() && !sign_bit_set) ||
                   (value == i8_neg1 && sign_bit_set);

        let byte_val = if done {
            byte_val
        } else {
            byte_val | 0x80
        };

        buf.push(byte_val);

        if done { break }
    }

    buf
}

/// Decode SLEB128 into a signed integer.
/// Returns `(value, bytes_used)`.
pub fn decode_sleb128<T>(bytes: &[u8]) -> anyhow::Result<(T, usize)>
where
    T: PrimInt + Signed + FromPrimitive,
{
    let mut ret = T::zero();
    let mut shift = 0;
    let size = mem::size_of::<T>() * 8;

    for (i, &byte) in bytes.iter().enumerate() {
        let ck = T::from_u8(byte & 0x7F).unwrap();
        ret = ret | (ck << shift);
        shift += 7;

        if (byte & 0x80) == 0 {
            // sext if needed
            if (shift < size) && ((byte & 0x40) != 0) {
                ret = ret | (!T::zero() << shift);
            }

            return Ok((ret, i + 1))
        }
    }

    Err(anyhow::anyhow!("incomplete SLEB128 sequence"))
}

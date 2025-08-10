use std::borrow::Cow;
use std::{slice, mem};

use smallvec::SmallVec;

pub trait IntoBytes<'a> {
    #[must_use]
    fn into_bytes(self) -> Cow<'a, [u8]>;

    #[allow(unused)]
    #[inline(always)]
    fn move_into(self, dst: &mut Vec<u8>)
    where
        Self: Sized
    {
        dst.extend_from_slice(&self.into_bytes())
    }
}

impl<'a> IntoBytes<'a> for &'a [u8] {
    #[inline(always)]
    fn into_bytes(self) -> Cow<'a, [u8]> {
        Cow::Borrowed(self)
    }
}

impl<'a, const N: usize> IntoBytes<'a> for &'a [u8; N] {
    #[inline(always)]
    fn into_bytes(self) -> Cow<'a, [u8]> {
        Cow::Borrowed(&self[..])
    }
}

impl<'a> IntoBytes<'a> for Vec<u8> {
    #[inline(always)]
    fn into_bytes(self) -> Cow<'a, [u8]> {
        Cow::Owned(self)
    }
}

impl<'a, A: smallvec::Array<Item = u8>> IntoBytes<'a> for SmallVec<A> {
    #[inline(always)]
    fn into_bytes(self) -> Cow<'a, [u8]> {
        Cow::Owned(self.into_vec())
    }
}

impl<'a> IntoBytes<'a> for u32 {
    #[inline(always)]
    fn into_bytes(self) -> Cow<'a, [u8]> {
        let bytes = unsafe {
            slice::from_raw_parts(
                &self as *const Self as *const _,
                mem::size_of::<Self>(),
            )
        };
        Cow::Owned(bytes.to_vec())
    }
}

impl<'a> IntoBytes<'a> for asm_riscv::I {
    #[inline(always)]
    fn into_bytes(self) -> Cow<'a, [u8]> {
        u32::from(self).into_bytes()
    }
}


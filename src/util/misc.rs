//! Helper functions and macros

use core::fmt;

use num_traits::{PrimInt, FromBytes};

/// Convert `v` from 1-based to 0-based, clamping the result with `cap`
///
/// # Examples
///
/// ```
/// # const fn b0(v: usize, cap: usize) -> usize {
/// #     let v = v.saturating_sub(1);
/// #     if v < cap { v } else { cap }
/// # }
///
/// assert_eq!(b0(1, 10), 0);   // 1-based 1 -> 0-based 0
/// assert_eq!(b0(5, 10), 4);   // 1-based 5 -> 0-based 4
/// assert_eq!(b0(0, 10), 0);   // saturating_sub prevents underflow; 0 saturates to 0
/// assert_eq!(b0(15, 10), 10); // clamped to cap = 10
/// assert_eq!(b0(11, 10), 10); // clamped to cap = 10
/// ```
pub const fn b0(v: usize, cap: usize) -> usize {
    let v = v.saturating_sub(1);
    if v < cap { v } else { cap }
}

#[track_caller]
#[inline(always)]
#[doc(alias = "lint")]
pub fn le_bytes_into_int<T>(bytes: &[u8]) -> T
where
    T: PrimInt + FromBytes,
    <T as FromBytes>::Bytes: Sized + for<'a> TryFrom<&'a [u8]>,
    for<'a> <<T as FromBytes>::Bytes as TryFrom<&'a [u8]>>::Error: fmt::Debug,
{
    let array: <T as FromBytes>::Bytes = bytes.try_into().expect("wrong length");
    T::from_le_bytes(&array)
}

#[track_caller]
#[inline(always)]
#[doc(alias = "bint")]
pub fn be_bytes_into_int<T>(bytes: &[u8]) -> T
where
    T: PrimInt + FromBytes,
    <T as FromBytes>::Bytes: Sized + for<'a> TryFrom<&'a [u8]>,
    for<'a> <<T as FromBytes>::Bytes as TryFrom<&'a [u8]>>::Error: fmt::Debug,
{
    let array: <T as FromBytes>::Bytes = bytes.try_into().expect("wrong length");
    T::from_be_bytes(&array)
}

// Check if T fits into 12-bits integer (i12)
#[inline(always)]
pub fn fits_into_12_bits<T: TryInto<i16>>(v: T) -> bool {
    const BOUND: i16 = 1 << (12 - 1);

    matches!{
        v.try_into(),
        Ok(v) if v > -BOUND && v < BOUND
    }
}

#[doc(hidden)]
macro_rules! debug_from_display {
    ($type: ty, newline) => {
        const _: fn() = || {
            fn assert_impl_display<T: std::fmt::Display>() {}
            assert_impl_display::<$type>();
        };

        impl std::fmt::Debug for $type {
            #[inline(always)]
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                writeln!(f)?;
                std::fmt::Display::fmt(self, f)
            }
        }
    };

    ($type: ty) => {
        const _: fn() = || {
            fn assert_impl_display<T: std::fmt::Display>() {}
            assert_impl_display::<$type>();
        };

        impl std::fmt::Debug for $type {
            #[inline(always)]
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::Display::fmt(self, f)
            }
        }
    };
}

// TODO(#20): Make `with_at_end!` support for generics and `where` clauses
macro_rules! with_at_end {
    (
        $(#[$meta:meta])*
        $vis:vis fn $name:ident
        $(<$($generics:tt),*>)?
        (
            &mut $self:ident $(, $param_name:ident: $param_type:ty $(,)?)*
        ) $(-> $ret:ty)? $body:block
    ) => {
        $(#[$meta])*
        $vis fn $name
        $(<$($generics),*>)?
        (&mut $self $(, $param_name: $param_type)*)
        $(-> $ret)?
        $body

        // TODO(#21): Stop using paste in macros as it is bad for lsp jumping
        paste::paste! {
            #[inline(always)]
            $vis fn [<$name _at_end>]
            $(<$($generics),*>)?
            (&mut $self $(, $param_name: $param_type)*)
            $(-> $ret)?
            {
                let sid = $self.$name($($param_name),*);
                $self.position_at_end(sid);
                sid
            }
        }
    };
}

// TODO(#19): Make `with_at!` support for generics and `where` clauses
macro_rules! with_no_at {
    // section version
    (
        $no_at_name: ident,
        $(#[$meta:meta])*
        pub fn $name_at:ident
        $(<$($generics:tt),*>)?
        (
            &mut $self:ident,
            $section:ident: $section_type:ty $(, $arg:ident: $ty:ty $(,)?)*
        ) $(-> $ret:ty)? $body:block
    ) => {
        $(#[$meta])*
        pub fn $name_at
        $(<$($generics),*>)?
        (
            &mut $self, $section: $section_type $(, $arg: $ty)*
        )
        $(-> $ret)?
        $body

        $(#[$meta])*
        #[track_caller]
        #[inline(always)]
        #[allow(unused_attributes)]
        pub fn $no_at_name
        $(<$($generics),*>)?
        (&mut $self $(, $arg: $ty)*)
        $(-> $ret)?
        {
            let $section = $self.expect_curr_section();
            $self.$name_at($section $(, $arg)*)
        }
    };

    // symbol version
    (
        symbol
        $no_at_name: ident,
        $(#[$meta:meta])*
        pub fn $name_at:ident
        $(<$($generics:tt),*>)?
        (
            &mut $self:ident,
            $section:ident: $section_type:ty $(, $arg:ident: $ty:ty $(,)?)*
        ) $(-> $ret:ty)? $body:block
    ) => {

        $(#[$meta])*
        pub fn $name_at
        $(<$($generics),*>)?
        (
            &mut $self, $section: $section_type $(, $arg: $ty)*
        ) $(-> $ret)? $body

        $(#[$meta])*
        #[track_caller]
        #[inline(always)]
        #[allow(unused_attributes)]
        pub fn $no_at_name
        $(<$($generics),*>)?
        (&mut $self $(, $arg: $ty)*)
        $(-> $ret)?
        {
            let $section = $self.expect_curr_section();
            let $section = $crate::object::write::SymbolSection::Section($section);
            $self.$name_at($section $(, $arg)*)
        }
    };
}

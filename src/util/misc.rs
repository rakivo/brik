/// helper: Convert `v` from 1-based to 0-based, clamping the result with `cap`
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

#[inline(always)]
pub fn fits_into_12_bits<T: TryInto<i16>>(v: T) -> bool {
    const BOUND: i16 = 1 << (12 - 1);

    matches!{
        v.try_into(),
        Ok(v) if v > -BOUND && v < BOUND
    }
}

/// Macro that generates a Debug implementation that formats the same as Display
/// with an optional newline prefix
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

macro_rules! with_at_end {
    (
        $(#[$meta:meta])*
        $vis:vis fn $name:ident(
            &mut $self:ident $(, $param_name:ident: $param_type:ty $(,)?)*
        ) $(-> $ret:ty)? $body:block
    ) => {
        $(#[$meta])*
        $vis fn $name(&mut $self $(, $param_name: $param_type)*) $(-> $ret)? $body

        paste::paste! {
            #[inline(always)]
            $vis fn [<$name _at_end>](&mut $self $(, $param_name: $param_type)*) $(-> $ret)? {
                let sid = $self.$name($($param_name),*);
                $self.position_at_end(sid);
                sid
            }
        }
    };
}

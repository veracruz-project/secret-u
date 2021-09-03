//! local vm for executing bytecode

use crate::error::Error;
use std::mem::size_of;
use std::mem::align_of;
use std::mem::transmute;
use std::slice;
use std::slice::SliceIndex;
use std::convert::TryFrom;
use std::cmp::min;
use std::cmp::max;
use std::cmp::Ordering;

#[cfg(feature="debug-trace")]
use crate::opcode::OpIns;
#[cfg(feature="debug-cycle-count")]
use std::cell::Cell;

use secret_u_macros::engine_for_t;
use secret_u_macros::engine_match;


/// Trait to help with treating as generic byte arrays,
/// little-endian is required when order is important, but
/// fortunately order is usually not important.
///
/// Also some useful constants:
/// true  = ones = 0xffffff...
/// false = zero = 0x000000...
///
/// This pattern comes from the SIMD world, don't blame me!
///
trait Bytes: Sized {
    const ONES: Self;
    const ZERO: Self;

    type Bytes: AsRef<[u8]> + AsMut<[u8]> + for<'a> TryFrom<&'a [u8]>;

    fn to_ne_bytes(self) -> Self::Bytes;
    fn from_ne_bytes(bytes: Self::Bytes) -> Self;

    fn to_le_bytes(self) -> Self::Bytes;
    fn from_le_bytes(bytes: Self::Bytes) -> Self;

    fn to_le(self) -> Self;
    fn from_le(self) -> Self;

    // extract/replace
    fn extract<T>(self, i: u16) -> Option<T>
    where
        T: Bytes
    {
        let bytes = self.to_le_bytes();
        let i = i as usize;
        bytes.as_ref()
            .get(i*size_of::<T>() .. (i+1)*size_of::<T>())
            .map(|slice| {
                T::from_le_bytes(
                    <T as Bytes>::Bytes::try_from(slice).ok().unwrap()
                )
            })
    }

    fn replace<T>(self, i: u16, t: T) -> Option<Self>
    where
        T: Bytes
    {
        let mut bytes = self.to_le_bytes();
        let i = i as usize;

        bytes.as_mut()
            .get_mut(i*size_of::<T>() .. (i+1)*size_of::<T>())?
            .copy_from_slice(t.to_le_bytes().as_ref());

        Some(Self::from_le_bytes(bytes))
    }

    // common conversion operations
    fn extend_u<T>(lnpw2: u8, t: T) -> Self
    where
        T: Bytes,
    {
        let from_lane_size = size_of::<T>() >> lnpw2;
        let to_lane_size = size_of::<Self>() >> lnpw2;

        let from_bytes = t.to_le_bytes();
        let from_bytes = from_bytes.as_ref();
        let mut to_bytes = Self::ZERO.to_le_bytes();

        for i in 0 .. 1 << lnpw2 {
            to_bytes.as_mut()[i*to_lane_size .. i*to_lane_size+from_lane_size]
                .copy_from_slice(&from_bytes[i*from_lane_size .. (i+1)*from_lane_size]);
        }

        Self::from_le_bytes(to_bytes)
    }

    fn extend_s<T>(lnpw2: u8, t: T) -> Self
    where
        T: Bytes,
    {
        let from_lane_size = size_of::<T>() >> lnpw2;
        let to_lane_size = size_of::<Self>() >> lnpw2;

        let from_bytes = t.to_le_bytes();
        let from_bytes = from_bytes.as_ref();
        let mut to_bytes = Self::ZERO.to_le_bytes();

        for i in 0 .. 1 << lnpw2 {
            to_bytes.as_mut()[i*to_lane_size .. i*to_lane_size+from_lane_size]
                .copy_from_slice(&from_bytes[i*from_lane_size .. (i+1)*from_lane_size]);
            let sign = if to_bytes.as_ref()[i*to_lane_size+from_lane_size-1] & 0x80 == 0x80 { 0xff } else { 0x00 };
            to_bytes.as_mut()[i*to_lane_size+from_lane_size .. (i+1)*to_lane_size]
                .fill(sign);
        }

        Self::from_le_bytes(to_bytes)
    }

    fn truncate<T>(lnpw2: u8, t: T) -> Self
    where
        T: Bytes,
    {
        let from_lane_size = size_of::<T>() >> lnpw2;
        let to_lane_size = size_of::<Self>() >> lnpw2;

        let from_bytes = t.to_le_bytes();
        let from_bytes = from_bytes.as_ref();
        let mut to_bytes = Self::ZERO.to_le_bytes();

        for i in 0 .. 1 << lnpw2 {
            to_bytes.as_mut()[i*to_lane_size .. (i+1)*to_lane_size]
                .copy_from_slice(&from_bytes[i*from_lane_size .. i*from_lane_size+to_lane_size]);
        }

        Self::from_le_bytes(to_bytes)
    }

    // splat
    fn splat<T>(t: T) -> Self
    where
        T: Bytes + Copy,
    {
        let from_bytes = t.to_ne_bytes();
        let from_bytes = from_bytes.as_ref();
        let mut to_bytes = Self::ZERO.to_ne_bytes();

        for i in (0..size_of::<Self>()).step_by(size_of::<T>()) {
            to_bytes.as_mut()[i..i+size_of::<T>()]
                .copy_from_slice(from_bytes);
        }

        Self::from_ne_bytes(to_bytes)
    }

    // quick signed casting
    fn cast_s<T>(t: T) -> Self
    where
        T: Bytes + Copy,
    {
        if size_of::<T>() > size_of::<Self>() {
            Self::truncate(0, t)
        } else {
            Self::extend_s(0, t)
        }
    }
}

engine_for_t! {
    __if(!__has_lanes && __has_prim) {
        impl Bytes for U {
            const ONES: Self = Self::MAX;
            const ZERO: Self = 0;

            type Bytes = [u8; __size];

            #[inline]
            fn to_ne_bytes(self) -> Self::Bytes {
                Self::to_ne_bytes(self)
            }

            #[inline]
            fn from_ne_bytes(bytes: Self::Bytes) -> Self {
                Self::from_ne_bytes(bytes)
            }

            #[inline]
            fn to_le_bytes(self) -> Self::Bytes {
                Self::to_le_bytes(self)
            }

            #[inline]
            fn from_le_bytes(bytes: Self::Bytes) -> Self {
                Self::from_le_bytes(bytes)
            }

            #[inline]
            fn to_le(self) -> Self {
                Self::to_le(self)
            }

            #[inline]
            fn from_le(self) -> Self {
                Self::from_le(self)
            }
        }
    }

    __if(!__has_lanes && __has_limbs) {
        impl Bytes for U {
            const ONES: Self = [<__limb_t>::MAX; __limbs];
            const ZERO: Self = [0; __limbs];

            type Bytes = [u8; __size];

            #[inline]
            fn to_ne_bytes(self) -> Self::Bytes {
                unsafe { transmute(self) }
            }

            #[inline]
            fn from_ne_bytes(bytes: Self::Bytes) -> Self {
                unsafe { transmute(bytes) }
            }

            #[inline]
            fn to_le_bytes(self) -> Self::Bytes {
                self.to_le().to_ne_bytes()
            }

            #[inline]
            fn from_le_bytes(bytes: Self::Bytes) -> Self {
                Self::from_ne_bytes(bytes).from_le()
            }

            #[inline]
            fn to_le(mut self) -> Self {
                for i in 0..__limbs {
                    self[i] = self[i].to_le();
                }
                self
            }

            #[inline]
            fn from_le(mut self) -> Self {
                for i in 0..__limbs {
                    self[i] = self[i].from_le();
                }
                self
            }
        }
    }
}


/// Helper for converting into indices (u32)
trait IntoUsize: Sized {
    /// Cheap cast to u32
    fn wrapping_into_u32(self) -> u32;

    /// Cast to u32 with overflow checking
    fn try_into_u32(self) -> Option<u32>;

    /// Cheap cast from u32
    fn wrapping_from_u32(size: u32) -> Self;

    /// Cast from u32 with overflow checking
    fn try_from_u32(size: u32) -> Option<Self>;
}

engine_for_t! {
    __if(!__has_lanes && __has_prim) {
        impl IntoUsize for U {
            fn wrapping_into_u32(self) -> u32 {
                self as u32
            }

            fn try_into_u32(self) -> Option<u32> {
                u32::try_from(self).ok()
            }

            fn wrapping_from_u32(size: u32) -> Self {
                size as Self
            }

            fn try_from_u32(size: u32) -> Option<Self> {
                Self::try_from(size).ok()
            }
        }
    }

    __if(!__has_lanes && __has_limbs) {
        impl IntoUsize for U {
            fn wrapping_into_u32(self) -> u32 {
                self[0] as u32
            }

            fn try_into_u32(self) -> Option<u32> {
                if self[1..].iter().all(|x| *x == 0) {
                    u32::try_from(self[0]).ok()
                } else {
                    None
                }
            }

            fn wrapping_from_u32(size: u32) -> Self {
                let mut words = [0; __limbs];
                words[0] = size as __limb_t;
                words
            }

            fn try_from_u32(size: u32) -> Option<Self> {
                let mut words = [0; __limbs];
                words[0] = <__limb_t>::try_from(size).ok()?;
                Some(words)
            }
        }
    }
}


/// Trait to help perform multi-lane operations
///
/// Note we do make a big assumption here, that we can free transmute
/// between native-endian types of different sizes. This should be
/// true for little-endian and big-endian platforms, but is it true
/// for _all_ platforms?
///
/// The order of iteration does NOT matter and must not be relied on
///
trait Lanes<T: Sized>: Sized {
    fn xmap<F: FnMut(T) -> T>(self, f: F) -> Self;
    fn xfilter<F: FnMut(T) -> bool>(self, f: F) -> Self;
    fn xfold<A, F: FnMut(A, T) -> A>(self, f: F, init: A) -> A;

    // higher order operations, is this the best way to do this? not
    // sure of a better way...
    fn xmap2<F: FnMut(T, T) -> T>(self, b: Self, f: F) -> Self;
    fn xfilter2<F: FnMut(T, T) -> bool>(self, b: Self, f: F) -> Self;
    fn xfold2<A, F: FnMut(A, T, T) -> A>(self, b: Self, f: F, init: A) -> A;

    fn xmap3<F: FnMut(T, T, T) -> T>(self, b: Self, c: Self, f: F) -> Self;
    fn xfilter3<F: FnMut(T, T, T) -> bool>(self, b: Self, c: Self, f: F) -> Self;
    fn xfold3<A, F: FnMut(A, T, T, T) -> A>(self, b: Self, c: Self, f: F, init: A) -> A;
}

engine_for_t! {
    __if(__has_lanes) {
        impl Lanes<L> for U {
            #[inline]
            fn xmap<F: FnMut(L) -> L>(self, mut f: F) -> Self {
                let mut xs: [L; __lanes] = unsafe { transmute(self) };
                for i in 0..__lanes {
                    xs[i] = f(xs[i]);
                }
                unsafe { transmute(xs) }
            }

            #[inline]
            fn xfilter<F: FnMut(L) -> bool>(self, mut f: F) -> Self {
                let mut xs: [L; __lanes] = unsafe { transmute(self) };
                for i in 0..__lanes {
                    xs[i] = if f(xs[i]) { <L>::ONES } else { <L>::ZERO };
                }
                unsafe { transmute(xs) }
            }

            #[inline]
            fn xfold<A, F: FnMut(A, L) -> A>(self, mut f: F, mut a: A) -> A {
                let xs: [L; __lanes] = unsafe { transmute(self) };
                for i in 0..__lanes {
                    a = f(a, xs[i]);
                }
                a
            }

            #[inline]
            fn xmap2<F: FnMut(L, L) -> L>(self, b: U, mut f: F) -> U {
                let mut xs: [L; __lanes] = unsafe { transmute(self) };
                let     ys: [L; __lanes] = unsafe { transmute(b)    };
                for i in 0..__lanes {
                    xs[i] = f(xs[i], ys[i]);
                }
                unsafe { transmute(xs) }
            }
            #[inline]
            fn xfilter2<F: FnMut(L, L) -> bool>(self, b: U, mut f: F) -> U {
                let mut xs: [L; __lanes] = unsafe { transmute(self) };
                let     ys: [L; __lanes] = unsafe { transmute(b)    };
                for i in 0..__lanes {
                    xs[i] = if f(xs[i], ys[i]) { <L>::ONES } else { <L>::ZERO };
                }
                unsafe { transmute(xs) }
            }
            #[inline]
            fn xfold2<A, F: FnMut(A, L, L) -> A>(self, b: U, mut f: F, mut a: A) -> A {
                let xs: [L; __lanes] = unsafe { transmute(self) };
                let ys: [L; __lanes] = unsafe { transmute(b)    };
                for i in 0..__lanes {
                    a = f(a, xs[i], ys[i]);
                }
                a
            }

            #[inline]
            fn xmap3<F: FnMut(L, L, L) -> L>(self, b: U, c: U, mut f: F) -> U {
                let mut xs: [L; __lanes] = unsafe { transmute(self) };
                let     ys: [L; __lanes] = unsafe { transmute(b)    };
                let     zs: [L; __lanes] = unsafe { transmute(c)    };
                for i in 0..__lanes {
                    xs[i] = f(xs[i], ys[i], zs[i]);
                }
                unsafe { transmute(xs) }
            }
            #[inline]
            fn xfilter3<F: FnMut(L, L, L) -> bool>(self, b: U, c: U, mut f: F) -> U {
                let mut xs: [L; __lanes] = unsafe { transmute(self) };
                let     ys: [L; __lanes] = unsafe { transmute(b)    };
                let     zs: [L; __lanes] = unsafe { transmute(c)    };
                for i in 0..__lanes {
                    xs[i] = if f(xs[i], ys[i], zs[i]) { <L>::ONES } else { <L>::ZERO };
                }
                unsafe { transmute(xs) }
            }
            #[inline]
            fn xfold3<A, F: FnMut(A, L, L, L) -> A>(self, b: U, c: U, mut f: F, mut a: A) -> A {
                let xs: [L; __lanes] = unsafe { transmute(self) };
                let ys: [L; __lanes] = unsafe { transmute(b)    };
                let zs: [L; __lanes] = unsafe { transmute(c)    };
                for i in 0..__lanes {
                    a = f(a, xs[i], ys[i], zs[i]);
                }
                a
            }
        }
    }

    __if(!__has_lanes) {
        impl Lanes<L> for U {
            #[inline]
            fn xmap<F: FnMut(L) -> L>(self, mut f: F) -> Self {
                f(self)
            }

            #[inline]
            fn xfilter<F: FnMut(L) -> bool>(self, mut f: F) -> Self {
                if f(self) { <L>::ONES } else { <L>::ZERO }
            }

            #[inline]
            fn xfold<A, F: FnMut(A, L) -> A>(self, mut f: F, a: A) -> A {
                f(a, self)
            }

            #[inline]
            fn xmap2<F: FnMut(L, L) -> L>(self, b: U, mut f: F) -> Self {
                f(self, b)
            }
            #[inline]
            fn xfilter2<F: FnMut(L, L) -> bool>(self, b: U, mut f: F) -> Self {
                if f(self, b) { <L>::ONES } else { <L>::ZERO }
            }
            #[inline]
            fn xfold2<A, F: FnMut(A, L, L) -> A>(self, b: U, mut f: F, a: A) -> A {
                f(a, self, b)
            }

            #[inline]
            fn xmap3<F: FnMut(L, L, L) -> L>(self, b: U, c: U, mut f: F) -> Self {
                f(self, b, c)
            }
            #[inline]
            fn xfilter3<F: FnMut(L, L, L) -> bool>(self, b: U, c: U, mut f: F) -> Self {
                if f(self, b, c) { <L>::ONES } else { <L>::ZERO }
            }
            #[inline]
            fn xfold3<A, F: FnMut(A, L, L, L) -> A>(self, b: U, c: U, mut f: F, a: A) -> A {
                f(a, self, b, c)
            }
        }
    }
}


/// Primitive implementation of VM operations
trait Vop: Eq {
    fn vlt_u(self, b: Self) -> bool;
    fn vlt_s(self, b: Self) -> bool;
    fn vgt_u(self, b: Self) -> bool;
    fn vgt_s(self, b: Self) -> bool;
    fn vle_u(self, b: Self) -> bool;
    fn vle_s(self, b: Self) -> bool;
    fn vge_u(self, b: Self) -> bool;
    fn vge_s(self, b: Self) -> bool;

    fn vmin_u(self, b: Self) -> Self;
    fn vmin_s(self, b: Self) -> Self;
    fn vmax_u(self, b: Self) -> Self;
    fn vmax_s(self, b: Self) -> Self;

    fn vneg(self) -> Self;
    fn vabs(self) -> Self;
    fn vnot(self) -> Self;
    fn vclz(self) -> Self;
    fn vctz(self) -> Self;
    fn vpopcnt(self) -> Self;

    fn vadd(self, b: Self) -> Self;
    fn vsub(self, b: Self) -> Self;
    fn vmul(self, b: Self) -> Self;
    fn vand(self, b: Self) -> Self;
    fn vandnot(self, b: Self) -> Self;
    fn vor(self, b: Self) -> Self;
    fn vxor(self, b: Self) -> Self;
    fn vshl(self, b: Self) -> Self;
    fn vshr_u(self, b: Self) -> Self;
    fn vshr_s(self, b: Self) -> Self;
    fn vrotl(self, b: Self) -> Self;
    fn vrotr(self, b: Self) -> Self;
}

engine_for_t! {
    __if(!__has_lanes && __has_prim) {
        impl Vop for U {
            fn vlt_u(self, other: Self) -> bool {
                self < other
            }

            fn vlt_s(self, other: Self) -> bool {
                (self as __prim_i) < (other as __prim_i)
            }

            fn vgt_u(self, other: Self) -> bool {
                self > other
            }

            fn vgt_s(self, other: Self) -> bool {
                (self as __prim_i) > (other as __prim_i)
            }

            fn vle_u(self, other: Self) -> bool {
                self <= other
            }

            fn vle_s(self, other: Self) -> bool {
                (self as __prim_i) <= (other as __prim_i)
            }

            fn vge_u(self, other: Self) -> bool {
                self >= other
            }

            fn vge_s(self, other: Self) -> bool {
                (self as __prim_i) >= (other as __prim_i)
            }

            fn vmin_u(self, other: Self) -> Self {
                min(self, other)
            }

            fn vmin_s(self, other: Self) -> Self {
                min(self as __prim_i, other as __prim_i) as __prim_t
            }

            fn vmax_u(self, other: Self) -> Self {
                max(self, other)
            }

            fn vmax_s(self, other: Self) -> Self {
                max(self as __prim_i, other as __prim_i) as __prim_t
            }

            fn vneg(self) -> Self {
                (-(self as __prim_i)) as __prim_t
            }

            fn vabs(self) -> Self {
                (self as __prim_i).abs() as __prim_t
            }

            fn vnot(self) -> Self {
                !self
            }

            fn vclz(self) -> Self {
                self.leading_zeros() as __prim_t
            }

            fn vctz(self) -> Self {
                self.trailing_zeros() as __prim_t
            }

            fn vpopcnt(self) -> Self {
                self.count_ones() as __prim_t
            }

            fn vadd(self, other: Self) -> Self {
                self.wrapping_add(other)
            }

            fn vsub(self, other: Self) -> Self {
                self.wrapping_sub(other)
            }

            fn vmul(self, other: Self) -> Self {
                self.wrapping_mul(other)
            }

            fn vand(self, other: Self) -> Self {
                self & other
            }

            fn vandnot(self, other: Self) -> Self {
                self & !other
            }

            fn vor(self, other: Self) -> Self {
                self | other
            }

            fn vxor(self, other: Self) -> Self {
                self ^ other
            }

            fn vshl(self, other: Self) -> Self {
                self.wrapping_shl(other as u32)
            }

            fn vshr_u(self, other: Self) -> Self {
                self.wrapping_shr(other as u32)
            }

            fn vshr_s(self, other: Self) -> Self {
                (self as __prim_i).wrapping_shr(other as u32) as __prim_t
            }

            fn vrotl(self, other: Self) -> Self {
                self.rotate_left(other as u32)
            }

            fn vrotr(self, other: Self) -> Self {
                self.rotate_right(other as u32)
            }
        }
    }

    __if(!__has_lanes && __has_limbs) {
        impl Vop for U {
            fn vlt_u(self, other: Self) -> bool {
                let mut lt = false;
                for i in 0..__limbs {
                    lt = match self[i].cmp(&other[i]) {
                        Ordering::Less    => true,
                        Ordering::Greater => false,
                        Ordering::Equal   => lt,
                    }
                }
                lt
            }

            fn vlt_s(self, other: Self) -> bool {
                let lt = self.vlt_u(other);
                // the only difference from lt_u is when sign-bits mismatch
                match ((self[__limbs-1] as __limb_i) < 0, (other[__limbs-1] as __limb_i) < 0) {
                    (true, false) => true,
                    (false, true) => false,
                    _             => lt
                }
            }

            fn vgt_u(self, other: Self) -> bool {
                let mut gt = false;
                for i in 0..__limbs {
                    gt = match self[i].cmp(&other[i]) {
                        Ordering::Less    => false,
                        Ordering::Greater => true,
                        Ordering::Equal   => gt,
                    }
                }
                gt
            }

            fn vgt_s(self, other: Self) -> bool {
                let gt = self.vgt_u(other);
                // the only difference from gt_u is when sign-bits mismatch
                match ((self[__limbs-1] as __limb_i) < 0, (other[__limbs-1] as __limb_i) < 0) {
                    (true, false) => false,
                    (false, true) => true,
                    _             => gt
                }
            }

            fn vle_u(self, other: Self) -> bool {
                !self.vgt_u(other)
            }

            fn vle_s(self, other: Self) -> bool {
                !self.vgt_s(other)
            }

            fn vge_u(self, other: Self) -> bool {
                !self.vlt_u(other)
            }

            fn vge_s(self, other: Self) -> bool {
                !self.vlt_s(other)
            }

            fn vmin_u(self, other: Self) -> Self {
                if self.vlt_u(other) {
                    self
                } else {
                    other
                }
            }

            fn vmin_s(self, other: Self) -> Self {
                if self.vlt_s(other) {
                    self
                } else {
                    other
                }
            }

            fn vmax_u(self, other: Self) -> Self {
                if self.vgt_u(other) {
                    self
                } else {
                    other
                }
            }

            fn vmax_s(self, other: Self) -> Self {
                if self.vgt_s(other) {
                    self
                } else {
                    other
                }
            }

            fn vneg(self) -> Self {
                let zero = [0; __limbs];
                zero.vsub(self)
            }

            fn vabs(self) -> Self {
                let neg = self.vneg();
                if (self[__limbs-1] as __limb_i) < 0 {
                    neg
                } else {
                    self
                }
            }

            fn vnot(mut self) -> Self {
                for i in 0..__limbs {
                    self[i] = !self[i];
                }
                self
            }

            fn vclz(self) -> Self {
                let mut sum = 0;
                for i in 0..__limbs {
                    sum = if self[i] == 0 { sum } else { 0 }
                        + self[i].leading_zeros();
                }
                Self::wrapping_from_u32(sum)
            }

            fn vctz(self) -> Self {
                let mut sum = 0;
                let mut done = false;
                for i in 0..__limbs {
                    sum += if !done { self[i].trailing_zeros() } else { 0 };
                    done |= self[i] == 0;
                }
                Self::wrapping_from_u32(sum)
            }

            fn vpopcnt(self) -> Self {
                let mut sum = 0;
                for i in 0..__limbs {
                    sum += self[i].count_ones();
                }
                Self::wrapping_from_u32(sum)
            }

            fn vadd(mut self, other: Self) -> Self {
                let mut overflow = false;
                for i in 0..__limbs {
                    let (v, o1) = self[i].overflowing_add(other[i]);
                    let (v, o2) = v.overflowing_add(<__limb_t>::from(overflow));
                    self[i] = v;
                    overflow = o1 || o2;
                }
                self
            }

            fn vsub(mut self, other: Self) -> Self {
                let mut overflow = false;
                for i in 0..__limbs {
                    let (v, o1) = self[i].overflowing_sub(other[i]);
                    let (v, o2) = v.overflowing_sub(<__limb_t>::from(overflow));
                    self[i] = v;
                    overflow = o1 || o2;
                }
                self
            }

            fn vmul(self, other: Self) -> Self {
                // simple long multiplication based on wikipedia
                // https://en.wikipedia.org/wiki/Multiplication_algorithm#Long_multiplication
                let mut words = [0; __limbs];
                for i in 0..__limbs {
                    let mut overflow: __limb2_t = 0;
                    for j in 0..__limbs {
                        if i+j < __limbs {
                            let v = <__limb2_t>::from(words[i+j])
                                + (<__limb2_t>::from(self[i]) * <__limb2_t>::from(other[j]))
                                + overflow;
                            words[i+j] = v as __limb_t;
                            overflow = v >> (8*__limb_size);
                        }
                    }
                }
                words
            }

            fn vand(mut self, other: Self) -> Self {
                for i in 0..__limbs {
                    self[i] = self[i] & other[i];
                }
                self
            }

            fn vandnot(mut self, other: Self) -> Self {
                for i in 0..__limbs {
                    self[i] = self[i] & !other[i];
                }
                self
            }

            fn vor(mut self, other: Self) -> Self {
                for i in 0..__limbs {
                    self[i] = self[i] | other[i];
                }
                self
            }

            fn vxor(mut self, other: Self) -> Self {
                for i in 0..__limbs {
                    self[i] = self[i] ^ other[i];
                }
                self
            }

            fn vshl(self, other: Self) -> Self {
                let b = other.wrapping_into_u32() % (8*__size as u32);
                let width = 8*__limb_size as u32;
                let sh_lo = b % width;
                let sh_hi = (b / width) as usize;

                let mut words = [0; __limbs];
                for i in 0..__limbs {
                    words[i]
                        = (i.checked_sub(sh_hi)
                            .and_then(|j| self.get(j))
                            .unwrap_or(&0)
                            << sh_lo)
                        | (i.checked_sub(sh_hi+1)
                            .and_then(|j| self.get(j))
                            .unwrap_or(&0)
                            .checked_shr(width - sh_lo)
                            .unwrap_or(0));
                }

                words
            }

            fn vshr_u(self, other: Self) -> Self {
                let b = other.wrapping_into_u32() % (8*__size as u32);
                let width = 8*__limb_size as u32;
                let sh_lo = b % width;
                let sh_hi = (b / width) as usize;

                let mut words = [0; __limbs];
                for i in 0..__limbs {
                    words[i]
                        = (i.checked_add(sh_hi)
                            .and_then(|j| self.get(j))
                            .unwrap_or(&0)
                            >> sh_lo)
                        | (i.checked_add(sh_hi+1)
                            .and_then(|j| self.get(j))
                            .unwrap_or(&0)
                            .checked_shl(width - sh_lo)
                            .unwrap_or(0));
                }

                words
            }

            fn vshr_s(self, other: Self) -> Self {
                let b = other.wrapping_into_u32() % (8*__size as u32);
                let width = 8*__limb_size as u32;
                let sh_lo = b % width;
                let sh_hi = (b / width) as usize;
                let sig = if (self[__limbs-1] as __limb_i) < 0 { 0 } else { <__limb_t>::MAX };

                let mut words = [0; __limbs];
                for i in 0..__limbs {
                    words[i]
                        = (((*i.checked_add(sh_hi)
                            .and_then(|j| self.get(j))
                            .unwrap_or(&sig)
                            as __limb_i) >> sh_lo) as __limb_t)
                        | (i.checked_add(sh_hi+1)
                            .and_then(|j| self.get(j))
                            .unwrap_or(&sig)
                            .checked_shl(width - sh_lo)
                            .unwrap_or(0));
                }

                words
            }

            fn vrotl(self, other: Self) -> Self {
                let b = other.wrapping_into_u32() % (8*__size as u32);
                let width = 8*__limb_size as u32;
                let sh_lo = b % width;
                let sh_hi = (b / width) as usize;

                let mut words = [0; __limbs];
                for i in 0..__limbs {
                    words[i]
                        = (self[i.wrapping_sub(sh_hi  ) % __limbs]
                            << sh_lo)
                        | (self[i.wrapping_sub(sh_hi+1) % __limbs]
                            .checked_shr(width - sh_lo).unwrap_or(0));
                }

                words
            }

            fn vrotr(self, other: Self) -> Self {
                let b = other.wrapping_into_u32() % (8*__size as u32);
                let width = 8*__limb_size as u32;
                let sh_lo = b % width;
                let sh_hi = (b / width) as usize;

                let mut words = [0; __limbs];
                for i in 0..__limbs {
                    words[i]
                        = (self[i.wrapping_add(sh_hi) % __limbs]
                            >> sh_lo)
                        | (self[i.wrapping_add(sh_hi+1) % __limbs]
                            .checked_shl(width - sh_lo).unwrap_or(0));
                }

                words
            }
        }
    }
}


/// Wrapper for handling different type access to state
#[derive(Debug)]
struct State<'a> {
    state: &'a mut [u8],
    align: usize,
}

impl<'a> From<&'a mut [u8]> for State<'a> {
    fn from(state: &mut [u8]) -> State {
        // find max alignment here
        let align = 1 << (state.as_ptr() as usize).trailing_zeros();

        State {
            state: state,
            align: align,
        }
    }
}

impl AsRef<[u8]> for State<'_> {
    fn as_ref(&self) -> &[u8] {
        self.state
    }
}

impl AsMut<[u8]> for State<'_> {
    fn as_mut(&mut self) -> &mut [u8] {
        self.state
    }
}

impl State<'_> {
    // accessors
    fn reg<'a, T: 'a>(&'a self, idx: u16) -> Result<&'a T, Error> {
        self.slice(usize::from(idx))
    }

    fn reg_mut<'a, T: 'a>(&'a mut self, idx: u16) -> Result<&'a mut T, Error> {
        self.slice_mut(usize::from(idx))
    }

    fn slice<'a, T: 'a, I: SliceIndex<[T]>>(
        &'a self,
        idx: I
    ) -> Result<&'a <I as SliceIndex<[T]>>::Output, Error> {
        if self.align >= align_of::<T>() {
            let ptr = self.state.as_ptr().cast();
            let len = self.state.len() / size_of::<T>();
            let slice = unsafe { slice::from_raw_parts(ptr, len) };
            slice.get(idx).ok_or(Error::OutOfBounds)
        } else {
            Err(Error::Unaligned)
        }
    }

    fn slice_mut<'a, T: 'a, I: SliceIndex<[T]>>(
        &'a mut self,
        idx: I
    ) -> Result<&'a mut <I as SliceIndex<[T]>>::Output, Error> {
        if self.align >= align_of::<T>() {
            let ptr = self.state.as_mut_ptr().cast();
            let len = self.state.len() / size_of::<T>();
            let slice = unsafe { slice::from_raw_parts_mut(ptr, len) };
            slice.get_mut(idx).ok_or(Error::OutOfBounds)
        } else {
            Err(Error::Unaligned)
        }
    }
}

impl<'a> State<'a> {
    // needed due to ownership rules
    fn ret(mut self, ret_size: usize) -> Result<&'a [u8], Error> {
        // zero memory outside of register to avoid leaking info
        self.slice_mut::<u8, _>(ret_size..)?.fill(0x00);

        #[cfg(feature="debug-trace")]
        {
            println!("result:");
            print!("    0x");
            for i in (0..ret_size).rev() {
                print!("{:02x}", self.state.get(i).ok_or(Error::OutOfBounds)?);
            }
            println!();
        }

        // print accumulative cycle count so far
        #[cfg(feature="debug-cycle-count")]
        {
            let cycles = CYCLE_COUNT.with(|c| c.get());
            println!("engine-cycle-count: {}", cycles);
        }

        // return ret value, consuming our lifetime
        self.state.get(..ret_size).ok_or(Error::OutOfBounds)
    }
}


#[cfg(feature="debug-cycle-count")]
thread_local! {
    static CYCLE_COUNT: Cell<u64> = Cell::new(0);
}


/// Simple non-constant crypto-VM for testing 
///
/// NOTE! This is a quick simulated VM for testing and proof-of-concept!
/// Not constant time!
///
pub fn exec<'a>(
    bytecode: &[u64],
    state: &'a mut [u8]
) -> Result<&'a [u8], Error> {
    // setup PC, bytecode must end in return, which means we can avoid
    // checking for end-of-code every step
    let mut pc: *const u64 = bytecode.as_ptr();

    let last = bytecode.last().copied().unwrap_or(0);
    if last & 0x00ffffff00000000 != 0x0002000000000000 {
        // bytecode must end in return
        Err(Error::InvalidReturn)?;
    }

    // setup state
    let mut s = State::from(state);

    #[cfg(feature="debug-trace")]
    {
        println!("trace:");
    }

    // core loop
    loop {
        let ins: u64 = unsafe { *pc };
        pc = unsafe { pc.add(1) };

        #[cfg(feature="debug-cycle-count")]
        CYCLE_COUNT.with(|c| c.set(c.get() + 1));

        #[cfg(feature="debug-trace")]
        {
            match OpIns::try_from(ins) {
                Ok(ins) => print!("    {:<24} :", format!("{}", ins)),
                _       => print!("    {:<24} :", format!("unknown {:#018x}", ins)),
            }
            for i in 0..s.state.len() {
                print!(" {:02x}", s.state[i]);
            }
            println!();
        }

        let npw2  = ((ins & 0xf000000000000000) >> 60) as u8;
        let lnpw2 = ((ins & 0x0f00000000000000) >> 56) as u8;
        let op    = ((ins & 0x00ff000000000000) >> 48) as u8;
        let d     = ((ins & 0x0000ffff00000000) >> 32) as u16;
        let a     = ((ins & 0x00000000ffff0000) >> 16) as u16;
        let b     = ((ins & 0x000000000000ffff) >>  0) as u16;
        let ab    = ((ins & 0x00000000ffffffff) >>  0) as u32;

        // engine_match sort of breaks macro hygiene, this was much easier than
        // proper scoping and engine_match is really only intended to be used here
        //
        // aside from relying on opc, engine_match also introduces
        // - U: type of word
        // - L: type of lane
        engine_match! {
            //// arg/ret instructions ////

            // arg (convert to ne)
            0x01 if __lnpw2 == 0 => {
                let ra = s.reg::<U>(a)?;
                *s.reg_mut::<U>(d)? = ra.from_le();
            }

            // ret (convert from ne and exit)
            0x02 if __lnpw2 == 0 => {
                let ra = s.reg::<U>(a)?;
                *s.reg_mut::<U>(d)? = ra.to_le();
                return s.ret(size_of::<U>());
            }


            //// conversion instructions ////

            // extend_u
            0x03 => {
                let ra = s.reg::<L>(a)?;
                *s.reg_mut::<U>(d)? = <U>::extend_u(b as u8, *ra);
            }

            // extend_s
            0x04 => {
                let ra = s.reg::<L>(a)?;
                *s.reg_mut::<U>(d)? = <U>::extend_s(b as u8, *ra);
            }

            // truncate
            0x05 => {
                let ra = s.reg::<U>(a)?;
                *s.reg_mut::<L>(d)? = <L>::truncate(b as u8, *ra);
            }

            // splat
            0x06 => {
                let ra = s.reg::<L>(a)?;
                *s.reg_mut::<U>(d)? = <U>::splat(*ra);
            }

            // splat_const
            0x07 => {
                // small const encoded in low 32-bits of instruction
                // sign extend and splat
                let c = <L>::cast_s(ab);
                *s.reg_mut::<U>(d)? = <U>::splat(c);
            }

            // splat_long_const
            0x08 => {
                // b encodes size of const here, must be u64 aligned
                if b < 3 {
                    Err(Error::InvalidOpcode(ins))?;
                }
                let words = (1 << b) / 8;

                // we need to check the bounds on this
                if unsafe { bytecode.as_ptr_range().end.offset_from(pc) } < words as isize {
                    Err(Error::OutOfBounds)?;
                }

                // load from instruction stream
                let mut bytes = [0u8; __lane_size];
                for i in 0..words {
                    let word = unsafe { *pc };
                    pc = unsafe { pc.add(1) };
                    bytes[i*8..(i+1)*8].copy_from_slice(&word.to_le_bytes());
                }
                // sign extend
                let sign = if bytes[8*words-1] & 0x80 == 0x80 { 0xff } else { 0x00 };
                bytes[8*words..].fill(sign);

                // splat
                let c = <L>::from_le_bytes(bytes);
                *s.reg_mut::<U>(d)? = <U>::splat(c);
            }


            //// special instructions ////

            // extract (le)
            0x09 => {
                let ra = s.reg::<U>(a)?;
                *s.reg_mut::<L>(d)? = ra.extract(b).unwrap();
            }

            // replace (le)
            0x0a => {
                let rd = s.reg::<U>(d)?;
                let ra = s.reg::<L>(a)?;
                *s.reg_mut::<U>(d)? = rd.replace(b, *ra).unwrap();
            }

            // select
            0x0b => {
                let rd = s.reg::<U>(d)?;
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = rb.xmap3(*ra, *rd, |x: L, y: L, z: L| {
                    if x != <L>::ZERO {
                        y
                    } else {
                        z
                    }
                });
            }

            // shuffle
            0x0c => {
                let rd = s.reg::<U>(d)?;
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                let mut i  = 0;
                *s.reg_mut::<U>(d)? = ra.xfold2(*rd, |r, x: L, y: L| {
                    let r = rb.xmap2(r, |w: L, z: L| {
                        let j = w.try_into_u32().unwrap_or(u32::MAX);
                        if j == i {
                            x
                        } else if j == i+(1<<__lnpw2) {
                            y
                        } else {
                            z
                        }
                    });
                    i += 1;
                    r
                }, <U>::ZERO);
            }


            //// comparison instructions ////

            // eq
            0x0d => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.xfilter2(*rb, |x: L, y: L| x == y);
            }

            // eq_c
            0x0e => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xfilter(|x: L| x == c);
            }

            // ne
            0x0f => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.xfilter2(*rb, |x: L, y: L| x != y);
            }

            // ne_c
            0x10 => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xfilter(|x: L| x != c);
            }

            // lt_u
            0x11 => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.xfilter2(*rb, |x: L, y: L| x.vlt_u(y));
            }

            // lt_u_c
            0x12 => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xfilter(|x: L| x.vlt_u(c));
            }

            // lt_s
            0x13 => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.xfilter2(*rb, |x: L, y: L| x.vlt_s(y));
            }

            // lt_s_c
            0x14 => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xfilter(|x: L| x.vlt_s(c));
            }

            // gt_u
            0x15 => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.xfilter2(*rb, |x: L, y: L| x.vgt_u(y));
            }

            // gt_u_c
            0x16 => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xfilter(|x: L| x.vgt_u(c));
            }

            // gt_s
            0x17 => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.xfilter2(*rb, |x: L, y: L| x.vgt_s(y));
            }

            // gt_s_c
            0x18 => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xfilter(|x: L| x.vgt_s(c));
            }

            // le_u
            0x19 => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.xfilter2(*rb, |x: L, y: L| x.vle_u(y));
            }

            // le_u_c
            0x1a => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xfilter(|x: L| x.vle_u(c));
            }

            // le_s
            0x1b => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.xfilter2(*rb, |x: L, y: L| x.vle_s(y));
            }

            // le_s_c
            0x1c => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xfilter(|x: L| x.vle_s(c));
            }

            // ge_u
            0x1d => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.xfilter2(*rb, |x: L, y: L| x.vge_u(y));
            }

            // ge_u_c
            0x1e => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xfilter(|x: L| x.vge_u(c));
            }

            // ge_s
            0x1f => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.xfilter2(*rb, |x: L, y: L| x.vge_s(y));
            }

            // min_u
            0x21 => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.xmap2(*rb, |x: L, y: L| x.vmin_u(y));
            }

            // min_u_c
            0x22 => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xmap(|x: L| x.vmin_u(c));
            }

            // min_s
            0x23 => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.xmap2(*rb, |x: L, y: L| x.vmin_s(y));
            }

            // min_s_c
            0x24 => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xmap(|x: L| x.vmin_s(c));
            }

            // max_u
            0x25 => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.xmap2(*rb, |x: L, y: L| x.vmax_u(y));
            }

            // max_u_c
            0x26 => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xmap(|x: L| x.vmax_u(c));
            }

            // max_s
            0x27 => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.xmap2(*rb, |x: L, y: L| x.vmax_s(y));
            }

            // max_s_c
            0x28 => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xmap(|x: L| x.vmax_s(c));
            }


            //// integer instructions ////

            // neg
            0x29 => {
                let ra = s.reg::<U>(a)?;
                *s.reg_mut::<U>(d)? = ra.xmap(|x: L| x.vneg());
            }

            // abs
            0x2a => {
                let ra = s.reg::<U>(a)?;
                *s.reg_mut::<U>(d)? = ra.xmap(|x: L| x.vabs());
            }

            // not
            0x2b => {
                let ra = s.reg::<U>(a)?;
                *s.reg_mut::<U>(d)? = ra.vnot();
            }

            // clz
            0x2c => {
                let ra = s.reg::<U>(a)?;
                *s.reg_mut::<U>(d)? = ra.xmap(|x: L| x.vclz());
            }

            // ctz
            0x2d => {
                let ra = s.reg::<U>(a)?;
                *s.reg_mut::<U>(d)? = ra.xmap(|x: L| x.vctz());
            }

            // popcnt
            0x2e => {
                let ra = s.reg::<U>(a)?;
                *s.reg_mut::<U>(d)? = ra.xmap(|x: L| x.vpopcnt());
            }

            // add
            0x2f => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.xmap2(*rb, |x: L, y: L| x.vadd(y));
            }

            // add_c
            0x30 => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xmap(|x: L| x.vadd(c));
            }

            // sub
            0x31 => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.xmap2(*rb, |x: L, y: L| x.vsub(y));
            }

            // sub_c
            0x32 => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xmap(|x: L| x.vsub(c));
            }

            // mul
            0x33 => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.xmap2(*rb, |x: L, y: L| x.vmul(y));
            }

            // mul_c
            0x34 => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xmap(|x: L| x.vmul(c));
            }

            // and
            0x35 => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.vand(*rb);
            }

            // and_c
            0x36 => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xmap(|x: L| x.vand(c));
            }

            // andnot
            0x37 => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.vandnot(*rb);
            }

            // andnot_c
            0x38 => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xmap(|x: L| x.vandnot(c));
            }

            // or
            0x39 => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.vor(*rb);
            }

            // or_c
            0x3a => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xmap(|x: L| x.vor(c));
            }

            // xor
            0x3b => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.vxor(*rb);
            }

            // xor_c
            0x3c => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xmap(|x: L| x.vxor(c));
            }

            // shl
            0x3d => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.xmap2(*rb, |x: L, y: L| x.vshl(y));
            }

            // shl_c
            0x3e => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xmap(|x: L| x.vshl(c));
            }

            // shr_u
            0x3f => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.xmap2(*rb, |x: L, y: L| x.vshr_u(y));
            }

            // shr_u_c
            0x40 => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xmap(|x: L| x.vshr_u(c));
            }

            // shr_s
            0x41 => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.xmap2(*rb, |x: L, y: L| x.vshr_s(y));
            }

            // shr_s_c
            0x42 => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xmap(|x: L| x.vshr_s(c));
            }

            // rotl
            0x43 => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.xmap2(*rb, |x: L, y: L| x.vrotl(y));
            }

            // rotl_c
            0x44 => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xmap(|x: L| x.vrotl(c));
            }

            // rotr
            0x45 => {
                let ra = s.reg::<U>(a)?;
                let rb = s.reg::<U>(b)?;
                *s.reg_mut::<U>(d)? = ra.xmap2(*rb, |x: L, y: L| x.vrotr(y));
            }

            // rotr_c
            0x46 => {
                let ra = s.reg::<U>(a)?;
                let c = <L>::cast_s(b);
                *s.reg_mut::<U>(d)? = ra.xmap(|x: L| x.vrotr(c));
            }
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::opcode::*;
    use std::io;

    #[test]
    fn exec_add() {
        let example = OpTree::add(0,
            OpTree::<U32>::imm(1u32),
            OpTree::<U32>::imm(2u32)
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, mut stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        let result = exec(&bytecode, &mut stack).unwrap();
        print!("  result:");
        for i in 0..result.len() {
            print!(" {:02x}", result[i]);
        }
        println!();

        assert_eq!(result, &[0x03, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn exec_add_parallel() {
        let example = OpTree::add(2,
            OpTree::<U32>::imm(0x01020304u32),
            OpTree::<U32>::imm(0x0506fffeu32)
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, mut stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        let result = exec(&bytecode, &mut stack).unwrap();
        print!("  result:");
        for i in 0..result.len() {
            print!(" {:02x}", result[i]);
        }
        println!();

        assert_eq!(result, &[0x02, 0x02, 0x08, 0x06]);
    }


    #[test]
    fn exec_alignment() {
        let example = OpTree::add(0,
            OpTree::<U16>::extend_s(0,
                OpTree::<U8>::imm(2u8)
            ),
            OpTree::<U16>::truncate(0,
                OpTree::<U32>::imm(1u32),
            ),
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, mut stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        let result = exec(&bytecode, &mut stack).unwrap();
        print!("  result:");
        for i in 0..result.len() {
            print!(" {:02x}", result[i]);
        }
        println!();

        assert_eq!(result, &[0x03, 0x00]);
    }

    #[test]
    fn exec_dag() {
        let two = OpTree::<U32>::imm(2u32);
        let a = OpTree::add(0,
            OpTree::<U32>::imm(1u32),
            OpTree::<U32>::imm(2u32)
        );
        let b = OpTree::shr_s(0,
            a.clone(), two.clone()
        );
        let c = OpTree::shl(0,
            a.clone(), two.clone()
        );
        let example = OpTree::eq(0,
            OpTree::add(0,
                OpTree::mul(0, b, two),
                c,
            ),
            a,
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, mut stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        let result = exec(&bytecode, &mut stack).unwrap();
        print!("  result:");
        for i in 0..result.len() {
            print!(" {:02x}", result[i]);
        }
        println!();

        assert_eq!(result, &[0x00, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn exec_pythag() {
        let a = OpTree::<U32>::imm(3u32);
        let b = OpTree::<U32>::imm(4u32);
        let c = OpTree::<U32>::imm(5u32);
        let example = OpTree::eq(0,
            OpTree::add(0,
                OpTree::mul(0, a.clone(), a),
                OpTree::mul(0, b.clone(), b)
            ),
            OpTree::mul(0, c.clone(), c)
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, mut stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        let result = exec(&bytecode, &mut stack).unwrap();
        print!("  result:");
        for i in 0..result.len() {
            print!(" {:02x}", result[i]);
        }
        println!();

        assert_eq!(result, &[0xff, 0xff, 0xff, 0xff]);
    }

    #[test]
    fn exec_too_many_casts() {
        // this intentionally has an obnoxious amount of casting
        let a = OpTree::<U8>::const_(1u8);
        let b = OpTree::<U16>::const_(1u16);
        let c = OpTree::<U32>::imm(2u32);
        let d = OpTree::<U64>::imm(3u64);
        let e = OpTree::<U128>::const_(5u128);
        let fib_3 = OpTree::add(0,
            OpTree::<U32>::extend_u(0, b.clone()), OpTree::<U32>::extend_u(0, a.clone())
        );
        let fib_4 = OpTree::add(0,
            OpTree::<U64>::extend_u(0, fib_3.clone()), OpTree::<U64>::extend_u(0, b.clone())
        );
        let fib_5 = OpTree::add(0,
            OpTree::<U128>::extend_u(0, fib_4.clone()), OpTree::<U128>::extend_u(0, fib_3.clone())
        );
        let example = OpTree::and(
            OpTree::and(
                OpTree::<U8>::truncate(0, OpTree::eq(0, fib_3.clone(), c)),
                OpTree::<U8>::truncate(0, OpTree::eq(0, fib_4.clone(), d))
            ),
            OpTree::<U8>::truncate(0, OpTree::eq(0, fib_5.clone(), e))
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, mut stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        let result = exec(&bytecode, &mut stack).unwrap();
        print!("  result:");
        for i in 0..result.len() {
            print!(" {:02x}", result[i]);
        }
        println!();

        assert_eq!(result, &[0xff]);
    }

    // tests for individual instructions
    macro_rules! test_ins {
        () => {};
        (
            $name:ident { $u:ident.$op:ident($($a:expr),+) => $expected:expr}
            $($rest:tt)*
        ) => {
            test_ins! {
                $name { $u.$op(; $($a),+) => $expected }
                $($rest)*
            }
        };
        (
            $name:ident { $u:ident.$op:ident($($x:expr)?; $($a:expr),+) => $expected:expr }
            $($rest:tt)*
        ) => {
            #[test]
            fn $name() {
                let input = OpTree::$op(
                    $(
                        $x,
                    )?
                    $(
                        OpTree::<$u>::imm($a)
                    ),+
                );

                println!();
                println!("input:");
                input.disas(io::stdout()).unwrap();
                let (bytecode, mut stack) = input.compile(true);
                println!("  bytecode:");
                disas(&bytecode, io::stdout()).unwrap();
                print!("  stack:");
                for i in 0..stack.len() {
                    print!(" {:02x}", stack[i]);
                }
                println!();

                let result = exec(&bytecode, &mut stack).unwrap();
                print!("  result:");
                for i in 0..result.len() {
                    print!(" {:02x}", result[i]);
                }
                println!();

                assert_eq!(result, &$expected);
            }

            test_ins! { $($rest)* }
        };
    }

    test_ins! {
        ins_select_t   { U32.select(0; [1,0,0,0], [2,0,0,0], [3,0,0,0]) => [2,0,0,0] }
        ins_select_f   { U32.select(0; [0,0,0,0], [2,0,0,0], [3,0,0,0]) => [3,0,0,0] }
        ins_select_par { U32.select(2; [1,0,1,0], [2,3,4,5], [6,7,8,9]) => [2,7,4,9] }
        ins_shuffle    { U32.shuffle(2; [7,2,0xff,0], [5,6,7,8], [9,10,11,12]) => [12,7,0,5] }

        ins_eq     { U32.eq(0; [1,2,3,0xff], [1,3,3,0]) => [0x00,0x00,0x00,0x00] }
        ins_eq_par { U32.eq(2; [1,2,3,0xff], [1,3,3,0]) => [0xff,0x00,0xff,0x00] }
        ins_ne     { U32.ne(0; [1,2,3,0xff], [1,3,3,0]) => [0xff,0xff,0xff,0xff] }
        ins_ne_par { U32.ne(2; [1,2,3,0xff], [1,3,3,0]) => [0x00,0xff,0x00,0xff] }
        ins_lt_u     { U32.lt_u(0; [1,2,3,0xff], [1,3,3,0]) => [0x00,0x00,0x00,0x00] }
        ins_lt_u_par { U32.lt_u(2; [1,2,3,0xff], [1,3,3,0]) => [0x00,0xff,0x00,0x00] }
        ins_lt_s     { U32.lt_s(0; [1,2,3,0xff], [1,3,3,0]) => [0xff,0xff,0xff,0xff] }
        ins_lt_s_par { U32.lt_s(2; [1,2,3,0xff], [1,3,3,0]) => [0x00,0xff,0x00,0xff] }
        ins_gt_u     { U32.gt_u(0; [1,2,3,0xff], [1,3,3,0]) => [0xff,0xff,0xff,0xff] }
        ins_gt_u_par { U32.gt_u(2; [1,2,3,0xff], [1,3,3,0]) => [0x00,0x00,0x00,0xff] }
        ins_gt_s     { U32.gt_s(0; [1,2,3,0xff], [1,3,3,0]) => [0x00,0x00,0x00,0x00] }
        ins_gt_s_par { U32.gt_s(2; [1,2,3,0xff], [1,3,3,0]) => [0x00,0x00,0x00,0x00] }
        ins_le_u     { U32.le_u(0; [1,2,3,0xff], [1,3,3,0]) => [0x00,0x00,0x00,0x00] }
        ins_le_u_par { U32.le_u(2; [1,2,3,0xff], [1,3,3,0]) => [0xff,0xff,0xff,0x00] }
        ins_le_s     { U32.le_s(0; [1,2,3,0xff], [1,3,3,0]) => [0xff,0xff,0xff,0xff] }
        ins_le_s_par { U32.le_s(2; [1,2,3,0xff], [1,3,3,0]) => [0xff,0xff,0xff,0xff] }
        ins_ge_u     { U32.ge_u(0; [1,2,3,0xff], [1,3,3,0]) => [0xff,0xff,0xff,0xff] }
        ins_ge_u_par { U32.ge_u(2; [1,2,3,0xff], [1,3,3,0]) => [0xff,0x00,0xff,0xff] }
        ins_ge_s     { U32.ge_s(0; [1,2,3,0xff], [1,3,3,0]) => [0x00,0x00,0x00,0x00] }
        ins_ge_s_par { U32.ge_s(2; [1,2,3,0xff], [1,3,3,0]) => [0xff,0x00,0xff,0x00] }
        ins_min_u     { U32.min_u(0; [1,2,3,0xff], [1,3,3,0]) => [1,3,3,   0] }
        ins_min_u_par { U32.min_u(2; [1,2,3,0xff], [1,3,3,0]) => [1,2,3,   0] }
        ins_min_s     { U32.min_s(0; [1,2,3,0xff], [1,3,3,0]) => [1,2,3,0xff] }
        ins_min_s_par { U32.min_s(2; [1,2,3,0xff], [1,3,3,0]) => [1,2,3,0xff] }
        ins_max_u     { U32.max_u(0; [1,2,3,0xff], [1,3,3,0]) => [1,2,3,0xff] }
        ins_max_u_par { U32.max_u(2; [1,2,3,0xff], [1,3,3,0]) => [1,3,3,0xff] }
        ins_max_s     { U32.max_s(0; [1,2,3,0xff], [1,3,3,0]) => [1,3,3,   0] }
        ins_max_s_par { U32.max_s(2; [1,2,3,0xff], [1,3,3,0]) => [1,3,3,   0] }

        ins_neg        { U32.neg(0;    [0x00,0xfe,0x02,0xff]) => [0x00,0x02,0xfd,0x00] } 
        ins_neg_par    { U32.neg(2;    [0x00,0xfe,0x02,0xff]) => [0x00,0x02,0xfe,0x01] }
        ins_abs        { U32.abs(0;    [0x00,0xfe,0x02,0xff]) => [0x00,0x02,0xfd,0x00] } 
        ins_abs_par    { U32.abs(2;    [0x00,0xfe,0x02,0xff]) => [0x00,0x02,0x02,0x01] }
        ins_not        { U32.not(      [0x00,0xfe,0x02,0xff]) => [0xff,0x01,0xfd,0x00] } 
        ins_clz        { U32.clz(0;    [0x00,0xfe,0x02,0xff]) => [0x00,0x00,0x00,0x00] } 
        ins_clz_par    { U32.clz(2;    [0x00,0xfe,0x02,0xff]) => [0x08,0x00,0x06,0x00] } 
        ins_ctz        { U32.ctz(0;    [0x00,0xfe,0x02,0xff]) => [0x09,0x00,0x00,0x00] } 
        ins_ctz_par    { U32.ctz(2;    [0x00,0xfe,0x02,0xff]) => [0x08,0x01,0x01,0x00] } 
        ins_popcnt     { U32.popcnt(0; [0x00,0xfe,0x02,0xff]) => [0x10,0x00,0x00,0x00] } 
        ins_popcnt_par { U32.popcnt(2; [0x00,0xfe,0x02,0xff]) => [0x00,0x07,0x01,0x08] } 

        ins_add     { U32.add(0; [0xff,0x02,0x03,0x04], [0xff,0x06,0x07,0x08]) => [0xfe,0x09,0x0a,0x0c] }
        ins_add_par { U32.add(2; [0xff,0x02,0x03,0x04], [0xff,0x06,0x07,0x08]) => [0xfe,0x08,0x0a,0x0c] }
        ins_sub     { U32.sub(0; [0xff,0x02,0x03,0x04], [0xff,0x06,0x07,0x08]) => [0x00,0xfc,0xfb,0xfb] }
        ins_sub_par { U32.sub(2; [0xff,0x02,0x03,0x04], [0xff,0x06,0x07,0x08]) => [0x00,0xfc,0xfc,0xfc] }
        ins_mul     { U32.mul(0; [0xff,0x02,0x03,0x04], [0xff,0x06,0x07,0x08]) => [0x01,0xf6,0x0a,0x1e] }
        ins_mul_par { U32.mul(2; [0xff,0x02,0x03,0x04], [0xff,0x06,0x07,0x08]) => [0x01,0x0c,0x15,0x20] }
        ins_and     { U32.and(   [0xff,0x02,0x03,0x04], [0xff,0x06,0x07,0x08]) => [0xff,0x02,0x03,0x00] }
        ins_andnot  { U32.andnot([0xff,0x02,0x03,0x04], [0xff,0x06,0x07,0x08]) => [0x00,0x00,0x00,0x04] }
        ins_or      { U32.or(    [0xff,0x02,0x03,0x04], [0xff,0x06,0x07,0x08]) => [0xff,0x06,0x07,0x0c] }
        ins_xor     { U32.xor(   [0xff,0x02,0x03,0x04], [0xff,0x06,0x07,0x08]) => [0x00,0x04,0x04,0x0c] }

        ins_shl       { U32.shl(0;   [0xff,0x02,0x03,0x04], [0x03,0x00,0x00,0x00]) => [0xf8,0x17,0x18,0x20] }
        ins_shl_par   { U32.shl(2;   [0xff,0x02,0x03,0x04], [0x03,0x03,0x03,0x03]) => [0xf8,0x10,0x18,0x20] }
        ins_shr_u     { U32.shr_u(0; [0xff,0x02,0x03,0x04], [0x03,0x00,0x00,0x00]) => [0x5f,0x60,0x80,0x00] }
        ins_shr_u_par { U32.shr_u(2; [0xff,0x02,0x03,0x04], [0x03,0x03,0x03,0x03]) => [0x1f,0x00,0x00,0x00] }
        ins_shr_s     { U32.shr_s(0; [0xff,0x02,0x03,0x04], [0x03,0x00,0x00,0x00]) => [0x5f,0x60,0x80,0x00] }
        ins_shr_s_par { U32.shr_s(2; [0xff,0x02,0x03,0x04], [0x03,0x03,0x03,0x03]) => [0xff,0x00,0x00,0x00] }
        ins_rotl      { U32.rotl(0;  [0xff,0x02,0x03,0x04], [0x03,0x00,0x00,0x00]) => [0xf8,0x17,0x18,0x20] }
        ins_rotl_par  { U32.rotl(2;  [0xff,0x02,0x03,0x04], [0x03,0x03,0x03,0x03]) => [0xff,0x10,0x18,0x20] }
        ins_rotr      { U32.rotr(0;  [0xff,0x02,0x03,0x04], [0x03,0x00,0x00,0x00]) => [0x5f,0x60,0x80,0xe0] }
        ins_rotr_par  { U32.rotr(2;  [0xff,0x02,0x03,0x04], [0x03,0x03,0x03,0x03]) => [0xff,0x40,0x60,0x80] }
    }

    // here are some really big ones
    test_ins! {
        ins_select_big_par { U512.select(6; 
           [0x00,0x01,0x00,0x01,0x00,0x01,0x00,0x01,0x00,0x01,0x00,0x01,0x00,0x01,0x00,0x01,
            0x00,0x01,0x00,0x01,0x00,0x01,0x00,0x01,0x00,0x01,0x00,0x01,0x00,0x01,0x00,0x01,
            0x00,0x01,0x00,0x01,0x00,0x01,0x00,0x01,0x00,0x01,0x00,0x01,0x00,0x01,0x00,0x01,
            0x00,0x01,0x00,0x01,0x00,0x01,0x00,0x01,0x00,0x01,0x00,0x01,0x00,0x01,0x00,0x01],
           [0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,
            0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x19,0x1a,0x1b,0x1c,0x1d,0x1e,0x1f,
            0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27,0x28,0x29,0x2a,0x2b,0x2c,0x2d,0x2e,0x2f,
            0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37,0x38,0x39,0x3a,0x3b,0x3c,0x3d,0x3e,0x3f],
           [0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47,0x48,0x49,0x4a,0x4b,0x4c,0x4d,0x4e,0x4f,
            0x50,0x51,0x52,0x53,0x54,0x55,0x56,0x57,0x58,0x59,0x5a,0x5b,0x5c,0x5d,0x5e,0x5f,
            0x60,0x61,0x62,0x63,0x64,0x65,0x66,0x67,0x68,0x69,0x6a,0x6b,0x6c,0x6d,0x6e,0x6f,
            0x70,0x71,0x72,0x73,0x74,0x75,0x76,0x77,0x78,0x79,0x7a,0x7b,0x7c,0x7d,0x7e,0x7f]
        ) => [
            0x40,0x01,0x42,0x03,0x44,0x05,0x46,0x07,0x48,0x09,0x4a,0x0b,0x4c,0x0d,0x4e,0x0f,
            0x50,0x11,0x52,0x13,0x54,0x15,0x56,0x17,0x58,0x19,0x5a,0x1b,0x5c,0x1d,0x5e,0x1f,
            0x60,0x21,0x62,0x23,0x64,0x25,0x66,0x27,0x68,0x29,0x6a,0x2b,0x6c,0x2d,0x6e,0x2f,
            0x70,0x31,0x72,0x33,0x74,0x35,0x76,0x37,0x78,0x39,0x7a,0x3b,0x7c,0x3d,0x7e,0x3f] }
        ins_shuffle_big_par { U512.shuffle(6; 
           [0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x10,0x11,0x12,0x13,0x14,0x15,0x16,
            0x32,0x31,0x30,0x29,0x28,0x27,0x26,0x25,0x24,0x23,0x22,0x21,0x20,0x19,0x18,0x17,
            0x33,0x34,0x35,0x36,0x37,0x38,0x39,0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47,0x48,
            0x64,0x63,0x62,0x61,0x60,0x59,0x58,0x57,0x56,0x55,0x54,0x53,0x52,0x51,0x50,0x49],
           [0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,
            0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x19,0x1a,0x1b,0x1c,0x1d,0x1e,0x1f,
            0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27,0x28,0x29,0x2a,0x2b,0x2c,0x2d,0x2e,0x2f,
            0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37,0x38,0x39,0x3a,0x3b,0x3c,0x3d,0x3e,0x3f],
           [0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47,0x48,0x49,0x4a,0x4b,0x4c,0x4d,0x4e,0x4f,
            0x50,0x51,0x52,0x53,0x54,0x55,0x56,0x57,0x58,0x59,0x5a,0x5b,0x5c,0x5d,0x5e,0x5f,
            0x60,0x61,0x62,0x63,0x64,0x65,0x66,0x67,0x68,0x69,0x6a,0x6b,0x6c,0x6d,0x6e,0x6f,
            0x70,0x71,0x72,0x73,0x74,0x75,0x76,0x77,0x78,0x79,0x7a,0x7b,0x7c,0x7d,0x7e,0x7f]
        ) => [
            0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x10,0x11,0x12,0x13,0x14,0x15,0x16,
            0x32,0x31,0x30,0x29,0x28,0x27,0x26,0x25,0x24,0x23,0x22,0x21,0x20,0x19,0x18,0x17,
            0x33,0x34,0x35,0x36,0x37,0x38,0x39,0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47,0x48,
            0x64,0x63,0x62,0x61,0x60,0x59,0x58,0x57,0x56,0x55,0x54,0x53,0x52,0x51,0x50,0x49] }

        ins_lt_u_big { U512.lt_u(0; U512::one(), U512::ones()) => [
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] }
        ins_lt_s_big { U512.lt_s(0; U512::one(), U512::ones()) => [
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00] }
        ins_min_u_big { U512.min_u(0; U512::one(), U512::ones()) => [
            0x01,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00] }
        ins_min_s_big { U512.min_s(0; U512::one(), U512::ones()) => [
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] }
        ins_abs_big { U512.abs(0; U512::ones()) => [
            0x01,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00] }

        ins_add_big { U512.add(0; U512::ones(), U512::ones()) => [
            0xfe,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] }
        ins_add_big_par { U512.add(4; U512::ones(), U512::ones()) => [
            0xfe,0xff,0xff,0xff,0xfe,0xff,0xff,0xff,0xfe,0xff,0xff,0xff,0xfe,0xff,0xff,0xff,
            0xfe,0xff,0xff,0xff,0xfe,0xff,0xff,0xff,0xfe,0xff,0xff,0xff,0xfe,0xff,0xff,0xff,
            0xfe,0xff,0xff,0xff,0xfe,0xff,0xff,0xff,0xfe,0xff,0xff,0xff,0xfe,0xff,0xff,0xff,
            0xfe,0xff,0xff,0xff,0xfe,0xff,0xff,0xff,0xfe,0xff,0xff,0xff,0xfe,0xff,0xff,0xff] }
        ins_sub_big { U512.sub(0; U512::ones(), U512::one()) => [
            0xfe,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] }
        ins_sub_big_par { U512.sub(4; U512::ones(), U512::splat(U32::one())) => [
            0xfe,0xff,0xff,0xff,0xfe,0xff,0xff,0xff,0xfe,0xff,0xff,0xff,0xfe,0xff,0xff,0xff,
            0xfe,0xff,0xff,0xff,0xfe,0xff,0xff,0xff,0xfe,0xff,0xff,0xff,0xfe,0xff,0xff,0xff,
            0xfe,0xff,0xff,0xff,0xfe,0xff,0xff,0xff,0xfe,0xff,0xff,0xff,0xfe,0xff,0xff,0xff,
            0xfe,0xff,0xff,0xff,0xfe,0xff,0xff,0xff,0xfe,0xff,0xff,0xff,0xfe,0xff,0xff,0xff] }
        ins_mul_big { U512.mul(0;
           [0x72,0x34,0x21,0xd8,0xf0,0x73,0xc7,0xd5,0x1e,0x7e,0x5e,0xe6,0x94,0x11,0xda,0x8e,
            0x1f,0x97,0xc5,0x76,0x0b,0xce,0x9d,0x02,0xeb,0xe2,0x14,0x19,0xd7,0x85,0x02,0x3a,
            0xe9,0x0c,0xd0,0x20,0xbf,0x85,0xb7,0x27,0x8b,0x8a,0x3c,0x9e,0x07,0xea,0x0d,0xb6,
            0x82,0x2e,0x02,0xd5,0xfb,0xc6,0x5e,0xcd,0x67,0xe1,0x5b,0xbc,0xcc,0x4c,0x48,0xa6],
           [0xc6,0xac,0x8d,0x67,0x96,0xfb,0x17,0x9d,0x61,0xe7,0x27,0xb4,0x8c,0xd7,0xa7,0xcb,
            0xfe,0xee,0x39,0xcd,0x7c,0xa8,0x80,0xc3,0x6a,0xf0,0x9e,0xa9,0x9e,0x22,0xca,0xa1,
            0xa6,0x2d,0x9c,0x16,0xae,0xec,0x6f,0x5e,0x2d,0xa1,0xbf,0xd5,0x57,0x82,0x75,0xf2,
            0x6e,0x2e,0x9a,0x7e,0x8a,0xbe,0x8d,0xde,0x88,0x4f,0x2b,0x2e,0xbe,0x2e,0x86,0xd3]
        ) => [
            0x2c,0x28,0xb5,0x39,0xad,0x64,0xe4,0xee,0x5a,0xda,0xd1,0x79,0xfc,0x26,0x7f,0x24,
            0x99,0xe2,0x89,0xb8,0x8c,0xf5,0x3f,0x7f,0xc8,0x24,0xdd,0x63,0x2a,0xf2,0xd8,0x8e,
            0xfe,0xc2,0x60,0x68,0xfe,0xc4,0x25,0x34,0xdd,0x91,0x89,0xa3,0xfb,0x08,0x4e,0x3c,
            0x2a,0x98,0x0e,0x08,0xbb,0x7a,0xee,0x0b,0xc7,0xd6,0x10,0xa1,0x76,0xbb,0x5b,0xea] }
        ins_mul_big_par { U512.mul(6;
           [0x72,0x34,0x21,0xd8,0xf0,0x73,0xc7,0xd5,0x1e,0x7e,0x5e,0xe6,0x94,0x11,0xda,0x8e,
            0x1f,0x97,0xc5,0x76,0x0b,0xce,0x9d,0x02,0xeb,0xe2,0x14,0x19,0xd7,0x85,0x02,0x3a,
            0xe9,0x0c,0xd0,0x20,0xbf,0x85,0xb7,0x27,0x8b,0x8a,0x3c,0x9e,0x07,0xea,0x0d,0xb6,
            0x82,0x2e,0x02,0xd5,0xfb,0xc6,0x5e,0xcd,0x67,0xe1,0x5b,0xbc,0xcc,0x4c,0x48,0xa6],
           [0xc6,0xac,0x8d,0x67,0x96,0xfb,0x17,0x9d,0x61,0xe7,0x27,0xb4,0x8c,0xd7,0xa7,0xcb,
            0xfe,0xee,0x39,0xcd,0x7c,0xa8,0x80,0xc3,0x6a,0xf0,0x9e,0xa9,0x9e,0x22,0xca,0xa1,
            0xa6,0x2d,0x9c,0x16,0xae,0xec,0x6f,0x5e,0x2d,0xa1,0xbf,0xd5,0x57,0x82,0x75,0xf2,
            0x6e,0x2e,0x9a,0x7e,0x8a,0xbe,0x8d,0xde,0x88,0x4f,0x2b,0x2e,0xbe,0x2e,0x86,0xd3]
        ) => [
            0x2c,0xf0,0x2d,0xe8,0xa0,0xc1,0xe1,0xa1,0x5e,0xb2,0x52,0xb8,0xf0,0x47,0x36,0x9a,
            0xc2,0x62,0xdd,0x7e,0x54,0x30,0x80,0x86,0x4e,0xe0,0x58,0x81,0xb2,0xaa,0x94,0x7a,
            0x16,0x1c,0xc0,0xc0,0xd2,0x9c,0x59,0x52,0x6f,0xca,0xc4,0x76,0x61,0xd4,0xf1,0x0c,
            0xdc,0x44,0x34,0xd6,0x4e,0xf4,0xc6,0xc6,0xb8,0x6f,0x49,0xc8,0x68,0xa8,0xb0,0xd2] }

        ins_and_big { U512.and(U512::ones(), U512::one()) => [
            0x01,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00] }
        ins_andnot_big { U512.andnot(U512::ones(), U512::one()) => [
            0xfe,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] }
        ins_or_big { U512.or(U512::ones(), U512::one()) => [
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] }
        ins_xor_big { U512.xor(U512::ones(), U512::one()) => [
            0xfe,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
            0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] }
        ins_shl_big { U512.shl(0; U512::one(), U512::extend_u(U32::from(123))) => [
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x08,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00] }
        ins_shr_big { U512.shr_u(0; U512::one(), U512::extend_u(U32::from(123))) => [
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00] }
        ins_rotl_big { U512.rotl(0; U512::one(), U512::extend_u(U32::from(123))) => [
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x08,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00] }
        ins_rotr_big { U512.rotr(0; U512::one(), U512::extend_u(U32::from(123))) => [
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
            0x20,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00] }
    }
}


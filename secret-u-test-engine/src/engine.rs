//! local vm for executing bytecode

use std::mem::size_of;
use std::mem::transmute;
use std::slice;
use std::slice::SliceIndex;
use std::convert::TryFrom;
use std::cmp::min;
use std::cmp::max;
use std::cmp::Ordering;

use secret_u_opcode::Error;

#[cfg(feature="debug-trace")]
use secret_u_opcode::OpIns;
#[cfg(feature="debug-cycle-count")]
use std::cell::Cell;

use secret_u_macros::engine_for_t;
use secret_u_macros::engine_match;
use secret_u_macros::engine_limb_t;

#[allow(non_camel_case_types)]
type __limb_t = engine_limb_t!();


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

/// Trait to help with treating as generic byte arrays,
/// little-endian is required when order is important, but
/// fortunately order is usually not important.
///
/// Normally we'd want to treat types as limb arrays where
/// possible, but treating types as byte array is useful for
/// generic conversion operations
///
/// Also some useful constants:
/// true  = ones = 0xffffff...
/// false = zero = 0x000000...
///
/// This pattern comes from the SIMD world, don't blame me!
///
trait Bytes_ {
    fn zero(d: &mut Self);
    fn ones(d: &mut Self);

    fn to_ne_bytes(d: &mut Self, a: &Self);
    fn from_ne_bytes(d: &mut Self, a: &Self);

    fn to_le_bytes(d: &mut Self, a: &Self);
    fn from_le_bytes(d: &mut Self, a: &Self);

    // extract/replace
    fn extract<T>(d: &mut T, a: &Self, i: u16) -> Result<(), Error>;
//    where
//        T: Bytes_
//    {
//        let bytes = self.to_le_bytes();
//        let i = i as usize;
//        bytes.as_ref()
//            .get(i*size_of::<T>() .. (i+1)*size_of::<T>())
//            .map(|slice| {
//                T::from_le_bytes(
//                    <T as Bytes>::Bytes::try_from(slice).ok().unwrap()
//                )
//            })
//    }

    fn replace<T>(d: &mut Self, a: &T, i: u16) -> Result<(), Error>;
//    where
//        T: Bytes
//    {
//        let mut bytes = self.to_le_bytes();
//        let i = i as usize;
//
//        bytes.as_mut()
//            .get_mut(i*size_of::<T>() .. (i+1)*size_of::<T>())?
//            .copy_from_slice(t.to_le_bytes().as_ref());
//
//        Some(Self::from_le_bytes(bytes))
//    }

    // common conversion operations
    fn extend_u<T>(d: &mut Self, a: &T, lnpw2: u8);
//    where
//        T: Bytes,
//    {
//        let from_lane_size = size_of::<T>() >> lnpw2;
//        let to_lane_size = size_of::<Self>() >> lnpw2;
//
//        let from_bytes = t.to_le_bytes();
//        let from_bytes = from_bytes.as_ref();
//        let mut to_bytes = Self::ZERO.to_le_bytes();
//
//        for i in 0 .. 1 << lnpw2 {
//            to_bytes.as_mut()[i*to_lane_size .. i*to_lane_size+from_lane_size]
//                .copy_from_slice(&from_bytes[i*from_lane_size .. (i+1)*from_lane_size]);
//        }
//
//        Self::from_le_bytes(to_bytes)
//    }

    fn extend_s<T>(d: &mut Self, a: &T, lnpw2: u8);
//    where
//        T: Bytes,
//    {
//        let from_lane_size = size_of::<T>() >> lnpw2;
//        let to_lane_size = size_of::<Self>() >> lnpw2;
//
//        let from_bytes = t.to_le_bytes();
//        let from_bytes = from_bytes.as_ref();
//        let mut to_bytes = Self::ZERO.to_le_bytes();
//
//        for i in 0 .. 1 << lnpw2 {
//            to_bytes.as_mut()[i*to_lane_size .. i*to_lane_size+from_lane_size]
//                .copy_from_slice(&from_bytes[i*from_lane_size .. (i+1)*from_lane_size]);
//            let sign = if to_bytes.as_ref()[i*to_lane_size+from_lane_size-1] & 0x80 == 0x80 { 0xff } else { 0x00 };
//            to_bytes.as_mut()[i*to_lane_size+from_lane_size .. (i+1)*to_lane_size]
//                .fill(sign);
//        }
//
//        Self::from_le_bytes(to_bytes)
//    }

    fn truncate<T>(d: &mut Self, a: &T, lnpw2: u8);
//    fn truncate<T>(lnpw2: u8, t: T) -> Self
//    where
//        T: Bytes,
//    {
//        let from_lane_size = size_of::<T>() >> lnpw2;
//        let to_lane_size = size_of::<Self>() >> lnpw2;
//
//        let from_bytes = t.to_le_bytes();
//        let from_bytes = from_bytes.as_ref();
//        let mut to_bytes = Self::ZERO.to_le_bytes();
//
//        for i in 0 .. 1 << lnpw2 {
//            to_bytes.as_mut()[i*to_lane_size .. (i+1)*to_lane_size]
//                .copy_from_slice(&from_bytes[i*from_lane_size .. i*from_lane_size+to_lane_size]);
//        }
//
//        Self::from_le_bytes(to_bytes)
//    }

    // splat
    fn splat<T>(d: &mut Self, a: &T);
//    fn splat<T>(t: T) -> Self
//    where
//        T: Bytes + Copy,
//    {
//        let from_bytes = t.to_ne_bytes();
//        let from_bytes = from_bytes.as_ref();
//        let mut to_bytes = Self::ZERO.to_ne_bytes();
//
//        for i in (0..size_of::<Self>()).step_by(size_of::<T>()) {
//            to_bytes.as_mut()[i..i+size_of::<T>()]
//                .copy_from_slice(from_bytes);
//        }
//
//        Self::from_ne_bytes(to_bytes)
//    }

    // TODO just provide immediate operation?
    // quick signed casting
//    fn cast_s<T>(t: T) -> Self
//    where
//        T: Bytes + Copy,
//    {
//        if size_of::<T>() > size_of::<Self>() {
//            Self::truncate(0, t)
//        } else {
//            Self::extend_s(0, t)
//        }
//    }
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
        if self.align >= size_of::<T>() {
            let ptr = self.state.as_ptr().cast();
            let len = self.state.len() / size_of::<T>();
            let slice = unsafe { slice::from_raw_parts(ptr, len) };
            slice.get(usize::from(idx)).ok_or(Error::OutOfBounds)
        } else {
            Err(Error::Unaligned)
        }
    }

    fn reg_mut<'a, T: 'a>(&'a mut self, idx: u16) -> Result<&'a mut T, Error> {
        if self.align >= size_of::<T>() {
            let ptr = self.state.as_mut_ptr().cast();
            let len = self.state.len() / size_of::<T>();
            let slice = unsafe { slice::from_raw_parts_mut(ptr, len) };
            slice.get_mut(usize::from(idx)).ok_or(Error::OutOfBounds)
        } else {
            Err(Error::Unaligned)
        }
    }

    fn short_reg<'a, T: 'a>(&'a self, idx: u16) -> Result<&'a T, Error> {
        if self.align >= size_of::<T>() {
            let ptr = self.state.as_ptr().cast();
            let len = self.state.len() / size_of::<T>();
            let slice = unsafe { slice::from_raw_parts(ptr, len) };
            slice.get(usize::from(idx)).ok_or(Error::OutOfBounds)
        } else {
            Err(Error::Unaligned)
        }
    }

    fn short_reg_mut<'a, T: 'a>(&'a mut self, idx: u16) -> Result<&'a mut T, Error> {
        if self.align >= size_of::<T>() {
            let ptr = self.state.as_mut_ptr().cast();
            let len = self.state.len() / size_of::<T>();
            let slice = unsafe { slice::from_raw_parts_mut(ptr, len) };
            slice.get_mut(usize::from(idx)).ok_or(Error::OutOfBounds)
        } else {
            Err(Error::Unaligned)
        }
    }

    fn long_reg<'a>(&'a self, idx: u16, npw2: u8) -> Result<&'a [__limb_t], Error> {
        let size = 1 << npw2;
        let limbs = size / size_of::<__limb_t>();
        if self.align >= size {
            let ptr = self.state.as_ptr().cast();
            let len = self.state.len() / size_of::<__limb_t>();
            let slice = unsafe { slice::from_raw_parts(ptr, len) };
            slice.get(
                usize::from(idx)*limbs .. (usize::from(idx)+1)*limbs
            ).ok_or(Error::OutOfBounds)
        } else {
            Err(Error::Unaligned)
        }
    }

    fn long_reg_mut<'a>(&'a mut self, idx: u16, npw2: u8) -> Result<&'a mut [__limb_t], Error> {
        let size = 1 << npw2;
        let limbs = size / size_of::<__limb_t>();
        if self.align >= size {
            let ptr = self.state.as_mut_ptr().cast();
            let len = self.state.len() / size_of::<__limb_t>();
            let slice = unsafe { slice::from_raw_parts_mut(ptr, len) };
            slice.get_mut(
                usize::from(idx)*limbs .. (usize::from(idx)+1)*limbs
            ).ok_or(Error::OutOfBounds)
        } else {
            Err(Error::Unaligned)
        }
    }

    fn slice<'a, I: SliceIndex<[u8]>>(
        &'a self,
        idx: I
    ) -> Result<&'a <I as SliceIndex<[u8]>>::Output, Error> {
        let ptr = self.state.as_ptr().cast();
        let len = self.state.len();
        let slice = unsafe { slice::from_raw_parts(ptr, len) };
        slice.get(idx).ok_or(Error::OutOfBounds)
    }

    fn slice_mut<'a, I: SliceIndex<[u8]>>(
        &'a mut self,
        idx: I
    ) -> Result<&'a mut <I as SliceIndex<[u8]>>::Output, Error> {
        let ptr = self.state.as_mut_ptr().cast();
        let len = self.state.len();
        let slice = unsafe { slice::from_raw_parts_mut(ptr, len) };
        slice.get_mut(idx).ok_or(Error::OutOfBounds)
    }
}

impl<'a> State<'a> {
    // needed due to ownership rules
    fn ret(mut self, ret_size: usize) -> Result<&'a [u8], Error> {
        // zero memory outside of register to avoid leaking info
        self.slice_mut(ret_size..)?.fill(0x00);

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


//! local vm for executing bytecode

use std::mem::size_of;
use std::slice;
use std::convert::TryFrom;
use std::cmp::min;
use std::cmp::max;
use std::cmp::Ordering;
use std::cell::UnsafeCell;

use secret_u_opcode::Error;

#[cfg(feature="debug-trace")]
use secret_u_opcode::OpIns;
#[cfg(feature="debug-cycle-count")]
use std::cell::Cell;

use secret_u_macros::engine_limb_t;
use secret_u_macros::engine_limbi_t;
use secret_u_macros::engine_limb2_t;
use secret_u_macros::engine_for_short_t;
use secret_u_macros::engine_match;

#[allow(non_upper_case_globals)]
const __limb_size: usize = size_of::<__limb_t>();
#[allow(non_camel_case_types)]
type __limb_t = engine_limb_t!();
#[allow(non_camel_case_types)]
type __limbi_t = engine_limbi_t!();
#[allow(non_camel_case_types)]
type __limb2_t = engine_limb2_t!();


/// Generalized VM operations
trait VType {
    // size in bytes
    fn vsize(&self) -> usize;

    // native-endian reference building
    unsafe fn vref(a: &[u8]) -> &Self;
    unsafe fn vref_mut(a: &mut [u8]) -> &mut Self;

    fn vraw_bytes(&self) -> &[u8];
    fn vraw_bytes_mut(&mut self) -> &mut [u8];

    // zero and ones, truthy constants
    fn vzero(&mut self);
    fn vones(&mut self);
    fn vis_zero(&self) -> bool;

    // copy
    fn vcopy(&mut self, b: &Self);

    // to/from other integer types for convenience
    fn vfrom_u32(&mut self, a: u32);
    fn vto_u32(&self) -> u32;
    fn vtry_to_u32(&self) -> Option<u32>;
    fn vfrom_i32(&mut self, a: i32);
    fn vfrom_i16(&mut self, a: i16);

    unsafe fn vas<T>(a: &T) -> &Self
    where
        T: VType + ?Sized
    {
        Self::vref(a.vraw_bytes())
    }

    unsafe fn vas_mut<T>(a: &mut T) -> &mut Self
    where
        T: VType + ?Sized
    {
        Self::vref_mut(a.vraw_bytes_mut())
    }

    // little-endian byte access
    fn vget_byte(&self, i: usize) -> Option<&u8>;
    fn vget_byte_mut(&mut self, i: usize) -> Option<&mut u8>;

    fn vbyte(&self, i: usize) -> &u8 {
        self.vget_byte(i).unwrap()
    }

    fn vbyte_mut(&mut self, i: usize) -> &mut u8 {
        self.vget_byte_mut(i).unwrap()
    }

    // to/from little-endian
    fn vfrom_le(&mut self, a: &Self);
    fn vto_le(&mut self, a: &Self);

    fn vfrom_le_bytes(&mut self, a: &[u8]) {
        for i in 0..self.vsize() {
            *self.vbyte_mut(i) = a[i];
        }
    }

    fn vto_le_bytes(d: &mut [u8], a: &Self) {
        for i in 0..d.len() {
            d[i] = *a.vbyte(i);
        }
    }

    // extract/replace
    fn vextract<T>(&mut self, a: &T, i: usize) -> bool
    where
        T: VType + ?Sized
    {
        if i*self.vsize() < a.vsize() {
            for j in 0..self.vsize() {
                *self.vbyte_mut(j) = *a.vbyte(i*self.vsize() + j);
            }
            true
        } else {
            false
        }
    }

    fn vreplace<T>(&mut self, a: &T, i: usize) -> bool
    where
        T: VType + ?Sized
    {
        if i*a.vsize() < self.vsize() {
            for j in 0..a.vsize() {
                *self.vbyte_mut(i*a.vsize() + j) = *a.vbyte(j);
            }
            true
        } else {
            false
        }
    }

    // common conversion operations
    fn vextend_u<T>(&mut self, a: &T, lnpw2: u8)
    where
        T: VType + ?Sized
    {
        let from_lane_size = a.vsize() >> lnpw2;
        let to_lane_size = self.vsize() >> lnpw2;

        self.vzero();

        for i in 0 .. 1 << lnpw2 {
            for j in 0..from_lane_size {
                *self.vbyte_mut(i*to_lane_size+j) = *a.vbyte(i*from_lane_size+j);
            }
        }
    }

    fn vextend_s<T>(&mut self, a: &T, lnpw2: u8)
    where
        T: VType + ?Sized
    {
        let from_lane_size = a.vsize() >> lnpw2;
        let to_lane_size = self.vsize() >> lnpw2;

        for i in 0 .. 1 << lnpw2 {
            for j in 0..from_lane_size {
                *self.vbyte_mut(i*to_lane_size+j) = *a.vbyte(i*from_lane_size+j);
            }

            let sign = if a.vbyte(i*from_lane_size+from_lane_size-1) & 0x80 == 0x80 {
                0xff
            } else {
                0x00
            };
            for j in from_lane_size..to_lane_size {
                *self.vbyte_mut(i*to_lane_size+j) = sign;
            }
        }
    }

    fn vtruncate<T>(&mut self, a: &T, lnpw2: u8)
    where
        T: VType + ?Sized
    {
        let from_lane_size = a.vsize() >> lnpw2;
        let to_lane_size = self.vsize() >> lnpw2;

        for i in 0 .. 1 << lnpw2 {
            for j in 0..to_lane_size {
                *self.vbyte_mut(i*to_lane_size+j) = *a.vbyte(i*from_lane_size+j);
            }
        }
    }

    fn vsplat<T>(&mut self, a: &T)
    where
        T: VType + ?Sized
    {
        for i in 0 .. self.vsize()/a.vsize() {
            for j in 0..a.vsize() {
                *self.vbyte_mut(i*a.vsize() + j) = *a.vbyte(j);
            }
        }
    }

    // vm operations
    fn veq(&self, b: &Self) -> bool;
    fn vne(&self, b: &Self) -> bool;
    fn vlt_u(&self, b: &Self) -> bool;
    fn vlt_s(&self, b: &Self) -> bool;
    fn vgt_u(&self, b: &Self) -> bool;
    fn vgt_s(&self, b: &Self) -> bool;
    fn vle_u(&self, b: &Self) -> bool;
    fn vle_s(&self, b: &Self) -> bool;
    fn vge_u(&self, b: &Self) -> bool;
    fn vge_s(&self, b: &Self) -> bool;

    fn veq_i16(&self, b: i16) -> bool;
    fn vne_i16(&self, b: i16) -> bool;
    fn vlt_u_i16(&self, b: i16) -> bool;
    fn vlt_s_i16(&self, b: i16) -> bool;
    fn vgt_u_i16(&self, b: i16) -> bool;
    fn vgt_s_i16(&self, b: i16) -> bool;
    fn vle_u_i16(&self, b: i16) -> bool;
    fn vle_s_i16(&self, b: i16) -> bool;
    fn vge_u_i16(&self, b: i16) -> bool;
    fn vge_s_i16(&self, b: i16) -> bool;

    fn vmin_u(&mut self, a: &Self, b: &Self);
    fn vmin_s(&mut self, a: &Self, b: &Self);
    fn vmax_u(&mut self, a: &Self, b: &Self);
    fn vmax_s(&mut self, a: &Self, b: &Self);

    fn vmin_u_i16(&mut self, a: &Self, b: i16);
    fn vmin_s_i16(&mut self, a: &Self, b: i16);
    fn vmax_u_i16(&mut self, a: &Self, b: i16);
    fn vmax_s_i16(&mut self, a: &Self, b: i16);

    fn vneg(&mut self, a: &Self);
    fn vabs(&mut self, a: &Self);
    fn vnot(&mut self, a: &Self);
    fn vclz(&mut self, a: &Self);
    fn vctz(&mut self, a: &Self);
    fn vpopcnt(&mut self, a: &Self);

    fn vadd(&mut self, a: &Self, b: &Self);
    fn vsub(&mut self, a: &Self, b: &Self);
    fn vmul(&mut self, a: &Self, b: &Self);
    fn vand(&mut self, a: &Self, b: &Self);
    fn vandnot(&mut self, a: &Self, b: &Self);
    fn vor(&mut self, a: &Self, b: &Self);
    fn vxor(&mut self, a: &Self, b: &Self);
    fn vshl(&mut self, a: &Self, b: &Self);
    fn vshr_u(&mut self, a: &Self, b: &Self);
    fn vshr_s(&mut self, a: &Self, b: &Self);
    fn vrotl(&mut self, a: &Self, b: &Self);
    fn vrotr(&mut self, a: &Self, b: &Self);

    fn vadd_i16(&mut self, a: &Self, b: i16);
    fn vsub_i16(&mut self, a: &Self, b: i16);
    fn vmul_i16(&mut self, a: &Self, b: i16);
    fn vand_i16(&mut self, a: &Self, b: i16);
    fn vandnot_i16(&mut self, a: &Self, b: i16);
    fn vor_i16(&mut self, a: &Self, b: i16);
    fn vxor_i16(&mut self, a: &Self, b: i16);
    fn vshl_i16(&mut self, a: &Self, b: i16);
    fn vshr_u_i16(&mut self, a: &Self, b: i16);
    fn vshr_s_i16(&mut self, a: &Self, b: i16);
    fn vrotl_i16(&mut self, a: &Self, b: i16);
    fn vrotr_i16(&mut self, a: &Self, b: i16);

    // multi-lane operations
    //
    // note, no garauntee is made about the order of these functions
    //
    // also note, this only works because the underlying types have the same
    // native byte layout
    fn xmap<T, F>(&mut self, a: &Self, lnpw2: u8, mut f: F)
    where
        F: FnMut(&mut T, &T),
        T: VType + ?Sized
    {
        let lane_size = self.vsize() >> lnpw2;
        let bytes   = self.vraw_bytes_mut();
        let a_bytes = a.vraw_bytes();
        for i in 0 .. 1 << lnpw2 {
            let slice   = &mut bytes[i*lane_size .. (i+1)*lane_size];
            let a_slice = &a_bytes[i*lane_size .. (i+1)*lane_size];
            unsafe { f(T::vref_mut(slice), T::vref(a_slice)) };
        }
    }

    fn xmap2<T, F>(&mut self, a: &Self, b: &Self, lnpw2: u8, mut f: F)
    where
        F: FnMut(&mut T, &T, &T),
        T: VType + ?Sized
    {
        let lane_size = self.vsize() >> lnpw2;
        let bytes   = self.vraw_bytes_mut();
        let a_bytes = a.vraw_bytes();
        let b_bytes = b.vraw_bytes();
        for i in 0 .. 1 << lnpw2 {
            let slice   = &mut bytes[i*lane_size .. (i+1)*lane_size];
            let a_slice = &a_bytes[i*lane_size .. (i+1)*lane_size];
            let b_slice = &b_bytes[i*lane_size .. (i+1)*lane_size];
            unsafe { f(T::vref_mut(slice), T::vref(a_slice), T::vref(b_slice)) };
        }
    }

    fn xmap3<T, F>(&mut self, a: &Self, b: &Self, c: &Self, lnpw2: u8, mut f: F)
    where
        F: FnMut(&mut T, &T, &T, &T),
        T: VType + ?Sized
    {
        let lane_size = self.vsize() >> lnpw2;
        let bytes   = self.vraw_bytes_mut();
        let a_bytes = a.vraw_bytes();
        let b_bytes = b.vraw_bytes();
        let c_bytes = c.vraw_bytes();
        for i in 0 .. 1 << lnpw2 {
            let slice   = &mut bytes[i*lane_size .. (i+1)*lane_size];
            let a_slice = &a_bytes[i*lane_size .. (i+1)*lane_size];
            let b_slice = &b_bytes[i*lane_size .. (i+1)*lane_size];
            let c_slice = &c_bytes[i*lane_size .. (i+1)*lane_size];
            unsafe { f(T::vref_mut(slice), T::vref(a_slice), T::vref(b_slice), T::vref(c_slice)) };
        }
    }

    fn xfilter<T, F>(&mut self, a: &Self, lnpw2: u8, mut f: F)
    where
        F: FnMut(&T) -> bool,
        T: VType + ?Sized
    {
        self.xmap(a, lnpw2, |d, x| {
            if f(x) {
                T::vones(d)
            } else {
                T::vzero(d)
            }
        })
    }

    fn xfilter2<T, F>(&mut self, a: &Self, b: &Self, lnpw2: u8, mut f: F)
    where
        F: FnMut(&T, &T) -> bool,
        T: VType + ?Sized
    {
        self.xmap2(a, b, lnpw2, |d, x, y| {
            if f(x, y) {
                T::vones(d)
            } else {
                T::vzero(d)
            }
        })
    }

    fn xfilter3<T, F>(&mut self, a: &Self, b: &Self, c: &Self, lnpw2: u8, mut f: F)
    where
        F: FnMut(&T, &T, &T) -> bool,
        T: VType + ?Sized
    {
        self.xmap3(a, b, c, lnpw2, |d, x, y, z| {
            if f(x, y, z) {
                T::vones(d)
            } else {
                T::vzero(d)
            }
        })
    }
}

engine_for_short_t! {
    impl VType for __prim_t {
        fn vsize(&self) -> usize {
            __size
        }

        unsafe fn vref(a: &[u8]) -> &Self {
            &*(a.as_ptr() as *const Self)
        }

        unsafe fn vref_mut(a: &mut [u8]) -> &mut Self {
            &mut *(a.as_mut_ptr() as *mut Self)
        }

        fn vraw_bytes(&self) -> &[u8] {
            unsafe { &*(self as *const __prim_t as *const [u8; __size]) }
        }

        fn vraw_bytes_mut(&mut self) -> &mut [u8] {
            unsafe { &mut *(self as *mut __prim_t as *mut [u8; __size]) }
        }

        fn vzero(&mut self) {
            *self = 0;
        }

        fn vones(&mut self) {
            *self = __prim_t::MAX;
        }

        fn vis_zero(&self) -> bool {
            *self == 0
        }

        fn vcopy(&mut self, b: &Self) {
            *self = *b;
        }

        fn vfrom_u32(&mut self, a: u32) {
            *self = a as Self;
        }

        fn vfrom_i32(&mut self, a: i32) {
            *self = a as Self;
        }

        fn vfrom_i16(&mut self, a: i16) {
            *self = a as Self;
        }

        fn vto_u32(&self) -> u32 {
            *self as u32
        }

        fn vtry_to_u32(&self) -> Option<u32> {
            u32::try_from(*self).ok()
        }

        #[cfg(target_endian="little")]
        fn vget_byte(&self, i: usize) -> Option<&u8> {
            self.vraw_bytes().get(i)
        }

        #[cfg(target_endian="big")]
        fn vget_byte(&self, i: usize) -> Option<&u8> {
            self.vraw_bytes().get(self.vsize()-1 - i)
        }

        #[cfg(target_endian="little")]
        fn vget_byte_mut(&mut self, i: usize) -> Option<&mut u8> {
            self.vraw_bytes_mut().get_mut(i)
        }

        #[cfg(target_endian="big")]
        fn vget_byte_mut(&mut self, i: usize) -> Option<&mut u8> {
            self.vraw_bytes_mut().get_mut(self.vsize()-1 - i)
        }

        fn vfrom_le(&mut self, a: &Self) {
            *self = Self::from_le(*a);
        }

        fn vto_le(&mut self, a: &Self) {
            *self = a.to_le();
        }

        fn veq(&self, b: &Self) -> bool {
            *self == *b
        }

        fn vne(&self, b: &Self) -> bool {
            *self != *b
        }

        fn vlt_u(&self, b: &Self) -> bool {
            *self < *b
        }

        fn vlt_s(&self, b: &Self) -> bool {
            (*self as __primi_t) < (*b as __primi_t)
        }

        fn vgt_u(&self, b: &Self) -> bool {
            *self > *b
        }

        fn vgt_s(&self, b: &Self) -> bool {
            (*self as __primi_t) > (*b as __primi_t)
        }

        fn vle_u(&self, b: &Self) -> bool {
            *self <= *b
        }

        fn vle_s(&self, b: &Self) -> bool {
            (*self as __primi_t) <= (*b as __primi_t)
        }

        fn vge_u(&self, b: &Self) -> bool {
            *self >= *b
        }

        fn vge_s(&self, b: &Self) -> bool {
            (*self as __primi_t) >= (*b as __primi_t)
        }

        fn veq_i16(&self, b: i16) -> bool {
            *self == b as Self
        }

        fn vne_i16(&self, b: i16) -> bool {
            *self != b as Self
        }

        fn vlt_u_i16(&self, b: i16) -> bool {
            *self < b as Self
        }

        fn vlt_s_i16(&self, b: i16) -> bool {
            (*self as __primi_t) < (b as __primi_t)
        }

        fn vgt_u_i16(&self, b: i16) -> bool {
            *self > b as Self
        }

        fn vgt_s_i16(&self, b: i16) -> bool {
            (*self as __primi_t) > (b as __primi_t)
        }

        fn vle_u_i16(&self, b: i16) -> bool {
            *self <= b as Self
        }

        fn vle_s_i16(&self, b: i16) -> bool {
            (*self as __primi_t) <= (b as __primi_t)
        }

        fn vge_u_i16(&self, b: i16) -> bool {
            *self >= b as Self
        }

        fn vge_s_i16(&self, b: i16) -> bool {
            (*self as __primi_t) >= (b as __primi_t)
        }

        fn vmin_u(&mut self, a: &Self, b: &Self) {
            *self = min(*a, *b);
        }

        fn vmin_s(&mut self, a: &Self, b: &Self) {
            *self = min(*a as __primi_t, *b as __primi_t) as __prim_t;
        }

        fn vmax_u(&mut self, a: &Self, b: &Self) {
            *self = max(*a, *b)
        }

        fn vmax_s(&mut self, a: &Self, b: &Self) {
            *self = max(*a as __primi_t, *b as __primi_t) as __prim_t
        }

        fn vmin_u_i16(&mut self, a: &Self, b: i16) {
            *self = min(*a, b as Self);
        }

        fn vmin_s_i16(&mut self, a: &Self, b: i16) {
            *self = min(*a as __primi_t, b as __primi_t) as __prim_t;
        }

        fn vmax_u_i16(&mut self, a: &Self, b: i16) {
            *self = max(*a, b as Self)
        }

        fn vmax_s_i16(&mut self, a: &Self, b: i16) {
            *self = max(*a as __primi_t, b as __primi_t) as __prim_t
        }

        fn vneg(&mut self, a: &Self) {
            *self = (-(*a as __primi_t)) as __prim_t;
        }

        fn vabs(&mut self, a: &Self) {
            *self = (*a as __primi_t).abs() as __prim_t;
        }

        fn vnot(&mut self, a: &Self) {
            *self = !*a;
        }

        fn vclz(&mut self, a: &Self) {
            *self = a.leading_zeros() as __prim_t;
        }

        fn vctz(&mut self, a: &Self) {
            *self = a.trailing_zeros() as __prim_t;
        }

        fn vpopcnt(&mut self, a: &Self) {
            *self = a.count_ones() as __prim_t;
        }

        fn vadd(&mut self, a: &Self, b: &Self) {
            *self = a.wrapping_add(*b);
        }

        fn vsub(&mut self, a: &Self, b: &Self) {
            *self = a.wrapping_sub(*b);
        }

        fn vmul(&mut self, a: &Self, b: &Self) {
            *self = a.wrapping_mul(*b);
        }

        fn vand(&mut self, a: &Self, b: &Self) {
            *self = *a & *b;
        }

        fn vandnot(&mut self, a: &Self, b: &Self) {
            *self = *a & !*b;
        }

        fn vor(&mut self, a: &Self, b: &Self) {
            *self = *a | *b;
        }

        fn vxor(&mut self, a: &Self, b: &Self) {
            *self = *a ^ *b;
        }

        fn vshl(&mut self, a: &Self, b: &Self) {
            *self = a.wrapping_shl(*b as u32);
        }

        fn vshr_u(&mut self, a: &Self, b: &Self) {
            *self = a.wrapping_shr(*b as u32);
        }

        fn vshr_s(&mut self, a: &Self, b: &Self) {
            *self = (*a as __primi_t).wrapping_shr(*b as u32) as __prim_t;
        }

        fn vrotl(&mut self, a: &Self, b: &Self) {
            *self = a.rotate_left(*b as u32);
        }

        fn vrotr(&mut self, a: &Self, b: &Self) {
            *self = a.rotate_right(*b as u32);
        }

        fn vadd_i16(&mut self, a: &Self, b: i16) {
            *self = a.wrapping_add(b as Self);
        }

        fn vsub_i16(&mut self, a: &Self, b: i16) {
            *self = a.wrapping_sub(b as Self);
        }

        fn vmul_i16(&mut self, a: &Self, b: i16) {
            *self = a.wrapping_mul(b as Self);
        }

        fn vand_i16(&mut self, a: &Self, b: i16) {
            *self = *a & (b as Self);
        }

        fn vandnot_i16(&mut self, a: &Self, b: i16) {
            *self = *a & !(b as Self);
        }

        fn vor_i16(&mut self, a: &Self, b: i16) {
            *self = *a | (b as Self);
        }

        fn vxor_i16(&mut self, a: &Self, b: i16) {
            *self = *a ^ (b as Self);
        }

        fn vshl_i16(&mut self, a: &Self, b: i16) {
            *self = a.wrapping_shl(b as u32);
        }

        fn vshr_u_i16(&mut self, a: &Self, b: i16) {
            *self = a.wrapping_shr(b as u32);
        }

        fn vshr_s_i16(&mut self, a: &Self, b: i16) {
            *self = (*a as __primi_t).wrapping_shr(b as u32) as __prim_t;
        }

        fn vrotl_i16(&mut self, a: &Self, b: i16) {
            *self = a.rotate_left(b as u32);
        }

        fn vrotr_i16(&mut self, a: &Self, b: i16) {
            *self = a.rotate_right(b as u32);
        }
    }
}

impl VType for [__limb_t] {
    fn vsize(&self) -> usize {
        self.len() * __limb_size
    }

    unsafe fn vref(a: &[u8]) -> &Self {
        slice::from_raw_parts(
            a.as_ptr() as *const __limb_t,
            a.len() / __limb_size
        )
    }

    unsafe fn vref_mut(a: &mut [u8]) -> &mut Self {
        slice::from_raw_parts_mut(
            a.as_mut_ptr() as *mut __limb_t,
            a.len() / __limb_size
        )
    }

    fn vraw_bytes(&self) -> &[u8] {
        unsafe {
            slice::from_raw_parts(
                self.as_ptr() as *const u8,
                self.len() * __limb_size
            )
        }
    }

    fn vraw_bytes_mut(&mut self) -> &mut [u8] {
        unsafe {
            slice::from_raw_parts_mut(
                self.as_mut_ptr() as *mut u8,
                self.len() * __limb_size
            )
        }
    }

    fn vzero(&mut self) {
        for i in 0..self.len() {
            self[i] = 0;
        }
    }

    fn vones(&mut self) {
        for i in 0..self.len() {
            self[i] = __limb_t::MAX;
        }
    }

    fn vis_zero(&self) -> bool {
        let mut is_zero = true;
        for i in 0..self.len() {
            is_zero = is_zero && self[i] == 0
        }

        is_zero
    }

    fn vcopy(&mut self, b: &Self) {
        for i in 0..self.len() {
            self[i] = b[i];
        }
    }

    fn vfrom_u32(&mut self, a: u32) {
        self[0] = __limb_t::from(a);
        for i in 1..self.len() {
            self[i] = 0;
        }
    }

    fn vto_u32(&self) -> u32 {
        self[0] as u32
    }

    fn vtry_to_u32(&self) -> Option<u32> {
        let mut is_zero = true;
        for i in 1..self.len() {
            is_zero = is_zero && self[i] == 0;
        }

        if is_zero {
            u32::try_from(self[0]).ok()
        } else {
            None
        }
    }

    fn vfrom_i32(&mut self, a: i32) {
        self[0] = a as __limb_t;
        for i in 1..self.len() {
            self[i] = if a < 0 { __limb_t::MAX } else { 0 };
        }
    }

    fn vfrom_i16(&mut self, a: i16) {
        self.vfrom_i32(a as i32);
    }

    fn vget_byte(&self, i: usize) -> Option<&u8> {
        self.get(i / __limb_size).and_then(|x| x.vget_byte(i % __limb_size))
    }

    fn vget_byte_mut(&mut self, i: usize) -> Option<&mut u8> {
        self.get_mut(i / __limb_size).and_then(|x| x.vget_byte_mut(i % __limb_size))
    }

    fn vfrom_le(&mut self, a: &Self) {
        for i in 0..self.len() {
            self[i] = __limb_t::from_le(a[i]);
        }
    }

    fn vto_le(&mut self, a: &Self) {
        for i in 0..self.len() {
            self[i] = a[i].to_le();
        }

    }

    fn veq(&self, b: &Self) -> bool {
        let mut eq = true;
        for i in 0..self.len() {
            eq = eq && self[i] == b[i];
        }
        eq
    }

    fn vne(&self, b: &Self) -> bool {
        let mut ne = false;
        for i in 0..self.len() {
            ne = ne || self[i] != b[i];
        }
        ne
    }

    fn vlt_u(&self, b: &Self) -> bool {
        let mut lt = false;
        for i in 0..self.len() {
            lt = match self[i].cmp(&b[i]) {
                Ordering::Less    => true,
                Ordering::Greater => false,
                Ordering::Equal   => lt,
            }
        }
        lt
    }

    fn vlt_s(&self, b: &Self) -> bool {
        let lt = self.vlt_u(b);
        // the only difference from lt_u is when sign-bits mismatch
        match ((self[self.len()-1] as __limbi_t) < 0, (b[self.len()-1] as __limbi_t) < 0) {
            (true, false) => true,
            (false, true) => false,
            _             => lt
        }
    }

    fn vgt_u(&self, b: &Self) -> bool {
        let mut gt = false;
        for i in 0..self.len() {
            gt = match self[i].cmp(&b[i]) {
                Ordering::Less    => false,
                Ordering::Greater => true,
                Ordering::Equal   => gt,
            }
        }
        gt
    }

    fn vgt_s(&self, b: &Self) -> bool {
        let gt = self.vgt_u(b);
        // the only difference from gt_u is when sign-bits mismatch
        match ((self[self.len()-1] as __limbi_t) < 0, (b[self.len()-1] as __limbi_t) < 0) {
            (true, false) => false,
            (false, true) => true,
            _             => gt
        }
    }

    fn vle_u(&self, b: &Self) -> bool {
        !self.vgt_u(b)
    }

    fn vle_s(&self, b: &Self) -> bool {
        !self.vgt_s(b)
    }

    fn vge_u(&self, b: &Self) -> bool {
        !self.vlt_u(b)
    }

    fn vge_s(&self, b: &Self) -> bool {
        !self.vlt_s(b)
    }

    fn veq_i16(&self, b: i16) -> bool {
        let mut eq = true;
        for i in 0..self.len() {
            eq = eq && self[i] == if i == 0 {
                b as __limb_t
            } else if b < 0 {
                __limb_t::MAX
            } else {
                0
            }
        }
        eq
    }

    fn vne_i16(&self, b: i16) -> bool {
        let mut ne = false;
        for i in 0..self.len() {
            ne = ne || self[i] != if i == 0 {
                b as __limb_t
            } else if b < 0 {
                __limb_t::MAX
            } else {
                0
            }
        }
        ne
    }

    fn vlt_u_i16(&self, b: i16) -> bool {
        let mut lt = false;
        for i in 0..self.len() {
            lt = match self[i].cmp(&if i == 0 {
                b as __limb_t
            } else if b < 0 {
                __limb_t::MAX
            } else {
                0
            }) {
                Ordering::Less    => true,
                Ordering::Greater => false,
                Ordering::Equal   => lt,
            }
        }
        lt
    }

    fn vlt_s_i16(&self, b: i16) -> bool {
        let lt = self.vlt_u_i16(b);
        // the only difference from lt_u is when sign-bits mismatch
        match ((self[self.len()-1] as __limbi_t) < 0, b < 0) {
            (true, false) => true,
            (false, true) => false,
            _             => lt
        }
    }

    fn vgt_u_i16(&self, b: i16) -> bool {
        let mut gt = false;
        for i in 0..self.len() {
            gt = match self[i].cmp(&if i == 0 {
                b as __limb_t
            } else if b < 0 {
                __limb_t::MAX
            } else {
                0
            }) {
                Ordering::Less    => false,
                Ordering::Greater => true,
                Ordering::Equal   => gt,
            }
        }
        gt
    }

    fn vgt_s_i16(&self, b: i16) -> bool {
        let gt = self.vgt_u_i16(b);
        // the only difference from gt_u is when sign-bits mismatch
        match ((self[self.len()-1] as __limbi_t) < 0, b < 0) {
            (true, false) => false,
            (false, true) => true,
            _             => gt
        }
    }

    fn vle_u_i16(&self, b: i16) -> bool {
        !self.vgt_u_i16(b)
    }

    fn vle_s_i16(&self, b: i16) -> bool {
        !self.vgt_s_i16(b)
    }

    fn vge_u_i16(&self, b: i16) -> bool {
        !self.vlt_u_i16(b)
    }

    fn vge_s_i16(&self, b: i16) -> bool {
        !self.vlt_s_i16(b)
    }

    fn vmin_u(&mut self, a: &Self, b: &Self) {
        if a.vlt_u(b) {
            self.copy_from_slice(a);
        } else {
            self.copy_from_slice(b);
        }
    }

    fn vmin_s(&mut self, a: &Self, b: &Self) {
        if a.vlt_s(b) {
            self.copy_from_slice(a);
        } else {
            self.copy_from_slice(b);
        }
    }

    fn vmax_u(&mut self, a: &Self, b: &Self) {
        if a.vgt_u(b) {
            self.copy_from_slice(a);
        } else {
            self.copy_from_slice(b);
        }
    }

    fn vmax_s(&mut self, a: &Self, b: &Self) {
        if a.vgt_s(b) {
            self.copy_from_slice(a);
        } else {
            self.copy_from_slice(b);
        }
    }

    fn vmin_u_i16(&mut self, a: &Self, b: i16) {
        if a.vlt_u_i16(b) {
            self.copy_from_slice(a);
        } else {
            self.vfrom_i16(b);
        }
    }

    fn vmin_s_i16(&mut self, a: &Self, b: i16) {
        if a.vlt_s_i16(b) {
            self.copy_from_slice(a);
        } else {
            self.vfrom_i16(b);
        }
    }

    fn vmax_u_i16(&mut self, a: &Self, b: i16) {
        if a.vgt_u_i16(b) {
            self.copy_from_slice(a);
        } else {
            self.vfrom_i16(b);
        }
    }

    fn vmax_s_i16(&mut self, a: &Self, b: i16) {
        if a.vgt_s_i16(b) {
            self.copy_from_slice(a);
        } else {
            self.vfrom_i16(b);
        }
    }

    fn vneg(&mut self, a: &Self) {
        let mut overflow = false;
        for i in 0..self.len() {
            let (v, o1) = (!a[i]).overflowing_add(if i == 0 { 1 } else { 0 });
            let (v, o2) = v.overflowing_add(__limb_t::from(overflow));
            self[i] = v;
            overflow = o1 || o2;
        }
    }

    fn vabs(&mut self, a: &Self) {
        if (a[a.len()-1] as __limbi_t) < 0 {
            self.vneg(a);
        } else {
            self.copy_from_slice(a);
        }
    }

    fn vnot(&mut self, a: &Self) {
        for i in 0..self.len() {
            self[i] = !a[i];
        }
    }

    fn vclz(&mut self, a: &Self) {
        let mut sum = 0;
        for i in 0..a.len() {
            sum = if a[i] == 0 { sum } else { 0 }
                + a[i].leading_zeros();
        }
        self.vfrom_u32(sum);
    }

    fn vctz(&mut self, a: &Self) {
        let mut sum = 0;
        let mut done = false;
        for i in 0..a.len() {
            sum += if !done { a[i].trailing_zeros() } else { 0 };
            done |= a[i] == 0;
        }
        self.vfrom_u32(sum);
    }

    fn vpopcnt(&mut self, a: &Self) {
        let mut sum = 0;
        for i in 0..a.len() {
            sum += a[i].count_ones();
        }
        self.vfrom_u32(sum);
    }

    fn vadd(&mut self, a: &Self, b: &Self) {
        let mut overflow = false;
        for i in 0..self.len() {
            let res1 = a[i].overflowing_add(b[i]);
            let res2 = res1.0.overflowing_add(__limb_t::from(overflow));
            self[i] = res2.0;
            overflow = res1.1 || res2.1;
        }
    }

    fn vsub(&mut self, a: &Self, b: &Self) {
        let mut overflow = false;
        for i in 0..self.len() {
            let res1 = a[i].overflowing_sub(b[i]);
            let res2 = res1.0.overflowing_sub(__limb_t::from(overflow));
            self[i] = res2.0;
            overflow = res1.1 || res2.1;
        }
    }

    fn vmul(&mut self, a: &Self, b: &Self) {
        // Top-to-bottom long-multiplication to allow in-place multiplication,
        // this was a bit complicated to get right
        //
        // We need to multiply top-to-bottom through both arguments, in case
        // overlap our destination. Fortunately this can just barely be
        // accomplished by multiplying inwards a pair of digits at a time.
        //
        // Most implementations I've seen end up needing an extra log n space
        // to hold the carry during computation, however we can sum the carry
        // directly into the result as we go along. Note that this may have
        // some performance implications I haven't thought about, though it's
        // an open question if the performance cost is higher than the required
        // allocation for additional space
        //
        // The diagram here is very helpful:
        //
        //               x0     y3
        //                 \   /
        //                  \ /
        //                   X
        //           x1     /|\     y2
        //             \   / | \   /
        //              \ /  |  \ /
        //               X   |   X
        //       x2     /|\  |  /|\     y1
        //         \   / | \ | / | \   /
        //          \ /  |  \|/  |  \ /
        //           X   |   X   |   X
        //   x3     /|\  |  /|\  |  /|\     y0
        //     \   / | \ | / | \ | / | \   /
        //      \ /  |  \|/  |  \|/  |  \ /
        //       V   |   X   |   X   |   V
        //       |\  |  /|\  |  /|\  |  /|
        //       | \ | / | \ | / | \ | / |
        //       |  \|/  |  \|/  |  \|/  |
        //       |   V   |   X   |   V   |
        //       |   |\  |  /|\  |  /|   |
        //       |   | \ | / | \ | / |   |
        //       |   |  \|/  |  \|/  |   |
        //       |   |   V   |   V   |   |
        //       |   |   |\  |  /|   |   |
        //       |   |   | \ | / |   |   |
        //       |   |   |  \|/  |   |   |
        //       |   |   |   V   |   |   |
        //       |   |   |   |   |   |   |
        //   n7  n6  n5  n4  n3  n2  n1  n0
        //
        //   https://stackoverflow.com/questions/2755086/multiplication-algorithm-for-abritrary-precision-bignum-integers
        //
        // Though note since we are performing truncated multiplication, we
        // only have to worry about digits <= n3
        //
        // TODO does this need to use pointers to avoid aliases issues?
        //
        for i in (0..self.len()).rev() {
            let mut sum: __limb2_t = 0;
            let mut overflow: __limb_t = 0;

            for j in 0 .. (i+2)/2 {
                // multiply inward 2 digits at a time to avoid overlap with
                // either argument
                let (u, v);
                if i-j != j {
                    let x = <__limb2_t>::from(a[i-j]);
                    let y = <__limb2_t>::from(b[j]);
                    let z = <__limb2_t>::from(b[i-j]);
                    let w = <__limb2_t>::from(a[j]);
                    u = x*y;
                    v = z*w;
                } else {
                    let x = <__limb2_t>::from(a[i-j]);
                    let y = <__limb2_t>::from(b[j]);
                    u = x*y;
                    v = 0;
                }

                // sum, making sure to catch overflow
                //
                // note there can be at most n multiplications for each digit,
                // requiring at most log(n)-bits of overflow in addition to the
                // overflow for each multiplication)
                //
                // since we are already limited to u16::MAX bytes, the maximum
                // number of limbs we will ever multiply comfortably fits
                // in __limb2_t
                let res1 = sum.overflowing_add(u);
                let res2 = res1.0.overflowing_add(v);
                sum = res2.0;
                overflow += <__limb_t>::from(res1.1) + <__limb_t>::from(res2.1);
            }

            // store result
            self[i] = sum as __limb_t;
            let mut overflow
                = (<__limb2_t>::from(overflow) << 8*__limb_size)
                | (sum >> 8*__limb_size);

            // propagate carry
            for k in i+1..self.len() {
                let sum = <__limb2_t>::from(self[k]) + overflow;
                self[k] = sum as __limb_t;
                overflow = sum >> 8*__limb_size;
            }
        }
    }

    fn vand(&mut self, a: &Self, b: &Self) {
        for i in 0..self.len() {
            self[i] = a[i] & b[i];
        }
    }

    fn vandnot(&mut self, a: &Self, b: &Self) {
        for i in 0..self.len() {
            self[i] = a[i] & !b[i];
        }
    }

    fn vor(&mut self, a: &Self, b: &Self) {
        for i in 0..self.len() {
            self[i] = a[i] | b[i];
        }
    }

    fn vxor(&mut self, a: &Self, b: &Self) {
        for i in 0..self.len() {
            self[i] = a[i] ^ b[i];
        }
    }

    fn vshl(&mut self, a: &Self, b: &Self) {
        let b = b.vto_u32() % (8*a.vsize() as u32);
        let width = 8*__limb_size as u32;
        let sh_lo = b % width;
        let sh_hi = (b / width) as usize;

        for i in 0..self.len() {
            self[i]
                = (i.checked_sub(sh_hi)
                    .and_then(|j| a.get(j))
                    .unwrap_or(&0)
                    << sh_lo)
                | (i.checked_sub(sh_hi+1)
                    .and_then(|j| a.get(j))
                    .unwrap_or(&0)
                    .checked_shr(width - sh_lo)
                    .unwrap_or(0));
        }
    }

    fn vshr_u(&mut self, a: &Self, b: &Self) {
        let b = b.vto_u32() % (8*a.vsize() as u32);
        let width = 8*__limb_size as u32;
        let sh_lo = b % width;
        let sh_hi = (b / width) as usize;

        for i in 0..self.len() {
            self[i]
                = (i.checked_add(sh_hi)
                    .and_then(|j| a.get(j))
                    .unwrap_or(&0)
                    >> sh_lo)
                | (i.checked_add(sh_hi+1)
                    .and_then(|j| a.get(j))
                    .unwrap_or(&0)
                    .checked_shl(width - sh_lo)
                    .unwrap_or(0));
        }
    }

    fn vshr_s(&mut self, a: &Self, b: &Self) {
        let b = b.vto_u32() % (8*a.vsize() as u32);
        let width = 8*__limb_size as u32;
        let sh_lo = b % width;
        let sh_hi = (b / width) as usize;
        let sign = if (a[a.len()-1] as __limbi_t) < 0 { 0 } else { __limb_t::MAX };

        for i in 0..self.len() {
            self[i]
                = (((*i.checked_add(sh_hi)
                    .and_then(|j| a.get(j))
                    .unwrap_or(&sign)
                    as __limbi_t) >> sh_lo) as __limb_t)
                | (i.checked_add(sh_hi+1)
                    .and_then(|j| a.get(j))
                    .unwrap_or(&sign)
                    .checked_shl(width - sh_lo)
                    .unwrap_or(0));
        }
    }

    fn vrotl(&mut self, a: &Self, b: &Self) {
        let b = b.vto_u32() % (8*a.vsize() as u32);
        let width = 8*__limb_size as u32;
        let sh_lo = b % width;
        let sh_hi = (b / width) as usize;

        for i in 0..self.len() {
            self[i]
                = (a[i.wrapping_sub(sh_hi  ) % a.len()]
                    << sh_lo)
                | (a[i.wrapping_sub(sh_hi+1) % a.len()]
                    .checked_shr(width - sh_lo).unwrap_or(0));
        }
    }

    fn vrotr(&mut self, a: &Self, b: &Self) {
        let b = b.vto_u32() % (8*a.vsize() as u32);
        let width = 8*__limb_size as u32;
        let sh_lo = b % width;
        let sh_hi = (b / width) as usize;

        for i in 0..self.len() {
            self[i]
                = (a[i.wrapping_add(sh_hi) % a.len()]
                    >> sh_lo)
                | (a[i.wrapping_add(sh_hi+1) % a.len()]
                    .checked_shl(width - sh_lo).unwrap_or(0));
        }
    }

    fn vadd_i16(&mut self, a: &Self, b: i16) {
        let mut overflow = false;
        for i in 0..self.len() {
            let res1 = a[i].overflowing_add(
                if i == 0 {
                    b as __limb_t
                } else if b < 0 {
                    __limb_t::MAX
                } else {
                    0
                }
            );
            let res2 = res1.0.overflowing_add(__limb_t::from(overflow));
            self[i] = res2.0;
            overflow = res1.1 || res2.1;
        }
    }

    fn vsub_i16(&mut self, a: &Self, b: i16) {
        let mut overflow = false;
        for i in 0..self.len() {
            let res1 = a[i].overflowing_sub(
                if i == 0 {
                    b as __limb_t
                } else if b < 0 {
                    __limb_t::MAX
                } else {
                    0
                }
            );
            let res2 = res1.0.overflowing_sub(__limb_t::from(overflow));
            self[i] = res2.0;
            overflow = res1.1 || res2.1;
        }
    }

    fn vmul_i16(&mut self, a: &Self, b: i16) {
        // Note this is the same as vmul, just modified to operate on an i16,
        // see above for an explanation of this algorithm
        for i in (0..self.len()).rev() {
            let mut sum: __limb2_t = 0;
            let mut overflow: __limb_t = 0;

            for j in 0 .. (i+2)/2 {
                // multiply inward 2 digits at a time to avoid overlap with
                // either argument
                let (u, v);
                if i-j != j {
                    let x = <__limb2_t>::from(a[i-j]);
                    let y = <__limb2_t>::from(
                        if j == 0 {
                            b as __limb_t
                        } else if b < 0 {
                            __limb_t::MAX
                        } else {
                            0
                        }
                    );
                    let z = <__limb2_t>::from(
                        if i-j == 0 {
                            b as __limb_t
                        } else if b < 0 {
                            __limb_t::MAX
                        } else {
                            0
                        }
                    );
                    let w = <__limb2_t>::from(a[j]);
                    u = x*y;
                    v = z*w;
                } else {
                    let x = <__limb2_t>::from(a[i-j]);
                    let y = <__limb2_t>::from(
                        if j == 0 {
                            b as __limb_t
                        } else if b < 0 {
                            __limb_t::MAX
                        } else {
                            0
                        }
                    );
                    u = x*y;
                    v = 0;
                }

                // sum, making sure to catch overflow
                //
                // note there can be at most n multiplications for each digit,
                // requiring at most log(n)-bits of overflow (in addition to the
                // overflow for each multiplication)
                //
                // since we are already limited to u16::MAX bytes, the maximum
                // number of limbs we will ever multiply comfortably fits
                // in __limb2_t
                let res1 = sum.overflowing_add(u);
                let res2 = res1.0.overflowing_add(v);
                sum = res2.0;
                overflow += <__limb_t>::from(res1.1) + <__limb_t>::from(res2.1);
            }

            // store result
            self[i] = sum as __limb_t;
            let mut overflow
                = (<__limb2_t>::from(overflow) << 8*__limb_size)
                | (sum >> 8*__limb_size);

            // propagate carry
            for k in i+1..self.len() {
                let sum = <__limb2_t>::from(self[k]) + overflow;
                self[k] = sum as __limb_t;
                overflow = sum >> 8*__limb_size;
            }
        }
    }

    fn vand_i16(&mut self, a: &Self, b: i16) {
        for i in 0..self.len() {
            self[i] = a[i] & if i == 0 {
                b as __limb_t
            } else if b < 0 {
                __limb_t::MAX
            } else {
                0
            }
        }
    }

    fn vandnot_i16(&mut self, a: &Self, b: i16) {
        for i in 0..self.len() {
            self[i] = a[i] & !if i == 0 {
                b as __limb_t
            } else if b < 0 {
                __limb_t::MAX
            } else {
                0
            }
        }
    }

    fn vor_i16(&mut self, a: &Self, b: i16) {
        for i in 0..self.len() {
            self[i] = a[i] | if i == 0 {
                b as __limb_t
            } else if b < 0 {
                __limb_t::MAX
            } else {
                0
            }
        }
    }

    fn vxor_i16(&mut self, a: &Self, b: i16) {
        for i in 0..self.len() {
            self[i] = a[i] ^ if i == 0 {
                b as __limb_t
            } else if b < 0 {
                __limb_t::MAX
            } else {
                0
            }
        }
    }

    fn vshl_i16(&mut self, a: &Self, b: i16) {
        let b = b as u32 % (8*a.vsize() as u32);
        let width = 8*__limb_size as u32;
        let sh_lo = b % width;
        let sh_hi = (b / width) as usize;

        for i in 0..self.len() {
            self[i]
                = (i.checked_sub(sh_hi)
                    .and_then(|j| a.get(j))
                    .unwrap_or(&0)
                    << sh_lo)
                | (i.checked_sub(sh_hi+1)
                    .and_then(|j| a.get(j))
                    .unwrap_or(&0)
                    .checked_shr(width - sh_lo)
                    .unwrap_or(0));
        }
    }

    fn vshr_u_i16(&mut self, a: &Self, b: i16) {
        let b = b as u32 % (8*a.vsize() as u32);
        let width = 8*__limb_size as u32;
        let sh_lo = b % width;
        let sh_hi = (b / width) as usize;

        for i in 0..self.len() {
            self[i]
                = (i.checked_add(sh_hi)
                    .and_then(|j| a.get(j))
                    .unwrap_or(&0)
                    >> sh_lo)
                | (i.checked_add(sh_hi+1)
                    .and_then(|j| a.get(j))
                    .unwrap_or(&0)
                    .checked_shl(width - sh_lo)
                    .unwrap_or(0));
        }
    }

    fn vshr_s_i16(&mut self, a: &Self, b: i16) {
        let b = b as u32 % (8*a.vsize() as u32);
        let width = 8*__limb_size as u32;
        let sh_lo = b % width;
        let sh_hi = (b / width) as usize;
        let sign = if (a[a.len()-1] as __limbi_t) < 0 { 0 } else { __limb_t::MAX };

        for i in 0..self.len() {
            self[i]
                = (((*i.checked_add(sh_hi)
                    .and_then(|j| a.get(j))
                    .unwrap_or(&sign)
                    as __limbi_t) >> sh_lo) as __limb_t)
                | (i.checked_add(sh_hi+1)
                    .and_then(|j| a.get(j))
                    .unwrap_or(&sign)
                    .checked_shl(width - sh_lo)
                    .unwrap_or(0));
        }
    }

    fn vrotl_i16(&mut self, a: &Self, b: i16) {
        let b = b as u32 % (8*a.vsize() as u32);
        let width = 8*__limb_size as u32;
        let sh_lo = b % width;
        let sh_hi = (b / width) as usize;

        for i in 0..self.len() {
            self[i]
                = (a[i.wrapping_sub(sh_hi  ) % a.len()]
                    << sh_lo)
                | (a[i.wrapping_sub(sh_hi+1) % a.len()]
                    .checked_shr(width - sh_lo).unwrap_or(0));
        }
    }

    fn vrotr_i16(&mut self, a: &Self, b: i16) {
        let b = b as u32 % (8*a.vsize() as u32);
        let width = 8*__limb_size as u32;
        let sh_lo = b % width;
        let sh_hi = (b / width) as usize;

        for i in 0..self.len() {
            self[i]
                = (a[i.wrapping_add(sh_hi) % a.len()]
                    >> sh_lo)
                | (a[i.wrapping_add(sh_hi+1) % a.len()]
                    .checked_shl(width - sh_lo).unwrap_or(0));
        }
    }
}


/// Wrapper for handling different type access to state
#[derive(Debug)]
struct State<'a> {
    state: &'a mut [u8],
    align: usize,

    scratch: Vec<__limb_t>,
}

impl<'a> From<&'a mut [u8]> for State<'a> {
    fn from(state: &mut [u8]) -> State {
        // find max alignment here
        let align = 1 << (state.as_ptr() as usize).trailing_zeros();

        State {
            state: state,
            align: align,
            // start with one so short_scratch never allocates
            scratch: vec![0],
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
    // register accessors
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

    // lazily allocated scratch space when needed
    fn short_scratch<'a, T: 'a>(&'a mut self) -> &'a mut T {
        unsafe { &mut *(self.scratch.as_mut_ptr() as *mut T) }
    }

    fn long_scratch<'a>(&'a mut self, npw2: u8) -> &'a mut [__limb_t] {
        let size = 1 << npw2;
        debug_assert!(size > __limb_size);
        let limbs = size / __limb_size;
        if limbs > self.scratch.len() {
            self.scratch.resize(limbs, 0);
        }

        &mut self.scratch[..limbs]
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
    let mut s = UnsafeCell::new(State::from(state));

    #[cfg(feature="debug-trace")]
    {
        println!("trace:");
    }

    // core loop
    let ret_npw2 = loop {
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
            for i in 0..s.get_mut().state.len() {
                print!(" {:02x}", s.get_mut().state[i]);
            }
            println!();
        }

        let npw2  = ((ins & 0xf000000000000000) >> 60) as u8;
        let lnpw2 = ((ins & 0x0f00000000000000) >> 56) as u8;
        let op    = ((ins & 0x00ff000000000000) >> 48) as u8;
        let d     = ((ins & 0x0000ffff00000000) >> 32) as u16;
        let a     = ((ins & 0x00000000ffff0000) >> 16) as u16;
        let b     = ((ins & 0x000000000000ffff) >>  0) as u16;
        let c     = ((ins & 0x000000000000ffff) >>  0) as i16;
        let ab    = ((ins & 0x00000000ffffffff) >>  0) as i32;

        // engine_match sort of breaks macro hygiene, this was much easier than
        // proper scoping and engine_match is really only intended to be used here
        //
        engine_match! {
            //// arg/ret instructions ////

            // arg (convert to ne)
            0x01 => {
                __rd.vfrom_le(__ra);
            }

            // ret (convert from ne and exit)
            0x02 => {
                __rd.vto_le(__ra);
                break npw2;
            }


            //// conversion instructions ////

            // extend_u
            0x03 => {
                __rx.vextend_u(__la, b as u8);
                __rd.vcopy(__rx);
            }

            // extend_s
            0x04 => {
                __rx.vextend_s(__la, b as u8);
                __rd.vcopy(__rx);
            }

            // truncate
            0x05 => {
                __lx.vtruncate(__ra, b as u8);
                __ld.vcopy(__lx);
            }

            // splat
            0x06 => {
                __rd.vsplat(__la);
            }

            // splat_c
            0x07 => {
                // small const encoded in low 32-bits of instruction
                // sign extend and splat
                __rd_0.vfrom_i32(ab);
                __rd.vsplat(__rd_0);
            }

            // splat_long_c
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
                let bytes = __rd_0.vraw_bytes_mut();
                for i in 0..words {
                    let word = unsafe { *pc };
                    pc = unsafe { pc.add(1) };
                    bytes[i*8..(i+1)*8].copy_from_slice(&word.to_le_bytes());
                }
                // sign extend
                let sign = if bytes[8*words-1] & 0x80 == 0x80 { 0xff } else { 0x00 };
                bytes[8*words..].fill(sign);

                // splat
                __rd_0.vfrom_le_bytes(bytes);
                __rd.vsplat(__rd_0);
            }


            //// special instructions ////

            // extract (le)
            0x09 => {
                if !__ld.vextract(__ra, usize::from(b)) {
                    Err(Error::InvalidOpcode(ins))?;
                }
            }

            // replace (le)
            0x0a => {
                if !__rd.vreplace(__la, usize::from(b)) {
                    Err(Error::InvalidOpcode(ins))?;
                }
            }

            // select
            0x0b => {
                __rx.xmap3::<__lane_t, _>(__rd, __ra, __rb, lnpw2, |lx, ld, la, lb| {
                    if !lb.vis_zero() {
                        lx.vcopy(la)
                    } else {
                        lx.vcopy(ld)
                    }
                });
                __rd.vcopy(__rx);
            }

            // shuffle
            0x0c => {
                // this is intentionally O(n^2), as this is what would be required
                // for software-based constant-time. Though it's likely the compiler
                // is smart enough to elide all of this...
                __rx.vzero();
                let ra = __ra;
                let rd = __rd;
                __rx.xmap::<__lane_t, _>(__rb, lnpw2, |lx, lb| {
                    let i = lb.vtry_to_u32().unwrap_or(u32::MAX) as usize;
                    for j in 0 .. 1 << lnpw2 {
                        if i == j {
                            lx.vextract(ra, j);
                        } else if i == j+(1 << lnpw2) {
                            lx.vextract(rd, j);
                        }
                    }
                });
                __rd.vcopy(__rx);
            }


            //// comparison instructions ////

            // eq
            0x0d => {
                __rd.xfilter2::<__lane_t, _>(__ra, __rb, lnpw2, |la, lb| la.veq(lb));
            }

            // eq_c
            0x0e => {
                __rd.xfilter::<__lane_t, _>(__ra, lnpw2, |la| la.veq_i16(c));
            }

            // ne
            0x0f => {
                __rd.xfilter2::<__lane_t, _>(__ra, __rb, lnpw2, |la, lb| la.vne(lb));
            }

            // ne_c
            0x10 => {
                __rd.xfilter::<__lane_t, _>(__ra, lnpw2, |la| la.vne_i16(c));
            }

            // lt_u
            0x11 => {
                __rd.xfilter2::<__lane_t, _>(__ra, __rb, lnpw2, |la, lb| la.vlt_u(lb));
            }

            // lt_u_c
            0x12 => {
                __rd.xfilter::<__lane_t, _>(__ra, lnpw2, |la| la.vlt_u_i16(c));
            }

            // lt_s
            0x13 => {
                __rd.xfilter2::<__lane_t, _>(__ra, __rb, lnpw2, |la, lb| la.vlt_s(lb));
            }

            // lt_s_c
            0x14 => {
                __rd.xfilter::<__lane_t, _>(__ra, lnpw2, |la| la.vlt_s_i16(c));
            }

            // gt_u
            0x15 => {
                __rd.xfilter2::<__lane_t, _>(__ra, __rb, lnpw2, |la, lb| la.vgt_u(lb));
            }

            // gt_u_c
            0x16 => {
                __rd.xfilter::<__lane_t, _>(__ra, lnpw2, |la| la.vgt_u_i16(c));
            }

            // gt_s
            0x17 => {
                __rd.xfilter2::<__lane_t, _>(__ra, __rb, lnpw2, |la, lb| la.vgt_s(lb));
            }

            // gt_s_c
            0x18 => {
                __rd.xfilter::<__lane_t, _>(__ra, lnpw2, |la| la.vgt_s_i16(c));
            }

            // le_u
            0x19 => {
                __rd.xfilter2::<__lane_t, _>(__ra, __rb, lnpw2, |la, lb| la.vle_u(lb));
            }

            // le_u_c
            0x1a => {
                __rd.xfilter::<__lane_t, _>(__ra, lnpw2, |la| la.vle_u_i16(c));
            }

            // le_s
            0x1b => {
                __rd.xfilter2::<__lane_t, _>(__ra, __rb, lnpw2, |la, lb| la.vle_s(lb));
            }

            // le_s_c
            0x1c => {
                __rd.xfilter::<__lane_t, _>(__ra, lnpw2, |la| la.vle_s_i16(c));
            }

            // ge_u
            0x1d => {
                __rd.xfilter2::<__lane_t, _>(__ra, __rb, lnpw2, |la, lb| la.vge_u(lb));
            }

            // ge_u_c
            0x1e => {
                __rd.xfilter::<__lane_t, _>(__ra, lnpw2, |la| la.vge_u_i16(c));
            }

            // ge_s
            0x1f => {
                __rd.xfilter2::<__lane_t, _>(__ra, __rb, lnpw2, |la, lb| la.vge_s(lb));
            }

            // ge_s_c
            0x20 => {
                __rd.xfilter::<__lane_t, _>(__ra, lnpw2, |la| la.vge_s_i16(c));
            }

            // min_u
            0x21 => {
                __rd.xmap2::<__lane_t, _>(__ra, __rb, lnpw2, |lx, la, lb| lx.vmin_u(la, lb));
            }

            // min_u_c
            0x22 => {
                __rd.xmap::<__lane_t, _>(__ra, lnpw2, |lx, la| lx.vmin_u_i16(la, c));
            }

            // min_s
            0x23 => {
                __rd.xmap2::<__lane_t, _>(__ra, __rb, lnpw2, |lx, la, lb| lx.vmin_s(la, lb));
            }

            // min_s_c
            0x24 => {
                __rd.xmap::<__lane_t, _>(__ra, lnpw2, |lx, la| lx.vmin_s_i16(la, c));
            }

            // max_u
            0x25 => {
                __rd.xmap2::<__lane_t, _>(__ra, __rb, lnpw2, |lx, la, lb| lx.vmax_u(la, lb));
            }

            // max_u_c
            0x26 => {
                __rd.xmap::<__lane_t, _>(__ra, lnpw2, |lx, la| lx.vmax_u_i16(la, c));
            }

            // max_s
            0x27 => {
                __rd.xmap2::<__lane_t, _>(__ra, __rb, lnpw2, |lx, la, lb| lx.vmax_s(la, lb));
            }

            // max_s_c
            0x28 => {
                __rd.xmap::<__lane_t, _>(__ra, lnpw2, |lx, la| lx.vmax_s_i16(la, c));
            }


            //// integer instructions ////

            // neg
            0x29 => {
                __rd.xmap::<__lane_t, _>(__ra, lnpw2, |lx, la| lx.vneg(la));
            }

            // abs
            0x2a => {
                __rd.xmap::<__lane_t, _>(__ra, lnpw2, |lx, la| lx.vabs(la));
            }

            // not
            0x2b => {
                __rd.xmap::<__lane_t, _>(__ra, lnpw2, |lx, la| lx.vnot(la));
            }

            // clz
            0x2c => {
                __rd.xmap::<__lane_t, _>(__ra, lnpw2, |lx, la| lx.vclz(la));
            }

            // ctz
            0x2d => {
                __rd.xmap::<__lane_t, _>(__ra, lnpw2, |lx, la| lx.vctz(la));
            }

            // popcnt
            0x2e => {
                __rd.xmap::<__lane_t, _>(__ra, lnpw2, |lx, la| lx.vpopcnt(la));
            }

            // add
            0x2f => {
                __rd.xmap2::<__lane_t, _>(__ra, __rb, lnpw2, |lx, la, lb| lx.vadd(la, lb));
            }

            // add_c
            0x30 => {
                __rd.xmap::<__lane_t, _>(__ra, lnpw2, |lx, la| lx.vadd_i16(la, c));
            }

            // sub
            0x31 => {
                __rd.xmap2::<__lane_t, _>(__ra, __rb, lnpw2, |lx, la, lb| lx.vsub(la, lb));
            }

            // sub_c
            0x32 => {
                __rd.xmap::<__lane_t, _>(__ra, lnpw2, |lx, la| lx.vsub_i16(la, c));
            }

            // mul
            0x33 => {
                __rd.xmap2::<__lane_t, _>(__ra, __rb, lnpw2, |lx, la, lb| lx.vmul(la, lb));
            }

            // mul_c
            0x34 => {
                __rd.xmap::<__lane_t, _>(__ra, lnpw2, |lx, la| lx.vmul_i16(la, c));
            }

            // and
            0x35 => {
                __rd.vand(__ra, __rb);
            }

            // and_c
            0x36 => {
                __rd.xmap::<__lane_t, _>(__ra, lnpw2, |lx, la| lx.vand_i16(la, c));
            }

            // andnot
            0x37 => {
                __rd.vandnot(__ra, __rb);
            }

            // andnot_c
            0x38 => {
                __rd.xmap::<__lane_t, _>(__ra, lnpw2, |lx, la| lx.vandnot_i16(la, c));
            }

            // or
            0x39 => {
                __rd.vor(__ra, __rb);
            }

            // or_c
            0x3a => {
                __rd.xmap::<__lane_t, _>(__ra, lnpw2, |lx, la| lx.vor_i16(la, c));
            }

            // xor
            0x3b => {
                __rd.vxor(__ra, __rb);
            }

            // xor_c
            0x3c => {
                __rd.xmap::<__lane_t, _>(__ra, lnpw2, |lx, la| lx.vxor_i16(la, c));
            }

            // shl
            0x3d => {
                __rx.xmap2::<__lane_t, _>(__ra, __rb, lnpw2, |lx, la, lb| lx.vshl(la, lb));
                __rd.vcopy(__rx);
            }

            // shl_c
            0x3e => {
                __rx.xmap::<__lane_t, _>(__ra, lnpw2, |lx, la| lx.vshl_i16(la, c));
                __rd.vcopy(__rx);
            }

            // shr_u
            0x3f => {
                __rx.xmap2::<__lane_t, _>(__ra, __rb, lnpw2, |lx, la, lb| lx.vshr_u(la, lb));
                __rd.vcopy(__rx);
            }

            // shr_u_c
            0x40 => {
                __rx.xmap::<__lane_t, _>(__ra, lnpw2, |lx, la| lx.vshr_u_i16(la, c));
                __rd.vcopy(__rx);
            }

            // shr_s
            0x41 => {
                __rx.xmap2::<__lane_t, _>(__ra, __rb, lnpw2, |lx, la, lb| lx.vshr_s(la, lb));
                __rd.vcopy(__rx);
            }

            // shr_s_c
            0x42 => {
                __rx.xmap::<__lane_t, _>(__ra, lnpw2, |lx, la| lx.vshr_s_i16(la, c));
                __rd.vcopy(__rx);
            }

            // rotl
            0x43 => {
                __rx.xmap2::<__lane_t, _>(__ra, __rb, lnpw2, |lx, la, lb| lx.vrotl(la, lb));
                __rd.vcopy(__rx);
            }

            // rotl_c
            0x44 => {
                __rx.xmap::<__lane_t, _>(__ra, lnpw2, |lx, la| lx.vrotl_i16(la, c));
                __rd.vcopy(__rx);
            }

            // rotr
            0x45 => {
                __rx.xmap2::<__lane_t, _>(__ra, __rb, lnpw2, |lx, la, lb| lx.vrotr(la, lb));
                __rd.vcopy(__rx);
            }

            // rotr_c
            0x46 => {
                __rx.xmap::<__lane_t, _>(__ra, lnpw2, |lx, la| lx.vrotr_i16(la, c));
                __rd.vcopy(__rx);
            }
        }
    };

    // zero memory outside of register to avoid leaking info
    let ret_size = 1 << ret_npw2;
    s.get_mut().state.get_mut(ret_size..).ok_or(Error::OutOfBounds)?.fill(0x00);
    s.get_mut().scratch.fill(0);

    #[cfg(feature="debug-trace")]
    {
        println!("result:");
        print!("    0x");
        for i in (0..ret_size).rev() {
            print!("{:02x}", s.get_mut().state.get(i).ok_or(Error::OutOfBounds)?);
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
    s.into_inner().state.get(..ret_size).ok_or(Error::OutOfBounds)
}


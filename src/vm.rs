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

#[cfg(feature="debug-trace")]
use crate::opcode::Op;
#[cfg(feature="debug-trace")]
use crate::opcode::OpIns_;


//// utility traits/functions ////
pub trait LoadStore: Sized {
    fn load(arr: &[u8], i: usize) -> Result<Self, Error>;
    fn store(arr: &mut [u8], i: usize, v: Self) -> Result<(), Error>;
    unsafe fn load_unchecked(arr: &[u8], i: usize) -> Self;
    unsafe fn store_unchecked(arr: &mut [u8], i: usize, v: Self);

    #[inline]
    fn pop(arr: &[u8], sp: &mut usize) -> Result<Self, Error> {
        let v = Self::load(arr, *sp)?;
        *sp = sp.wrapping_add(size_of::<Self>());
        Ok(v)
    }

    #[inline]
    fn push(arr: &mut [u8], sp: &mut usize, v: Self) -> Result<(), Error> {
        *sp = sp.checked_sub(size_of::<Self>())
            .ok_or_else(|| Error::OutOfBounds)?;
        Self::store(arr, *sp, v)
    }
}

macro_rules! loadstore_impl {
    (u8) => {
        // u8 has a trivial impl
        impl LoadStore for u8 {
            #[inline]
            fn load(arr: &[u8], i: usize) -> Result<Self, Error> {
                let p = arr.get(i).ok_or_else(|| Error::OutOfBounds)?;
                Ok(*p)
            }

            #[inline]
            fn store(arr: &mut [u8], i: usize, v: Self) -> Result<(), Error> {
                let p = arr.get_mut(i).ok_or_else(|| Error::OutOfBounds)?;
                Ok(*p = v)
            }

            #[inline]
            unsafe fn load_unchecked(arr: &[u8], i: usize) -> Self {
                *arr.get_unchecked(i)
            }

            #[inline]
            unsafe fn store_unchecked(arr: &mut [u8], i: usize, v: Self) {
                *arr.get_unchecked_mut(i) = v
            }
        }
    };

    ($t:ty) => {
        impl LoadStore for $t {
            #[inline]
            fn load(arr: &[u8], i: usize) -> Result<Self, Error> {
                let slice = arr.get(i..i+size_of::<$t>())
                    .ok_or_else(|| Error::OutOfBounds)?;

                let ptr = slice.as_ptr();
                if ptr as usize % size_of::<$t>() != 0 {
                    Err(Error::Unaligned)?;
                }

                // as far as I'm aware no function exists to
                // safely read with checked alignment
                let v = unsafe {
                    (
                        ptr as *const [u8; size_of::<$t>()]
                    ).read()
                };
                Ok(Self::from_le_bytes(v))
            }

            #[inline]
            fn store(arr: &mut [u8], i: usize, v: Self) -> Result<(), Error> {
                let slice = arr.get_mut(i..i+size_of::<$t>())
                    .ok_or_else(|| Error::OutOfBounds)?;

                let ptr = slice.as_mut_ptr();
                if ptr as usize % size_of::<$t>() != 0 {
                    Err(Error::Unaligned)?;
                }

                // as far as I'm aware no function exists to
                // safely write with checked alignment
                unsafe {
                    (
                        ptr as *mut [u8; size_of::<$t>()]
                    ).write(Self::to_le_bytes(v))
                };
                Ok(())
            }

            #[inline]
            unsafe fn load_unchecked(arr: &[u8], i: usize) -> Self {
                Self::from_le_bytes(
                    (
                        (
                            arr.get_unchecked(i..i+size_of::<$t>())
                        ).as_ptr() as *const [u8; size_of::<$t>()]
                    ).read()
                )
            }

            #[inline]
            unsafe fn store_unchecked(arr: &mut [u8], i: usize, v: Self) {
                (
                    (
                        arr.get_unchecked_mut(i..i+size_of::<$t>())
                    ).as_mut_ptr() as *mut [u8; size_of::<$t>()]
                ).write(Self::to_le_bytes(v))
            }
        }
    };
}

loadstore_impl! { u8  }
loadstore_impl! { u16 }
loadstore_impl! { u32 }
loadstore_impl! { u64 }


//// instructions here ////

// get
macro_rules! ins_get {
    ($t:ty, $imm:expr, $stack:expr, $sp:expr) => {{
        let v = <$t>::load($stack, $imm as usize * size_of::<$t>())?;
        // align
        $sp &= !(size_of::<$t>() - 1);
        <$t>::push($stack, &mut $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $imm:expr, $stack:expr, $sp:expr) => {{
        let width = 1 << $npw2;
        // align
        $sp &= !(width - 1);
        $sp = $sp.checked_sub($imm as usize * width)
            .ok_or_else(|| Error::OutOfBounds)?;
 
        for i in (0..width).step_by(size_of::<$t>()) {
            let v = <$t>::load($stack, ($imm as usize * width) + i)?;
            <$t>::store($stack, $sp + i, v)?;
        }
    }};
}

// set
macro_rules! ins_set {
    ($t:ty, $imm:expr, $stack:expr, $sp:expr) => {{
        let v = <$t>::load($stack, $sp)?;
        <$t>::store($stack, $imm as usize * size_of::<$t>(), v)?;
    }};
    (>$t:ty, $npw2:expr, $imm:expr, $stack:expr, $sp:expr) => {{
        let _ = ($npw2, $imm);
        todo!()
    }};
}

// truncate
macro_rules! ins_truncate {
    ($t:ty, $op:expr, $imm:expr, $stack:expr, $sp:expr) => {{
        let width = 1usize << ($imm & 0xf);
        if width <= size_of::<$t>() {
            Err(Error::InvalidOpcode($op))?;
        }

        let v = <$t>::load($stack, $sp)?;
        $sp += width - size_of::<$t>();
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $op:expr, $imm:expr, $stack:expr, $sp:expr) => {{
        let _ = ($npw2, $imm);
        todo!()
    }};
}

// extends
macro_rules! ins_extends {
    ($t:ty, $i:ty, $op:expr, $imm:expr, $stack:expr, $sp:expr) => {{
        let width = 1usize << ($imm & 0xf);
        if width <= size_of::<$t>() {
            Err(Error::InvalidOpcode($op))?;
        }

        let v = <$t>::pop($stack, &mut $sp)?;
        // align
        $sp &= !(width - 1);
        $sp = $sp.checked_sub(width)
            .ok_or_else(|| Error::OutOfBounds)?;
        $stack.get_mut($sp+size_of::<$t>() .. $sp+width)
            .ok_or_else(|| Error::OutOfBounds)?
            .fill(if (v as $i) < 0 { 0xff } else { 0x00 });
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $i:ty, $npw2:expr, $op:expr, $imm:expr, $stack:expr, $sp:expr) => {{
        let _ = ($npw2, $imm);
        todo!()
    }};
}

// extendu
macro_rules! ins_extendu {
    ($t:ty, $op:expr, $imm:expr, $stack:expr, $sp:expr) => {{
        let width = 1usize << ($imm & 0xf);
        if width <= size_of::<$t>() {
            Err(Error::InvalidOpcode($op))?;
        }

        let v = <$t>::pop($stack, &mut $sp)?;
        // align
        $sp &= !(width - 1);
        $sp = $sp.checked_sub(width)
            .ok_or_else(|| Error::OutOfBounds)?;
        $stack.get_mut($sp+size_of::<$t>() .. $sp+width)
            .ok_or_else(|| Error::OutOfBounds)?
            .fill(0x00);
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $op:expr, $imm:expr, $stack:expr, $sp:expr) => {{
        let _ = ($npw2, $imm);
        todo!()
    }};
}

// unalign
macro_rules! ins_unalign {
    ($t:ty, $imm:expr, $stack:expr, $sp:expr) => {{
        let v = <$t>::load($stack, $sp)?;
        $sp += $imm as usize * size_of::<$t>();
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $imm:expr, $stack:expr, $sp:expr) => {{
        let _ = ($npw2, $imm);
        todo!()
    }};
}

// return
macro_rules! ins_return {
    ($t:ty, $stack:expr, $sp:expr) => {{
        // check that resulting sp matches return type
        if $stack.len() - $sp != size_of::<$t>() {
            Err(Error::InvalidReturn)?;
        }
        // exit exec
        break;
    }};
    (>$t:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// select
macro_rules! ins_select {
    ($t:ty, $stack:expr, $sp:expr) => {{
        let c = <$t>::pop($stack, &mut $sp)?;
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        let v = if a != 0 { b } else { c };
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// eqz
macro_rules! ins_eqz {
    ($t:ty, $stack:expr, $sp:expr) => {{
        let a = <$t>::load($stack, $sp)?;
        let v = if a == 0 { 1 } else { 0 };
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// eq
macro_rules! ins_eq {
    ($t:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        let v = if a == b { 1 } else { 0 };
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// ne
macro_rules! ins_ne {
    ($t:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        let v = if a != b { 1 } else { 0 };
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// lts
macro_rules! ins_lts {
    ($t:ty, $i:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        let v = if (a as $i) < (b as $i) { 1 } else { 0 };
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $i:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// ltu
macro_rules! ins_ltu {
    ($t:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        let v = if a < b { 1 } else { 0 };
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// gts
macro_rules! ins_gts {
    ($t:ty, $i:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        let v = if (a as $i) > (b as $i) { 1 } else { 0 };
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $i:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// gtu
macro_rules! ins_gtu {
    ($t:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        let v = if a > b { 1 } else { 0 };
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// les
macro_rules! ins_les {
    ($t:ty, $i:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        let v = if (a as $i) <= (b as $i) { 1 } else { 0 };
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $i:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// leu
macro_rules! ins_leu {
    ($t:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        let v = if a <= b { 1 } else { 0 };
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// ges
macro_rules! ins_ges {
    ($t:ty, $i:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        let v = if (a as $i) >= (b as $i) { 1 } else { 0 };
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $i:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// geu
macro_rules! ins_geu {
    ($t:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        let v = if a >= b { 1 } else { 0 };
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// clz
macro_rules! ins_clz {
    ($t:ty, $stack:expr, $sp:expr) => {{
        let a = <$t>::load($stack, $sp)?;
        let v = a.leading_zeros() as $t;
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// ctz
macro_rules! ins_ctz {
    ($t:ty, $stack:expr, $sp:expr) => {{
        let a = <$t>::load($stack, $sp)?;
        let v = a.trailing_zeros() as $t;
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// popcnt
macro_rules! ins_popcnt {
    ($t:ty, $stack:expr, $sp:expr) => {{
        let a = <$t>::load($stack, $sp)?;
        let v = a.count_ones() as $t;
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// add
macro_rules! ins_add {
    ($t:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        let v = a.wrapping_add(b);
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// sub
macro_rules! ins_sub {
    ($t:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        let v = a.wrapping_sub(b);
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// mul
macro_rules! ins_mul {
    ($t:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        let v = a.wrapping_mul(b);
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// divs
macro_rules! ins_divs {
    ($t:ty, $i:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        if b == 0 {
            Err(Error::DivideByZero)?;
        }
        let v = (a as $i).wrapping_div(b as $i) as $t;
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $i:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// divu
macro_rules! ins_divu {
    ($t:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        if b == 0 {
            Err(Error::DivideByZero)?;
        }
        let v = a.wrapping_div(b);
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// rems
macro_rules! ins_rems {
    ($t:ty, $i:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        if b == 0 {
            Err(Error::DivideByZero)?;
        }
        let v = (a as $i).wrapping_rem(b as $i) as $t;
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $i:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// remu
macro_rules! ins_remu {
    ($t:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        if b == 0 {
            Err(Error::DivideByZero)?;
        }
        let v = a.wrapping_rem(b);
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// and
macro_rules! ins_and {
    ($t:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        let v = a & b;
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// or
macro_rules! ins_or {
    ($t:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        let v = a | b;
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// xor
macro_rules! ins_xor {
    ($t:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        let v = a ^ b;
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// shl
macro_rules! ins_shl {
    ($t:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        let v = a.wrapping_shl(b as u32);
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// shrs
macro_rules! ins_shrs {
    ($t:ty, $i:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        let v = (a as $i).wrapping_shr(b as u32) as $t;
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $i:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// shru
macro_rules! ins_shru {
    ($t:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        let v = a.wrapping_shr(b as u32);
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// rotl
macro_rules! ins_rotl {
    ($t:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        let v = a.rotate_left(b as u32);
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}

// rotr
macro_rules! ins_rotr {
    ($t:ty, $stack:expr, $sp:expr) => {{
        let b = <$t>::pop($stack, &mut $sp)?;
        let a = <$t>::load($stack, $sp)?;
        let v = a.rotate_right(b as u32);
        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $stack:expr, $sp:expr) => {{
        let _ = $npw2;
        todo!()
    }};
}


//// VM entry point ////

/// Execute the simple crypto-VM
///
/// NOTE! This is a quick simulated VM for testing and proof-of-concept!
/// Not constant time!
pub fn exec<'a>(
    bytecode: &[u8],
    stack: &'a mut [u8]
) -> Result<&'a [u8], Error> {
    // Setup VM
    if bytecode.as_ptr() as usize % 2 != 0 || bytecode.len() % 2 != 0{
        // bytecode alignment
        Err(Error::Unaligned)?;
    }

    let last = u16::load(bytecode, bytecode.len()-2).unwrap_or(0);
    if (last & 0x0fff) != 0x0f00 {
        // bytecode must end in return
        Err(Error::InvalidReturn)?;
    }

    let mut sp = stack.len();

    // exec loop
    let mut pc = 0;
    loop {
        let op = unsafe { u16::load_unchecked(bytecode, pc) };
        pc += 2;

        #[cfg(feature="debug-trace")]
        {
            match Op::try_from(op) {
                Ok(op) => print!("    {:<16} :", format!("{}", op)),
                _      => print!("    {:<16} :", format!("unknown {:#06x}", op)),
            }
            for i in 0..stack.len() {
                print!("{}{:02x}",
                    if i == sp { '|' } else { ' ' },
                    stack[i]
                );
            }
            println!();
        }

        let npw2   = ((op & 0xf000) >> 12) as u8;
        let opcode = ((op & 0x0f00) >>  8) as u8;
        let imm    = ((op & 0x00ff) >>  0) as u8;

        match (npw2, opcode, imm) {
            // get
            (0,    0x1, imm) => ins_get!(u8,         imm, stack, sp),
            (1,    0x1, imm) => ins_get!(u16,        imm, stack, sp),
            (2,    0x1, imm) => ins_get!(u32,        imm, stack, sp),
            (3,    0x1, imm) => ins_get!(u64,        imm, stack, sp),
            (npw2, 0x1, imm) => ins_get!(>u64, npw2, imm, stack, sp),

            // set
            (0,    0x2, imm) => ins_set!(u8,         imm, stack, sp),
            (1,    0x2, imm) => ins_set!(u16,        imm, stack, sp),
            (2,    0x2, imm) => ins_set!(u32,        imm, stack, sp),
            (3,    0x2, imm) => ins_set!(u64,        imm, stack, sp),
            (npw2, 0x2, imm) => ins_set!(>u64, npw2, imm, stack, sp),

            // truncate
            (0,    0x3, imm) => ins_truncate!(u8,         op, imm, stack, sp),
            (1,    0x3, imm) => ins_truncate!(u16,        op, imm, stack, sp),
            (2,    0x3, imm) => ins_truncate!(u32,        op, imm, stack, sp),
            (3,    0x3, imm) => ins_truncate!(u64,        op, imm, stack, sp),
            (npw2, 0x3, imm) => ins_truncate!(>u64, npw2, op, imm, stack, sp),

            // extends
            (0,    0x4, imm) => ins_extends!(u8,   i8,        op, imm, stack, sp),
            (1,    0x4, imm) => ins_extends!(u16,  i16,       op, imm, stack, sp),
            (2,    0x4, imm) => ins_extends!(u32,  i32,       op, imm, stack, sp),
            (3,    0x4, imm) => ins_extends!(u64,  i64,       op, imm, stack, sp),
            (npw2, 0x4, imm) => ins_extends!(>u64, i64, npw2, op, imm, stack, sp),

            // extendu
            (0,    0x5, imm) => ins_extendu!(u8,         op, imm, stack, sp),
            (1,    0x5, imm) => ins_extendu!(u16,        op, imm, stack, sp),
            (2,    0x5, imm) => ins_extendu!(u32,        op, imm, stack, sp),
            (3,    0x5, imm) => ins_extendu!(u64,        op, imm, stack, sp),
            (npw2, 0x5, imm) => ins_extendu!(>u64, npw2, op, imm, stack, sp),

            // unalign
            (0,    0x6, imm) => ins_unalign!(u8,         imm, stack, sp),
            (1,    0x6, imm) => ins_unalign!(u16,        imm, stack, sp),
            (2,    0x6, imm) => ins_unalign!(u32,        imm, stack, sp),
            (3,    0x6, imm) => ins_unalign!(u64,        imm, stack, sp),
            (npw2, 0x6, imm) => ins_unalign!(>u64, npw2, imm, stack, sp),

            // return
            (0,    0xf, 0x00) => ins_return!(u8,         stack, sp),
            (1,    0xf, 0x00) => ins_return!(u16,        stack, sp),
            (2,    0xf, 0x00) => ins_return!(u32,        stack, sp),
            (3,    0xf, 0x00) => ins_return!(u64,        stack, sp),
            (npw2, 0xf, 0x00) => ins_return!(>u64, npw2, stack, sp),

            // select
            (0,    0xf, 0x01) => ins_select!(u8,         stack, sp),
            (1,    0xf, 0x01) => ins_select!(u16,        stack, sp),
            (2,    0xf, 0x01) => ins_select!(u32,        stack, sp),
            (3,    0xf, 0x01) => ins_select!(u64,        stack, sp),
            (npw2, 0xf, 0x01) => ins_select!(>u64, npw2, stack, sp),

            // eqz
            (0,    0xf, 0x02) => ins_eqz!(u8,         stack, sp),
            (1,    0xf, 0x02) => ins_eqz!(u16,        stack, sp),
            (2,    0xf, 0x02) => ins_eqz!(u32,        stack, sp),
            (3,    0xf, 0x02) => ins_eqz!(u64,        stack, sp),
            (npw2, 0xf, 0x02) => ins_eqz!(>u64, npw2, stack, sp),

            // eq
            (0,    0xf, 0x03) => ins_eq!(u8,         stack, sp),
            (1,    0xf, 0x03) => ins_eq!(u16,        stack, sp),
            (2,    0xf, 0x03) => ins_eq!(u32,        stack, sp),
            (3,    0xf, 0x03) => ins_eq!(u64,        stack, sp),
            (npw2, 0xf, 0x03) => ins_eq!(>u64, npw2, stack, sp),

            // ne
            (0,    0xf, 0x04) => ins_ne!(u8,         stack, sp),
            (1,    0xf, 0x04) => ins_ne!(u16,        stack, sp),
            (2,    0xf, 0x04) => ins_ne!(u32,        stack, sp),
            (3,    0xf, 0x04) => ins_ne!(u64,        stack, sp),
            (npw2, 0xf, 0x04) => ins_ne!(>u64, npw2, stack, sp),

            // lts
            (0,    0xf, 0x05) => ins_lts!(u8,   i8,        stack, sp),
            (1,    0xf, 0x05) => ins_lts!(u16,  i16,       stack, sp),
            (2,    0xf, 0x05) => ins_lts!(u32,  i32,       stack, sp),
            (3,    0xf, 0x05) => ins_lts!(u64,  i64,       stack, sp),
            (npw2, 0xf, 0x05) => ins_lts!(>u64, i64, npw2, stack, sp),

            // ltu
            (0,    0xf, 0x06) => ins_ltu!(u8,         stack, sp),
            (1,    0xf, 0x06) => ins_ltu!(u16,        stack, sp),
            (2,    0xf, 0x06) => ins_ltu!(u32,        stack, sp),
            (3,    0xf, 0x06) => ins_ltu!(u64,        stack, sp),
            (npw2, 0xf, 0x06) => ins_ltu!(>u64, npw2, stack, sp),

            // gts
            (0,    0xf, 0x07) => ins_gts!(u8,   i8,        stack, sp),
            (1,    0xf, 0x07) => ins_gts!(u16,  i16,       stack, sp),
            (2,    0xf, 0x07) => ins_gts!(u32,  i32,       stack, sp),
            (3,    0xf, 0x07) => ins_gts!(u64,  i64,       stack, sp),
            (npw2, 0xf, 0x07) => ins_gts!(>u64, i64, npw2, stack, sp),

            // gtu
            (0,    0xf, 0x08) => ins_gtu!(u8,         stack, sp),
            (1,    0xf, 0x08) => ins_gtu!(u16,        stack, sp),
            (2,    0xf, 0x08) => ins_gtu!(u32,        stack, sp),
            (3,    0xf, 0x08) => ins_gtu!(u64,        stack, sp),
            (npw2, 0xf, 0x08) => ins_gtu!(>u64, npw2, stack, sp),

            // les
            (0,    0xf, 0x09) => ins_les!(u8,   i8,        stack, sp),
            (1,    0xf, 0x09) => ins_les!(u16,  i16,       stack, sp),
            (2,    0xf, 0x09) => ins_les!(u32,  i32,       stack, sp),
            (3,    0xf, 0x09) => ins_les!(u64,  i64,       stack, sp),
            (npw2, 0xf, 0x09) => ins_les!(>u64, i64, npw2, stack, sp),

            // leu
            (0,    0xf, 0x0a) => ins_leu!(u8,         stack, sp),
            (1,    0xf, 0x0a) => ins_leu!(u16,        stack, sp),
            (2,    0xf, 0x0a) => ins_leu!(u32,        stack, sp),
            (3,    0xf, 0x0a) => ins_leu!(u64,        stack, sp),
            (npw2, 0xf, 0x0a) => ins_leu!(>u64, npw2, stack, sp),

            // ges
            (0,    0xf, 0x0b) => ins_ges!(u8,   i8,        stack, sp),
            (1,    0xf, 0x0b) => ins_ges!(u16,  i16,       stack, sp),
            (2,    0xf, 0x0b) => ins_ges!(u32,  i32,       stack, sp),
            (3,    0xf, 0x0b) => ins_ges!(u64,  i64,       stack, sp),
            (npw2, 0xf, 0x0b) => ins_ges!(>u64, i64, npw2, stack, sp),

            // geu
            (0,    0xf, 0x0c) => ins_geu!(u8,         stack, sp),
            (1,    0xf, 0x0c) => ins_geu!(u16,        stack, sp),
            (2,    0xf, 0x0c) => ins_geu!(u32,        stack, sp),
            (3,    0xf, 0x0c) => ins_geu!(u64,        stack, sp),
            (npw2, 0xf, 0x0c) => ins_geu!(>u64, npw2, stack, sp),

            // clz
            (0,    0xf, 0x0d) => ins_clz!(u8,         stack, sp),
            (1,    0xf, 0x0d) => ins_clz!(u16,        stack, sp),
            (2,    0xf, 0x0d) => ins_clz!(u32,        stack, sp),
            (3,    0xf, 0x0d) => ins_clz!(u64,        stack, sp),
            (npw2, 0xf, 0x0d) => ins_clz!(>u64, npw2, stack, sp),

            // ctz
            (0,    0xf, 0x0e) => ins_ctz!(u8,         stack, sp),
            (1,    0xf, 0x0e) => ins_ctz!(u16,        stack, sp),
            (2,    0xf, 0x0e) => ins_ctz!(u32,        stack, sp),
            (3,    0xf, 0x0e) => ins_ctz!(u64,        stack, sp),
            (npw2, 0xf, 0x0e) => ins_ctz!(>u64, npw2, stack, sp),

            // popcnt
            (0,    0xf, 0x0f) => ins_popcnt!(u8,         stack, sp),
            (1,    0xf, 0x0f) => ins_popcnt!(u16,        stack, sp),
            (2,    0xf, 0x0f) => ins_popcnt!(u32,        stack, sp),
            (3,    0xf, 0x0f) => ins_popcnt!(u64,        stack, sp),
            (npw2, 0xf, 0x0f) => ins_popcnt!(>u64, npw2, stack, sp),

            // add
            (0,    0xf, 0x10) => ins_add!(u8,         stack, sp),
            (1,    0xf, 0x10) => ins_add!(u16,        stack, sp),
            (2,    0xf, 0x10) => ins_add!(u32,        stack, sp),
            (3,    0xf, 0x10) => ins_add!(u64,        stack, sp),
            (npw2, 0xf, 0x10) => ins_add!(>u64, npw2, stack, sp),

            // sub
            (0,    0xf, 0x11) => ins_sub!(u8,         stack, sp),
            (1,    0xf, 0x11) => ins_sub!(u16,        stack, sp),
            (2,    0xf, 0x11) => ins_sub!(u32,        stack, sp),
            (3,    0xf, 0x11) => ins_sub!(u64,        stack, sp),
            (npw2, 0xf, 0x11) => ins_sub!(>u64, npw2, stack, sp),

            // mul 
            (0,    0xf, 0x12) => ins_mul!(u8,         stack, sp),
            (1,    0xf, 0x12) => ins_mul!(u16,        stack, sp),
            (2,    0xf, 0x12) => ins_mul!(u32,        stack, sp),
            (3,    0xf, 0x12) => ins_mul!(u64,        stack, sp),
            (npw2, 0xf, 0x12) => ins_mul!(>u64, npw2, stack, sp),

            // divs
            (0,    0xf, 0x13) => ins_divs!(u8,   i8,        stack, sp),
            (1,    0xf, 0x13) => ins_divs!(u16,  i16,       stack, sp),
            (2,    0xf, 0x13) => ins_divs!(u32,  i32,       stack, sp),
            (3,    0xf, 0x13) => ins_divs!(u64,  i64,       stack, sp),
            (npw2, 0xf, 0x13) => ins_divs!(>u64, i64, npw2, stack, sp),

            // divu
            (0,    0xf, 0x14) => ins_divu!(u8,         stack, sp),
            (1,    0xf, 0x14) => ins_divu!(u16,        stack, sp),
            (2,    0xf, 0x14) => ins_divu!(u32,        stack, sp),
            (3,    0xf, 0x14) => ins_divu!(u64,        stack, sp),
            (npw2, 0xf, 0x14) => ins_divu!(>u64, npw2, stack, sp),

            // rems
            (0,    0xf, 0x15) => ins_rems!(u8,   i8,        stack, sp),
            (1,    0xf, 0x15) => ins_rems!(u16,  i16,       stack, sp),
            (2,    0xf, 0x15) => ins_rems!(u32,  i32,       stack, sp),
            (3,    0xf, 0x15) => ins_rems!(u64,  i64,       stack, sp),
            (npw2, 0xf, 0x15) => ins_rems!(>u64, i64, npw2, stack, sp),

            // remu
            (0,    0xf, 0x16) => ins_remu!(u8,         stack, sp),
            (1,    0xf, 0x16) => ins_remu!(u16,        stack, sp),
            (2,    0xf, 0x16) => ins_remu!(u32,        stack, sp),
            (3,    0xf, 0x16) => ins_remu!(u64,        stack, sp),
            (npw2, 0xf, 0x16) => ins_remu!(>u64, npw2, stack, sp),

            // and
            (0,    0xf, 0x17) => ins_and!(u8,         stack, sp),
            (1,    0xf, 0x17) => ins_and!(u16,        stack, sp),
            (2,    0xf, 0x17) => ins_and!(u32,        stack, sp),
            (3,    0xf, 0x17) => ins_and!(u64,        stack, sp),
            (npw2, 0xf, 0x17) => ins_and!(>u64, npw2, stack, sp),

            // or
            (0,    0xf, 0x18) => ins_or!(u8,         stack, sp),
            (1,    0xf, 0x18) => ins_or!(u16,        stack, sp),
            (2,    0xf, 0x18) => ins_or!(u32,        stack, sp),
            (3,    0xf, 0x18) => ins_or!(u64,        stack, sp),
            (npw2, 0xf, 0x18) => ins_or!(>u64, npw2, stack, sp),

            // xor
            (0,    0xf, 0x19) => ins_xor!(u8,         stack, sp),
            (1,    0xf, 0x19) => ins_xor!(u16,        stack, sp),
            (2,    0xf, 0x19) => ins_xor!(u32,        stack, sp),
            (3,    0xf, 0x19) => ins_xor!(u64,        stack, sp),
            (npw2, 0xf, 0x19) => ins_xor!(>u64, npw2, stack, sp),

            // shl
            (0,    0xf, 0x1a) => ins_shl!(u8,         stack, sp),
            (1,    0xf, 0x1a) => ins_shl!(u16,        stack, sp),
            (2,    0xf, 0x1a) => ins_shl!(u32,        stack, sp),
            (3,    0xf, 0x1a) => ins_shl!(u64,        stack, sp),
            (npw2, 0xf, 0x1a) => ins_shl!(>u64, npw2, stack, sp),

            // shrs
            (0,    0xf, 0x1b) => ins_shrs!(u8,   i8,        stack, sp),
            (1,    0xf, 0x1b) => ins_shrs!(u16,  i16,       stack, sp),
            (2,    0xf, 0x1b) => ins_shrs!(u32,  i32,       stack, sp),
            (3,    0xf, 0x1b) => ins_shrs!(u64,  i64,       stack, sp),
            (npw2, 0xf, 0x1b) => ins_shrs!(>u64, i64, npw2, stack, sp),

            // shru
            (0,    0xf, 0x1c) => ins_shru!(u8,         stack, sp),
            (1,    0xf, 0x1c) => ins_shru!(u16,        stack, sp),
            (2,    0xf, 0x1c) => ins_shru!(u32,        stack, sp),
            (3,    0xf, 0x1c) => ins_shru!(u64,        stack, sp),
            (npw2, 0xf, 0x1c) => ins_shru!(>u64, npw2, stack, sp),

            // rotl
            (0,    0xf, 0x1d) => ins_rotl!(u8,         stack, sp),
            (1,    0xf, 0x1d) => ins_rotl!(u16,        stack, sp),
            (2,    0xf, 0x1d) => ins_rotl!(u32,        stack, sp),
            (3,    0xf, 0x1d) => ins_rotl!(u64,        stack, sp),
            (npw2, 0xf, 0x1d) => ins_rotl!(>u64, npw2, stack, sp),

            // rotr
            (0,    0xf, 0x1e) => ins_rotr!(u8,         stack, sp),
            (1,    0xf, 0x1e) => ins_rotr!(u16,        stack, sp),
            (2,    0xf, 0x1e) => ins_rotr!(u32,        stack, sp),
            (3,    0xf, 0x1e) => ins_rotr!(u64,        stack, sp),
            (npw2, 0xf, 0x1e) => ins_rotr!(>u64, npw2, stack, sp),

            // unknown opcode?
            _ => {
                Err(Error::InvalidOpcode(op))?
            }
        }
    }

    // zero memory >sp to avoid leaking anything unnecessary
    stack.get_mut(..sp)
        .ok_or_else(|| Error::OutOfBounds)?
        .fill(0x00);

    // return the rest as our result
    Ok(&stack[sp..])
}


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
    fn extract<T>(self, i: usize) -> Option<T>
    where
        T: Bytes
    {
        let bytes = self.to_le_bytes();
        bytes.as_ref()
            .get(i*size_of::<T>() .. (i+1)*size_of::<T>())
            .map(|slice| {
                T::from_le_bytes(
                    <T as Bytes>::Bytes::try_from(slice).ok().unwrap()
                )
            })
    }

    fn replace<T>(self, i: usize, t: T) -> Option<Self>
    where
        T: Bytes
    {
        let mut bytes = self.to_le_bytes();

        bytes.as_mut()
            .get_mut(i*size_of::<T>() .. (i+1)*size_of::<T>())?
            .copy_from_slice(t.to_le_bytes().as_ref());

        Some(Self::from_le_bytes(bytes))
    }

    // Common conversion operations
    fn extend_u<T>(t: T) -> Self
    where
        T: Bytes,
    {
        let mut bytes = Self::ZERO.to_le_bytes();

        bytes.as_mut()[..size_of::<T>()]
            .copy_from_slice(t.to_le_bytes().as_ref());

        Self::from_le_bytes(bytes)
    }

    fn extend_s<T>(t: T) -> Self
    where
        T: Bytes,
    {
        let t = t.to_le_bytes();
        let mut bytes = if (*t.as_ref().last().unwrap() as i8) < 0 {
            Self::ONES.to_le_bytes()
        } else {
            Self::ZERO.to_le_bytes()
        };

        bytes.as_mut()[..size_of::<T>()]
            .copy_from_slice(t.as_ref());

        Self::from_le_bytes(bytes)
    }

    fn splat<T>(t: T) -> Self
    where
        T: Bytes + Copy,
    {
        let mut bytes = Self::ZERO.to_ne_bytes();

        for i in (0..size_of::<Self>()).step_by(size_of::<T>()) {
            bytes.as_mut()[i..i+size_of::<T>()]
                .copy_from_slice(t.to_ne_bytes().as_ref());
        }

        Self::from_ne_bytes(bytes)
    }
}

macro_rules! bytes_impl {
    ($t:ident => $zero:expr, $ones:expr) => {
        impl Bytes for $t {
            const ONES: Self = $ones;
            const ZERO: Self = $zero;

            type Bytes = [u8; size_of::<$t>()];

            #[inline]
            fn to_ne_bytes(self) -> Self::Bytes {
                <$t>::to_ne_bytes(self)
            }

            #[inline]
            fn from_ne_bytes(bytes: Self::Bytes) -> Self {
                <$t>::from_ne_bytes(bytes)
            }

            #[inline]
            fn to_le_bytes(self) -> Self::Bytes {
                <$t>::to_le_bytes(self)
            }

            #[inline]
            fn from_le_bytes(bytes: Self::Bytes) -> Self {
                <$t>::from_le_bytes(bytes)
            }

            #[inline]
            fn to_le(self) -> Self {
                <$t>::to_le(self)
            }

            #[inline]
            fn from_le(self) -> Self {
                <$t>::from_le(self)
            }
        }
    };
    ([$t:ty; $n:expr] => $ones:expr, $zero:expr) => {
        impl Bytes for [$t;$n] {
            const ONES: Self = $ones;
            const ZERO: Self = $zero;

            type Bytes = [u8; size_of::<[$t;$n]>()];

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
                for i in 0..$n {
                    self[i] = self[i].to_le();
                }
                self
            }

            #[inline]
            fn from_le(mut self) -> Self {
                for i in 0..$n {
                    self[i] = self[i].from_le();
                }
                self
            }
        }
    };
}

bytes_impl! { u8       => u8::MIN,       u8::MAX       }
bytes_impl! { u16      => u16::MIN,      u16::MAX      }
bytes_impl! { u32      => u32::MIN,      u32::MAX      }
bytes_impl! { u64      => u64::MIN,      u64::MAX      }
bytes_impl! { u128     => u128::MIN,     u128::MAX     }
bytes_impl! { [u128;2] => [u128::MIN;2], [u128::MAX;2] }
bytes_impl! { [u128;4] => [u128::MIN;4], [u128::MAX;4] }


/// Helper for converting into indices (usize)
trait IntoUsize {
    /// Cheap cast to usize
    fn wrapping_into_usize(self) -> usize;

    /// Cast to usize with overflow checking
    fn try_into_usize(self) -> Option<usize>;
}

macro_rules! into_usize_impl {
    ($t:ident) => {
        impl IntoUsize for $t {
            fn wrapping_into_usize(self) -> usize {
                self as usize
            }

            fn try_into_usize(self) -> Option<usize> {
                usize::try_from(self).ok()
            }
        }
    };
    ([$t:ty;$n:expr]) => {
        impl IntoUsize for [$t;$n] {
            fn wrapping_into_usize(self) -> usize {
                self[0] as usize
            }

            fn try_into_usize(self) -> Option<usize> {
                if self[1..].iter().all(|x| *x == 0) {
                    usize::try_from(self[0]).ok()
                } else {
                    None
                }
            }
        }
    };
}

into_usize_impl! { u8       }
into_usize_impl! { u16      }
into_usize_impl! { u32      }
into_usize_impl! { u64      }
into_usize_impl! { u128     }
into_usize_impl! { [u128;2] }
into_usize_impl! { [u128;4] }


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

macro_rules! lanes_impl {
    ($u:ty => $t:ty;$n:expr) => {
        impl Lanes<$t> for $u {
            #[inline]
            fn xmap<F: FnMut($t) -> $t>(self, mut f: F) -> Self {
                let mut xs: [$t; $n] = unsafe { transmute(self) };
                for i in 0..$n {
                    xs[i] = f(xs[i]);
                }
                unsafe { transmute(xs) }
            }

            #[inline]
            fn xfilter<F: FnMut($t) -> bool>(self, mut f: F) -> Self {
                let mut xs: [$t; $n] = unsafe { transmute(self) };
                for i in 0..$n {
                    xs[i] = if f(xs[i]) { <$t>::ONES } else { <$t>::ZERO };
                }
                unsafe { transmute(xs) }
            }

            #[inline]
            fn xfold<A, F: FnMut(A, $t) -> A>(self, mut f: F, mut a: A) -> A {
                let xs: [$t; $n] = unsafe { transmute(self) };
                for i in 0..$n {
                    a = f(a, xs[i]);
                }
                a
            }

            #[inline]
            fn xmap2<F: FnMut($t, $t) -> $t>(self, b: $u, mut f: F) -> $u {
                let mut xs: [$t; $n] = unsafe { transmute(self) };
                let     ys: [$t; $n] = unsafe { transmute(b)    };
                for i in 0..$n {
                    xs[i] = f(xs[i], ys[i]);
                }
                unsafe { transmute(xs) }
            }
            #[inline]
            fn xfilter2<F: FnMut($t, $t) -> bool>(self, b: $u, mut f: F) -> $u {
                let mut xs: [$t; $n] = unsafe { transmute(self) };
                let     ys: [$t; $n] = unsafe { transmute(b)    };
                for i in 0..$n {
                    xs[i] = if f(xs[i], ys[i]) { <$t>::ONES } else { <$t>::ZERO };
                }
                unsafe { transmute(xs) }
            }
            #[inline]
            fn xfold2<A, F: FnMut(A, $t, $t) -> A>(self, b: $u, mut f: F, mut a: A) -> A {
                let xs: [$t; $n] = unsafe { transmute(self) };
                let ys: [$t; $n] = unsafe { transmute(b)    };
                for i in 0..$n {
                    a = f(a, xs[i], ys[i]);
                }
                a
            }

            #[inline]
            fn xmap3<F: FnMut($t, $t, $t) -> $t>(self, b: $u, c: $u, mut f: F) -> $u {
                let mut xs: [$t; $n] = unsafe { transmute(self) };
                let     ys: [$t; $n] = unsafe { transmute(b)    };
                let     zs: [$t; $n] = unsafe { transmute(c)    };
                for i in 0..$n {
                    xs[i] = f(xs[i], ys[i], zs[i]);
                }
                unsafe { transmute(xs) }
            }
            #[inline]
            fn xfilter3<F: FnMut($t, $t, $t) -> bool>(self, b: $u, c: $u, mut f: F) -> $u {
                let mut xs: [$t; $n] = unsafe { transmute(self) };
                let     ys: [$t; $n] = unsafe { transmute(b)    };
                let     zs: [$t; $n] = unsafe { transmute(c)    };
                for i in 0..$n {
                    xs[i] = if f(xs[i], ys[i], zs[i]) { <$t>::ONES } else { <$t>::ZERO };
                }
                unsafe { transmute(xs) }
            }
            #[inline]
            fn xfold3<A, F: FnMut(A, $t, $t, $t) -> A>(self, b: $u, c: $u, mut f: F, mut a: A) -> A {
                let xs: [$t; $n] = unsafe { transmute(self) };
                let ys: [$t; $n] = unsafe { transmute(b)    };
                let zs: [$t; $n] = unsafe { transmute(c)    };
                for i in 0..$n {
                    a = f(a, xs[i], ys[i], zs[i]);
                }
                a
            }
        }
    };
    ($u:ty => $t:ty) => {
        impl Lanes<$t> for $u {
            #[inline]
            fn xmap<F: FnMut($t) -> $t>(self, mut f: F) -> Self {
                f(self)
            }

            #[inline]
            fn xfilter<F: FnMut($t) -> bool>(self, mut f: F) -> Self {
                if f(self) { <$t>::ONES } else { <$t>::ZERO }
            }

            #[inline]
            fn xfold<A, F: FnMut(A, $t) -> A>(self, mut f: F, a: A) -> A {
                f(a, self)
            }

            #[inline]
            fn xmap2<F: FnMut($t, $t) -> $t>(self, b: $u, mut f: F) -> Self {
                f(self, b)
            }
            #[inline]
            fn xfilter2<F: FnMut($t, $t) -> bool>(self, b: $u, mut f: F) -> Self {
                if f(self, b) { <$t>::ONES } else { <$t>::ZERO }
            }
            #[inline]
            fn xfold2<A, F: FnMut(A, $t, $t) -> A>(self, b: $u, mut f: F, a: A) -> A {
                f(a, self, b)
            }

            #[inline]
            fn xmap3<F: FnMut($t, $t, $t) -> $t>(self, b: $u, c: $u, mut f: F) -> Self {
                f(self, b, c)
            }
            #[inline]
            fn xfilter3<F: FnMut($t, $t, $t) -> bool>(self, b: $u, c: $u, mut f: F) -> Self {
                if f(self, b, c) { <$t>::ONES } else { <$t>::ZERO }
            }
            #[inline]
            fn xfold3<A, F: FnMut(A, $t, $t, $t) -> A>(self, b: $u, c: $u, mut f: F, a: A) -> A {
                f(a, self, b, c)
            }
        }
    };
}

lanes_impl! { u8 => u8 }

lanes_impl! { u16 => u8;2 }
lanes_impl! { u16 => u16  }

lanes_impl! { u32 => u8;4  }
lanes_impl! { u32 => u16;2 }
lanes_impl! { u32 => u32   }

lanes_impl! { u64 => u8;8  }
lanes_impl! { u64 => u16;4 }
lanes_impl! { u64 => u32;2 }
lanes_impl! { u64 => u64   }

lanes_impl! { u128 => u8;16 }
lanes_impl! { u128 => u16;8 }
lanes_impl! { u128 => u32;4 }
lanes_impl! { u128 => u64;2 }
lanes_impl! { u128 => u128  }

lanes_impl! { [u128;2] => u8;32    }
lanes_impl! { [u128;2] => u16;16   }
lanes_impl! { [u128;2] => u32;8    }
lanes_impl! { [u128;2] => u64;4    }
lanes_impl! { [u128;2] => u128;2   }
lanes_impl! { [u128;2] => [u128;2] }

lanes_impl! { [u128;4] => u8;64      }
lanes_impl! { [u128;4] => u16;32     }
lanes_impl! { [u128;4] => u32;16     }
lanes_impl! { [u128;4] => u64;8      }
lanes_impl! { [u128;4] => u128;4     }
lanes_impl! { [u128;4] => [u128;2];2 }
lanes_impl! { [u128;4] => [u128;4]   }


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

macro_rules! vop_impl {
    ($t:ident{$i:ty}) => {
        impl Vop for $t {
            fn vlt_u(self, b: Self) -> bool {
                self < b
            }

            fn vlt_s(self, b: Self) -> bool {
                (self as $i) < (b as $i)
            }

            fn vgt_u(self, b: Self) -> bool {
                self > b
            }

            fn vgt_s(self, b: Self) -> bool {
                (self as $i) > (b as $i)
            }

            fn vle_u(self, b: Self) -> bool {
                self <= b
            }

            fn vle_s(self, b: Self) -> bool {
                (self as $i) <= (b as $i)
            }

            fn vge_u(self, b: Self) -> bool {
                self >= b
            }

            fn vge_s(self, b: Self) -> bool {
                (self as $i) >= (b as $i)
            }

            fn vmin_u(self, b: Self) -> Self {
                min(self, b)
            }

            fn vmin_s(self, b: Self) -> Self {
                min((self as $i), (b as $i)) as $t
            }

            fn vmax_u(self, b: Self) -> Self {
                max(self, b)
            }

            fn vmax_s(self, b: Self) -> Self {
                max((self as $i), (b as $i)) as $t
            }

            fn vneg(self) -> Self {
                (-(self as $i)) as $t
            }

            fn vabs(self) -> Self {
                (self as $i).abs() as $t
            }

            fn vnot(self) -> Self {
                !self
            }

            fn vclz(self) -> Self {
                self.leading_zeros() as $t
            }

            fn vctz(self) -> Self {
                self.trailing_zeros() as $t
            }

            fn vpopcnt(self) -> Self {
                self.count_ones() as $t
            }

            fn vadd(self, b: Self) -> Self {
                self.wrapping_add(b)
            }

            fn vsub(self, b: Self) -> Self {
                self.wrapping_sub(b)
            }

            fn vmul(self, b: Self) -> Self {
                self.wrapping_mul(b)
            }

            fn vand(self, b: Self) -> Self {
                self & b
            }

            fn vandnot(self, b: Self) -> Self {
                self & !b
            }

            fn vor(self, b: Self) -> Self {
                self | b
            }

            fn vxor(self, b: Self) -> Self {
                self ^ b
            }

            fn vshl(self, b: Self) -> Self {
                self.wrapping_shl(b as u32)
            }

            fn vshr_u(self, b: Self) -> Self {
                self.wrapping_shr(b as u32)
            }

            fn vshr_s(self, b: Self) -> Self {
                (self as $i).wrapping_shr(b as u32) as $t
            }

            fn vrotl(self, b: Self) -> Self {
                self.rotate_left(b as u32)
            }

            fn vrotr(self, b: Self) -> Self {
                self.rotate_right(b as u32)
            }
        }
    };
    ([$t:ty; $n:expr]) => {
        #[allow(unused_variables)]
        impl Vop for [$t;$n] {
            fn vlt_u(self, b: Self) -> bool {
                todo!()
            }

            fn vlt_s(self, b: Self) -> bool {
                todo!()
            }

            fn vgt_u(self, b: Self) -> bool {
                todo!()
            }

            fn vgt_s(self, b: Self) -> bool {
                todo!()
            }

            fn vle_u(self, b: Self) -> bool {
                todo!()
            }

            fn vle_s(self, b: Self) -> bool {
                todo!()
            }

            fn vge_u(self, b: Self) -> bool {
                todo!()
            }

            fn vge_s(self, b: Self) -> bool {
                todo!()
            }

            fn vmin_u(self, b: Self) -> Self {
                todo!()
            }

            fn vmin_s(self, b: Self) -> Self {
                todo!()
            }

            fn vmax_u(self, b: Self) -> Self {
                todo!()
            }

            fn vmax_s(self, b: Self) -> Self {
                todo!()
            }
            fn vneg(self) -> Self {
                todo!()
            }

            fn vabs(self) -> Self {
                todo!()
            }

            fn vnot(self) -> Self {
                todo!()
            }

            fn vclz(self) -> Self {
                todo!()
            }

            fn vctz(self) -> Self {
                todo!()
            }

            fn vpopcnt(self) -> Self {
                todo!()
            }

            fn vadd(self, b: Self) -> Self {
                todo!()
            }

            fn vsub(self, b: Self) -> Self {
                todo!()
            }

            fn vmul(self, b: Self) -> Self {
                todo!()
            }

            fn vand(self, b: Self) -> Self {
                todo!()
            }

            fn vandnot(self, b: Self) -> Self {
                todo!()
            }

            fn vor(self, b: Self) -> Self {
                todo!()
            }

            fn vxor(self, b: Self) -> Self {
                todo!()
            }

            fn vshl(self, b: Self) -> Self {
                todo!()
            }

            fn vshr_u(self, b: Self) -> Self {
                todo!()
            }

            fn vshr_s(self, b: Self) -> Self {
                todo!()
            }

            fn vrotl(self, b: Self) -> Self {
                todo!()
            }

            fn vrotr(self, b: Self) -> Self {
                todo!()
            }
        }
    };
}

vop_impl! { u8{i8}     }
vop_impl! { u16{i16}   }
vop_impl! { u32{i32}   }
vop_impl! { u64{i64}   }
vop_impl! { u128{i128} }
vop_impl! { [u128;2]   }
vop_impl! { [u128;4]   }


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
    fn reg<'a, T: 'a>(&'a self, idx: u8) -> Result<&'a T, Error> {
        self.slice(usize::from(idx))
    }

    fn reg_mut<'a, T: 'a>(&'a mut self, idx: u8) -> Result<&'a mut T, Error> {
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

        // return ret value, consuming our lifetime
        self.state.get(..ret_size).ok_or(Error::OutOfBounds)
    }
}


//// Execution rules go! ////

// I wish there was a better way to build these but oh well

macro_rules! ex {
    //// arg/ret instructions ////

    // arg (convert to ne)
    (|$s:ident| arg $a:ident: $t:ty, $b:ident: $u:ty) => {{
        let _ = transmute::<$t, $u>;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = b.from_le();
    }};

    // ret (convert from ne and exit)
    (|$s:ident| ret $a:ident: $t:ty, $b:ident: $u:ty) => {{
        let _ = transmute::<$t, $u>;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = b.to_le();
        return $s.ret(size_of::<$t>());
    }};

    //// special instructions ////

    // select
    (|$s:ident| select $p:ident, $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let p = $s.reg::<$t>($p)?;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = p.xmap3(*a, *b, |x: $u, y: $u, z: $u| {
            if x != <$u>::ZERO {
                y
            } else {
                z
            }
        });
    }};

    // extract (le)
    (|$s:ident| extract $i:expr, $a:ident: $t:ty, $b:ident: $u:ty) => {{
        let b = $s.reg::<$u>($b)?;
        *$s.reg_mut::<$t>($a)? = b.extract(usize::from($i)).unwrap();
    }};

    // replace (le)
    (|$s:ident| replace $i:expr, $a:ident: $t:ty, $b:ident: $u:ty) => {{
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$u>($b)?;
        *$s.reg_mut::<$t>($a)? = a.replace(usize::from($i), *b).unwrap();
    }};


    //// conversion instructions ////

    // extend_const_u
    (|$s:ident, $bytecode:ident| extend_const_u $a:ident: $t:ty, $pc:ident: $u:ty) => {{
        // align to u32
        const WORDS: usize = (size_of::<$u>()+3) / 4;

        // we need to check the bounds on this
        if unsafe { $bytecode.as_ptr_range().end.offset_from($pc) } < WORDS as isize {
            Err(Error::OutOfBounds)?;
        }

        // load from instruction stream
        let mut bytes = [0u8; 4*WORDS];
        for i in 0..WORDS {
            let word = unsafe { *$pc };
            $pc = unsafe { $pc.add(1) };
            bytes[i*4..(i+1)*4].copy_from_slice(&word.to_le_bytes());
        }
        let b = <$u>::from_le_bytes(
            <[u8;size_of::<$u>()]>::try_from(&bytes[..size_of::<$u>()]).unwrap()
        );

        // cast if needed
        *$s.reg_mut::<$t>($a)? = <$t>::extend_u(b);
    }};

    // extend_const_s
    (|$s:ident, $bytecode:ident| extend_const_s $a:ident: $t:ty, $pc:ident: $u:ty) => {{
        // align to u32
        const WORDS: usize = (size_of::<$u>()+3) / 4;

        // we need to check the bounds on this
        if unsafe { $bytecode.as_ptr_range().end.offset_from($pc) } < WORDS as isize {
            Err(Error::OutOfBounds)?;
        }

        // load from instruction stream
        let mut bytes = [0u8; 4*WORDS];
        for i in 0..WORDS {
            let word = unsafe { *$pc };
            $pc = unsafe { $pc.add(1) };
            bytes[i*4..(i+1)*4].copy_from_slice(&word.to_le_bytes());
        }
        let b = <$u>::from_le_bytes(
            <[u8;size_of::<$u>()]>::try_from(&bytes[..size_of::<$u>()]).unwrap()
        );

        // cast if needed
        *$s.reg_mut::<$t>($a)? = <$t>::extend_s(b);
    }};

    // splat_const
    (|$s:ident, $bytecode:ident| splat_const $a:ident: $t:ty, $pc:ident: $u:ty) => {{
        // align to u32
        const WORDS: usize = (size_of::<$u>()+3) / 4;

        // we need to check the bounds on this
        if unsafe { $bytecode.as_ptr_range().end.offset_from($pc) } < WORDS as isize {
            Err(Error::OutOfBounds)?;
        }

        // load from instruction stream
        let mut bytes = [0u8; 4*WORDS];
        for i in 0..WORDS {
            let word = unsafe { *$pc };
            $pc = unsafe { $pc.add(1) };
            bytes[i*4..(i+1)*4].copy_from_slice(&word.to_le_bytes());
        }
        let b = <$u>::from_le_bytes(
            <[u8;size_of::<$u>()]>::try_from(&bytes[..size_of::<$u>()]).unwrap()
        );

        // cast if needed
        *$s.reg_mut::<$t>($a)? = <$t>::splat(b);
    }};

    // extend_const8_u
    (|$s:ident| extend_const8_u $a:ident: $t:ty, $b:ident) => {{
        *$s.reg_mut::<$t>($a)? = <$t>::extend_u($b);
    }};

    // extend_const8_s
    (|$s:ident| extend_const8_s $a:ident: $t:ty, $b:ident) => {{
        *$s.reg_mut::<$t>($a)? = <$t>::extend_s($b);
    }};

    // splat_const8
    (|$s:ident| splat_const8 $a:ident: $t:ty, $b:ident) => {{
        *$s.reg_mut::<$t>($a)? = <$t>::splat($b);
    }};

    // extend_u
    (|$s:ident| extend_u $a:ident: $t:ty, $b:ident: $u:ty) => {{
        let b = $s.reg::<$u>($b)?;
        *$s.reg_mut::<$t>($a)? = <$t>::extend_u(*b);
    }};

    // extend_s
    (|$s:ident| extend_s $a:ident: $t:ty, $b:ident: $u:ty) => {{
        let b = $s.reg::<$u>($b)?;
        *$s.reg_mut::<$t>($a)? = <$t>::extend_s(*b);
    }};

    // splat
    (|$s:ident| splat $a:ident: $t:ty, $b:ident: $u:ty) => {{
        let b = $s.reg::<$u>($b)?;
        *$s.reg_mut::<$t>($a)? = <$t>::splat(*b);
    }};

    // shuffle
    (|$s:ident| shuffle $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.xmap(|x: $u| {
            match x.try_into_usize().and_then(|i| b.extract(i)) {
                Some(y) => y,
                None    => <$u>::ZERO,
            }
        });
    }};


    //// comparison instructions ////

    // none
    (|$s:ident| none $a:ident: $t:ty, $b:ident: $u:ty) => {{
        let _ = transmute::<$t, $u>;
        let b = $s.reg::<$t>($b)?;
        // note these apply to whole word!
        *$s.reg_mut::<$t>($a)? = b.xfilter(|x: $t| x == <$t>::ZERO);
    }};

    // any
    (|$s:ident| any $a:ident: $t:ty, $b:ident: $u:ty) => {{
        let _ = transmute::<$t, $u>;
        let b = $s.reg::<$t>($b)?;
        // note these apply to whole word!
        *$s.reg_mut::<$t>($a)? = b.xfilter(|x: $t| x != <$t>::ZERO);
    }};

    // all
    (|$s:ident| all $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = b.xfilter(|x: $t| {
            // note the non-shortcutting and here
            x.xfold(|p, x: $u| p & (x != <$u>::ZERO), true)
        });
    }};

    // eq
    (|$s:ident| eq $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.xfilter2(*b, |x: $u, y: $u| x == y);
    }};

    // ne
    (|$s:ident| ne $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.xfilter2(*b, |x: $u, y: $u| x != y);
    }};

    // lt_u
    (|$s:ident| lt_u $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.xfilter2(*b, |x: $u, y: $u| x.vlt_u(y));
    }};

    // lt_s
    (|$s:ident| lt_s $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.xfilter2(*b, |x: $u, y: $u| x.vlt_s(y));
    }};

    // gt_u
    (|$s:ident| gt_u $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.xfilter2(*b, |x: $u, y: $u| x.vgt_u(y));
    }};

    // gt_s
    (|$s:ident| gt_s $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.xfilter2(*b, |x: $u, y: $u| x.vgt_s(y));
    }};

    // le_u
    (|$s:ident| le_u $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.xfilter2(*b, |x: $u, y: $u| x.vle_u(y));
    }};

    // le_s
    (|$s:ident| le_s $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.xfilter2(*b, |x: $u, y: $u| x.vle_s(y));
    }};

    // ge_u
    (|$s:ident| ge_u $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.xfilter2(*b, |x: $u, y: $u| x.vge_u(y));
    }};

    // ge_s
    (|$s:ident| ge_s $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.xfilter2(*b, |x: $u, y: $u| x.vge_s(y));
    }};

    // min_u
    (|$s:ident| min_u $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.xmap2(*b, |x: $u, y: $u| x.vmin_u(y));
    }};

    // min_s
    (|$s:ident| min_s $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.xmap2(*b, |x: $u, y: $u| x.vmin_s(y));
    }};

    // max_u
    (|$s:ident| max_u $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.xmap2(*b, |x: $u, y: $u| x.vmax_u(y));
    }};

    // max_s
    (|$s:ident| max_s $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.xmap2(*b, |x: $u, y: $u| x.vmax_s(y));
    }};


    //// integer instructions ////

    // neg
    (|$s:ident| neg $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = b.xmap(|x: $u| x.vneg());
    }};

    // abs
    (|$s:ident| abs $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = b.xmap(|x: $u| x.vabs());
    }};

    // not
    (|$s:ident| not $a:ident: $t:ty, $b:ident: $u:ty) => {{
        let _ = transmute::<$t, $u>;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = b.vnot();
    }};

    // clz
    (|$s:ident| clz $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = b.xmap(|x: $u| x.vclz());
    }};

    // ctz
    (|$s:ident| ctz $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = b.xmap(|x: $u| x.vctz());
    }};

    // popcnt
    (|$s:ident| popcnt $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = b.xmap(|x: $u| x.vpopcnt());
    }};

    // add
    (|$s:ident| add $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.xmap2(*b, |x: $u, y: $u| x.vadd(y));
    }};

    // sub
    (|$s:ident| sub $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.xmap2(*b, |x: $u, y: $u| x.vsub(y));
    }};

    // mul
    (|$s:ident| mul $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.xmap2(*b, |x: $u, y: $u| x.vmul(y));
    }};

    // and
    (|$s:ident| and $a:ident: $t:ty, $b:ident: $u:ty) => {{
        let _ = transmute::<$t, $u>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.vand(*b);
    }};

    // andnot
    (|$s:ident| andnot $a:ident: $t:ty, $b:ident: $u:ty) => {{
        let _ = transmute::<$t, $u>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.vandnot(*b);
    }};

    // or
    (|$s:ident| or $a:ident: $t:ty, $b:ident: $u:ty) => {{
        let _ = transmute::<$t, $u>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.vor(*b);
    }};

    // xor
    (|$s:ident| xor $a:ident: $t:ty, $b:ident: $u:ty) => {{
        let _ = transmute::<$t, $u>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.vxor(*b);
    }};

    // shl
    (|$s:ident| shl $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.xmap2(*b, |x: $u, y: $u| x.vshl(y));
    }};

    // shr_u
    (|$s:ident| shr_u $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.xmap2(*b, |x: $u, y: $u| x.vshr_u(y));
    }};

    // shr_s
    (|$s:ident| shr_s $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.xmap2(*b, |x: $u, y: $u| x.vshr_s(y));
    }};

    // rotl
    (|$s:ident| rotl $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.xmap2(*b, |x: $u, y: $u| x.vrotl(y));
    }};

    // rotr
    (|$s:ident| rotr $a:ident: $t:ty, $b:ident: $u:ty;$n:expr) => {{
        let _ = transmute::<$t, [$u;$n]>;
        let a = $s.reg::<$t>($a)?;
        let b = $s.reg::<$t>($b)?;
        *$s.reg_mut::<$t>($a)? = a.xmap2(*b, |x: $u, y: $u| x.vrotr(y));
    }};
}



/// Simple non-constant crypto-VM for testing 
///
/// NOTE! This is a quick simulated VM for testing and proof-of-concept!
/// Not constant time!
///
pub fn exec_<'a>(
    bytecode: &[u32],
    state: &'a mut [u8]
) -> Result<&'a [u8], Error> {
    // setup PC, bytecode must end in return, which means we can avoid
    // checking for end-of-code every step
    let mut pc: *const u32 = bytecode.as_ptr();

    let last = bytecode.last().copied().unwrap_or(0);
    if last & 0x03ffff00 != 0x00020000 {
        // bytecode must end in return
        Err(Error::InvalidReturn)?;
    }

    // setup state
    let mut s = State::from(state);

    // core loop
    loop {
        let ins: u32 = unsafe { *pc };
        pc = unsafe { pc.add(1) };

        #[cfg(feature="debug-trace")]
        {
            match OpIns_::try_from(ins) {
                Ok(ins) => print!("    {:<24} :", format!("{}", ins)),
                _       => print!("    {:<24} :", format!("unknown {:#06x}", ins)),
            }
            for i in 0..s.state.len() {
                print!(" {:02x}", s.state[i]);
            }
            println!();
        }

        let npw2  = ((ins & 0xe0000000) >> 29) as u8;
        let lnpw2 = ((ins & 0x1c000000) >> 26) as u8;
        let opc   = ((ins & 0x03ff0000) >> 16) as u16;
        let p     = ((ins & 0x00ff0000) >> 16) as u8;
        let a     = ((ins & 0x0000ff00) >>  8) as u8;
        let b     = ((ins & 0x000000ff) >>  0) as u8;

        match (npw2, lnpw2, opc) {
            //// arg/ret instructions ////

            // arg (convert to ne)
            (0, 0, 0x001) => ex!{|s| arg a: u8,       b: u8       },
            (1, 0, 0x001) => ex!{|s| arg a: u16,      b: u16      },
            (2, 0, 0x001) => ex!{|s| arg a: u32,      b: u32      },
            (3, 0, 0x001) => ex!{|s| arg a: u64,      b: u64      },
            (4, 0, 0x001) => ex!{|s| arg a: u128,     b: u128     },
            (5, 0, 0x001) => ex!{|s| arg a: [u128;2], b: [u128;2] },
            (6, 0, 0x001) => ex!{|s| arg a: [u128;4], b: [u128;4] },

            // ret (convert from ne and exit)
            (0, 0, 0x002) => ex!{|s| ret a: u8,       b: u8       },
            (1, 0, 0x002) => ex!{|s| ret a: u16,      b: u16      },
            (2, 0, 0x002) => ex!{|s| ret a: u32,      b: u32      },
            (3, 0, 0x002) => ex!{|s| ret a: u64,      b: u64      },
            (4, 0, 0x002) => ex!{|s| ret a: u128,     b: u128     },
            (5, 0, 0x002) => ex!{|s| ret a: [u128;2], b: [u128;2] },
            (6, 0, 0x002) => ex!{|s| ret a: [u128;4], b: [u128;4] },


            //// special instructions ////

            // select
            (0, 0, 0x100..=0x1ff) => ex!{|s| select p, a: u8,       b: u8;1       },

            (1, 0, 0x100..=0x1ff) => ex!{|s| select p, a: u16,      b: u16;1      },
            (1, 1, 0x100..=0x1ff) => ex!{|s| select p, a: u16,      b: u8;2       },

            (2, 0, 0x100..=0x1ff) => ex!{|s| select p, a: u32,      b: u32;1      },
            (2, 1, 0x100..=0x1ff) => ex!{|s| select p, a: u32,      b: u16;2      },
            (2, 2, 0x100..=0x1ff) => ex!{|s| select p, a: u32,      b: u8;4       },

            (3, 0, 0x100..=0x1ff) => ex!{|s| select p, a: u64,      b: u64;1      },
            (3, 1, 0x100..=0x1ff) => ex!{|s| select p, a: u64,      b: u32;2      },
            (3, 2, 0x100..=0x1ff) => ex!{|s| select p, a: u64,      b: u16;4      },
            (3, 3, 0x100..=0x1ff) => ex!{|s| select p, a: u64,      b: u8;8       },

            (4, 0, 0x100..=0x1ff) => ex!{|s| select p, a: u128,     b: u128;1     },
            (4, 1, 0x100..=0x1ff) => ex!{|s| select p, a: u128,     b: u64;2      },
            (4, 2, 0x100..=0x1ff) => ex!{|s| select p, a: u128,     b: u32;4      },
            (4, 3, 0x100..=0x1ff) => ex!{|s| select p, a: u128,     b: u16;8      },
            (4, 4, 0x100..=0x1ff) => ex!{|s| select p, a: u128,     b: u8;16      },

            (5, 0, 0x100..=0x1ff) => ex!{|s| select p, a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x100..=0x1ff) => ex!{|s| select p, a: [u128;2], b: u128;2     },
            (5, 2, 0x100..=0x1ff) => ex!{|s| select p, a: [u128;2], b: u64;4      },
            (5, 3, 0x100..=0x1ff) => ex!{|s| select p, a: [u128;2], b: u32;8      },
            (5, 4, 0x100..=0x1ff) => ex!{|s| select p, a: [u128;2], b: u16;16     },
            (5, 5, 0x100..=0x1ff) => ex!{|s| select p, a: [u128;2], b: u8;32      },

            (6, 0, 0x100..=0x1ff) => ex!{|s| select p, a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x100..=0x1ff) => ex!{|s| select p, a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x100..=0x1ff) => ex!{|s| select p, a: [u128;4], b: u128;4     },
            (6, 3, 0x100..=0x1ff) => ex!{|s| select p, a: [u128;4], b: u64;8      },
            (6, 4, 0x100..=0x1ff) => ex!{|s| select p, a: [u128;4], b: u32;16     },
            (6, 5, 0x100..=0x1ff) => ex!{|s| select p, a: [u128;4], b: u16;32     },
            (6, 6, 0x100..=0x1ff) => ex!{|s| select p, a: [u128;4], b: u8;64      },

            // extract
            (0, 0, 0x200..=0x200) => ex!{|s| extract p, a: u8,       b: u8       },

            (1, 0, 0x200..=0x201) => ex!{|s| extract p, a: u16,      b: u16      },
            (1, 1, 0x200..=0x200) => ex!{|s| extract p, a: u8,       b: u16      },

            (2, 0, 0x200..=0x203) => ex!{|s| extract p, a: u32,      b: u32      },
            (2, 1, 0x200..=0x201) => ex!{|s| extract p, a: u16,      b: u32      },
            (2, 2, 0x200..=0x200) => ex!{|s| extract p, a: u8,       b: u32      },

            (3, 0, 0x200..=0x207) => ex!{|s| extract p, a: u64,      b: u64      },
            (3, 1, 0x200..=0x203) => ex!{|s| extract p, a: u32,      b: u64      },
            (3, 2, 0x200..=0x201) => ex!{|s| extract p, a: u16,      b: u64      },
            (3, 3, 0x200..=0x200) => ex!{|s| extract p, a: u8,       b: u64      },

            (4, 0, 0x200..=0x20f) => ex!{|s| extract p, a: u128,     b: u128     },
            (4, 1, 0x200..=0x207) => ex!{|s| extract p, a: u64,      b: u128     },
            (4, 2, 0x200..=0x203) => ex!{|s| extract p, a: u32,      b: u128     },
            (4, 3, 0x200..=0x201) => ex!{|s| extract p, a: u16,      b: u128     },
            (4, 4, 0x200..=0x200) => ex!{|s| extract p, a: u8,       b: u128     },

            (5, 0, 0x200..=0x21f) => ex!{|s| extract p, a: [u128;2], b: [u128;2] },
            (5, 1, 0x200..=0x20f) => ex!{|s| extract p, a: u128,     b: [u128;2] },
            (5, 2, 0x200..=0x207) => ex!{|s| extract p, a: u64,      b: [u128;2] },
            (5, 3, 0x200..=0x203) => ex!{|s| extract p, a: u32,      b: [u128;2] },
            (5, 4, 0x200..=0x201) => ex!{|s| extract p, a: u16,      b: [u128;2] },
            (5, 5, 0x200..=0x200) => ex!{|s| extract p, a: u8,       b: [u128;2] },

            (6, 0, 0x200..=0x23f) => ex!{|s| extract p, a: [u128;4], b: [u128;4] },
            (6, 1, 0x200..=0x21f) => ex!{|s| extract p, a: [u128;2], b: [u128;4] },
            (6, 2, 0x200..=0x20f) => ex!{|s| extract p, a: u128,     b: [u128;4] },
            (6, 3, 0x200..=0x207) => ex!{|s| extract p, a: u64,      b: [u128;4] },
            (6, 4, 0x200..=0x203) => ex!{|s| extract p, a: u32,      b: [u128;4] },
            (6, 5, 0x200..=0x201) => ex!{|s| extract p, a: u16,      b: [u128;4] },
            (6, 6, 0x200..=0x200) => ex!{|s| extract p, a: u8,       b: [u128;4] },

            // replace
            (0, 0, 0x300..=0x300) => ex!{|s| replace p, a: u8,       b: u8       },

            (1, 0, 0x300..=0x301) => ex!{|s| replace p, a: u16,      b: u16      },
            (1, 1, 0x300..=0x300) => ex!{|s| replace p, a: u16,      b: u8       },

            (2, 0, 0x300..=0x303) => ex!{|s| replace p, a: u32,      b: u32      },
            (2, 1, 0x300..=0x301) => ex!{|s| replace p, a: u32,      b: u16      },
            (2, 2, 0x300..=0x300) => ex!{|s| replace p, a: u32,      b: u8       },

            (3, 0, 0x300..=0x307) => ex!{|s| replace p, a: u64,      b: u64      },
            (3, 1, 0x300..=0x303) => ex!{|s| replace p, a: u64,      b: u32      },
            (3, 2, 0x300..=0x301) => ex!{|s| replace p, a: u64,      b: u16      },
            (3, 3, 0x300..=0x300) => ex!{|s| replace p, a: u64,      b: u8       },

            (4, 0, 0x300..=0x30f) => ex!{|s| replace p, a: u128,     b: u128     },
            (4, 1, 0x300..=0x307) => ex!{|s| replace p, a: u128,     b: u64      },
            (4, 2, 0x300..=0x303) => ex!{|s| replace p, a: u128,     b: u32      },
            (4, 3, 0x300..=0x301) => ex!{|s| replace p, a: u128,     b: u16      },
            (4, 4, 0x300..=0x300) => ex!{|s| replace p, a: u128,     b: u8       },

            (5, 0, 0x300..=0x31f) => ex!{|s| replace p, a: [u128;2], b: [u128;2] },
            (5, 1, 0x300..=0x30f) => ex!{|s| replace p, a: [u128;2], b: u128     },
            (5, 2, 0x300..=0x307) => ex!{|s| replace p, a: [u128;2], b: u64      },
            (5, 3, 0x300..=0x303) => ex!{|s| replace p, a: [u128;2], b: u32      },
            (5, 4, 0x300..=0x301) => ex!{|s| replace p, a: [u128;2], b: u16      },
            (5, 5, 0x300..=0x300) => ex!{|s| replace p, a: [u128;2], b: u8       },

            (6, 0, 0x300..=0x33f) => ex!{|s| replace p, a: [u128;4], b: [u128;4] },
            (6, 1, 0x300..=0x31f) => ex!{|s| replace p, a: [u128;4], b: [u128;2] },
            (6, 2, 0x300..=0x30f) => ex!{|s| replace p, a: [u128;4], b: u128     },
            (6, 3, 0x300..=0x307) => ex!{|s| replace p, a: [u128;4], b: u64      },
            (6, 4, 0x300..=0x303) => ex!{|s| replace p, a: [u128;4], b: u32      },
            (6, 5, 0x300..=0x301) => ex!{|s| replace p, a: [u128;2], b: u16      },
            (6, 6, 0x300..=0x300) => ex!{|s| replace p, a: [u128;4], b: u8       },


            //// conversion instructions ////

            // extend_const_u
            (0, 0, 0x003) => ex!{|s, bytecode| extend_const_u a: u8,       pc: u8       },

            (1, 0, 0x003) => ex!{|s, bytecode| extend_const_u a: u16,      pc: u8       },
            (1, 1, 0x003) => ex!{|s, bytecode| extend_const_u a: u16,      pc: u16      },

            (2, 0, 0x003) => ex!{|s, bytecode| extend_const_u a: u32,      pc: u8       },
            (2, 1, 0x003) => ex!{|s, bytecode| extend_const_u a: u32,      pc: u16      },
            (2, 2, 0x003) => ex!{|s, bytecode| extend_const_u a: u32,      pc: u32      },

            (3, 0, 0x003) => ex!{|s, bytecode| extend_const_u a: u64,      pc: u8       },
            (3, 1, 0x003) => ex!{|s, bytecode| extend_const_u a: u64,      pc: u16      },
            (3, 2, 0x003) => ex!{|s, bytecode| extend_const_u a: u64,      pc: u32      },
            (3, 3, 0x003) => ex!{|s, bytecode| extend_const_u a: u64,      pc: u64      },

            (4, 0, 0x003) => ex!{|s, bytecode| extend_const_u a: u128,     pc: u8       },
            (4, 1, 0x003) => ex!{|s, bytecode| extend_const_u a: u128,     pc: u16      },
            (4, 2, 0x003) => ex!{|s, bytecode| extend_const_u a: u128,     pc: u32      },
            (4, 3, 0x003) => ex!{|s, bytecode| extend_const_u a: u128,     pc: u64      },
            (4, 4, 0x003) => ex!{|s, bytecode| extend_const_u a: u128,     pc: u128     },

            (5, 0, 0x003) => ex!{|s, bytecode| extend_const_u a: [u128;2], pc: u8       },
            (5, 1, 0x003) => ex!{|s, bytecode| extend_const_u a: [u128;2], pc: u16      },
            (5, 2, 0x003) => ex!{|s, bytecode| extend_const_u a: [u128;2], pc: u32      },
            (5, 3, 0x003) => ex!{|s, bytecode| extend_const_u a: [u128;2], pc: u64      },
            (5, 4, 0x003) => ex!{|s, bytecode| extend_const_u a: [u128;2], pc: u128     },
            (5, 5, 0x003) => ex!{|s, bytecode| extend_const_u a: [u128;2], pc: [u128;2] },

            (6, 0, 0x003) => ex!{|s, bytecode| extend_const_u a: [u128;4], pc: u8       },
            (6, 1, 0x003) => ex!{|s, bytecode| extend_const_u a: [u128;4], pc: u16      },
            (6, 2, 0x003) => ex!{|s, bytecode| extend_const_u a: [u128;4], pc: u32      },
            (6, 3, 0x003) => ex!{|s, bytecode| extend_const_u a: [u128;4], pc: u64      },
            (6, 4, 0x003) => ex!{|s, bytecode| extend_const_u a: [u128;4], pc: u128     },
            (6, 5, 0x003) => ex!{|s, bytecode| extend_const_u a: [u128;4], pc: [u128;2] },
            (6, 6, 0x003) => ex!{|s, bytecode| extend_const_u a: [u128;4], pc: [u128;4] },

            // extend_const_s
            (0, 0, 0x004) => ex!{|s, bytecode| extend_const_s a: u8,       pc: u8       },

            (1, 0, 0x004) => ex!{|s, bytecode| extend_const_s a: u16,      pc: u8       },
            (1, 1, 0x004) => ex!{|s, bytecode| extend_const_s a: u16,      pc: u16      },

            (2, 0, 0x004) => ex!{|s, bytecode| extend_const_s a: u32,      pc: u8       },
            (2, 1, 0x004) => ex!{|s, bytecode| extend_const_s a: u32,      pc: u16      },
            (2, 2, 0x004) => ex!{|s, bytecode| extend_const_s a: u32,      pc: u32      },

            (3, 0, 0x004) => ex!{|s, bytecode| extend_const_s a: u64,      pc: u8       },
            (3, 1, 0x004) => ex!{|s, bytecode| extend_const_s a: u64,      pc: u16      },
            (3, 2, 0x004) => ex!{|s, bytecode| extend_const_s a: u64,      pc: u32      },
            (3, 3, 0x004) => ex!{|s, bytecode| extend_const_s a: u64,      pc: u64      },

            (4, 0, 0x004) => ex!{|s, bytecode| extend_const_s a: u128,     pc: u8       },
            (4, 1, 0x004) => ex!{|s, bytecode| extend_const_s a: u128,     pc: u16      },
            (4, 2, 0x004) => ex!{|s, bytecode| extend_const_s a: u128,     pc: u32      },
            (4, 3, 0x004) => ex!{|s, bytecode| extend_const_s a: u128,     pc: u64      },
            (4, 4, 0x004) => ex!{|s, bytecode| extend_const_s a: u128,     pc: u128     },

            (5, 0, 0x004) => ex!{|s, bytecode| extend_const_s a: [u128;2], pc: u8       },
            (5, 1, 0x004) => ex!{|s, bytecode| extend_const_s a: [u128;2], pc: u16      },
            (5, 2, 0x004) => ex!{|s, bytecode| extend_const_s a: [u128;2], pc: u32      },
            (5, 3, 0x004) => ex!{|s, bytecode| extend_const_s a: [u128;2], pc: u64      },
            (5, 4, 0x004) => ex!{|s, bytecode| extend_const_s a: [u128;2], pc: u128     },
            (5, 5, 0x004) => ex!{|s, bytecode| extend_const_s a: [u128;2], pc: [u128;2] },

            (6, 0, 0x004) => ex!{|s, bytecode| extend_const_s a: [u128;4], pc: u8       },
            (6, 1, 0x004) => ex!{|s, bytecode| extend_const_s a: [u128;4], pc: u16      },
            (6, 2, 0x004) => ex!{|s, bytecode| extend_const_s a: [u128;4], pc: u32      },
            (6, 3, 0x004) => ex!{|s, bytecode| extend_const_s a: [u128;4], pc: u64      },
            (6, 4, 0x004) => ex!{|s, bytecode| extend_const_s a: [u128;4], pc: u128     },
            (6, 5, 0x004) => ex!{|s, bytecode| extend_const_s a: [u128;4], pc: [u128;2] },
            (6, 6, 0x004) => ex!{|s, bytecode| extend_const_s a: [u128;4], pc: [u128;4] },

            // splat_const
            (0, 0, 0x005) => ex!{|s, bytecode| splat_const a: u8,       pc: u8       },

            (1, 0, 0x005) => ex!{|s, bytecode| splat_const a: u16,      pc: u8       },
            (1, 1, 0x005) => ex!{|s, bytecode| splat_const a: u16,      pc: u16      },

            (2, 0, 0x005) => ex!{|s, bytecode| splat_const a: u32,      pc: u8       },
            (2, 1, 0x005) => ex!{|s, bytecode| splat_const a: u32,      pc: u16      },
            (2, 2, 0x005) => ex!{|s, bytecode| splat_const a: u32,      pc: u32      },

            (3, 0, 0x005) => ex!{|s, bytecode| splat_const a: u64,      pc: u8       },
            (3, 1, 0x005) => ex!{|s, bytecode| splat_const a: u64,      pc: u16      },
            (3, 2, 0x005) => ex!{|s, bytecode| splat_const a: u64,      pc: u32      },
            (3, 3, 0x005) => ex!{|s, bytecode| splat_const a: u64,      pc: u64      },

            (4, 0, 0x005) => ex!{|s, bytecode| splat_const a: u128,     pc: u8       },
            (4, 1, 0x005) => ex!{|s, bytecode| splat_const a: u128,     pc: u16      },
            (4, 2, 0x005) => ex!{|s, bytecode| splat_const a: u128,     pc: u32      },
            (4, 3, 0x005) => ex!{|s, bytecode| splat_const a: u128,     pc: u64      },
            (4, 4, 0x005) => ex!{|s, bytecode| splat_const a: u128,     pc: u128     },

            (5, 0, 0x005) => ex!{|s, bytecode| splat_const a: [u128;2], pc: u8       },
            (5, 1, 0x005) => ex!{|s, bytecode| splat_const a: [u128;2], pc: u16      },
            (5, 2, 0x005) => ex!{|s, bytecode| splat_const a: [u128;2], pc: u32      },
            (5, 3, 0x005) => ex!{|s, bytecode| splat_const a: [u128;2], pc: u64      },
            (5, 4, 0x005) => ex!{|s, bytecode| splat_const a: [u128;2], pc: u128     },
            (5, 5, 0x005) => ex!{|s, bytecode| splat_const a: [u128;2], pc: [u128;2] },

            (6, 0, 0x005) => ex!{|s, bytecode| splat_const a: [u128;4], pc: u8       },
            (6, 1, 0x005) => ex!{|s, bytecode| splat_const a: [u128;4], pc: u16      },
            (6, 2, 0x005) => ex!{|s, bytecode| splat_const a: [u128;4], pc: u32      },
            (6, 3, 0x005) => ex!{|s, bytecode| splat_const a: [u128;4], pc: u64      },
            (6, 4, 0x005) => ex!{|s, bytecode| splat_const a: [u128;4], pc: u128     },
            (6, 5, 0x005) => ex!{|s, bytecode| splat_const a: [u128;4], pc: [u128;2] },
            (6, 6, 0x005) => ex!{|s, bytecode| splat_const a: [u128;4], pc: [u128;4] },

            // extend_const8_u
            (0, 0, 0x006) => ex!{|s| extend_const8_u a: u8,       b },

            (1, 0, 0x006) => ex!{|s| extend_const8_u a: u16,      b },
            (1, 1, 0x006) => ex!{|s| extend_const8_u a: u16,      b },

            (2, 0, 0x006) => ex!{|s| extend_const8_u a: u32,      b },
            (2, 1, 0x006) => ex!{|s| extend_const8_u a: u32,      b },
            (2, 2, 0x006) => ex!{|s| extend_const8_u a: u32,      b },

            (3, 0, 0x006) => ex!{|s| extend_const8_u a: u64,      b },
            (3, 1, 0x006) => ex!{|s| extend_const8_u a: u64,      b },
            (3, 2, 0x006) => ex!{|s| extend_const8_u a: u64,      b },
            (3, 3, 0x006) => ex!{|s| extend_const8_u a: u64,      b },

            (4, 0, 0x006) => ex!{|s| extend_const8_u a: u128,     b },
            (4, 1, 0x006) => ex!{|s| extend_const8_u a: u128,     b },
            (4, 2, 0x006) => ex!{|s| extend_const8_u a: u128,     b },
            (4, 3, 0x006) => ex!{|s| extend_const8_u a: u128,     b },
            (4, 4, 0x006) => ex!{|s| extend_const8_u a: u128,     b },

            (5, 0, 0x006) => ex!{|s| extend_const8_u a: [u128;2], b },
            (5, 1, 0x006) => ex!{|s| extend_const8_u a: [u128;2], b },
            (5, 2, 0x006) => ex!{|s| extend_const8_u a: [u128;2], b },
            (5, 3, 0x006) => ex!{|s| extend_const8_u a: [u128;2], b },
            (5, 4, 0x006) => ex!{|s| extend_const8_u a: [u128;2], b },
            (5, 5, 0x006) => ex!{|s| extend_const8_u a: [u128;2], b },

            (6, 0, 0x006) => ex!{|s| extend_const8_u a: [u128;4], b },
            (6, 1, 0x006) => ex!{|s| extend_const8_u a: [u128;4], b },
            (6, 2, 0x006) => ex!{|s| extend_const8_u a: [u128;4], b },
            (6, 3, 0x006) => ex!{|s| extend_const8_u a: [u128;4], b },
            (6, 4, 0x006) => ex!{|s| extend_const8_u a: [u128;4], b },
            (6, 5, 0x006) => ex!{|s| extend_const8_u a: [u128;4], b },
            (6, 6, 0x006) => ex!{|s| extend_const8_u a: [u128;4], b },

            // extend_const8_s
            (0, 0, 0x007) => ex!{|s| extend_const8_s a: u8,       b },

            (1, 0, 0x007) => ex!{|s| extend_const8_s a: u16,      b },
            (1, 1, 0x007) => ex!{|s| extend_const8_s a: u16,      b },

            (2, 0, 0x007) => ex!{|s| extend_const8_s a: u32,      b },
            (2, 1, 0x007) => ex!{|s| extend_const8_s a: u32,      b },
            (2, 2, 0x007) => ex!{|s| extend_const8_s a: u32,      b },

            (3, 0, 0x007) => ex!{|s| extend_const8_s a: u64,      b },
            (3, 1, 0x007) => ex!{|s| extend_const8_s a: u64,      b },
            (3, 2, 0x007) => ex!{|s| extend_const8_s a: u64,      b },
            (3, 3, 0x007) => ex!{|s| extend_const8_s a: u64,      b },

            (4, 0, 0x007) => ex!{|s| extend_const8_s a: u128,     b },
            (4, 1, 0x007) => ex!{|s| extend_const8_s a: u128,     b },
            (4, 2, 0x007) => ex!{|s| extend_const8_s a: u128,     b },
            (4, 3, 0x007) => ex!{|s| extend_const8_s a: u128,     b },
            (4, 4, 0x007) => ex!{|s| extend_const8_s a: u128,     b },

            (5, 0, 0x007) => ex!{|s| extend_const8_s a: [u128;2], b },
            (5, 1, 0x007) => ex!{|s| extend_const8_s a: [u128;2], b },
            (5, 2, 0x007) => ex!{|s| extend_const8_s a: [u128;2], b },
            (5, 3, 0x007) => ex!{|s| extend_const8_s a: [u128;2], b },
            (5, 4, 0x007) => ex!{|s| extend_const8_s a: [u128;2], b },
            (5, 5, 0x007) => ex!{|s| extend_const8_s a: [u128;2], b },

            (6, 0, 0x007) => ex!{|s| extend_const8_s a: [u128;4], b },
            (6, 1, 0x007) => ex!{|s| extend_const8_s a: [u128;4], b },
            (6, 2, 0x007) => ex!{|s| extend_const8_s a: [u128;4], b },
            (6, 3, 0x007) => ex!{|s| extend_const8_s a: [u128;4], b },
            (6, 4, 0x007) => ex!{|s| extend_const8_s a: [u128;4], b },
            (6, 5, 0x007) => ex!{|s| extend_const8_s a: [u128;4], b },
            (6, 6, 0x007) => ex!{|s| extend_const8_s a: [u128;4], b },

            // splat_const8
            (0, 0, 0x008) => ex!{|s| splat_const8 a: u8,       b },

            (1, 0, 0x008) => ex!{|s| splat_const8 a: u16,      b },
            (1, 1, 0x008) => ex!{|s| splat_const8 a: u16,      b },

            (2, 0, 0x008) => ex!{|s| splat_const8 a: u32,      b },
            (2, 1, 0x008) => ex!{|s| splat_const8 a: u32,      b },
            (2, 2, 0x008) => ex!{|s| splat_const8 a: u32,      b },

            (3, 0, 0x008) => ex!{|s| splat_const8 a: u64,      b },
            (3, 1, 0x008) => ex!{|s| splat_const8 a: u64,      b },
            (3, 2, 0x008) => ex!{|s| splat_const8 a: u64,      b },
            (3, 3, 0x008) => ex!{|s| splat_const8 a: u64,      b },

            (4, 0, 0x008) => ex!{|s| splat_const8 a: u128,     b },
            (4, 1, 0x008) => ex!{|s| splat_const8 a: u128,     b },
            (4, 2, 0x008) => ex!{|s| splat_const8 a: u128,     b },
            (4, 3, 0x008) => ex!{|s| splat_const8 a: u128,     b },
            (4, 4, 0x008) => ex!{|s| splat_const8 a: u128,     b },

            (5, 0, 0x008) => ex!{|s| splat_const8 a: [u128;2], b },
            (5, 1, 0x008) => ex!{|s| splat_const8 a: [u128;2], b },
            (5, 2, 0x008) => ex!{|s| splat_const8 a: [u128;2], b },
            (5, 3, 0x008) => ex!{|s| splat_const8 a: [u128;2], b },
            (5, 4, 0x008) => ex!{|s| splat_const8 a: [u128;2], b },
            (5, 5, 0x008) => ex!{|s| splat_const8 a: [u128;2], b },

            (6, 0, 0x008) => ex!{|s| splat_const8 a: [u128;4], b },
            (6, 1, 0x008) => ex!{|s| splat_const8 a: [u128;4], b },
            (6, 2, 0x008) => ex!{|s| splat_const8 a: [u128;4], b },
            (6, 3, 0x008) => ex!{|s| splat_const8 a: [u128;4], b },
            (6, 4, 0x008) => ex!{|s| splat_const8 a: [u128;4], b },
            (6, 5, 0x008) => ex!{|s| splat_const8 a: [u128;4], b },
            (6, 6, 0x008) => ex!{|s| splat_const8 a: [u128;4], b },

            // extend_u
            (0, 0, 0x009) => ex!{|s| extend_u a: u8,       b: u8       },

            (1, 0, 0x009) => ex!{|s| extend_u a: u16,      b: u8       },
            (1, 1, 0x009) => ex!{|s| extend_u a: u16,      b: u16      },

            (2, 0, 0x009) => ex!{|s| extend_u a: u32,      b: u8       },
            (2, 1, 0x009) => ex!{|s| extend_u a: u32,      b: u16      },
            (2, 2, 0x009) => ex!{|s| extend_u a: u32,      b: u32      },

            (3, 0, 0x009) => ex!{|s| extend_u a: u64,      b: u8       },
            (3, 1, 0x009) => ex!{|s| extend_u a: u64,      b: u16      },
            (3, 2, 0x009) => ex!{|s| extend_u a: u64,      b: u32      },
            (3, 3, 0x009) => ex!{|s| extend_u a: u64,      b: u64      },

            (4, 0, 0x009) => ex!{|s| extend_u a: u128,     b: u8       },
            (4, 1, 0x009) => ex!{|s| extend_u a: u128,     b: u16      },
            (4, 2, 0x009) => ex!{|s| extend_u a: u128,     b: u32      },
            (4, 3, 0x009) => ex!{|s| extend_u a: u128,     b: u64      },
            (4, 4, 0x009) => ex!{|s| extend_u a: u128,     b: u128     },

            (5, 0, 0x009) => ex!{|s| extend_u a: [u128;2], b: u8       },
            (5, 1, 0x009) => ex!{|s| extend_u a: [u128;2], b: u16      },
            (5, 2, 0x009) => ex!{|s| extend_u a: [u128;2], b: u32      },
            (5, 3, 0x009) => ex!{|s| extend_u a: [u128;2], b: u64      },
            (5, 4, 0x009) => ex!{|s| extend_u a: [u128;2], b: u128     },
            (5, 5, 0x009) => ex!{|s| extend_u a: [u128;2], b: [u128;2] },

            (6, 0, 0x009) => ex!{|s| extend_u a: [u128;4], b: u8       },
            (6, 1, 0x009) => ex!{|s| extend_u a: [u128;4], b: u16      },
            (6, 2, 0x009) => ex!{|s| extend_u a: [u128;4], b: u32      },
            (6, 3, 0x009) => ex!{|s| extend_u a: [u128;4], b: u64      },
            (6, 4, 0x009) => ex!{|s| extend_u a: [u128;4], b: u128     },
            (6, 5, 0x009) => ex!{|s| extend_u a: [u128;4], b: [u128;2] },
            (6, 6, 0x009) => ex!{|s| extend_u a: [u128;4], b: [u128;4] },

            // extend_s
            (0, 0, 0x00a) => ex!{|s| extend_s a: u8,       b: u8       },

            (1, 0, 0x00a) => ex!{|s| extend_s a: u16,      b: u8       },
            (1, 1, 0x00a) => ex!{|s| extend_s a: u16,      b: u16      },

            (2, 0, 0x00a) => ex!{|s| extend_s a: u32,      b: u8       },
            (2, 1, 0x00a) => ex!{|s| extend_s a: u32,      b: u16      },
            (2, 2, 0x00a) => ex!{|s| extend_s a: u32,      b: u32      },

            (3, 0, 0x00a) => ex!{|s| extend_s a: u64,      b: u8       },
            (3, 1, 0x00a) => ex!{|s| extend_s a: u64,      b: u16      },
            (3, 2, 0x00a) => ex!{|s| extend_s a: u64,      b: u32      },
            (3, 3, 0x00a) => ex!{|s| extend_s a: u64,      b: u64      },

            (4, 0, 0x00a) => ex!{|s| extend_s a: u128,     b: u8       },
            (4, 1, 0x00a) => ex!{|s| extend_s a: u128,     b: u16      },
            (4, 2, 0x00a) => ex!{|s| extend_s a: u128,     b: u32      },
            (4, 3, 0x00a) => ex!{|s| extend_s a: u128,     b: u64      },
            (4, 4, 0x00a) => ex!{|s| extend_s a: u128,     b: u128     },

            (5, 0, 0x00a) => ex!{|s| extend_s a: [u128;2], b: u8       },
            (5, 1, 0x00a) => ex!{|s| extend_s a: [u128;2], b: u16      },
            (5, 2, 0x00a) => ex!{|s| extend_s a: [u128;2], b: u32      },
            (5, 3, 0x00a) => ex!{|s| extend_s a: [u128;2], b: u64      },
            (5, 4, 0x00a) => ex!{|s| extend_s a: [u128;2], b: u128     },
            (5, 5, 0x00a) => ex!{|s| extend_s a: [u128;2], b: [u128;2] },

            (6, 0, 0x00a) => ex!{|s| extend_s a: [u128;4], b: u8       },
            (6, 1, 0x00a) => ex!{|s| extend_s a: [u128;4], b: u16      },
            (6, 2, 0x00a) => ex!{|s| extend_s a: [u128;4], b: u32      },
            (6, 3, 0x00a) => ex!{|s| extend_s a: [u128;4], b: u64      },
            (6, 4, 0x00a) => ex!{|s| extend_s a: [u128;4], b: u128     },
            (6, 5, 0x00a) => ex!{|s| extend_s a: [u128;4], b: [u128;2] },
            (6, 6, 0x00a) => ex!{|s| extend_s a: [u128;4], b: [u128;4] },

            // splat
            (0, 0, 0x00b) => ex!{|s| splat a: u8,       b: u8       },

            (1, 0, 0x00b) => ex!{|s| splat a: u16,      b: u8       },
            (1, 1, 0x00b) => ex!{|s| splat a: u16,      b: u16      },

            (2, 0, 0x00b) => ex!{|s| splat a: u32,      b: u8       },
            (2, 1, 0x00b) => ex!{|s| splat a: u32,      b: u16      },
            (2, 2, 0x00b) => ex!{|s| splat a: u32,      b: u32      },

            (3, 0, 0x00b) => ex!{|s| splat a: u64,      b: u8       },
            (3, 1, 0x00b) => ex!{|s| splat a: u64,      b: u16      },
            (3, 2, 0x00b) => ex!{|s| splat a: u64,      b: u32      },
            (3, 3, 0x00b) => ex!{|s| splat a: u64,      b: u64      },

            (4, 0, 0x00b) => ex!{|s| splat a: u128,     b: u8       },
            (4, 1, 0x00b) => ex!{|s| splat a: u128,     b: u16      },
            (4, 2, 0x00b) => ex!{|s| splat a: u128,     b: u32      },
            (4, 3, 0x00b) => ex!{|s| splat a: u128,     b: u64      },
            (4, 4, 0x00b) => ex!{|s| splat a: u128,     b: u128     },

            (5, 0, 0x00b) => ex!{|s| splat a: [u128;2], b: u8       },
            (5, 1, 0x00b) => ex!{|s| splat a: [u128;2], b: u16      },
            (5, 2, 0x00b) => ex!{|s| splat a: [u128;2], b: u32      },
            (5, 3, 0x00b) => ex!{|s| splat a: [u128;2], b: u64      },
            (5, 4, 0x00b) => ex!{|s| splat a: [u128;2], b: u128     },
            (5, 5, 0x00b) => ex!{|s| splat a: [u128;2], b: [u128;2] },

            (6, 0, 0x00b) => ex!{|s| splat a: [u128;4], b: u8       },
            (6, 1, 0x00b) => ex!{|s| splat a: [u128;4], b: u16      },
            (6, 2, 0x00b) => ex!{|s| splat a: [u128;4], b: u32      },
            (6, 3, 0x00b) => ex!{|s| splat a: [u128;4], b: u64      },
            (6, 4, 0x00b) => ex!{|s| splat a: [u128;4], b: u128     },
            (6, 5, 0x00b) => ex!{|s| splat a: [u128;4], b: [u128;2] },
            (6, 6, 0x00b) => ex!{|s| splat a: [u128;4], b: [u128;4] },

            // shuffle
            (0, 0, 0x00c) => ex!{|s| shuffle a: u8,       b: u8;1       },

            (1, 0, 0x00c) => ex!{|s| shuffle a: u16,      b: u16;1      },
            (1, 1, 0x00c) => ex!{|s| shuffle a: u16,      b: u8;2       },

            (2, 0, 0x00c) => ex!{|s| shuffle a: u32,      b: u32;1      },
            (2, 1, 0x00c) => ex!{|s| shuffle a: u32,      b: u16;2      },
            (2, 2, 0x00c) => ex!{|s| shuffle a: u32,      b: u8;4       },

            (3, 0, 0x00c) => ex!{|s| shuffle a: u64,      b: u64;1      },
            (3, 1, 0x00c) => ex!{|s| shuffle a: u64,      b: u32;2      },
            (3, 2, 0x00c) => ex!{|s| shuffle a: u64,      b: u16;4      },
            (3, 3, 0x00c) => ex!{|s| shuffle a: u64,      b: u8;8       },

            (4, 0, 0x00c) => ex!{|s| shuffle a: u128,     b: u128;1     },
            (4, 1, 0x00c) => ex!{|s| shuffle a: u128,     b: u64;2      },
            (4, 2, 0x00c) => ex!{|s| shuffle a: u128,     b: u32;4      },
            (4, 3, 0x00c) => ex!{|s| shuffle a: u128,     b: u16;8      },
            (4, 4, 0x00c) => ex!{|s| shuffle a: u128,     b: u8;16      },

            (5, 0, 0x00c) => ex!{|s| shuffle a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x00c) => ex!{|s| shuffle a: [u128;2], b: u128;2     },
            (5, 2, 0x00c) => ex!{|s| shuffle a: [u128;2], b: u64;4      },
            (5, 3, 0x00c) => ex!{|s| shuffle a: [u128;2], b: u32;8      },
            (5, 4, 0x00c) => ex!{|s| shuffle a: [u128;2], b: u16;16     },
            (5, 5, 0x00c) => ex!{|s| shuffle a: [u128;2], b: u8;32      },

            (6, 0, 0x00c) => ex!{|s| shuffle a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x00c) => ex!{|s| shuffle a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x00c) => ex!{|s| shuffle a: [u128;4], b: u128;4     },
            (6, 3, 0x00c) => ex!{|s| shuffle a: [u128;4], b: u64;8      },
            (6, 4, 0x00c) => ex!{|s| shuffle a: [u128;4], b: u32;16     },
            (6, 5, 0x00c) => ex!{|s| shuffle a: [u128;4], b: u16;32     },
            (6, 6, 0x00c) => ex!{|s| shuffle a: [u128;4], b: u8;64      },


            //// comparison instructions ////

            // none
            (0, 0..=0, 0x00d) => ex!{|s| none a: u8,       b: u8       },
            (1, 0..=1, 0x00d) => ex!{|s| none a: u16,      b: u16      },
            (2, 0..=2, 0x00d) => ex!{|s| none a: u32,      b: u32      },
            (3, 0..=3, 0x00d) => ex!{|s| none a: u64,      b: u64      },
            (4, 0..=4, 0x00d) => ex!{|s| none a: u128,     b: u128     },
            (5, 0..=5, 0x00d) => ex!{|s| none a: [u128;2], b: [u128;2] },
            (6, 0..=6, 0x00d) => ex!{|s| none a: [u128;4], b: [u128;4] },

            // any
            (0, 0..=0, 0x00e) => ex!{|s| any a: u8,       b: u8       },
            (1, 0..=1, 0x00e) => ex!{|s| any a: u16,      b: u16      },
            (2, 0..=2, 0x00e) => ex!{|s| any a: u32,      b: u32      },
            (3, 0..=3, 0x00e) => ex!{|s| any a: u64,      b: u64      },
            (4, 0..=4, 0x00e) => ex!{|s| any a: u128,     b: u128     },
            (5, 0..=5, 0x00e) => ex!{|s| any a: [u128;2], b: [u128;2] },
            (6, 0..=6, 0x00e) => ex!{|s| any a: [u128;4], b: [u128;4] },

            // all
            (0, 0, 0x00f) => ex!{|s| all a: u8,       b: u8;1       },

            (1, 0, 0x00f) => ex!{|s| all a: u16,      b: u16;1      },
            (1, 1, 0x00f) => ex!{|s| all a: u16,      b: u8;2       },

            (2, 0, 0x00f) => ex!{|s| all a: u32,      b: u32;1      },
            (2, 1, 0x00f) => ex!{|s| all a: u32,      b: u16;2      },
            (2, 2, 0x00f) => ex!{|s| all a: u32,      b: u8;4       },

            (3, 0, 0x00f) => ex!{|s| all a: u64,      b: u64;1      },
            (3, 1, 0x00f) => ex!{|s| all a: u64,      b: u32;2      },
            (3, 2, 0x00f) => ex!{|s| all a: u64,      b: u16;4      },
            (3, 3, 0x00f) => ex!{|s| all a: u64,      b: u8;8       },

            (4, 0, 0x00f) => ex!{|s| all a: u128,     b: u128;1     },
            (4, 1, 0x00f) => ex!{|s| all a: u128,     b: u64;2      },
            (4, 2, 0x00f) => ex!{|s| all a: u128,     b: u32;4      },
            (4, 3, 0x00f) => ex!{|s| all a: u128,     b: u16;8      },
            (4, 4, 0x00f) => ex!{|s| all a: u128,     b: u8;16      },

            (5, 0, 0x00f) => ex!{|s| all a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x00f) => ex!{|s| all a: [u128;2], b: u128;2     },
            (5, 2, 0x00f) => ex!{|s| all a: [u128;2], b: u64;4      },
            (5, 3, 0x00f) => ex!{|s| all a: [u128;2], b: u32;8      },
            (5, 4, 0x00f) => ex!{|s| all a: [u128;2], b: u16;16     },
            (5, 5, 0x00f) => ex!{|s| all a: [u128;2], b: u8;32      },

            (6, 0, 0x00f) => ex!{|s| all a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x00f) => ex!{|s| all a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x00f) => ex!{|s| all a: [u128;4], b: u128;4     },
            (6, 3, 0x00f) => ex!{|s| all a: [u128;4], b: u64;8      },
            (6, 4, 0x00f) => ex!{|s| all a: [u128;4], b: u32;16     },
            (6, 5, 0x00f) => ex!{|s| all a: [u128;4], b: u16;32     },
            (6, 6, 0x00f) => ex!{|s| all a: [u128;4], b: u8;64      },

            // eq
            (0, 0, 0x010) => ex!{|s| eq a: u8,       b: u8;1       },

            (1, 0, 0x010) => ex!{|s| eq a: u16,      b: u16;1      },
            (1, 1, 0x010) => ex!{|s| eq a: u16,      b: u8;2       },

            (2, 0, 0x010) => ex!{|s| eq a: u32,      b: u32;1      },
            (2, 1, 0x010) => ex!{|s| eq a: u32,      b: u16;2      },
            (2, 2, 0x010) => ex!{|s| eq a: u32,      b: u8;4       },

            (3, 0, 0x010) => ex!{|s| eq a: u64,      b: u64;1      },
            (3, 1, 0x010) => ex!{|s| eq a: u64,      b: u32;2      },
            (3, 2, 0x010) => ex!{|s| eq a: u64,      b: u16;4      },
            (3, 3, 0x010) => ex!{|s| eq a: u64,      b: u8;8       },

            (4, 0, 0x010) => ex!{|s| eq a: u128,     b: u128;1     },
            (4, 1, 0x010) => ex!{|s| eq a: u128,     b: u64;2      },
            (4, 2, 0x010) => ex!{|s| eq a: u128,     b: u32;4      },
            (4, 3, 0x010) => ex!{|s| eq a: u128,     b: u16;8      },
            (4, 4, 0x010) => ex!{|s| eq a: u128,     b: u8;16      },

            (5, 0, 0x010) => ex!{|s| eq a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x010) => ex!{|s| eq a: [u128;2], b: u128;2     },
            (5, 2, 0x010) => ex!{|s| eq a: [u128;2], b: u64;4      },
            (5, 3, 0x010) => ex!{|s| eq a: [u128;2], b: u32;8      },
            (5, 4, 0x010) => ex!{|s| eq a: [u128;2], b: u16;16     },
            (5, 5, 0x010) => ex!{|s| eq a: [u128;2], b: u8;32      },

            (6, 0, 0x010) => ex!{|s| eq a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x010) => ex!{|s| eq a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x010) => ex!{|s| eq a: [u128;4], b: u128;4     },
            (6, 3, 0x010) => ex!{|s| eq a: [u128;4], b: u64;8      },
            (6, 4, 0x010) => ex!{|s| eq a: [u128;4], b: u32;16     },
            (6, 5, 0x010) => ex!{|s| eq a: [u128;4], b: u16;32     },
            (6, 6, 0x010) => ex!{|s| eq a: [u128;4], b: u8;64      },

            // ne
            (0, 0, 0x011) => ex!{|s| ne a: u8,       b: u8;1       },

            (1, 0, 0x011) => ex!{|s| ne a: u16,      b: u16;1      },
            (1, 1, 0x011) => ex!{|s| ne a: u16,      b: u8;2       },

            (2, 0, 0x011) => ex!{|s| ne a: u32,      b: u32;1      },
            (2, 1, 0x011) => ex!{|s| ne a: u32,      b: u16;2      },
            (2, 2, 0x011) => ex!{|s| ne a: u32,      b: u8;4       },

            (3, 0, 0x011) => ex!{|s| ne a: u64,      b: u64;1      },
            (3, 1, 0x011) => ex!{|s| ne a: u64,      b: u32;2      },
            (3, 2, 0x011) => ex!{|s| ne a: u64,      b: u16;4      },
            (3, 3, 0x011) => ex!{|s| ne a: u64,      b: u8;8       },

            (4, 0, 0x011) => ex!{|s| ne a: u128,     b: u128;1     },
            (4, 1, 0x011) => ex!{|s| ne a: u128,     b: u64;2      },
            (4, 2, 0x011) => ex!{|s| ne a: u128,     b: u32;4      },
            (4, 3, 0x011) => ex!{|s| ne a: u128,     b: u16;8      },
            (4, 4, 0x011) => ex!{|s| ne a: u128,     b: u8;16      },

            (5, 0, 0x011) => ex!{|s| ne a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x011) => ex!{|s| ne a: [u128;2], b: u128;2     },
            (5, 2, 0x011) => ex!{|s| ne a: [u128;2], b: u64;4      },
            (5, 3, 0x011) => ex!{|s| ne a: [u128;2], b: u32;8      },
            (5, 4, 0x011) => ex!{|s| ne a: [u128;2], b: u16;16     },
            (5, 5, 0x011) => ex!{|s| ne a: [u128;2], b: u8;32      },

            (6, 0, 0x011) => ex!{|s| ne a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x011) => ex!{|s| ne a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x011) => ex!{|s| ne a: [u128;4], b: u128;4     },
            (6, 3, 0x011) => ex!{|s| ne a: [u128;4], b: u64;8      },
            (6, 4, 0x011) => ex!{|s| ne a: [u128;4], b: u32;16     },
            (6, 5, 0x011) => ex!{|s| ne a: [u128;4], b: u16;32     },
            (6, 6, 0x011) => ex!{|s| ne a: [u128;4], b: u8;64      },

            // lt_u
            (0, 0, 0x012) => ex!{|s| lt_u a: u8,       b: u8;1       },

            (1, 0, 0x012) => ex!{|s| lt_u a: u16,      b: u16;1      },
            (1, 1, 0x012) => ex!{|s| lt_u a: u16,      b: u8;2       },

            (2, 0, 0x012) => ex!{|s| lt_u a: u32,      b: u32;1      },
            (2, 1, 0x012) => ex!{|s| lt_u a: u32,      b: u16;2      },
            (2, 2, 0x012) => ex!{|s| lt_u a: u32,      b: u8;4       },

            (3, 0, 0x012) => ex!{|s| lt_u a: u64,      b: u64;1      },
            (3, 1, 0x012) => ex!{|s| lt_u a: u64,      b: u32;2      },
            (3, 2, 0x012) => ex!{|s| lt_u a: u64,      b: u16;4      },
            (3, 3, 0x012) => ex!{|s| lt_u a: u64,      b: u8;8       },

            (4, 0, 0x012) => ex!{|s| lt_u a: u128,     b: u128;1     },
            (4, 1, 0x012) => ex!{|s| lt_u a: u128,     b: u64;2      },
            (4, 2, 0x012) => ex!{|s| lt_u a: u128,     b: u32;4      },
            (4, 3, 0x012) => ex!{|s| lt_u a: u128,     b: u16;8      },
            (4, 4, 0x012) => ex!{|s| lt_u a: u128,     b: u8;16      },

            (5, 0, 0x012) => ex!{|s| lt_u a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x012) => ex!{|s| lt_u a: [u128;2], b: u128;2     },
            (5, 2, 0x012) => ex!{|s| lt_u a: [u128;2], b: u64;4      },
            (5, 3, 0x012) => ex!{|s| lt_u a: [u128;2], b: u32;8      },
            (5, 4, 0x012) => ex!{|s| lt_u a: [u128;2], b: u16;16     },
            (5, 5, 0x012) => ex!{|s| lt_u a: [u128;2], b: u8;32      },

            (6, 0, 0x012) => ex!{|s| lt_u a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x012) => ex!{|s| lt_u a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x012) => ex!{|s| lt_u a: [u128;4], b: u128;4     },
            (6, 3, 0x012) => ex!{|s| lt_u a: [u128;4], b: u64;8      },
            (6, 4, 0x012) => ex!{|s| lt_u a: [u128;4], b: u32;16     },
            (6, 5, 0x012) => ex!{|s| lt_u a: [u128;4], b: u16;32     },
            (6, 6, 0x012) => ex!{|s| lt_u a: [u128;4], b: u8;64      },

            // lt_s
            (0, 0, 0x013) => ex!{|s| lt_s a: u8,       b: u8;1       },

            (1, 0, 0x013) => ex!{|s| lt_s a: u16,      b: u16;1      },
            (1, 1, 0x013) => ex!{|s| lt_s a: u16,      b: u8;2       },

            (2, 0, 0x013) => ex!{|s| lt_s a: u32,      b: u32;1      },
            (2, 1, 0x013) => ex!{|s| lt_s a: u32,      b: u16;2      },
            (2, 2, 0x013) => ex!{|s| lt_s a: u32,      b: u8;4       },

            (3, 0, 0x013) => ex!{|s| lt_s a: u64,      b: u64;1      },
            (3, 1, 0x013) => ex!{|s| lt_s a: u64,      b: u32;2      },
            (3, 2, 0x013) => ex!{|s| lt_s a: u64,      b: u16;4      },
            (3, 3, 0x013) => ex!{|s| lt_s a: u64,      b: u8;8       },

            (4, 0, 0x013) => ex!{|s| lt_s a: u128,     b: u128;1     },
            (4, 1, 0x013) => ex!{|s| lt_s a: u128,     b: u64;2      },
            (4, 2, 0x013) => ex!{|s| lt_s a: u128,     b: u32;4      },
            (4, 3, 0x013) => ex!{|s| lt_s a: u128,     b: u16;8      },
            (4, 4, 0x013) => ex!{|s| lt_s a: u128,     b: u8;16      },

            (5, 0, 0x013) => ex!{|s| lt_s a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x013) => ex!{|s| lt_s a: [u128;2], b: u128;2     },
            (5, 2, 0x013) => ex!{|s| lt_s a: [u128;2], b: u64;4      },
            (5, 3, 0x013) => ex!{|s| lt_s a: [u128;2], b: u32;8      },
            (5, 4, 0x013) => ex!{|s| lt_s a: [u128;2], b: u16;16     },
            (5, 5, 0x013) => ex!{|s| lt_s a: [u128;2], b: u8;32      },

            (6, 0, 0x013) => ex!{|s| lt_s a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x013) => ex!{|s| lt_s a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x013) => ex!{|s| lt_s a: [u128;4], b: u128;4     },
            (6, 3, 0x013) => ex!{|s| lt_s a: [u128;4], b: u64;8      },
            (6, 4, 0x013) => ex!{|s| lt_s a: [u128;4], b: u32;16     },
            (6, 5, 0x013) => ex!{|s| lt_s a: [u128;4], b: u16;32     },
            (6, 6, 0x013) => ex!{|s| lt_s a: [u128;4], b: u8;64      },

            // gt_u
            (0, 0, 0x014) => ex!{|s| gt_u a: u8,       b: u8;1       },

            (1, 0, 0x014) => ex!{|s| gt_u a: u16,      b: u16;1      },
            (1, 1, 0x014) => ex!{|s| gt_u a: u16,      b: u8;2       },

            (2, 0, 0x014) => ex!{|s| gt_u a: u32,      b: u32;1      },
            (2, 1, 0x014) => ex!{|s| gt_u a: u32,      b: u16;2      },
            (2, 2, 0x014) => ex!{|s| gt_u a: u32,      b: u8;4       },

            (3, 0, 0x014) => ex!{|s| gt_u a: u64,      b: u64;1      },
            (3, 1, 0x014) => ex!{|s| gt_u a: u64,      b: u32;2      },
            (3, 2, 0x014) => ex!{|s| gt_u a: u64,      b: u16;4      },
            (3, 3, 0x014) => ex!{|s| gt_u a: u64,      b: u8;8       },

            (4, 0, 0x014) => ex!{|s| gt_u a: u128,     b: u128;1     },
            (4, 1, 0x014) => ex!{|s| gt_u a: u128,     b: u64;2      },
            (4, 2, 0x014) => ex!{|s| gt_u a: u128,     b: u32;4      },
            (4, 3, 0x014) => ex!{|s| gt_u a: u128,     b: u16;8      },
            (4, 4, 0x014) => ex!{|s| gt_u a: u128,     b: u8;16      },

            (5, 0, 0x014) => ex!{|s| gt_u a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x014) => ex!{|s| gt_u a: [u128;2], b: u128;2     },
            (5, 2, 0x014) => ex!{|s| gt_u a: [u128;2], b: u64;4      },
            (5, 3, 0x014) => ex!{|s| gt_u a: [u128;2], b: u32;8      },
            (5, 4, 0x014) => ex!{|s| gt_u a: [u128;2], b: u16;16     },
            (5, 5, 0x014) => ex!{|s| gt_u a: [u128;2], b: u8;32      },

            (6, 0, 0x014) => ex!{|s| gt_u a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x014) => ex!{|s| gt_u a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x014) => ex!{|s| gt_u a: [u128;4], b: u128;4     },
            (6, 3, 0x014) => ex!{|s| gt_u a: [u128;4], b: u64;8      },
            (6, 4, 0x014) => ex!{|s| gt_u a: [u128;4], b: u32;16     },
            (6, 5, 0x014) => ex!{|s| gt_u a: [u128;4], b: u16;32     },
            (6, 6, 0x014) => ex!{|s| gt_u a: [u128;4], b: u8;64      },

            // gt_s
            (0, 0, 0x015) => ex!{|s| gt_s a: u8,       b: u8;1       },

            (1, 0, 0x015) => ex!{|s| gt_s a: u16,      b: u16;1      },
            (1, 1, 0x015) => ex!{|s| gt_s a: u16,      b: u8;2       },

            (2, 0, 0x015) => ex!{|s| gt_s a: u32,      b: u32;1      },
            (2, 1, 0x015) => ex!{|s| gt_s a: u32,      b: u16;2      },
            (2, 2, 0x015) => ex!{|s| gt_s a: u32,      b: u8;4       },

            (3, 0, 0x015) => ex!{|s| gt_s a: u64,      b: u64;1      },
            (3, 1, 0x015) => ex!{|s| gt_s a: u64,      b: u32;2      },
            (3, 2, 0x015) => ex!{|s| gt_s a: u64,      b: u16;4      },
            (3, 3, 0x015) => ex!{|s| gt_s a: u64,      b: u8;8       },

            (4, 0, 0x015) => ex!{|s| gt_s a: u128,     b: u128;1     },
            (4, 1, 0x015) => ex!{|s| gt_s a: u128,     b: u64;2      },
            (4, 2, 0x015) => ex!{|s| gt_s a: u128,     b: u32;4      },
            (4, 3, 0x015) => ex!{|s| gt_s a: u128,     b: u16;8      },
            (4, 4, 0x015) => ex!{|s| gt_s a: u128,     b: u8;16      },

            (5, 0, 0x015) => ex!{|s| gt_s a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x015) => ex!{|s| gt_s a: [u128;2], b: u128;2     },
            (5, 2, 0x015) => ex!{|s| gt_s a: [u128;2], b: u64;4      },
            (5, 3, 0x015) => ex!{|s| gt_s a: [u128;2], b: u32;8      },
            (5, 4, 0x015) => ex!{|s| gt_s a: [u128;2], b: u16;16     },
            (5, 5, 0x015) => ex!{|s| gt_s a: [u128;2], b: u8;32      },

            (6, 0, 0x015) => ex!{|s| gt_s a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x015) => ex!{|s| gt_s a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x015) => ex!{|s| gt_s a: [u128;4], b: u128;4     },
            (6, 3, 0x015) => ex!{|s| gt_s a: [u128;4], b: u64;8      },
            (6, 4, 0x015) => ex!{|s| gt_s a: [u128;4], b: u32;16     },
            (6, 5, 0x015) => ex!{|s| gt_s a: [u128;4], b: u16;32     },
            (6, 6, 0x015) => ex!{|s| gt_s a: [u128;4], b: u8;64      },

            // le_u
            (0, 0, 0x016) => ex!{|s| le_u a: u8,       b: u8;1       },

            (1, 0, 0x016) => ex!{|s| le_u a: u16,      b: u16;1      },
            (1, 1, 0x016) => ex!{|s| le_u a: u16,      b: u8;2       },

            (2, 0, 0x016) => ex!{|s| le_u a: u32,      b: u32;1      },
            (2, 1, 0x016) => ex!{|s| le_u a: u32,      b: u16;2      },
            (2, 2, 0x016) => ex!{|s| le_u a: u32,      b: u8;4       },

            (3, 0, 0x016) => ex!{|s| le_u a: u64,      b: u64;1      },
            (3, 1, 0x016) => ex!{|s| le_u a: u64,      b: u32;2      },
            (3, 2, 0x016) => ex!{|s| le_u a: u64,      b: u16;4      },
            (3, 3, 0x016) => ex!{|s| le_u a: u64,      b: u8;8       },

            (4, 0, 0x016) => ex!{|s| le_u a: u128,     b: u128;1     },
            (4, 1, 0x016) => ex!{|s| le_u a: u128,     b: u64;2      },
            (4, 2, 0x016) => ex!{|s| le_u a: u128,     b: u32;4      },
            (4, 3, 0x016) => ex!{|s| le_u a: u128,     b: u16;8      },
            (4, 4, 0x016) => ex!{|s| le_u a: u128,     b: u8;16      },

            (5, 0, 0x016) => ex!{|s| le_u a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x016) => ex!{|s| le_u a: [u128;2], b: u128;2     },
            (5, 2, 0x016) => ex!{|s| le_u a: [u128;2], b: u64;4      },
            (5, 3, 0x016) => ex!{|s| le_u a: [u128;2], b: u32;8      },
            (5, 4, 0x016) => ex!{|s| le_u a: [u128;2], b: u16;16     },
            (5, 5, 0x016) => ex!{|s| le_u a: [u128;2], b: u8;32      },

            (6, 0, 0x016) => ex!{|s| le_u a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x016) => ex!{|s| le_u a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x016) => ex!{|s| le_u a: [u128;4], b: u128;4     },
            (6, 3, 0x016) => ex!{|s| le_u a: [u128;4], b: u64;8      },
            (6, 4, 0x016) => ex!{|s| le_u a: [u128;4], b: u32;16     },
            (6, 5, 0x016) => ex!{|s| le_u a: [u128;4], b: u16;32     },
            (6, 6, 0x016) => ex!{|s| le_u a: [u128;4], b: u8;64      },

            // le_s
            (0, 0, 0x017) => ex!{|s| le_s a: u8,       b: u8;1       },

            (1, 0, 0x017) => ex!{|s| le_s a: u16,      b: u16;1      },
            (1, 1, 0x017) => ex!{|s| le_s a: u16,      b: u8;2       },

            (2, 0, 0x017) => ex!{|s| le_s a: u32,      b: u32;1      },
            (2, 1, 0x017) => ex!{|s| le_s a: u32,      b: u16;2      },
            (2, 2, 0x017) => ex!{|s| le_s a: u32,      b: u8;4       },

            (3, 0, 0x017) => ex!{|s| le_s a: u64,      b: u64;1      },
            (3, 1, 0x017) => ex!{|s| le_s a: u64,      b: u32;2      },
            (3, 2, 0x017) => ex!{|s| le_s a: u64,      b: u16;4      },
            (3, 3, 0x017) => ex!{|s| le_s a: u64,      b: u8;8       },

            (4, 0, 0x017) => ex!{|s| le_s a: u128,     b: u128;1     },
            (4, 1, 0x017) => ex!{|s| le_s a: u128,     b: u64;2      },
            (4, 2, 0x017) => ex!{|s| le_s a: u128,     b: u32;4      },
            (4, 3, 0x017) => ex!{|s| le_s a: u128,     b: u16;8      },
            (4, 4, 0x017) => ex!{|s| le_s a: u128,     b: u8;16      },

            (5, 0, 0x017) => ex!{|s| le_s a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x017) => ex!{|s| le_s a: [u128;2], b: u128;2     },
            (5, 2, 0x017) => ex!{|s| le_s a: [u128;2], b: u64;4      },
            (5, 3, 0x017) => ex!{|s| le_s a: [u128;2], b: u32;8      },
            (5, 4, 0x017) => ex!{|s| le_s a: [u128;2], b: u16;16     },
            (5, 5, 0x017) => ex!{|s| le_s a: [u128;2], b: u8;32      },

            (6, 0, 0x017) => ex!{|s| le_s a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x017) => ex!{|s| le_s a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x017) => ex!{|s| le_s a: [u128;4], b: u128;4     },
            (6, 3, 0x017) => ex!{|s| le_s a: [u128;4], b: u64;8      },
            (6, 4, 0x017) => ex!{|s| le_s a: [u128;4], b: u32;16     },
            (6, 5, 0x017) => ex!{|s| le_s a: [u128;4], b: u16;32     },
            (6, 6, 0x017) => ex!{|s| le_s a: [u128;4], b: u8;64      },

            // ge_u
            (0, 0, 0x018) => ex!{|s| ge_u a: u8,       b: u8;1       },

            (1, 0, 0x018) => ex!{|s| ge_u a: u16,      b: u16;1      },
            (1, 1, 0x018) => ex!{|s| ge_u a: u16,      b: u8;2       },

            (2, 0, 0x018) => ex!{|s| ge_u a: u32,      b: u32;1      },
            (2, 1, 0x018) => ex!{|s| ge_u a: u32,      b: u16;2      },
            (2, 2, 0x018) => ex!{|s| ge_u a: u32,      b: u8;4       },

            (3, 0, 0x018) => ex!{|s| ge_u a: u64,      b: u64;1      },
            (3, 1, 0x018) => ex!{|s| ge_u a: u64,      b: u32;2      },
            (3, 2, 0x018) => ex!{|s| ge_u a: u64,      b: u16;4      },
            (3, 3, 0x018) => ex!{|s| ge_u a: u64,      b: u8;8       },

            (4, 0, 0x018) => ex!{|s| ge_u a: u128,     b: u128;1     },
            (4, 1, 0x018) => ex!{|s| ge_u a: u128,     b: u64;2      },
            (4, 2, 0x018) => ex!{|s| ge_u a: u128,     b: u32;4      },
            (4, 3, 0x018) => ex!{|s| ge_u a: u128,     b: u16;8      },
            (4, 4, 0x018) => ex!{|s| ge_u a: u128,     b: u8;16      },

            (5, 0, 0x018) => ex!{|s| ge_u a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x018) => ex!{|s| ge_u a: [u128;2], b: u128;2     },
            (5, 2, 0x018) => ex!{|s| ge_u a: [u128;2], b: u64;4      },
            (5, 3, 0x018) => ex!{|s| ge_u a: [u128;2], b: u32;8      },
            (5, 4, 0x018) => ex!{|s| ge_u a: [u128;2], b: u16;16     },
            (5, 5, 0x018) => ex!{|s| ge_u a: [u128;2], b: u8;32      },

            (6, 0, 0x018) => ex!{|s| ge_u a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x018) => ex!{|s| ge_u a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x018) => ex!{|s| ge_u a: [u128;4], b: u128;4     },
            (6, 3, 0x018) => ex!{|s| ge_u a: [u128;4], b: u64;8      },
            (6, 4, 0x018) => ex!{|s| ge_u a: [u128;4], b: u32;16     },
            (6, 5, 0x018) => ex!{|s| ge_u a: [u128;4], b: u16;32     },
            (6, 6, 0x018) => ex!{|s| ge_u a: [u128;4], b: u8;64      },

            // ge_s
            (0, 0, 0x019) => ex!{|s| ge_s a: u8,       b: u8;1       },

            (1, 0, 0x019) => ex!{|s| ge_s a: u16,      b: u16;1      },
            (1, 1, 0x019) => ex!{|s| ge_s a: u16,      b: u8;2       },

            (2, 0, 0x019) => ex!{|s| ge_s a: u32,      b: u32;1      },
            (2, 1, 0x019) => ex!{|s| ge_s a: u32,      b: u16;2      },
            (2, 2, 0x019) => ex!{|s| ge_s a: u32,      b: u8;4       },

            (3, 0, 0x019) => ex!{|s| ge_s a: u64,      b: u64;1      },
            (3, 1, 0x019) => ex!{|s| ge_s a: u64,      b: u32;2      },
            (3, 2, 0x019) => ex!{|s| ge_s a: u64,      b: u16;4      },
            (3, 3, 0x019) => ex!{|s| ge_s a: u64,      b: u8;8       },

            (4, 0, 0x019) => ex!{|s| ge_s a: u128,     b: u128;1     },
            (4, 1, 0x019) => ex!{|s| ge_s a: u128,     b: u64;2      },
            (4, 2, 0x019) => ex!{|s| ge_s a: u128,     b: u32;4      },
            (4, 3, 0x019) => ex!{|s| ge_s a: u128,     b: u16;8      },
            (4, 4, 0x019) => ex!{|s| ge_s a: u128,     b: u8;16      },

            (5, 0, 0x019) => ex!{|s| ge_s a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x019) => ex!{|s| ge_s a: [u128;2], b: u128;2     },
            (5, 2, 0x019) => ex!{|s| ge_s a: [u128;2], b: u64;4      },
            (5, 3, 0x019) => ex!{|s| ge_s a: [u128;2], b: u32;8      },
            (5, 4, 0x019) => ex!{|s| ge_s a: [u128;2], b: u16;16     },
            (5, 5, 0x019) => ex!{|s| ge_s a: [u128;2], b: u8;32      },

            (6, 0, 0x019) => ex!{|s| ge_s a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x019) => ex!{|s| ge_s a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x019) => ex!{|s| ge_s a: [u128;4], b: u128;4     },
            (6, 3, 0x019) => ex!{|s| ge_s a: [u128;4], b: u64;8      },
            (6, 4, 0x019) => ex!{|s| ge_s a: [u128;4], b: u32;16     },
            (6, 5, 0x019) => ex!{|s| ge_s a: [u128;4], b: u16;32     },
            (6, 6, 0x019) => ex!{|s| ge_s a: [u128;4], b: u8;64      },

            // min_u
            (0, 0, 0x01a) => ex!{|s| min_u a: u8,       b: u8;1       },

            (1, 0, 0x01a) => ex!{|s| min_u a: u16,      b: u16;1      },
            (1, 1, 0x01a) => ex!{|s| min_u a: u16,      b: u8;2       },

            (2, 0, 0x01a) => ex!{|s| min_u a: u32,      b: u32;1      },
            (2, 1, 0x01a) => ex!{|s| min_u a: u32,      b: u16;2      },
            (2, 2, 0x01a) => ex!{|s| min_u a: u32,      b: u8;4       },

            (3, 0, 0x01a) => ex!{|s| min_u a: u64,      b: u64;1      },
            (3, 1, 0x01a) => ex!{|s| min_u a: u64,      b: u32;2      },
            (3, 2, 0x01a) => ex!{|s| min_u a: u64,      b: u16;4      },
            (3, 3, 0x01a) => ex!{|s| min_u a: u64,      b: u8;8       },

            (4, 0, 0x01a) => ex!{|s| min_u a: u128,     b: u128;1     },
            (4, 1, 0x01a) => ex!{|s| min_u a: u128,     b: u64;2      },
            (4, 2, 0x01a) => ex!{|s| min_u a: u128,     b: u32;4      },
            (4, 3, 0x01a) => ex!{|s| min_u a: u128,     b: u16;8      },
            (4, 4, 0x01a) => ex!{|s| min_u a: u128,     b: u8;16      },

            (5, 0, 0x01a) => ex!{|s| min_u a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x01a) => ex!{|s| min_u a: [u128;2], b: u128;2     },
            (5, 2, 0x01a) => ex!{|s| min_u a: [u128;2], b: u64;4      },
            (5, 3, 0x01a) => ex!{|s| min_u a: [u128;2], b: u32;8      },
            (5, 4, 0x01a) => ex!{|s| min_u a: [u128;2], b: u16;16     },
            (5, 5, 0x01a) => ex!{|s| min_u a: [u128;2], b: u8;32      },

            (6, 0, 0x01a) => ex!{|s| min_u a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x01a) => ex!{|s| min_u a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x01a) => ex!{|s| min_u a: [u128;4], b: u128;4     },
            (6, 3, 0x01a) => ex!{|s| min_u a: [u128;4], b: u64;8      },
            (6, 4, 0x01a) => ex!{|s| min_u a: [u128;4], b: u32;16     },
            (6, 5, 0x01a) => ex!{|s| min_u a: [u128;4], b: u16;32     },
            (6, 6, 0x01a) => ex!{|s| min_u a: [u128;4], b: u8;64      },

            // min_s
            (0, 0, 0x01b) => ex!{|s| min_s a: u8,       b: u8;1       },

            (1, 0, 0x01b) => ex!{|s| min_s a: u16,      b: u16;1      },
            (1, 1, 0x01b) => ex!{|s| min_s a: u16,      b: u8;2       },

            (2, 0, 0x01b) => ex!{|s| min_s a: u32,      b: u32;1      },
            (2, 1, 0x01b) => ex!{|s| min_s a: u32,      b: u16;2      },
            (2, 2, 0x01b) => ex!{|s| min_s a: u32,      b: u8;4       },

            (3, 0, 0x01b) => ex!{|s| min_s a: u64,      b: u64;1      },
            (3, 1, 0x01b) => ex!{|s| min_s a: u64,      b: u32;2      },
            (3, 2, 0x01b) => ex!{|s| min_s a: u64,      b: u16;4      },
            (3, 3, 0x01b) => ex!{|s| min_s a: u64,      b: u8;8       },

            (4, 0, 0x01b) => ex!{|s| min_s a: u128,     b: u128;1     },
            (4, 1, 0x01b) => ex!{|s| min_s a: u128,     b: u64;2      },
            (4, 2, 0x01b) => ex!{|s| min_s a: u128,     b: u32;4      },
            (4, 3, 0x01b) => ex!{|s| min_s a: u128,     b: u16;8      },
            (4, 4, 0x01b) => ex!{|s| min_s a: u128,     b: u8;16      },

            (5, 0, 0x01b) => ex!{|s| min_s a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x01b) => ex!{|s| min_s a: [u128;2], b: u128;2     },
            (5, 2, 0x01b) => ex!{|s| min_s a: [u128;2], b: u64;4      },
            (5, 3, 0x01b) => ex!{|s| min_s a: [u128;2], b: u32;8      },
            (5, 4, 0x01b) => ex!{|s| min_s a: [u128;2], b: u16;16     },
            (5, 5, 0x01b) => ex!{|s| min_s a: [u128;2], b: u8;32      },

            (6, 0, 0x01b) => ex!{|s| min_s a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x01b) => ex!{|s| min_s a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x01b) => ex!{|s| min_s a: [u128;4], b: u128;4     },
            (6, 3, 0x01b) => ex!{|s| min_s a: [u128;4], b: u64;8      },
            (6, 4, 0x01b) => ex!{|s| min_s a: [u128;4], b: u32;16     },
            (6, 5, 0x01b) => ex!{|s| min_s a: [u128;4], b: u16;32     },
            (6, 6, 0x01b) => ex!{|s| min_s a: [u128;4], b: u8;64      },

            // max_u
            (0, 0, 0x01c) => ex!{|s| max_u a: u8,       b: u8;1       },

            (1, 0, 0x01c) => ex!{|s| max_u a: u16,      b: u16;1      },
            (1, 1, 0x01c) => ex!{|s| max_u a: u16,      b: u8;2       },

            (2, 0, 0x01c) => ex!{|s| max_u a: u32,      b: u32;1      },
            (2, 1, 0x01c) => ex!{|s| max_u a: u32,      b: u16;2      },
            (2, 2, 0x01c) => ex!{|s| max_u a: u32,      b: u8;4       },

            (3, 0, 0x01c) => ex!{|s| max_u a: u64,      b: u64;1      },
            (3, 1, 0x01c) => ex!{|s| max_u a: u64,      b: u32;2      },
            (3, 2, 0x01c) => ex!{|s| max_u a: u64,      b: u16;4      },
            (3, 3, 0x01c) => ex!{|s| max_u a: u64,      b: u8;8       },

            (4, 0, 0x01c) => ex!{|s| max_u a: u128,     b: u128;1     },
            (4, 1, 0x01c) => ex!{|s| max_u a: u128,     b: u64;2      },
            (4, 2, 0x01c) => ex!{|s| max_u a: u128,     b: u32;4      },
            (4, 3, 0x01c) => ex!{|s| max_u a: u128,     b: u16;8      },
            (4, 4, 0x01c) => ex!{|s| max_u a: u128,     b: u8;16      },

            (5, 0, 0x01c) => ex!{|s| max_u a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x01c) => ex!{|s| max_u a: [u128;2], b: u128;2     },
            (5, 2, 0x01c) => ex!{|s| max_u a: [u128;2], b: u64;4      },
            (5, 3, 0x01c) => ex!{|s| max_u a: [u128;2], b: u32;8      },
            (5, 4, 0x01c) => ex!{|s| max_u a: [u128;2], b: u16;16     },
            (5, 5, 0x01c) => ex!{|s| max_u a: [u128;2], b: u8;32      },

            (6, 0, 0x01c) => ex!{|s| max_u a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x01c) => ex!{|s| max_u a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x01c) => ex!{|s| max_u a: [u128;4], b: u128;4     },
            (6, 3, 0x01c) => ex!{|s| max_u a: [u128;4], b: u64;8      },
            (6, 4, 0x01c) => ex!{|s| max_u a: [u128;4], b: u32;16     },
            (6, 5, 0x01c) => ex!{|s| max_u a: [u128;4], b: u16;32     },
            (6, 6, 0x01c) => ex!{|s| max_u a: [u128;4], b: u8;64      },

            // max_s
            (0, 0, 0x01d) => ex!{|s| max_s a: u8,       b: u8;1       },

            (1, 0, 0x01d) => ex!{|s| max_s a: u16,      b: u16;1      },
            (1, 1, 0x01d) => ex!{|s| max_s a: u16,      b: u8;2       },

            (2, 0, 0x01d) => ex!{|s| max_s a: u32,      b: u32;1      },
            (2, 1, 0x01d) => ex!{|s| max_s a: u32,      b: u16;2      },
            (2, 2, 0x01d) => ex!{|s| max_s a: u32,      b: u8;4       },

            (3, 0, 0x01d) => ex!{|s| max_s a: u64,      b: u64;1      },
            (3, 1, 0x01d) => ex!{|s| max_s a: u64,      b: u32;2      },
            (3, 2, 0x01d) => ex!{|s| max_s a: u64,      b: u16;4      },
            (3, 3, 0x01d) => ex!{|s| max_s a: u64,      b: u8;8       },

            (4, 0, 0x01d) => ex!{|s| max_s a: u128,     b: u128;1     },
            (4, 1, 0x01d) => ex!{|s| max_s a: u128,     b: u64;2      },
            (4, 2, 0x01d) => ex!{|s| max_s a: u128,     b: u32;4      },
            (4, 3, 0x01d) => ex!{|s| max_s a: u128,     b: u16;8      },
            (4, 4, 0x01d) => ex!{|s| max_s a: u128,     b: u8;16      },

            (5, 0, 0x01d) => ex!{|s| max_s a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x01d) => ex!{|s| max_s a: [u128;2], b: u128;2     },
            (5, 2, 0x01d) => ex!{|s| max_s a: [u128;2], b: u64;4      },
            (5, 3, 0x01d) => ex!{|s| max_s a: [u128;2], b: u32;8      },
            (5, 4, 0x01d) => ex!{|s| max_s a: [u128;2], b: u16;16     },
            (5, 5, 0x01d) => ex!{|s| max_s a: [u128;2], b: u8;32      },

            (6, 0, 0x01d) => ex!{|s| max_s a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x01d) => ex!{|s| max_s a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x01d) => ex!{|s| max_s a: [u128;4], b: u128;4     },
            (6, 3, 0x01d) => ex!{|s| max_s a: [u128;4], b: u64;8      },
            (6, 4, 0x01d) => ex!{|s| max_s a: [u128;4], b: u32;16     },
            (6, 5, 0x01d) => ex!{|s| max_s a: [u128;4], b: u16;32     },
            (6, 6, 0x01d) => ex!{|s| max_s a: [u128;4], b: u8;64      },


            //// integer instructions ////

            // neg
            (0, 0, 0x01e) => ex!{|s| neg a: u8,       b: u8;1       },

            (1, 0, 0x01e) => ex!{|s| neg a: u16,      b: u16;1      },
            (1, 1, 0x01e) => ex!{|s| neg a: u16,      b: u8;2       },

            (2, 0, 0x01e) => ex!{|s| neg a: u32,      b: u32;1      },
            (2, 1, 0x01e) => ex!{|s| neg a: u32,      b: u16;2      },
            (2, 2, 0x01e) => ex!{|s| neg a: u32,      b: u8;4       },

            (3, 0, 0x01e) => ex!{|s| neg a: u64,      b: u64;1      },
            (3, 1, 0x01e) => ex!{|s| neg a: u64,      b: u32;2      },
            (3, 2, 0x01e) => ex!{|s| neg a: u64,      b: u16;4      },
            (3, 3, 0x01e) => ex!{|s| neg a: u64,      b: u8;8       },

            (4, 0, 0x01e) => ex!{|s| neg a: u128,     b: u128;1     },
            (4, 1, 0x01e) => ex!{|s| neg a: u128,     b: u64;2      },
            (4, 2, 0x01e) => ex!{|s| neg a: u128,     b: u32;4      },
            (4, 3, 0x01e) => ex!{|s| neg a: u128,     b: u16;8      },
            (4, 4, 0x01e) => ex!{|s| neg a: u128,     b: u8;16      },

            (5, 0, 0x01e) => ex!{|s| neg a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x01e) => ex!{|s| neg a: [u128;2], b: u128;2     },
            (5, 2, 0x01e) => ex!{|s| neg a: [u128;2], b: u64;4      },
            (5, 3, 0x01e) => ex!{|s| neg a: [u128;2], b: u32;8      },
            (5, 4, 0x01e) => ex!{|s| neg a: [u128;2], b: u16;16     },
            (5, 5, 0x01e) => ex!{|s| neg a: [u128;2], b: u8;32      },

            (6, 0, 0x01e) => ex!{|s| neg a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x01e) => ex!{|s| neg a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x01e) => ex!{|s| neg a: [u128;4], b: u128;4     },
            (6, 3, 0x01e) => ex!{|s| neg a: [u128;4], b: u64;8      },
            (6, 4, 0x01e) => ex!{|s| neg a: [u128;4], b: u32;16     },
            (6, 5, 0x01e) => ex!{|s| neg a: [u128;4], b: u16;32     },
            (6, 6, 0x01e) => ex!{|s| neg a: [u128;4], b: u8;64      },

            // abs
            (0, 0, 0x01f) => ex!{|s| abs a: u8,       b: u8;1       },

            (1, 0, 0x01f) => ex!{|s| abs a: u16,      b: u16;1      },
            (1, 1, 0x01f) => ex!{|s| abs a: u16,      b: u8;2       },

            (2, 0, 0x01f) => ex!{|s| abs a: u32,      b: u32;1      },
            (2, 1, 0x01f) => ex!{|s| abs a: u32,      b: u16;2      },
            (2, 2, 0x01f) => ex!{|s| abs a: u32,      b: u8;4       },

            (3, 0, 0x01f) => ex!{|s| abs a: u64,      b: u64;1      },
            (3, 1, 0x01f) => ex!{|s| abs a: u64,      b: u32;2      },
            (3, 2, 0x01f) => ex!{|s| abs a: u64,      b: u16;4      },
            (3, 3, 0x01f) => ex!{|s| abs a: u64,      b: u8;8       },

            (4, 0, 0x01f) => ex!{|s| abs a: u128,     b: u128;1     },
            (4, 1, 0x01f) => ex!{|s| abs a: u128,     b: u64;2      },
            (4, 2, 0x01f) => ex!{|s| abs a: u128,     b: u32;4      },
            (4, 3, 0x01f) => ex!{|s| abs a: u128,     b: u16;8      },
            (4, 4, 0x01f) => ex!{|s| abs a: u128,     b: u8;16      },

            (5, 0, 0x01f) => ex!{|s| abs a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x01f) => ex!{|s| abs a: [u128;2], b: u128;2     },
            (5, 2, 0x01f) => ex!{|s| abs a: [u128;2], b: u64;4      },
            (5, 3, 0x01f) => ex!{|s| abs a: [u128;2], b: u32;8      },
            (5, 4, 0x01f) => ex!{|s| abs a: [u128;2], b: u16;16     },
            (5, 5, 0x01f) => ex!{|s| abs a: [u128;2], b: u8;32      },

            (6, 0, 0x01f) => ex!{|s| abs a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x01f) => ex!{|s| abs a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x01f) => ex!{|s| abs a: [u128;4], b: u128;4     },
            (6, 3, 0x01f) => ex!{|s| abs a: [u128;4], b: u64;8      },
            (6, 4, 0x01f) => ex!{|s| abs a: [u128;4], b: u32;16     },
            (6, 5, 0x01f) => ex!{|s| abs a: [u128;4], b: u16;32     },
            (6, 6, 0x01f) => ex!{|s| abs a: [u128;4], b: u8;64      },

            // not
            (0, 0..=0, 0x020) => ex!{|s| not a: u8,       b: u8       },
            (1, 0..=1, 0x020) => ex!{|s| not a: u16,      b: u16      },
            (2, 0..=2, 0x020) => ex!{|s| not a: u32,      b: u32      },
            (3, 0..=3, 0x020) => ex!{|s| not a: u64,      b: u64      },
            (4, 0..=4, 0x020) => ex!{|s| not a: u128,     b: u128     },
            (5, 0..=5, 0x020) => ex!{|s| not a: [u128;2], b: [u128;2] },
            (6, 0..=6, 0x020) => ex!{|s| not a: [u128;4], b: [u128;4] },

            // clz
            (0, 0, 0x021) => ex!{|s| clz a: u8,       b: u8;1       },

            (1, 0, 0x021) => ex!{|s| clz a: u16,      b: u16;1      },
            (1, 1, 0x021) => ex!{|s| clz a: u16,      b: u8;2       },

            (2, 0, 0x021) => ex!{|s| clz a: u32,      b: u32;1      },
            (2, 1, 0x021) => ex!{|s| clz a: u32,      b: u16;2      },
            (2, 2, 0x021) => ex!{|s| clz a: u32,      b: u8;4       },

            (3, 0, 0x021) => ex!{|s| clz a: u64,      b: u64;1      },
            (3, 1, 0x021) => ex!{|s| clz a: u64,      b: u32;2      },
            (3, 2, 0x021) => ex!{|s| clz a: u64,      b: u16;4      },
            (3, 3, 0x021) => ex!{|s| clz a: u64,      b: u8;8       },

            (4, 0, 0x021) => ex!{|s| clz a: u128,     b: u128;1     },
            (4, 1, 0x021) => ex!{|s| clz a: u128,     b: u64;2      },
            (4, 2, 0x021) => ex!{|s| clz a: u128,     b: u32;4      },
            (4, 3, 0x021) => ex!{|s| clz a: u128,     b: u16;8      },
            (4, 4, 0x021) => ex!{|s| clz a: u128,     b: u8;16      },

            (5, 0, 0x021) => ex!{|s| clz a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x021) => ex!{|s| clz a: [u128;2], b: u128;2     },
            (5, 2, 0x021) => ex!{|s| clz a: [u128;2], b: u64;4      },
            (5, 3, 0x021) => ex!{|s| clz a: [u128;2], b: u32;8      },
            (5, 4, 0x021) => ex!{|s| clz a: [u128;2], b: u16;16     },
            (5, 5, 0x021) => ex!{|s| clz a: [u128;2], b: u8;32      },

            (6, 0, 0x021) => ex!{|s| clz a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x021) => ex!{|s| clz a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x021) => ex!{|s| clz a: [u128;4], b: u128;4     },
            (6, 3, 0x021) => ex!{|s| clz a: [u128;4], b: u64;8      },
            (6, 4, 0x021) => ex!{|s| clz a: [u128;4], b: u32;16     },
            (6, 5, 0x021) => ex!{|s| clz a: [u128;4], b: u16;32     },
            (6, 6, 0x021) => ex!{|s| clz a: [u128;4], b: u8;64      },

            // ctz
            (0, 0, 0x022) => ex!{|s| ctz a: u8,       b: u8;1       },

            (1, 0, 0x022) => ex!{|s| ctz a: u16,      b: u16;1      },
            (1, 1, 0x022) => ex!{|s| ctz a: u16,      b: u8;2       },

            (2, 0, 0x022) => ex!{|s| ctz a: u32,      b: u32;1      },
            (2, 1, 0x022) => ex!{|s| ctz a: u32,      b: u16;2      },
            (2, 2, 0x022) => ex!{|s| ctz a: u32,      b: u8;4       },

            (3, 0, 0x022) => ex!{|s| ctz a: u64,      b: u64;1      },
            (3, 1, 0x022) => ex!{|s| ctz a: u64,      b: u32;2      },
            (3, 2, 0x022) => ex!{|s| ctz a: u64,      b: u16;4      },
            (3, 3, 0x022) => ex!{|s| ctz a: u64,      b: u8;8       },

            (4, 0, 0x022) => ex!{|s| ctz a: u128,     b: u128;1     },
            (4, 1, 0x022) => ex!{|s| ctz a: u128,     b: u64;2      },
            (4, 2, 0x022) => ex!{|s| ctz a: u128,     b: u32;4      },
            (4, 3, 0x022) => ex!{|s| ctz a: u128,     b: u16;8      },
            (4, 4, 0x022) => ex!{|s| ctz a: u128,     b: u8;16      },

            (5, 0, 0x022) => ex!{|s| ctz a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x022) => ex!{|s| ctz a: [u128;2], b: u128;2     },
            (5, 2, 0x022) => ex!{|s| ctz a: [u128;2], b: u64;4      },
            (5, 3, 0x022) => ex!{|s| ctz a: [u128;2], b: u32;8      },
            (5, 4, 0x022) => ex!{|s| ctz a: [u128;2], b: u16;16     },
            (5, 5, 0x022) => ex!{|s| ctz a: [u128;2], b: u8;32      },

            (6, 0, 0x022) => ex!{|s| ctz a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x022) => ex!{|s| ctz a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x022) => ex!{|s| ctz a: [u128;4], b: u128;4     },
            (6, 3, 0x022) => ex!{|s| ctz a: [u128;4], b: u64;8      },
            (6, 4, 0x022) => ex!{|s| ctz a: [u128;4], b: u32;16     },
            (6, 5, 0x022) => ex!{|s| ctz a: [u128;4], b: u16;32     },
            (6, 6, 0x022) => ex!{|s| ctz a: [u128;4], b: u8;64      },

            // popcnt
            (0, 0, 0x023) => ex!{|s| popcnt a: u8,       b: u8;1       },

            (1, 0, 0x023) => ex!{|s| popcnt a: u16,      b: u16;1      },
            (1, 1, 0x023) => ex!{|s| popcnt a: u16,      b: u8;2       },

            (2, 0, 0x023) => ex!{|s| popcnt a: u32,      b: u32;1      },
            (2, 1, 0x023) => ex!{|s| popcnt a: u32,      b: u16;2      },
            (2, 2, 0x023) => ex!{|s| popcnt a: u32,      b: u8;4       },

            (3, 0, 0x023) => ex!{|s| popcnt a: u64,      b: u64;1      },
            (3, 1, 0x023) => ex!{|s| popcnt a: u64,      b: u32;2      },
            (3, 2, 0x023) => ex!{|s| popcnt a: u64,      b: u16;4      },
            (3, 3, 0x023) => ex!{|s| popcnt a: u64,      b: u8;8       },

            (4, 0, 0x023) => ex!{|s| popcnt a: u128,     b: u128;1     },
            (4, 1, 0x023) => ex!{|s| popcnt a: u128,     b: u64;2      },
            (4, 2, 0x023) => ex!{|s| popcnt a: u128,     b: u32;4      },
            (4, 3, 0x023) => ex!{|s| popcnt a: u128,     b: u16;8      },
            (4, 4, 0x023) => ex!{|s| popcnt a: u128,     b: u8;16      },

            (5, 0, 0x023) => ex!{|s| popcnt a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x023) => ex!{|s| popcnt a: [u128;2], b: u128;2     },
            (5, 2, 0x023) => ex!{|s| popcnt a: [u128;2], b: u64;4      },
            (5, 3, 0x023) => ex!{|s| popcnt a: [u128;2], b: u32;8      },
            (5, 4, 0x023) => ex!{|s| popcnt a: [u128;2], b: u16;16     },
            (5, 5, 0x023) => ex!{|s| popcnt a: [u128;2], b: u8;32      },

            (6, 0, 0x023) => ex!{|s| popcnt a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x023) => ex!{|s| popcnt a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x023) => ex!{|s| popcnt a: [u128;4], b: u128;4     },
            (6, 3, 0x023) => ex!{|s| popcnt a: [u128;4], b: u64;8      },
            (6, 4, 0x023) => ex!{|s| popcnt a: [u128;4], b: u32;16     },
            (6, 5, 0x023) => ex!{|s| popcnt a: [u128;4], b: u16;32     },
            (6, 6, 0x023) => ex!{|s| popcnt a: [u128;4], b: u8;64      },

            // add
            (0, 0, 0x024) => ex!{|s| add a: u8,       b: u8;1       },

            (1, 0, 0x024) => ex!{|s| add a: u16,      b: u16;1      },
            (1, 1, 0x024) => ex!{|s| add a: u16,      b: u8;2       },

            (2, 0, 0x024) => ex!{|s| add a: u32,      b: u32;1      },
            (2, 1, 0x024) => ex!{|s| add a: u32,      b: u16;2      },
            (2, 2, 0x024) => ex!{|s| add a: u32,      b: u8;4       },

            (3, 0, 0x024) => ex!{|s| add a: u64,      b: u64;1      },
            (3, 1, 0x024) => ex!{|s| add a: u64,      b: u32;2      },
            (3, 2, 0x024) => ex!{|s| add a: u64,      b: u16;4      },
            (3, 3, 0x024) => ex!{|s| add a: u64,      b: u8;8       },

            (4, 0, 0x024) => ex!{|s| add a: u128,     b: u128;1     },
            (4, 1, 0x024) => ex!{|s| add a: u128,     b: u64;2      },
            (4, 2, 0x024) => ex!{|s| add a: u128,     b: u32;4      },
            (4, 3, 0x024) => ex!{|s| add a: u128,     b: u16;8      },
            (4, 4, 0x024) => ex!{|s| add a: u128,     b: u8;16      },

            (5, 0, 0x024) => ex!{|s| add a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x024) => ex!{|s| add a: [u128;2], b: u128;2     },
            (5, 2, 0x024) => ex!{|s| add a: [u128;2], b: u64;4      },
            (5, 3, 0x024) => ex!{|s| add a: [u128;2], b: u32;8      },
            (5, 4, 0x024) => ex!{|s| add a: [u128;2], b: u16;16     },
            (5, 5, 0x024) => ex!{|s| add a: [u128;2], b: u8;32      },

            (6, 0, 0x024) => ex!{|s| add a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x024) => ex!{|s| add a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x024) => ex!{|s| add a: [u128;4], b: u128;4     },
            (6, 3, 0x024) => ex!{|s| add a: [u128;4], b: u64;8      },
            (6, 4, 0x024) => ex!{|s| add a: [u128;4], b: u32;16     },
            (6, 5, 0x024) => ex!{|s| add a: [u128;4], b: u16;32     },
            (6, 6, 0x024) => ex!{|s| add a: [u128;4], b: u8;64      },

            // sub
            (0, 0, 0x025) => ex!{|s| sub a: u8,       b: u8;1       },

            (1, 0, 0x025) => ex!{|s| sub a: u16,      b: u16;1      },
            (1, 1, 0x025) => ex!{|s| sub a: u16,      b: u8;2       },

            (2, 0, 0x025) => ex!{|s| sub a: u32,      b: u32;1      },
            (2, 1, 0x025) => ex!{|s| sub a: u32,      b: u16;2      },
            (2, 2, 0x025) => ex!{|s| sub a: u32,      b: u8;4       },

            (3, 0, 0x025) => ex!{|s| sub a: u64,      b: u64;1      },
            (3, 1, 0x025) => ex!{|s| sub a: u64,      b: u32;2      },
            (3, 2, 0x025) => ex!{|s| sub a: u64,      b: u16;4      },
            (3, 3, 0x025) => ex!{|s| sub a: u64,      b: u8;8       },

            (4, 0, 0x025) => ex!{|s| sub a: u128,     b: u128;1     },
            (4, 1, 0x025) => ex!{|s| sub a: u128,     b: u64;2      },
            (4, 2, 0x025) => ex!{|s| sub a: u128,     b: u32;4      },
            (4, 3, 0x025) => ex!{|s| sub a: u128,     b: u16;8      },
            (4, 4, 0x025) => ex!{|s| sub a: u128,     b: u8;16      },

            (5, 0, 0x025) => ex!{|s| sub a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x025) => ex!{|s| sub a: [u128;2], b: u128;2     },
            (5, 2, 0x025) => ex!{|s| sub a: [u128;2], b: u64;4      },
            (5, 3, 0x025) => ex!{|s| sub a: [u128;2], b: u32;8      },
            (5, 4, 0x025) => ex!{|s| sub a: [u128;2], b: u16;16     },
            (5, 5, 0x025) => ex!{|s| sub a: [u128;2], b: u8;32      },

            (6, 0, 0x025) => ex!{|s| sub a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x025) => ex!{|s| sub a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x025) => ex!{|s| sub a: [u128;4], b: u128;4     },
            (6, 3, 0x025) => ex!{|s| sub a: [u128;4], b: u64;8      },
            (6, 4, 0x025) => ex!{|s| sub a: [u128;4], b: u32;16     },
            (6, 5, 0x025) => ex!{|s| sub a: [u128;4], b: u16;32     },
            (6, 6, 0x025) => ex!{|s| sub a: [u128;4], b: u8;64      },

            // mul
            (0, 0, 0x026) => ex!{|s| mul a: u8,       b: u8;1       },

            (1, 0, 0x026) => ex!{|s| mul a: u16,      b: u16;1      },
            (1, 1, 0x026) => ex!{|s| mul a: u16,      b: u8;2       },

            (2, 0, 0x026) => ex!{|s| mul a: u32,      b: u32;1      },
            (2, 1, 0x026) => ex!{|s| mul a: u32,      b: u16;2      },
            (2, 2, 0x026) => ex!{|s| mul a: u32,      b: u8;4       },

            (3, 0, 0x026) => ex!{|s| mul a: u64,      b: u64;1      },
            (3, 1, 0x026) => ex!{|s| mul a: u64,      b: u32;2      },
            (3, 2, 0x026) => ex!{|s| mul a: u64,      b: u16;4      },
            (3, 3, 0x026) => ex!{|s| mul a: u64,      b: u8;8       },

            (4, 0, 0x026) => ex!{|s| mul a: u128,     b: u128;1     },
            (4, 1, 0x026) => ex!{|s| mul a: u128,     b: u64;2      },
            (4, 2, 0x026) => ex!{|s| mul a: u128,     b: u32;4      },
            (4, 3, 0x026) => ex!{|s| mul a: u128,     b: u16;8      },
            (4, 4, 0x026) => ex!{|s| mul a: u128,     b: u8;16      },

            (5, 0, 0x026) => ex!{|s| mul a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x026) => ex!{|s| mul a: [u128;2], b: u128;2     },
            (5, 2, 0x026) => ex!{|s| mul a: [u128;2], b: u64;4      },
            (5, 3, 0x026) => ex!{|s| mul a: [u128;2], b: u32;8      },
            (5, 4, 0x026) => ex!{|s| mul a: [u128;2], b: u16;16     },
            (5, 5, 0x026) => ex!{|s| mul a: [u128;2], b: u8;32      },

            (6, 0, 0x026) => ex!{|s| mul a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x026) => ex!{|s| mul a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x026) => ex!{|s| mul a: [u128;4], b: u128;4     },
            (6, 3, 0x026) => ex!{|s| mul a: [u128;4], b: u64;8      },
            (6, 4, 0x026) => ex!{|s| mul a: [u128;4], b: u32;16     },
            (6, 5, 0x026) => ex!{|s| mul a: [u128;4], b: u16;32     },
            (6, 6, 0x026) => ex!{|s| mul a: [u128;4], b: u8;64      },

            // and
            (0, 0..=0, 0x027) => ex!{|s| and a: u8,       b: u8       },
            (1, 0..=1, 0x027) => ex!{|s| and a: u16,      b: u16      },
            (2, 0..=2, 0x027) => ex!{|s| and a: u32,      b: u32      },
            (3, 0..=3, 0x027) => ex!{|s| and a: u64,      b: u64      },
            (4, 0..=4, 0x027) => ex!{|s| and a: u128,     b: u128     },
            (5, 0..=5, 0x027) => ex!{|s| and a: [u128;2], b: [u128;2] },
            (6, 0..=6, 0x027) => ex!{|s| and a: [u128;4], b: [u128;4] },

            // andnot
            (0, 0..=0, 0x028) => ex!{|s| andnot a: u8,       b: u8       },
            (1, 0..=1, 0x028) => ex!{|s| andnot a: u16,      b: u16      },
            (2, 0..=2, 0x028) => ex!{|s| andnot a: u32,      b: u32      },
            (3, 0..=3, 0x028) => ex!{|s| andnot a: u64,      b: u64      },
            (4, 0..=4, 0x028) => ex!{|s| andnot a: u128,     b: u128     },
            (5, 0..=5, 0x028) => ex!{|s| andnot a: [u128;2], b: [u128;2] },
            (6, 0..=6, 0x028) => ex!{|s| andnot a: [u128;4], b: [u128;4] },

            // or
            (0, 0..=0, 0x029) => ex!{|s| or a: u8,       b: u8       },
            (1, 0..=1, 0x029) => ex!{|s| or a: u16,      b: u16      },
            (2, 0..=2, 0x029) => ex!{|s| or a: u32,      b: u32      },
            (3, 0..=3, 0x029) => ex!{|s| or a: u64,      b: u64      },
            (4, 0..=4, 0x029) => ex!{|s| or a: u128,     b: u128     },
            (5, 0..=5, 0x029) => ex!{|s| or a: [u128;2], b: [u128;2] },
            (6, 0..=6, 0x029) => ex!{|s| or a: [u128;4], b: [u128;4] },

            // xor
            (0, 0..=0, 0x02a) => ex!{|s| xor a: u8,       b: u8       },
            (1, 0..=1, 0x02a) => ex!{|s| xor a: u16,      b: u16      },
            (2, 0..=2, 0x02a) => ex!{|s| xor a: u32,      b: u32      },
            (3, 0..=3, 0x02a) => ex!{|s| xor a: u64,      b: u64      },
            (4, 0..=4, 0x02a) => ex!{|s| xor a: u128,     b: u128     },
            (5, 0..=5, 0x02a) => ex!{|s| xor a: [u128;2], b: [u128;2] },
            (6, 0..=6, 0x02a) => ex!{|s| xor a: [u128;4], b: [u128;4] },

            // shl
            (0, 0, 0x02b) => ex!{|s| shl a: u8,       b: u8;1       },

            (1, 0, 0x02b) => ex!{|s| shl a: u16,      b: u16;1      },
            (1, 1, 0x02b) => ex!{|s| shl a: u16,      b: u8;2       },

            (2, 0, 0x02b) => ex!{|s| shl a: u32,      b: u32;1      },
            (2, 1, 0x02b) => ex!{|s| shl a: u32,      b: u16;2      },
            (2, 2, 0x02b) => ex!{|s| shl a: u32,      b: u8;4       },

            (3, 0, 0x02b) => ex!{|s| shl a: u64,      b: u64;1      },
            (3, 1, 0x02b) => ex!{|s| shl a: u64,      b: u32;2      },
            (3, 2, 0x02b) => ex!{|s| shl a: u64,      b: u16;4      },
            (3, 3, 0x02b) => ex!{|s| shl a: u64,      b: u8;8       },

            (4, 0, 0x02b) => ex!{|s| shl a: u128,     b: u128;1     },
            (4, 1, 0x02b) => ex!{|s| shl a: u128,     b: u64;2      },
            (4, 2, 0x02b) => ex!{|s| shl a: u128,     b: u32;4      },
            (4, 3, 0x02b) => ex!{|s| shl a: u128,     b: u16;8      },
            (4, 4, 0x02b) => ex!{|s| shl a: u128,     b: u8;16      },

            (5, 0, 0x02b) => ex!{|s| shl a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x02b) => ex!{|s| shl a: [u128;2], b: u128;2     },
            (5, 2, 0x02b) => ex!{|s| shl a: [u128;2], b: u64;4      },
            (5, 3, 0x02b) => ex!{|s| shl a: [u128;2], b: u32;8      },
            (5, 4, 0x02b) => ex!{|s| shl a: [u128;2], b: u16;16     },
            (5, 5, 0x02b) => ex!{|s| shl a: [u128;2], b: u8;32      },

            (6, 0, 0x02b) => ex!{|s| shl a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x02b) => ex!{|s| shl a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x02b) => ex!{|s| shl a: [u128;4], b: u128;4     },
            (6, 3, 0x02b) => ex!{|s| shl a: [u128;4], b: u64;8      },
            (6, 4, 0x02b) => ex!{|s| shl a: [u128;4], b: u32;16     },
            (6, 5, 0x02b) => ex!{|s| shl a: [u128;4], b: u16;32     },
            (6, 6, 0x02b) => ex!{|s| shl a: [u128;4], b: u8;64      },

            // shr_u
            (0, 0, 0x02c) => ex!{|s| shr_u a: u8,       b: u8;1       },

            (1, 0, 0x02c) => ex!{|s| shr_u a: u16,      b: u16;1      },
            (1, 1, 0x02c) => ex!{|s| shr_u a: u16,      b: u8;2       },

            (2, 0, 0x02c) => ex!{|s| shr_u a: u32,      b: u32;1      },
            (2, 1, 0x02c) => ex!{|s| shr_u a: u32,      b: u16;2      },
            (2, 2, 0x02c) => ex!{|s| shr_u a: u32,      b: u8;4       },

            (3, 0, 0x02c) => ex!{|s| shr_u a: u64,      b: u64;1      },
            (3, 1, 0x02c) => ex!{|s| shr_u a: u64,      b: u32;2      },
            (3, 2, 0x02c) => ex!{|s| shr_u a: u64,      b: u16;4      },
            (3, 3, 0x02c) => ex!{|s| shr_u a: u64,      b: u8;8       },

            (4, 0, 0x02c) => ex!{|s| shr_u a: u128,     b: u128;1     },
            (4, 1, 0x02c) => ex!{|s| shr_u a: u128,     b: u64;2      },
            (4, 2, 0x02c) => ex!{|s| shr_u a: u128,     b: u32;4      },
            (4, 3, 0x02c) => ex!{|s| shr_u a: u128,     b: u16;8      },
            (4, 4, 0x02c) => ex!{|s| shr_u a: u128,     b: u8;16      },

            (5, 0, 0x02c) => ex!{|s| shr_u a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x02c) => ex!{|s| shr_u a: [u128;2], b: u128;2     },
            (5, 2, 0x02c) => ex!{|s| shr_u a: [u128;2], b: u64;4      },
            (5, 3, 0x02c) => ex!{|s| shr_u a: [u128;2], b: u32;8      },
            (5, 4, 0x02c) => ex!{|s| shr_u a: [u128;2], b: u16;16     },
            (5, 5, 0x02c) => ex!{|s| shr_u a: [u128;2], b: u8;32      },

            (6, 0, 0x02c) => ex!{|s| shr_u a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x02c) => ex!{|s| shr_u a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x02c) => ex!{|s| shr_u a: [u128;4], b: u128;4     },
            (6, 3, 0x02c) => ex!{|s| shr_u a: [u128;4], b: u64;8      },
            (6, 4, 0x02c) => ex!{|s| shr_u a: [u128;4], b: u32;16     },
            (6, 5, 0x02c) => ex!{|s| shr_u a: [u128;4], b: u16;32     },
            (6, 6, 0x02c) => ex!{|s| shr_u a: [u128;4], b: u8;64      },

            // shr_s
            (0, 0, 0x02d) => ex!{|s| shr_s a: u8,       b: u8;1       },

            (1, 0, 0x02d) => ex!{|s| shr_s a: u16,      b: u16;1      },
            (1, 1, 0x02d) => ex!{|s| shr_s a: u16,      b: u8;2       },

            (2, 0, 0x02d) => ex!{|s| shr_s a: u32,      b: u32;1      },
            (2, 1, 0x02d) => ex!{|s| shr_s a: u32,      b: u16;2      },
            (2, 2, 0x02d) => ex!{|s| shr_s a: u32,      b: u8;4       },

            (3, 0, 0x02d) => ex!{|s| shr_s a: u64,      b: u64;1      },
            (3, 1, 0x02d) => ex!{|s| shr_s a: u64,      b: u32;2      },
            (3, 2, 0x02d) => ex!{|s| shr_s a: u64,      b: u16;4      },
            (3, 3, 0x02d) => ex!{|s| shr_s a: u64,      b: u8;8       },

            (4, 0, 0x02d) => ex!{|s| shr_s a: u128,     b: u128;1     },
            (4, 1, 0x02d) => ex!{|s| shr_s a: u128,     b: u64;2      },
            (4, 2, 0x02d) => ex!{|s| shr_s a: u128,     b: u32;4      },
            (4, 3, 0x02d) => ex!{|s| shr_s a: u128,     b: u16;8      },
            (4, 4, 0x02d) => ex!{|s| shr_s a: u128,     b: u8;16      },

            (5, 0, 0x02d) => ex!{|s| shr_s a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x02d) => ex!{|s| shr_s a: [u128;2], b: u128;2     },
            (5, 2, 0x02d) => ex!{|s| shr_s a: [u128;2], b: u64;4      },
            (5, 3, 0x02d) => ex!{|s| shr_s a: [u128;2], b: u32;8      },
            (5, 4, 0x02d) => ex!{|s| shr_s a: [u128;2], b: u16;16     },
            (5, 5, 0x02d) => ex!{|s| shr_s a: [u128;2], b: u8;32      },

            (6, 0, 0x02d) => ex!{|s| shr_s a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x02d) => ex!{|s| shr_s a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x02d) => ex!{|s| shr_s a: [u128;4], b: u128;4     },
            (6, 3, 0x02d) => ex!{|s| shr_s a: [u128;4], b: u64;8      },
            (6, 4, 0x02d) => ex!{|s| shr_s a: [u128;4], b: u32;16     },
            (6, 5, 0x02d) => ex!{|s| shr_s a: [u128;4], b: u16;32     },
            (6, 6, 0x02d) => ex!{|s| shr_s a: [u128;4], b: u8;64      },

            // rotl
            (0, 0, 0x02e) => ex!{|s| rotl a: u8,       b: u8;1       },

            (1, 0, 0x02e) => ex!{|s| rotl a: u16,      b: u16;1      },
            (1, 1, 0x02e) => ex!{|s| rotl a: u16,      b: u8;2       },

            (2, 0, 0x02e) => ex!{|s| rotl a: u32,      b: u32;1      },
            (2, 1, 0x02e) => ex!{|s| rotl a: u32,      b: u16;2      },
            (2, 2, 0x02e) => ex!{|s| rotl a: u32,      b: u8;4       },

            (3, 0, 0x02e) => ex!{|s| rotl a: u64,      b: u64;1      },
            (3, 1, 0x02e) => ex!{|s| rotl a: u64,      b: u32;2      },
            (3, 2, 0x02e) => ex!{|s| rotl a: u64,      b: u16;4      },
            (3, 3, 0x02e) => ex!{|s| rotl a: u64,      b: u8;8       },

            (4, 0, 0x02e) => ex!{|s| rotl a: u128,     b: u128;1     },
            (4, 1, 0x02e) => ex!{|s| rotl a: u128,     b: u64;2      },
            (4, 2, 0x02e) => ex!{|s| rotl a: u128,     b: u32;4      },
            (4, 3, 0x02e) => ex!{|s| rotl a: u128,     b: u16;8      },
            (4, 4, 0x02e) => ex!{|s| rotl a: u128,     b: u8;16      },

            (5, 0, 0x02e) => ex!{|s| rotl a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x02e) => ex!{|s| rotl a: [u128;2], b: u128;2     },
            (5, 2, 0x02e) => ex!{|s| rotl a: [u128;2], b: u64;4      },
            (5, 3, 0x02e) => ex!{|s| rotl a: [u128;2], b: u32;8      },
            (5, 4, 0x02e) => ex!{|s| rotl a: [u128;2], b: u16;16     },
            (5, 5, 0x02e) => ex!{|s| rotl a: [u128;2], b: u8;32      },

            (6, 0, 0x02e) => ex!{|s| rotl a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x02e) => ex!{|s| rotl a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x02e) => ex!{|s| rotl a: [u128;4], b: u128;4     },
            (6, 3, 0x02e) => ex!{|s| rotl a: [u128;4], b: u64;8      },
            (6, 4, 0x02e) => ex!{|s| rotl a: [u128;4], b: u32;16     },
            (6, 5, 0x02e) => ex!{|s| rotl a: [u128;4], b: u16;32     },
            (6, 6, 0x02e) => ex!{|s| rotl a: [u128;4], b: u8;64      },

            // rotr
            (0, 0, 0x02f) => ex!{|s| rotr a: u8,       b: u8;1       },

            (1, 0, 0x02f) => ex!{|s| rotr a: u16,      b: u16;1      },
            (1, 1, 0x02f) => ex!{|s| rotr a: u16,      b: u8;2       },

            (2, 0, 0x02f) => ex!{|s| rotr a: u32,      b: u32;1      },
            (2, 1, 0x02f) => ex!{|s| rotr a: u32,      b: u16;2      },
            (2, 2, 0x02f) => ex!{|s| rotr a: u32,      b: u8;4       },

            (3, 0, 0x02f) => ex!{|s| rotr a: u64,      b: u64;1      },
            (3, 1, 0x02f) => ex!{|s| rotr a: u64,      b: u32;2      },
            (3, 2, 0x02f) => ex!{|s| rotr a: u64,      b: u16;4      },
            (3, 3, 0x02f) => ex!{|s| rotr a: u64,      b: u8;8       },

            (4, 0, 0x02f) => ex!{|s| rotr a: u128,     b: u128;1     },
            (4, 1, 0x02f) => ex!{|s| rotr a: u128,     b: u64;2      },
            (4, 2, 0x02f) => ex!{|s| rotr a: u128,     b: u32;4      },
            (4, 3, 0x02f) => ex!{|s| rotr a: u128,     b: u16;8      },
            (4, 4, 0x02f) => ex!{|s| rotr a: u128,     b: u8;16      },

            (5, 0, 0x02f) => ex!{|s| rotr a: [u128;2], b: [u128;2];1 },
            (5, 1, 0x02f) => ex!{|s| rotr a: [u128;2], b: u128;2     },
            (5, 2, 0x02f) => ex!{|s| rotr a: [u128;2], b: u64;4      },
            (5, 3, 0x02f) => ex!{|s| rotr a: [u128;2], b: u32;8      },
            (5, 4, 0x02f) => ex!{|s| rotr a: [u128;2], b: u16;16     },
            (5, 5, 0x02f) => ex!{|s| rotr a: [u128;2], b: u8;32      },

            (6, 0, 0x02f) => ex!{|s| rotr a: [u128;4], b: [u128;4];1 },
            (6, 1, 0x02f) => ex!{|s| rotr a: [u128;4], b: [u128;2];2 },
            (6, 2, 0x02f) => ex!{|s| rotr a: [u128;4], b: u128;4     },
            (6, 3, 0x02f) => ex!{|s| rotr a: [u128;4], b: u64;8      },
            (6, 4, 0x02f) => ex!{|s| rotr a: [u128;4], b: u32;16     },
            (6, 5, 0x02f) => ex!{|s| rotr a: [u128;4], b: u16;32     },
            (6, 6, 0x02f) => ex!{|s| rotr a: [u128;4], b: u8;64      },


            //// unknown instruction? ////

            // unknown instruction?
            _ => {
                Err(Error::InvalidOpcode_(ins))?
            },
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
        let example = OpTree_::add(0,
            OpTree_::imm(1u32.to_le_bytes()),
            OpTree_::imm(2u32.to_le_bytes())
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, mut stack) = example.compile(true);
        println!("  bytecode:");
        disas_(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        let result = exec_(&bytecode, &mut stack).unwrap();
        print!("  result:");
        for i in 0..result.len() {
            print!(" {:02x}", result[i]);
        }
        println!();

        assert_eq!(result, &[0x03, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn exec_add_parallel() {
        let example = OpTree_::add(2,
            OpTree_::imm(0x01020304u32.to_le_bytes()),
            OpTree_::imm(0x0506fffeu32.to_le_bytes())
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, mut stack) = example.compile(true);
        println!("  bytecode:");
        disas_(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        let result = exec_(&bytecode, &mut stack).unwrap();
        print!("  result:");
        for i in 0..result.len() {
            print!(" {:02x}", result[i]);
        }
        println!();

        assert_eq!(result, &[0x02, 0x02, 0x08, 0x06]);
    }


    #[test]
    fn exec_alignment() {
        let example = OpTree_::add(0,
            OpTree_::<[u8;2]>::extend_s(
                OpTree_::imm(2u8.to_le_bytes())
            ),
            OpTree_::<[u8;2]>::extract(0,
                OpTree_::imm(1u32.to_le_bytes()),
            ),
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, mut stack) = example.compile(true);
        println!("  bytecode:");
        disas_(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        let result = exec_(&bytecode, &mut stack).unwrap();
        print!("  result:");
        for i in 0..result.len() {
            print!(" {:02x}", result[i]);
        }
        println!();

        assert_eq!(result, &[0x03, 0x00]);
    }

    #[test]
    fn exec_dag() {
        let two = OpTree_::imm(2u32.to_le_bytes());
        let a = OpTree_::add(0,
            OpTree_::imm(1u32.to_le_bytes()),
            OpTree_::imm(2u32.to_le_bytes())
        );
        let b = OpTree_::shr_s(0,
            a.clone(), two.clone()
        );
        let c = OpTree_::shl(0,
            a.clone(), two.clone()
        );
        let example = OpTree_::eq(0,
            OpTree_::add(0,
                OpTree_::mul(0, b, two),
                c,
            ),
            a,
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, mut stack) = example.compile(true);
        println!("  bytecode:");
        disas_(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        let result = exec_(&bytecode, &mut stack).unwrap();
        print!("  result:");
        for i in 0..result.len() {
            print!(" {:02x}", result[i]);
        }
        println!();

        assert_eq!(result, &[0x00, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn exec_pythag() {
        let a = OpTree_::imm(3u32.to_le_bytes());
        let b = OpTree_::imm(4u32.to_le_bytes());
        let c = OpTree_::imm(5u32.to_le_bytes());
        let example = OpTree_::eq(0,
            OpTree_::add(0,
                OpTree_::mul(0, a.clone(), a),
                OpTree_::mul(0, b.clone(), b)
            ),
            OpTree_::mul(0, c.clone(), c)
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, mut stack) = example.compile(true);
        println!("  bytecode:");
        disas_(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        let result = exec_(&bytecode, &mut stack).unwrap();
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
        let a = OpTree_::const_(1u8.to_le_bytes());
        let b = OpTree_::const_(1u16.to_le_bytes());
        let c = OpTree_::imm(2u32.to_le_bytes());
        let d = OpTree_::imm(3u64.to_le_bytes());
        let e = OpTree_::const_(5u128.to_le_bytes());
        let fib_3 = OpTree_::add(0,
            OpTree_::<[u8;4]>::extend_u(b.clone()), OpTree_::<[u8;4]>::extend_u(a.clone())
        );
        let fib_4 = OpTree_::add(0,
            OpTree_::<[u8;8]>::extend_u(fib_3.clone()), OpTree_::<[u8;8]>::extend_u(b.clone())
        );
        let fib_5 = OpTree_::add(0,
            OpTree_::<[u8;16]>::extend_u(fib_4.clone()), OpTree_::<[u8;16]>::extend_u(fib_3.clone())
        );
        let example = OpTree_::and(
            OpTree_::and(
                OpTree_::<[u8;1]>::extract(0, OpTree_::eq(0, fib_3.clone(), c)),
                OpTree_::<[u8;1]>::extract(0, OpTree_::eq(0, fib_4.clone(), d))
            ),
            OpTree_::<[u8;1]>::extract(0, OpTree_::eq(0, fib_5.clone(), e))
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, mut stack) = example.compile(true);
        println!("  bytecode:");
        disas_(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        let result = exec_(&bytecode, &mut stack).unwrap();
        print!("  result:");
        for i in 0..result.len() {
            print!(" {:02x}", result[i]);
        }
        println!();

        assert_eq!(result, &[0xff]);
    }
//
//
//    #[test]
//    fn exec_add() {
//        let example = OpTree_::add(0,
//            OpTree_::imm(1u32.to_le_bytes()),
//            OpTree_::imm(2u32.to_le_bytes())
//        );
//
//        println!();
//        println!("input:");
//        example.disas(io::stdout()).unwrap();
//        let (bytecode, mut stack) = example.compile(true);
//        println!("  bytecode:");
//        disas_(&bytecode, io::stdout()).unwrap();
//        print!("  stack:");
//        for i in 0..stack.len() {
//            print!(" {:02x}", stack[i]);
//        }
//        println!();
//
//        let result = exec_(&bytecode, &mut stack).unwrap();
//        print!("  stack:");
//        for i in 0..result.len() {
//            print!(" {:02x}", result[i]);
//        }
//        println!();
//
//        assert_eq!(result, &[0x03, 0x00, 0x00, 0x00]);
//    }
//
//    #[test]
//    fn exec_add_parallel() {
//        let example = OpTree_::add(2,
//            OpTree_::imm(0x01020304u32.to_le_bytes()),
//            OpTree_::imm(0x0506fffeu32.to_le_bytes())
//        );
//
//        println!();
//        println!("input:");
//        example.disas(io::stdout()).unwrap();
//        let (bytecode, mut stack) = example.compile(true);
//        println!("  bytecode:");
//        disas_(&bytecode, io::stdout()).unwrap();
//        print!("  stack:");
//        for i in 0..stack.len() {
//            print!(" {:02x}", stack[i]);
//        }
//        println!();
//
//        let result = exec_(&bytecode, &mut stack).unwrap();
//        print!("  stack:");
//        for i in 0..result.len() {
//            print!(" {:02x}", result[i]);
//        }
//        println!();
//
//        assert_eq!(result, &[0x02, 0x02, 0x08, 0x06]);
//    }
//
//    #[test]
//    fn exec_alignment() {
//        let example = OpTree_::add(0,
//            OpTree_::<[u8;2]>::extend_s(
//                OpTree_::imm(2u8.to_le_bytes())
//            ),
//            OpTree_::<[u8;2]>::extract(0,
//                OpTree_::imm(1u32.to_le_bytes()),
//            ),
//        );
//
//        println!();
//        println!("input:");
//        example.disas(io::stdout()).unwrap();
//        let (bytecode, mut stack) = example.compile(true);
//        println!("  bytecode:");
//        disas_(&bytecode, io::stdout()).unwrap();
//        print!("  stack:");
//        for i in 0..stack.len() {
//            print!(" {:02x}", stack[i]);
//        }
//        println!();
//
//        let result = exec_(&bytecode, &mut stack).unwrap();
//        print!("  stack:");
//        for i in 0..result.len() {
//            print!(" {:02x}", result[i]);
//        }
//        println!();
//
//        assert_eq!(result, &[0x03, 0x00]);
//    }
//
//    #[test]
//    fn exec_dag() {
//        let two = OpTree::imm(2u32.to_le_bytes());
//        let a = OpTree::add(
//            OpTree::imm(1u32.to_le_bytes()),
//            OpTree::imm(2u32.to_le_bytes())
//        );
//        let b = OpTree::divu(
//            a.clone(), two.clone()
//        );
//        let c = OpTree::remu(
//            a.clone(), two.clone()
//        );
//        let example = OpTree::eq(
//            OpTree::add(
//                OpTree::mul(b, two),
//                c,
//            ),
//            a,
//        );
//
//        println!();
//        println!("input:");
//        example.disas(io::stdout()).unwrap();
//        let (bytecode, mut stack) = example.compile(true);
//        print!("  bytecode:");
//        for i in (0..bytecode.len()).step_by(2) {
//            print!(" {:04x}", u16::from_le_bytes(
//                <[u8; 2]>::try_from(&bytecode[i..i+2]).unwrap()
//            ));
//        }
//        println!();
//        disas(&bytecode, &mut io::stdout()).unwrap();
//        print!("  stack:");
//        for i in 0..stack.len() {
//            print!(" {:02x}", stack[i]);
//        }
//        println!();
//
//        let result = exec(&bytecode, &mut stack).unwrap();
//        print!("  stack:");
//        for i in 0..result.len() {
//            print!(" {:02x}", result[i]);
//        }
//        println!();
//
//        assert_eq!(result, &[0x01, 0x00, 0x00, 0x00]);
//    }
//
//    #[test]
//    fn exec_pythag() {
//        let a = OpTree::imm(3u32.to_le_bytes());
//        let b = OpTree::imm(4u32.to_le_bytes());
//        let c = OpTree::imm(5u32.to_le_bytes());
//        let example = OpTree::eq(
//            OpTree::add(
//                OpTree::mul(a.clone(), a),
//                OpTree::mul(b.clone(), b)
//            ),
//            OpTree::mul(c.clone(), c)
//        );
//
//        println!();
//        println!("input:");
//        example.disas(io::stdout()).unwrap();
//        let (bytecode, mut stack) = example.compile(true);
//        print!("  bytecode:");
//        for i in (0..bytecode.len()).step_by(2) {
//            print!(" {:04x}", u16::from_le_bytes(
//                <[u8; 2]>::try_from(&bytecode[i..i+2]).unwrap()
//            ));
//        }
//        println!();
//        disas(&bytecode, &mut io::stdout()).unwrap();
//        print!("  stack:");
//        for i in 0..stack.len() {
//            print!(" {:02x}", stack[i]);
//        }
//        println!();
//
//        let result = exec(&bytecode, &mut stack).unwrap();
//        print!("  stack:");
//        for i in 0..result.len() {
//            print!(" {:02x}", result[i]);
//        }
//        println!();
//
//        assert_eq!(result, &[0x01, 0x00, 0x00, 0x00]);
//    }


    // tests for individual instructions
    macro_rules! test_ins {
        () => {};
        (
            $name:ident { $op:ident($($a:expr),+) => $expected:expr}
            $($rest:tt)*
        ) => {
            test_ins! {
                $name { $op(; $($a),+) => $expected }
                $($rest)*
            }
        };
        (
            $name:ident { $op:ident($($l:expr)?; $($a:expr),+) => $expected:expr }
            $($rest:tt)*
        ) => {
            #[test]
            fn $name() {
                let input = OpTree_::$op(
                    $(
                        $l,
                    )?
                    $(
                        OpTree_::imm($a)
                    ),+
                );

                println!();
                println!("input:");
                input.disas(io::stdout()).unwrap();
                let (bytecode, mut stack) = input.compile(true);
                println!("  bytecode:");
                disas_(&bytecode, io::stdout()).unwrap();
                print!("  stack:");
                for i in 0..stack.len() {
                    print!(" {:02x}", stack[i]);
                }
                println!();

                let result = exec_(&bytecode, &mut stack).unwrap();
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
        ins_select_t   { select(0; [1,0,0,0], [2,0,0,0], [3,0,0,0]) => [2,0,0,0] }
        ins_select_f   { select(0; [0,0,0,0], [2,0,0,0], [3,0,0,0]) => [3,0,0,0] }
        ins_select_par { select(2; [1,0,1,0], [2,3,4,5], [6,7,8,9]) => [2,7,4,9] }

        ins_shuffle  { shuffle(2; [3,2,0xff,0], [5,6,7,8]) => [8,7,0,5] }

        ins_none { none(  [0,0,1,0]) => [0x00,0x00,0x00,0x00] }
        ins_any  { any(   [0,0,1,0]) => [0xff,0xff,0xff,0xff] }
        ins_all  { all(0; [1,1,1,1]) => [0xff,0xff,0xff,0xff] }

        ins_eq     { eq(0; [1,2,3,0xff], [1,3,3,0]) => [0x00,0x00,0x00,0x00] }
        ins_eq_par { eq(2; [1,2,3,0xff], [1,3,3,0]) => [0xff,0x00,0xff,0x00] }
        ins_ne     { ne(0; [1,2,3,0xff], [1,3,3,0]) => [0xff,0xff,0xff,0xff] }
        ins_ne_par { ne(2; [1,2,3,0xff], [1,3,3,0]) => [0x00,0xff,0x00,0xff] }
        ins_lt_u     { lt_u(0; [1,2,3,0xff], [1,3,3,0]) => [0x00,0x00,0x00,0x00] }
        ins_lt_u_par { lt_u(2; [1,2,3,0xff], [1,3,3,0]) => [0x00,0xff,0x00,0x00] }
        ins_lt_s     { lt_s(0; [1,2,3,0xff], [1,3,3,0]) => [0xff,0xff,0xff,0xff] }
        ins_lt_s_par { lt_s(2; [1,2,3,0xff], [1,3,3,0]) => [0x00,0xff,0x00,0xff] }
        ins_gt_u     { gt_u(0; [1,2,3,0xff], [1,3,3,0]) => [0xff,0xff,0xff,0xff] }
        ins_gt_u_par { gt_u(2; [1,2,3,0xff], [1,3,3,0]) => [0x00,0x00,0x00,0xff] }
        ins_gt_s     { gt_s(0; [1,2,3,0xff], [1,3,3,0]) => [0x00,0x00,0x00,0x00] }
        ins_gt_s_par { gt_s(2; [1,2,3,0xff], [1,3,3,0]) => [0x00,0x00,0x00,0x00] }
        ins_le_u     { le_u(0; [1,2,3,0xff], [1,3,3,0]) => [0x00,0x00,0x00,0x00] }
        ins_le_u_par { le_u(2; [1,2,3,0xff], [1,3,3,0]) => [0xff,0xff,0xff,0x00] }
        ins_le_s     { le_s(0; [1,2,3,0xff], [1,3,3,0]) => [0xff,0xff,0xff,0xff] }
        ins_le_s_par { le_s(2; [1,2,3,0xff], [1,3,3,0]) => [0xff,0xff,0xff,0xff] }
        ins_ge_u     { ge_u(0; [1,2,3,0xff], [1,3,3,0]) => [0xff,0xff,0xff,0xff] }
        ins_ge_u_par { ge_u(2; [1,2,3,0xff], [1,3,3,0]) => [0xff,0x00,0xff,0xff] }
        ins_ge_s     { ge_s(0; [1,2,3,0xff], [1,3,3,0]) => [0x00,0x00,0x00,0x00] }
        ins_ge_s_par { ge_s(2; [1,2,3,0xff], [1,3,3,0]) => [0xff,0x00,0xff,0x00] }
        ins_min_u     { min_u(0; [1,2,3,0xff], [1,3,3,0]) => [1,3,3,   0] }
        ins_min_u_par { min_u(2; [1,2,3,0xff], [1,3,3,0]) => [1,2,3,   0] }
        ins_min_s     { min_s(0; [1,2,3,0xff], [1,3,3,0]) => [1,2,3,0xff] }
        ins_min_s_par { min_s(2; [1,2,3,0xff], [1,3,3,0]) => [1,2,3,0xff] }
        ins_max_u     { max_u(0; [1,2,3,0xff], [1,3,3,0]) => [1,2,3,0xff] }
        ins_max_u_par { max_u(2; [1,2,3,0xff], [1,3,3,0]) => [1,3,3,0xff] }
        ins_max_s     { max_s(0; [1,2,3,0xff], [1,3,3,0]) => [1,3,3,   0] }
        ins_max_s_par { max_s(2; [1,2,3,0xff], [1,3,3,0]) => [1,3,3,   0] }

        ins_neg        { neg(0;    [0x00,0xfe,0x02,0xff]) => [0x00,0x02,0xfd,0x00] } 
        ins_neg_par    { neg(2;    [0x00,0xfe,0x02,0xff]) => [0x00,0x02,0xfe,0x01] }
        ins_abs        { abs(0;    [0x00,0xfe,0x02,0xff]) => [0x00,0x02,0xfd,0x00] } 
        ins_abs_par    { abs(2;    [0x00,0xfe,0x02,0xff]) => [0x00,0x02,0x02,0x01] }
        ins_not        { not(      [0x00,0xfe,0x02,0xff]) => [0xff,0x01,0xfd,0x00] } 
        ins_clz        { clz(0;    [0x00,0xfe,0x02,0xff]) => [0x00,0x00,0x00,0x00] } 
        ins_clz_par    { clz(2;    [0x00,0xfe,0x02,0xff]) => [0x08,0x00,0x06,0x00] } 
        ins_ctz        { ctz(0;    [0x00,0xfe,0x02,0xff]) => [0x09,0x00,0x00,0x00] } 
        ins_ctz_par    { ctz(2;    [0x00,0xfe,0x02,0xff]) => [0x08,0x01,0x01,0x00] } 
        ins_popcnt     { popcnt(0; [0x00,0xfe,0x02,0xff]) => [0x10,0x00,0x00,0x00] } 
        ins_popcnt_par { popcnt(2; [0x00,0xfe,0x02,0xff]) => [0x00,0x07,0x01,0x08] } 

        ins_add     { add(0; [0xff,0x02,0x03,0x04], [0xff,0x06,0x07,0x08]) => [0xfe,0x09,0x0a,0x0c] }
        ins_add_par { add(2; [0xff,0x02,0x03,0x04], [0xff,0x06,0x07,0x08]) => [0xfe,0x08,0x0a,0x0c] }
        ins_sub     { sub(0; [0xff,0x02,0x03,0x04], [0xff,0x06,0x07,0x08]) => [0x00,0xfc,0xfb,0xfb] }
        ins_sub_par { sub(2; [0xff,0x02,0x03,0x04], [0xff,0x06,0x07,0x08]) => [0x00,0xfc,0xfc,0xfc] }
        ins_mul     { mul(0; [0xff,0x02,0x03,0x04], [0xff,0x06,0x07,0x08]) => [0x01,0xf6,0x0a,0x1e] }
        ins_mul_par { mul(2; [0xff,0x02,0x03,0x04], [0xff,0x06,0x07,0x08]) => [0x01,0x0c,0x15,0x20] }
        ins_and     { and(   [0xff,0x02,0x03,0x04], [0xff,0x06,0x07,0x08]) => [0xff,0x02,0x03,0x00] }
        ins_andnot  { andnot([0xff,0x02,0x03,0x04], [0xff,0x06,0x07,0x08]) => [0x00,0x00,0x00,0x04] }
        ins_or      { or(    [0xff,0x02,0x03,0x04], [0xff,0x06,0x07,0x08]) => [0xff,0x06,0x07,0x0c] }
        ins_xor     { xor(   [0xff,0x02,0x03,0x04], [0xff,0x06,0x07,0x08]) => [0x00,0x04,0x04,0x0c] }

        ins_shl       { shl(0;   [0xff,0x02,0x03,0x04], [0x03,0x00,0x00,0x00]) => [0xf8,0x17,0x18,0x20] }
        ins_shl_par   { shl(2;   [0xff,0x02,0x03,0x04], [0x03,0x03,0x03,0x03]) => [0xf8,0x10,0x18,0x20] }
        ins_shr_u     { shr_u(0; [0xff,0x02,0x03,0x04], [0x03,0x00,0x00,0x00]) => [0x5f,0x60,0x80,0x00] }
        ins_shr_u_par { shr_u(2; [0xff,0x02,0x03,0x04], [0x03,0x03,0x03,0x03]) => [0x1f,0x00,0x00,0x00] }
        ins_shr_s     { shr_s(0; [0xff,0x02,0x03,0x04], [0x03,0x00,0x00,0x00]) => [0x5f,0x60,0x80,0x00] }
        ins_shr_s_par { shr_s(2; [0xff,0x02,0x03,0x04], [0x03,0x03,0x03,0x03]) => [0xff,0x00,0x00,0x00] }
        ins_rotl      { rotl(0;  [0xff,0x02,0x03,0x04], [0x03,0x00,0x00,0x00]) => [0xf8,0x17,0x18,0x20] }
        ins_rotl_par  { rotl(2;  [0xff,0x02,0x03,0x04], [0x03,0x03,0x03,0x03]) => [0xff,0x10,0x18,0x20] }
        ins_rotr      { rotr(0;  [0xff,0x02,0x03,0x04], [0x03,0x00,0x00,0x00]) => [0x5f,0x60,0x80,0xe0] }
        ins_rotr_par  { rotr(2;  [0xff,0x02,0x03,0x04], [0x03,0x03,0x03,0x03]) => [0xff,0x40,0x60,0x80] }

//add
//sub
//mul
//and
//andnot
//or
//xor
//shl
//shr_u
//shr_s
//rotl
//rotr
    }

//    // tests for low-level instructions
//    macro_rules! test_ins {
//        (@arr u8)   => { [u8;1]  };
//        (@arr u16)  => { [u8;2]  };
//        (@arr u32)  => { [u8;4]  };
//        (@arr u64)  => { [u8;8]  };
//        (@arr u128) => { [u8;16] };
//        ($name:ident, $op:ident, $u:ident, $($a:expr),+ => $t:ident, $expected:expr) => {
//            #[test]
//            fn $name() {
//                let input = OpTree::<test_ins!(@arr $t)>::$op(
//                    $(
//                        OpTree::imm(($a as $u).to_le_bytes())
//                    ),+
//                );
//
//                println!();
//                let (bytecode, mut stack) = input.compile(true);
//                print!("  bytecode:");
//                for i in (0..bytecode.len()).step_by(2) {
//                    print!(" {:04x}", u16::from_le_bytes(
//                        <[u8; 2]>::try_from(&bytecode[i..i+2]).unwrap()
//                    ));
//                }
//                println!();
//                print!("  stack:");
//                for i in 0..stack.len() {
//                    print!(" {:02x}", stack[i]);
//                }
//                println!();
//
//                let result = exec(&bytecode, &mut stack).unwrap();
//                let result = <$t>::load(&result, 0).unwrap();
//                input.disas(io::stdout()).unwrap();
//                println!("=> {}", result);
//
//                assert_eq!(result, $expected);
//            }
//        };
//        ($name:ident, $op:ident, $t:ident, $($a:expr),+ => $expected:expr) => {
//            test_ins! { $name, $op, $t, $($a),+ => $t, $expected }
//        };
//    }
//
//    test_ins! { ins_truncate, truncate, u32, 0x12345678 => u8, 0x78 }
//    test_ins! { ins_extends,  extends, u8, 0x85 => u32, 0xffffff85 }
//    test_ins! { ins_extendu,  extendu, u8, 0x85 => u32, 0x00000085 }
//
//    test_ins! { ins_select1, select, u32, 1, 2, 3 => 2}
//    test_ins! { ins_select2, select, u32, 0, 2, 3 => 3}
//
//    test_ins! { ins_eqz, eqz, u32, 0    => 1 }
//    test_ins! { ins_eq,  eq,  u32, 2, 2 => 1 }
//    test_ins! { ins_ne,  ne,  u32, 2, 3 => 1 }
//    test_ins! { ins_lts, lts, u8, 0xff, 1 => 1 }
//    test_ins! { ins_ltu, ltu, u8, 0xff, 1 => 0 }
//    test_ins! { ins_gts, gts, u8, 0xff, 1 => 0 }
//    test_ins! { ins_gtu, gtu, u8, 0xff, 1 => 1 }
//    test_ins! { ins_les, les, u8, 0xff, 1 => 1 }
//    test_ins! { ins_leu, leu, u8, 0xff, 1 => 0 }
//    test_ins! { ins_ges, ges, u8, 0xff, 1 => 0 }
//    test_ins! { ins_geu, geu, u8, 0xff, 1 => 1 }
//
//    test_ins! { ins_clz,    clz,    u16, 0x1234 => 3 }
//    test_ins! { ins_ctz,    ctz,    u16, 0x1234 => 2 }
//    test_ins! { ins_popcnt, popcnt, u16, 0x1234 => 5 }
//    test_ins! { ins_add, add, u32, 1, 2 => 3 }
//    test_ins! { ins_sub, sub, u32, 2, 1 => 1 }
//    test_ins! { ins_mul, mul, u32, 2, 3 => 6 }
//    test_ins! { ins_divs, divs, u8,  0xfd, 2 => 0xff }
//    test_ins! { ins_divu, divu, u32, 7,    2 => 3    }
//    test_ins! { ins_rems, rems, u8,  0xfd, 2 => 0xff }
//    test_ins! { ins_remu, remu, u32, 7,    2 => 1    }
//    test_ins! { ins_and, and, u16, 0x4321, 0x1234 => 0x0220 }
//    test_ins! { ins_or,  or,  u16, 0x4321, 0x1234 => 0x5335 }
//    test_ins! { ins_xor, xor, u16, 0x4321, 0x1234 => 0x5115 }
//    test_ins! { ins_shl,  shl,  u16, 0x89ab, 7 => 0xd580 }
//    test_ins! { ins_shrs, shrs, u16, 0x89ab, 7 => 0xff13 }
//    test_ins! { ins_shru, shru, u16, 0x89ab, 7 => 0x0113 }
//    test_ins! { ins_rotl, rotl, u16, 0x89ab, 7 => 0xd5c4 }
//    test_ins! { ins_rotr, rotr, u16, 0x89ab, 7 => 0x5713 }
}


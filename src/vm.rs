
use crate::Secret;
use crate::error::Error;
use std::mem::size_of;

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


//// instructions here ////

// get
macro_rules! ins_get {
    ($t:ty, $imm:expr, $stack:expr, $sp:expr) => {{
        let v = <$t>::load($stack, $imm as usize * size_of::<$t>())?;
        <$t>::push($stack, &mut $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $imm:expr, $stack:expr, $sp:expr) => {{
        let width = 1 << $npw2 as usize;
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

// extends
macro_rules! ins_extends {
    ($t:ty, $imm:expr, $stack:expr, $sp:expr) => {{
        let v = <$t>::load($stack, $sp)?;

        $sp = $sp.checked_sub($imm as usize * size_of::<$t>())
            .ok_or_else(|| Error::OutOfBounds)?;
        $stack.get_mut(
                $sp + size_of::<$t>()
                    .. $sp + (($imm as usize + 1) * size_of::<$t>())
            )
            .ok_or_else(|| Error::OutOfBounds)?
            .fill(
                if (v as i32) < 0 {
                    0xff
                } else {
                    0x00
                }
            );

        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $imm:expr, $stack:expr, $sp:expr) => {{
        let _ = ($npw2, $imm);
        todo!()
    }};
}

// extendu
macro_rules! ins_extendu {
    ($t:ty, $imm:expr, $stack:expr, $sp:expr) => {{
        let v = <$t>::load($stack, $sp)?;

        $sp = $sp.checked_sub($imm as usize * size_of::<$t>())
            .ok_or_else(|| Error::OutOfBounds)?;
        $stack.get_mut(
                $sp + size_of::<$t>()
                    .. $sp + (($imm as usize + 1) * size_of::<$t>())
            )
            .ok_or_else(|| Error::OutOfBounds)?
            .fill(0x00);

        <$t>::store($stack, $sp, v)?;
    }};
    (>$t:ty, $npw2:expr, $imm:expr, $stack:expr, $sp:expr) => {{
        let _ = ($npw2, $imm);
        todo!()
    }};
}

// align
macro_rules! ins_align {
    ($t:ty, $imm:expr, $stack:expr, $sp:expr) => {{
        // align just moves stack pointer around
        $sp = $sp.checked_sub($imm as usize * size_of::<$t>())
            .ok_or_else(|| Error::OutOfBounds)?;
    }};
    (>$t:ty, $npw2:expr, $imm:expr, $stack:expr, $sp:expr) => {{
        let _ = ($npw2, $imm);
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
pub unsafe fn exec<'a>(
    bytecode: &[u8],
    stack: &'a mut Secret<Vec<u8>>
) -> Result<Secret<&'a [u8]>, Error> {
    // Setup VM
    if bytecode.as_ptr() as usize % 2 != 0 || bytecode.len() % 2 != 0{
        Err(Error::Unaligned)?;
    }

    let stack = stack.as_mut().declassify();
    let mut sp = stack.len();

    for i in (0..bytecode.len()).step_by(2) {
        let op = u16::load_unchecked(bytecode, i);
    
        let opcode = ((op & 0xf000) >> 8) as u8;
        let npw2 = ((op & 0x0f00) >> 8) as u8;
        let imm = (op & 0x00ff) as u8;

        #[cfg(feature="trace")]
        {
            print!("    exec {:#04x} ::", op);
            for i in 0..stack.len() {
                print!(" {:02x}", stack[i]);
            }
            println!();
        }

        match (opcode, npw2, imm) {
            // unreachable
            (0x00, _, _) => {
                Err(Error::Unreachable)?
            }

            // nop
            (0x10, _, _) => {
                // do nothing
            }

            // get
            (0x20, 0,    imm) => ins_get!(u8,         imm, stack, sp),
            (0x20, 1,    imm) => ins_get!(u16,        imm, stack, sp),
            (0x20, 2,    imm) => ins_get!(u32,        imm, stack, sp),
            (0x20, npw2, imm) => ins_get!(>u32, npw2, imm, stack, sp),

            // set
            (0x30, 0,    imm) => ins_set!(u8,         imm, stack, sp),
            (0x30, 1,    imm) => ins_set!(u16,        imm, stack, sp),
            (0x30, 2,    imm) => ins_set!(u32,        imm, stack, sp),
            (0x30, npw2, imm) => ins_set!(>u32, npw2, imm, stack, sp),

            // truncate
            (0x40, 0,    imm) => ins_truncate!(u8,         imm, stack, sp),
            (0x40, 1,    imm) => ins_truncate!(u16,        imm, stack, sp),
            (0x40, 2,    imm) => ins_truncate!(u32,        imm, stack, sp),
            (0x40, npw2, imm) => ins_truncate!(>u32, npw2, imm, stack, sp),

            // extends
            (0x50, 0,    imm) => ins_extends!(u8,         imm, stack, sp),
            (0x50, 1,    imm) => ins_extends!(u16,        imm, stack, sp),
            (0x50, 2,    imm) => ins_extends!(u32,        imm, stack, sp),
            (0x50, npw2, imm) => ins_extends!(>u32, npw2, imm, stack, sp),

            // extendu
            (0x60, 0,    imm) => ins_extendu!(u8,         imm, stack, sp),
            (0x60, 1,    imm) => ins_extendu!(u16,        imm, stack, sp),
            (0x60, 2,    imm) => ins_extendu!(u32,        imm, stack, sp),
            (0x60, npw2, imm) => ins_extendu!(>u32, npw2, imm, stack, sp),

            // align
            (0x70, 0,    imm) => ins_align!(u8,         imm, stack, sp),
            (0x70, 1,    imm) => ins_align!(u16,        imm, stack, sp),
            (0x70, 2,    imm) => ins_align!(u32,        imm, stack, sp),
            (0x70, npw2, imm) => ins_align!(>u32, npw2, imm, stack, sp),

            // select
            (0xf0, 0,    0x00) => ins_select!(u8,         stack, sp),
            (0xf0, 1,    0x00) => ins_select!(u16,        stack, sp),
            (0xf0, 2,    0x00) => ins_select!(u32,        stack, sp),
            (0xf0, npw2, 0x00) => ins_select!(>u32, npw2, stack, sp),

            // eqz
            (0xf0, 0,    0x01) => ins_eqz!(u8,         stack, sp),
            (0xf0, 1,    0x01) => ins_eqz!(u16,        stack, sp),
            (0xf0, 2,    0x01) => ins_eqz!(u32,        stack, sp),
            (0xf0, npw2, 0x01) => ins_eqz!(>u32, npw2, stack, sp),

            // eq
            (0xf0, 0,    0x02) => ins_eq!(u8,         stack, sp),
            (0xf0, 1,    0x02) => ins_eq!(u16,        stack, sp),
            (0xf0, 2,    0x02) => ins_eq!(u32,        stack, sp),
            (0xf0, npw2, 0x02) => ins_eq!(>u32, npw2, stack, sp),

            // ne
            (0xf0, 0,    0x03) => ins_ne!(u8,         stack, sp),
            (0xf0, 1,    0x03) => ins_ne!(u16,        stack, sp),
            (0xf0, 2,    0x03) => ins_ne!(u32,        stack, sp),
            (0xf0, npw2, 0x03) => ins_ne!(>u32, npw2, stack, sp),

            // lts
            (0xf0, 0,    0x04) => ins_lts!(u8,   i8,        stack, sp),
            (0xf0, 1,    0x04) => ins_lts!(u16,  i16,       stack, sp),
            (0xf0, 2,    0x04) => ins_lts!(u32,  i32,       stack, sp),
            (0xf0, npw2, 0x04) => ins_lts!(>u32, i32, npw2, stack, sp),

            // ltu
            (0xf0, 0,    0x05) => ins_ltu!(u8,         stack, sp),
            (0xf0, 1,    0x05) => ins_ltu!(u16,        stack, sp),
            (0xf0, 2,    0x05) => ins_ltu!(u32,        stack, sp),
            (0xf0, npw2, 0x05) => ins_ltu!(>u32, npw2, stack, sp),

            // gts
            (0xf0, 0,    0x06) => ins_gts!(u8,   i8,        stack, sp),
            (0xf0, 1,    0x06) => ins_gts!(u16,  i16,       stack, sp),
            (0xf0, 2,    0x06) => ins_gts!(u32,  i32,       stack, sp),
            (0xf0, npw2, 0x06) => ins_gts!(>u32, i32, npw2, stack, sp),

            // gtu
            (0xf0, 0,    0x07) => ins_gtu!(u8,         stack, sp),
            (0xf0, 1,    0x07) => ins_gtu!(u16,        stack, sp),
            (0xf0, 2,    0x07) => ins_gtu!(u32,        stack, sp),
            (0xf0, npw2, 0x07) => ins_gtu!(>u32, npw2, stack, sp),

            // les
            (0xf0, 0,    0x08) => ins_les!(u8,   i8,        stack, sp),
            (0xf0, 1,    0x08) => ins_les!(u16,  i16,       stack, sp),
            (0xf0, 2,    0x08) => ins_les!(u32,  i32,       stack, sp),
            (0xf0, npw2, 0x08) => ins_les!(>u32, i32, npw2, stack, sp),

            // leu
            (0xf0, 0,    0x09) => ins_leu!(u8,         stack, sp),
            (0xf0, 1,    0x09) => ins_leu!(u16,        stack, sp),
            (0xf0, 2,    0x09) => ins_leu!(u32,        stack, sp),
            (0xf0, npw2, 0x09) => ins_leu!(>u32, npw2, stack, sp),

            // ges
            (0xf0, 0,    0x0a) => ins_ges!(u8,   i8,        stack, sp),
            (0xf0, 1,    0x0a) => ins_ges!(u16,  i16,       stack, sp),
            (0xf0, 2,    0x0a) => ins_ges!(u32,  i32,       stack, sp),
            (0xf0, npw2, 0x0a) => ins_ges!(>u32, i32, npw2, stack, sp),

            // geu
            (0xf0, 0,    0x0b) => ins_geu!(u8,         stack, sp),
            (0xf0, 1,    0x0b) => ins_geu!(u16,        stack, sp),
            (0xf0, 2,    0x0b) => ins_geu!(u32,        stack, sp),
            (0xf0, npw2, 0x0b) => ins_geu!(>u32, npw2, stack, sp),

            // clz
            (0xf0, 0,    0x0c) => ins_clz!(u8,         stack, sp),
            (0xf0, 1,    0x0c) => ins_clz!(u16,        stack, sp),
            (0xf0, 2,    0x0c) => ins_clz!(u32,        stack, sp),
            (0xf0, npw2, 0x0c) => ins_clz!(>u32, npw2, stack, sp),

            // ctz
            (0xf0, 0,    0x0d) => ins_ctz!(u8,         stack, sp),
            (0xf0, 1,    0x0d) => ins_ctz!(u16,        stack, sp),
            (0xf0, 2,    0x0d) => ins_ctz!(u32,        stack, sp),
            (0xf0, npw2, 0x0d) => ins_ctz!(>u32, npw2, stack, sp),

            // popcnt
            (0xf0, 0,    0x0e) => ins_popcnt!(u8,         stack, sp),
            (0xf0, 1,    0x0e) => ins_popcnt!(u16,        stack, sp),
            (0xf0, 2,    0x0e) => ins_popcnt!(u32,        stack, sp),
            (0xf0, npw2, 0x0e) => ins_popcnt!(>u32, npw2, stack, sp),

            // add
            (0xf0, 0,    0x0f) => ins_add!(u8,         stack, sp),
            (0xf0, 1,    0x0f) => ins_add!(u16,        stack, sp),
            (0xf0, 2,    0x0f) => ins_add!(u32,        stack, sp),
            (0xf0, npw2, 0x0f) => ins_add!(>u32, npw2, stack, sp),

            // sub
            (0xf0, 0,    0x10) => ins_sub!(u8,         stack, sp),
            (0xf0, 1,    0x10) => ins_sub!(u16,        stack, sp),
            (0xf0, 2,    0x10) => ins_sub!(u32,        stack, sp),
            (0xf0, npw2, 0x10) => ins_sub!(>u32, npw2, stack, sp),

            // mul 
            (0xf0, 0,    0x11) => ins_mul!(u8,         stack, sp),
            (0xf0, 1,    0x11) => ins_mul!(u16,        stack, sp),
            (0xf0, 2,    0x11) => ins_mul!(u32,        stack, sp),
            (0xf0, npw2, 0x11) => ins_mul!(>u32, npw2, stack, sp),

            // divs
            (0xf0, 0,    0x12) => ins_divs!(u8,   i8,        stack, sp),
            (0xf0, 1,    0x12) => ins_divs!(u16,  i16,       stack, sp),
            (0xf0, 2,    0x12) => ins_divs!(u32,  i32,       stack, sp),
            (0xf0, npw2, 0x12) => ins_divs!(>u32, i32, npw2, stack, sp),

            // divu
            (0xf0, 0,    0x13) => ins_divu!(u8,         stack, sp),
            (0xf0, 1,    0x13) => ins_divu!(u16,        stack, sp),
            (0xf0, 2,    0x13) => ins_divu!(u32,        stack, sp),
            (0xf0, npw2, 0x13) => ins_divu!(>u32, npw2, stack, sp),

            // rems
            (0xf0, 0,    0x14) => ins_rems!(u8,   i8,        stack, sp),
            (0xf0, 1,    0x14) => ins_rems!(u16,  i16,       stack, sp),
            (0xf0, 2,    0x14) => ins_rems!(u32,  i32,       stack, sp),
            (0xf0, npw2, 0x14) => ins_rems!(>u32, i32, npw2, stack, sp),

            // remu
            (0xf0, 0,    0x15) => ins_remu!(u8,         stack, sp),
            (0xf0, 1,    0x15) => ins_remu!(u16,        stack, sp),
            (0xf0, 2,    0x15) => ins_remu!(u32,        stack, sp),
            (0xf0, npw2, 0x15) => ins_remu!(>u32, npw2, stack, sp),

            // and
            (0xf0, 0,    0x16) => ins_and!(u8,         stack, sp),
            (0xf0, 1,    0x16) => ins_and!(u16,        stack, sp),
            (0xf0, 2,    0x16) => ins_and!(u32,        stack, sp),
            (0xf0, npw2, 0x16) => ins_and!(>u32, npw2, stack, sp),

            // or
            (0xf0, 0,    0x17) => ins_or!(u8,         stack, sp),
            (0xf0, 1,    0x17) => ins_or!(u16,        stack, sp),
            (0xf0, 2,    0x17) => ins_or!(u32,        stack, sp),
            (0xf0, npw2, 0x17) => ins_or!(>u32, npw2, stack, sp),

            // xor
            (0xf0, 0,    0x18) => ins_xor!(u8,         stack, sp),
            (0xf0, 1,    0x18) => ins_xor!(u16,        stack, sp),
            (0xf0, 2,    0x18) => ins_xor!(u32,        stack, sp),
            (0xf0, npw2, 0x18) => ins_xor!(>u32, npw2, stack, sp),

            // shl
            (0xf0, 0,    0x19) => ins_shl!(u8,         stack, sp),
            (0xf0, 1,    0x19) => ins_shl!(u16,        stack, sp),
            (0xf0, 2,    0x19) => ins_shl!(u32,        stack, sp),
            (0xf0, npw2, 0x19) => ins_shl!(>u32, npw2, stack, sp),

            // shrs
            (0xf0, 0,    0x1a) => ins_shrs!(u8,   i8,        stack, sp),
            (0xf0, 1,    0x1a) => ins_shrs!(u16,  i16,       stack, sp),
            (0xf0, 2,    0x1a) => ins_shrs!(u32,  i32,       stack, sp),
            (0xf0, npw2, 0x1a) => ins_shrs!(>u32, i32, npw2, stack, sp),

            // shru
            (0xf0, 0,    0x1b) => ins_shru!(u8,         stack, sp),
            (0xf0, 1,    0x1b) => ins_shru!(u16,        stack, sp),
            (0xf0, 2,    0x1b) => ins_shru!(u32,        stack, sp),
            (0xf0, npw2, 0x1b) => ins_shru!(>u32, npw2, stack, sp),

            // rotl
            (0xf0, 0,    0x1c) => ins_rotl!(u8,         stack, sp),
            (0xf0, 1,    0x1c) => ins_rotl!(u16,        stack, sp),
            (0xf0, 2,    0x1c) => ins_rotl!(u32,        stack, sp),
            (0xf0, npw2, 0x1c) => ins_rotl!(>u32, npw2, stack, sp),

            // rotr
            (0xf0, 0,    0x1d) => ins_rotr!(u8,         stack, sp),
            (0xf0, 1,    0x1d) => ins_rotr!(u16,        stack, sp),
            (0xf0, 2,    0x1d) => ins_rotr!(u32,        stack, sp),
            (0xf0, npw2, 0x1d) => ins_rotr!(>u32, npw2, stack, sp),

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
    Ok(Secret::new(&stack[sp..]))
}

/// Execute the simple crypto-VM, expecting the resulting type
///
/// NOTE! This is a quick simulated VM for testing and proof-of-concept!
/// Not constant time!
// TODO can we avoid exposing LoadStore publically?
pub unsafe fn eval<T: LoadStore>(
    bytecode: &[u8],
    stack: &mut Secret<Vec<u8>>
) -> Result<T, Error> {
    let result = exec(bytecode, stack)?;
    let result = result.declassify();

    if result.len() != size_of::<T>() {
        Err(Error::InvalidResult)?;
    }

    T::load(&result, 0)
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::opcode::*;
    use std::convert::TryFrom;
    use std::rc::Rc;
    use std::io;

    #[test]
    fn exec_add() {
        let example = OpTree::new(OpKind::<u32>::Add(
            Rc::new(OpTree::new(OpKind::<u32>::Imm(1))),
            Rc::new(OpTree::new(OpKind::<u32>::Imm(2)))
        ));

        println!();
        println!("input: {}", example);
        let (bytecode, stack) = example.compile();
        let stack = unsafe { stack.declassify() };
        print!("  bytecode:");
        for i in (0..bytecode.len()).step_by(2) {
            print!(" {:04x}", u16::from_le_bytes(
                <[u8; 2]>::try_from(&bytecode[i..i+2]).unwrap()
            ));
        }
        println!();
        disas(&bytecode, &mut io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 3*2);
        assert_eq!(stack.len(), 4*4);

        let mut stack = Secret::new(stack);
        let result = unsafe { exec(&bytecode, &mut stack) };
        let result = result.unwrap();
        let result = unsafe { result.declassify() };
        print!("  stack:");
        for i in 0..result.len() {
            print!(" {:02x}", result[i]);
        }
        println!();

        assert_eq!(result, &[0x03, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn exec_alignment() {
        let example = OpTree::new(OpKind::<u16>::Add(
            Rc::new(OpTree::new(OpKind::<u16>::Extends(
                Rc::new(OpTree::new(OpKind::<u8>::Imm(2)))
            ))),
            Rc::new(OpTree::new(OpKind::<u16>::Truncate(
                Rc::new(OpTree::new(OpKind::<u32>::Imm(1))),
            ))),
        ));

        println!();
        println!("input: {}", example);
        let (bytecode, stack) = example.compile();
        let stack = unsafe { stack.declassify() };
        print!("  bytecode:");
        for i in (0..bytecode.len()).step_by(2) {
            print!(" {:04x}", u16::from_le_bytes(
                <[u8; 2]>::try_from(&bytecode[i..i+2]).unwrap()
            ));
        }
        println!();
        disas(&bytecode, &mut io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 6*2);
        assert_eq!(stack.len(), 4*4);

        let mut stack = Secret::new(stack);
        let result = unsafe { exec(&bytecode, &mut stack) };
        let result = result.unwrap();
        let result = unsafe { result.declassify() };
        print!("  stack:");
        for i in 0..result.len() {
            print!(" {:02x}", result[i]);
        }
        println!();

        assert_eq!(result, &[0x03, 0x00]);
    }

    #[test]
    fn exec_dag() {
        let two = Rc::new(OpTree::new(OpKind::<u32>::Imm(2)));
        let a = Rc::new(OpTree::new(OpKind::<u32>::Add(
            Rc::new(OpTree::new(OpKind::<u32>::Imm(1))),
            Rc::new(OpTree::new(OpKind::<u32>::Imm(2)))
        )));
        let b = Rc::new(OpTree::new(OpKind::<u32>::Divu(
            a.clone(), two.clone()
        )));
        let c = Rc::new(OpTree::new(OpKind::<u32>::Remu(
            a.clone(), two.clone()
        )));
        let example = OpTree::new(OpKind::<u32>::Eq(
            Rc::new(OpTree::new(OpKind::<u32>::Add(
                Rc::new(OpTree::new(OpKind::<u32>::Mul(b, two))),
                c,
            ))),
            a,
        ));

        println!();
        println!("input: {}", example);
        let (bytecode, stack) = example.compile();
        let stack = unsafe { stack.declassify() };
        print!("  bytecode:");
        for i in (0..bytecode.len()).step_by(2) {
            print!(" {:04x}", u16::from_le_bytes(
                <[u8; 2]>::try_from(&bytecode[i..i+2]).unwrap()
            ));
        }
        println!();
        disas(&bytecode, &mut io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 14*2);
        assert_eq!(stack.len(), 7*4);

        let mut stack = Secret::new(stack);
        let result = unsafe { exec(&bytecode, &mut stack) };
        let result = result.unwrap();
        let result = unsafe { result.declassify() };
        print!("  stack:");
        for i in 0..result.len() {
            print!(" {:02x}", result[i]);
        }
        println!();

        assert_eq!(result, &[0x01, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn exec_pythag() {
        let a = Rc::new(OpTree::new(OpKind::<u32>::Imm(3)));
        let b = Rc::new(OpTree::new(OpKind::<u32>::Imm(4)));
        let c = Rc::new(OpTree::new(OpKind::<u32>::Imm(5)));
        let example = OpTree::new(OpKind::<u32>::Eq(
            Rc::new(OpTree::new(OpKind::<u32>::Add(
                Rc::new(OpTree::new(OpKind::<u32>::Mul(a.clone(), a))),
                Rc::new(OpTree::new(OpKind::<u32>::Mul(b.clone(), b)))
            ))),
            Rc::new(OpTree::new(OpKind::<u32>::Mul(c.clone(), c)))
        ));

        println!();
        println!("input: {}", example);
        let (bytecode, stack) = example.compile();
        let stack = unsafe { stack.declassify() };
        print!("  bytecode:");
        for i in (0..bytecode.len()).step_by(2) {
            print!(" {:04x}", u16::from_le_bytes(
                <[u8; 2]>::try_from(&bytecode[i..i+2]).unwrap()
            ));
        }
        println!();
        disas(&bytecode, &mut io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 11*2);
        assert_eq!(stack.len(), 6*4);

        let mut stack = Secret::new(stack);
        let result = unsafe { exec(&bytecode, &mut stack) };
        let result = result.unwrap();
        let result = unsafe { result.declassify() };
        print!("  stack:");
        for i in 0..result.len() {
            print!(" {:02x}", result[i]);
        }
        println!();

        assert_eq!(result, &[0x01, 0x00, 0x00, 0x00]);
    }


    // tests for low-level instructions
    macro_rules! test_ins {
        ($name:ident, $op:ident, $t:ty, $($a:expr),+ => $expected:expr) => {
            #[test]
            fn $name() {
                let input = OpTree::new(OpKind::<$t>::$op(
                    $(
                        Rc::new(OpTree::new(OpKind::<$t>::Imm($a)))
                    ),+
                ));

                println!();
                let (bytecode, stack) = input.compile();
                let stack = unsafe { stack.declassify() };
                print!("  bytecode:");
                for i in (0..bytecode.len()).step_by(2) {
                    print!(" {:04x}", u16::from_le_bytes(
                        <[u8; 2]>::try_from(&bytecode[i..i+2]).unwrap()
                    ));
                }
                println!();
                print!("  stack:");
                for i in 0..stack.len() {
                    print!(" {:02x}", stack[i]);
                }
                println!();

                let mut stack = Secret::new(stack);
                let result = unsafe { eval::<$t>(&bytecode, &mut stack) };
                let result = result.unwrap();
                println!("{} -> {}", input, result);

                assert_eq!(result, $expected);
            }
        };
    }

    test_ins! { ins_select1, Select, u32, 1, 2, 3 => 2}
    test_ins! { ins_select2, Select, u32, 0, 2, 3 => 3}

    test_ins! { ins_eqz, Eqz, u32, 0    => 1 }
    test_ins! { ins_eq,  Eq,  u32, 2, 2 => 1 }
    test_ins! { ins_ne,  Ne,  u32, 2, 3 => 1 }
    test_ins! { ins_lts, Lts, u8, 0xff, 1 => 1 }
    test_ins! { ins_ltu, Ltu, u8, 0xff, 1 => 0 }
    test_ins! { ins_gts, Gts, u8, 0xff, 1 => 0 }
    test_ins! { ins_gtu, Gtu, u8, 0xff, 1 => 1 }
    test_ins! { ins_les, Les, u8, 0xff, 1 => 1 }
    test_ins! { ins_leu, Leu, u8, 0xff, 1 => 0 }
    test_ins! { ins_ges, Ges, u8, 0xff, 1 => 0 }
    test_ins! { ins_geu, Geu, u8, 0xff, 1 => 1 }

    test_ins! { ins_clz,    Clz,    u16, 0x1234 => 3 }
    test_ins! { ins_ctz,    Ctz,    u16, 0x1234 => 2 }
    test_ins! { ins_popcnt, Popcnt, u16, 0x1234 => 5 }
    test_ins! { ins_add, Add, u32, 1, 2 => 3 }
    test_ins! { ins_sub, Sub, u32, 2, 1 => 1 }
    test_ins! { ins_mul, Mul, u32, 2, 3 => 6 }
    test_ins! { ins_divs, Divs, u8,  0xfd, 2 => 0xff }
    test_ins! { ins_divu, Divu, u32, 7,    2 => 3    }
    test_ins! { ins_rems, Rems, u8,  0xfd, 2 => 0xff }
    test_ins! { ins_remu, Remu, u32, 7,    2 => 1    }
    test_ins! { ins_and, And, u16, 0x4321, 0x1234 => 0x0220 }
    test_ins! { ins_or,  Or,  u16, 0x4321, 0x1234 => 0x5335 }
    test_ins! { ins_xor, Xor, u16, 0x4321, 0x1234 => 0x5115 }
    test_ins! { ins_shl,  Shl,  u16, 0x89ab, 7 => 0xd580 }
    test_ins! { ins_shrs, Shrs, u16, 0x89ab, 7 => 0xff13 }
    test_ins! { ins_shru, Shru, u16, 0x89ab, 7 => 0x0113 }
    test_ins! { ins_rotl, Rotl, u16, 0x89ab, 7 => 0xd5c4 }
    test_ins! { ins_rotr, Rotr, u16, 0x89ab, 7 => 0x5713 }
}


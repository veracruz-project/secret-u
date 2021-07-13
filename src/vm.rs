//! local vm for executing bytecode

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
            print!("    exec {:#06x} ::", op);
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


#[cfg(test)]
mod tests {
    use super::*;
    use crate::opcode::*;
    use std::convert::TryFrom;
    use std::io;

    #[test]
    fn exec_add() {
        let example = OpTree::add(
            OpTree::imm(1u32.to_le_bytes()),
            OpTree::imm(2u32.to_le_bytes())
        );

        println!();
        println!("input: {}", example);
        let (bytecode, mut stack) = example.compile(true);
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

        let result = exec(&bytecode, &mut stack).unwrap();
        print!("  stack:");
        for i in 0..result.len() {
            print!(" {:02x}", result[i]);
        }
        println!();

        assert_eq!(result, &[0x03, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn exec_alignment() {
        let example = OpTree::add(
            OpTree::<[u8;2]>::extends(
                OpTree::imm(2u8.to_le_bytes())
            ),
            OpTree::<[u8;2]>::truncate(
                OpTree::imm(1u32.to_le_bytes()),
            ),
        );

        println!();
        println!("input: {}", example);
        let (bytecode, mut stack) = example.compile(true);
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

        let result = exec(&bytecode, &mut stack).unwrap();
        print!("  stack:");
        for i in 0..result.len() {
            print!(" {:02x}", result[i]);
        }
        println!();

        assert_eq!(result, &[0x03, 0x00]);
    }

    #[test]
    fn exec_dag() {
        let two = OpTree::imm(2u32.to_le_bytes());
        let a = OpTree::add(
            OpTree::imm(1u32.to_le_bytes()),
            OpTree::imm(2u32.to_le_bytes())
        );
        let b = OpTree::divu(
            a.clone(), two.clone()
        );
        let c = OpTree::remu(
            a.clone(), two.clone()
        );
        let example = OpTree::eq(
            OpTree::add(
                OpTree::mul(b, two),
                c,
            ),
            a,
        );

        println!();
        println!("input: {}", example);
        let (bytecode, mut stack) = example.compile(true);
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

        let result = exec(&bytecode, &mut stack).unwrap();
        print!("  stack:");
        for i in 0..result.len() {
            print!(" {:02x}", result[i]);
        }
        println!();

        assert_eq!(result, &[0x01, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn exec_pythag() {
        let a = OpTree::imm(3u32.to_le_bytes());
        let b = OpTree::imm(4u32.to_le_bytes());
        let c = OpTree::imm(5u32.to_le_bytes());
        let example = OpTree::eq(
            OpTree::add(
                OpTree::mul(a.clone(), a),
                OpTree::mul(b.clone(), b)
            ),
            OpTree::mul(c.clone(), c)
        );

        println!();
        println!("input: {}", example);
        let (bytecode, mut stack) = example.compile(true);
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

        let result = exec(&bytecode, &mut stack).unwrap();
        print!("  stack:");
        for i in 0..result.len() {
            print!(" {:02x}", result[i]);
        }
        println!();

        assert_eq!(result, &[0x01, 0x00, 0x00, 0x00]);
    }


    // tests for low-level instructions
    macro_rules! test_ins {
        (@arr u8)   => { [u8;1]  };
        (@arr u16)  => { [u8;2]  };
        (@arr u32)  => { [u8;4]  };
        (@arr u64)  => { [u8;8]  };
        (@arr u128) => { [u8;16] };
        ($name:ident, $op:ident, $u:ident, $($a:expr),+ => $t:ident, $expected:expr) => {
            #[test]
            fn $name() {
                let input = OpTree::<test_ins!(@arr $t)>::$op(
                    $(
                        OpTree::imm(($a as $u).to_le_bytes())
                    ),+
                );

                println!();
                let (bytecode, mut stack) = input.compile(true);
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

                let result = exec(&bytecode, &mut stack).unwrap();
                let result = <$t>::load(&result, 0).unwrap();
                println!("{} -> {}", input, result);

                assert_eq!(result, $expected);
            }
        };
        ($name:ident, $op:ident, $t:ident, $($a:expr),+ => $expected:expr) => {
            test_ins! { $name, $op, $t, $($a),+ => $t, $expected }
        };
    }

    test_ins! { ins_truncate, truncate, u32, 0x12345678 => u8, 0x78 }
    test_ins! { ins_extends,  extends, u8, 0x85 => u32, 0xffffff85 }
    test_ins! { ins_extendu,  extendu, u8, 0x85 => u32, 0x00000085 }

    test_ins! { ins_select1, select, u32, 1, 2, 3 => 2}
    test_ins! { ins_select2, select, u32, 0, 2, 3 => 3}

    test_ins! { ins_eqz, eqz, u32, 0    => 1 }
    test_ins! { ins_eq,  eq,  u32, 2, 2 => 1 }
    test_ins! { ins_ne,  ne,  u32, 2, 3 => 1 }
    test_ins! { ins_lts, lts, u8, 0xff, 1 => 1 }
    test_ins! { ins_ltu, ltu, u8, 0xff, 1 => 0 }
    test_ins! { ins_gts, gts, u8, 0xff, 1 => 0 }
    test_ins! { ins_gtu, gtu, u8, 0xff, 1 => 1 }
    test_ins! { ins_les, les, u8, 0xff, 1 => 1 }
    test_ins! { ins_leu, leu, u8, 0xff, 1 => 0 }
    test_ins! { ins_ges, ges, u8, 0xff, 1 => 0 }
    test_ins! { ins_geu, geu, u8, 0xff, 1 => 1 }

    test_ins! { ins_clz,    clz,    u16, 0x1234 => 3 }
    test_ins! { ins_ctz,    ctz,    u16, 0x1234 => 2 }
    test_ins! { ins_popcnt, popcnt, u16, 0x1234 => 5 }
    test_ins! { ins_add, add, u32, 1, 2 => 3 }
    test_ins! { ins_sub, sub, u32, 2, 1 => 1 }
    test_ins! { ins_mul, mul, u32, 2, 3 => 6 }
    test_ins! { ins_divs, divs, u8,  0xfd, 2 => 0xff }
    test_ins! { ins_divu, divu, u32, 7,    2 => 3    }
    test_ins! { ins_rems, rems, u8,  0xfd, 2 => 0xff }
    test_ins! { ins_remu, remu, u32, 7,    2 => 1    }
    test_ins! { ins_and, and, u16, 0x4321, 0x1234 => 0x0220 }
    test_ins! { ins_or,  or,  u16, 0x4321, 0x1234 => 0x5335 }
    test_ins! { ins_xor, xor, u16, 0x4321, 0x1234 => 0x5115 }
    test_ins! { ins_shl,  shl,  u16, 0x89ab, 7 => 0xd580 }
    test_ins! { ins_shrs, shrs, u16, 0x89ab, 7 => 0xff13 }
    test_ins! { ins_shru, shru, u16, 0x89ab, 7 => 0x0113 }
    test_ins! { ins_rotl, rotl, u16, 0x89ab, 7 => 0xd5c4 }
    test_ins! { ins_rotr, rotr, u16, 0x89ab, 7 => 0x5713 }
}


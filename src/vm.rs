
use crate::Secret;
use crate::error::Error;
use std::mem::size_of;

// utility functions
trait LoadStore: Sized {
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

macro_rules! loadstore_impl {
    ($t:ty, $w:expr) => {
        impl LoadStore for $t {
            #[inline]
            fn load(arr: &[u8], i: usize) -> Result<Self, Error> {
                let slice = arr.get(i..i+$w)
                    .ok_or_else(|| Error::OutOfBounds)?;

                let ptr = slice.as_ptr();
                if ptr as usize % $w != 0 {
                    Err(Error::Unaligned)?;
                }

                // as far as I'm aware no function exists to
                // safely read with checked alignment
                let v = unsafe {
                    (
                        ptr as *const [u8; $w]
                    ).read()
                };
                Ok(Self::from_le_bytes(v))
            }

            #[inline]
            fn store(arr: &mut [u8], i: usize, v: Self) -> Result<(), Error> {
                let slice = arr.get_mut(i..i+$w)
                    .ok_or_else(|| Error::OutOfBounds)?;

                let ptr = slice.as_mut_ptr();
                if ptr as usize % $w != 0 {
                    Err(Error::Unaligned)?;
                }

                // as far as I'm aware no function exists to
                // safely write with checked alignment
                unsafe {
                    (
                        ptr as *mut [u8; $w]
                    ).write(Self::to_le_bytes(v))
                };
                Ok(())
            }

            #[inline]
            unsafe fn load_unchecked(arr: &[u8], i: usize) -> Self {
                Self::from_le_bytes(
                    (
                        (
                            arr.get_unchecked(i..i+$w)
                        ).as_ptr() as *const [u8; $w]
                    ).read()
                )
            }

            #[inline]
            unsafe fn store_unchecked(arr: &mut [u8], i: usize, v: Self) {
                (
                    (
                        arr.get_unchecked_mut(i..i+$w)
                    ).as_mut_ptr() as *mut [u8; $w]
                ).write(Self::to_le_bytes(v))
            }
        }
    }
}

loadstore_impl! { u16, 2 }
loadstore_impl! { u32, 4 }


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

        // TODO debug output somehow?
        print!("    exec {:#04x} ::", op);
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        match (opcode, npw2, imm) {
            // unreachable
            (0x00, _, _) => {
                Err(Error::Unreachable)?
            }

            // nop
            (0x10, _, _) => {
                // do nothing
            }

            // get (u8)
            (0x20, 0, imm) => {
                let v = u8::load(stack, imm as usize * 1)?;
                u8::push(stack, &mut sp, v)?;
            }

            // get (u16)
            (0x20, 1, imm) => {
                let v = u16::load(stack, imm as usize * 2)?;
                u16::push(stack, &mut sp, v)?;
            }

            // get (u32)
            (0x20, 2, imm) => {
                let v = u32::load(stack, imm as usize * 4)?;
                u32::push(stack, &mut sp, v)?;
            }

            // get (>u32)
            (0x20, _npw2, _imm) => {
//                let width = 1usize << npw2 as usize;
//                sp = sp.checked_sub(imm as usize * width)
//                    .ok_or_else(|| Error::OutOfBounds)?;
//
//                for i in (0..width).step_by(4) {
//                    let v = u32::load(stack, (imm as usize * width) + i)?;
//                    u32::store(stack, sp + i, v)?;
//                }
                todo!()
            }

            // set (u8)
            (0x30, 0, imm) => {
                let v = u8::pop(stack, &mut sp)?;
                u8::store(stack, imm as usize * 1, v)?;
            }

            // set (u16)
            (0x30, 1, imm) => {
                let v = u16::pop(stack, &mut sp)?;
                u16::store(stack, imm as usize * 2, v)?;
            }

            // set (u32)
            (0x30, 2, imm) => {
                let v = u32::pop(stack, &mut sp)?;
                u32::store(stack, imm as usize * 4, v)?;
            }

            // set (>u32)
            (0x30, _npw2, _imm) => {
                todo!()
            }

            // truncate (u8)
            (0x40, 0, imm) => {
                let v = u8::load(stack, sp)?;
                sp += imm as usize * 1;
                u8::store(stack, sp, v)?;
            }

            // truncate (u16)
            (0x40, 1, imm) => {
                let v = u16::load(stack, sp)?;
                sp += imm as usize * 2;
                u16::store(stack, sp, v)?;
            }

            // truncate (u32)
            (0x40, 2, imm) => {
                let v = u32::load(stack, sp)?;
                sp += imm as usize * 4;
                u32::store(stack, sp, v)?;
            }

            // truncate (>u32)
            (0x40, _npw2, _imm) => {
                todo!()
            }

            // extends (u8)
            (0x50, 0, imm) => {
                let v = u8::load(stack, sp)?;

                sp = sp.checked_sub(imm as usize * 1)
                    .ok_or_else(|| Error::OutOfBounds)?;
                stack.get_mut(sp .. sp + (imm as usize * 1))
                    .ok_or_else(|| Error::OutOfBounds)?
                    .fill(
                        if (v as i8) < 0 {
                            0xff
                        } else {
                            0x00
                        }
                    );

                u8::store(stack, sp, v)?;
            }

            // extends (u16)
            (0x50, 1, imm) => {
                let v = u16::load(stack, sp)?;

                sp = sp.checked_sub(imm as usize * 2)
                    .ok_or_else(|| Error::OutOfBounds)?;
                stack.get_mut(sp .. sp + (imm as usize * 2))
                    .ok_or_else(|| Error::OutOfBounds)?
                    .fill(
                        if (v as i16) < 0 {
                            0xff
                        } else {
                            0x00
                        }
                    );

                u16::store(stack, sp, v)?;
            }

            // extends (u32)
            (0x50, 2, imm) => {
                let v = u32::load(stack, sp)?;

                sp = sp.checked_sub(imm as usize * 4)
                    .ok_or_else(|| Error::OutOfBounds)?;
                stack.get_mut(sp .. sp + (imm as usize * 4))
                    .ok_or_else(|| Error::OutOfBounds)?
                    .fill(
                        if (v as i32) < 0 {
                            0xff
                        } else {
                            0x00
                        }
                    );

                u32::store(stack, sp, v)?;
            }

            // extends (>u32)
            (0x50, _npw2, _imm) => {
                todo!()
            }

            // extendu (u8)
            (0x60, 0, imm) => {
                let v = u8::load(stack, sp)?;

                sp = sp.checked_sub(imm as usize * 1)
                    .ok_or_else(|| Error::OutOfBounds)?;
                stack.get_mut(sp .. sp + (imm as usize * 1))
                    .ok_or_else(|| Error::OutOfBounds)?
                    .fill(0x00);

                u8::store(stack, sp, v)?;
            }

            // extendu (u16)
            (0x60, 1, imm) => {
                let v = u16::load(stack, sp)?;

                sp = sp.checked_sub(imm as usize * 2)
                    .ok_or_else(|| Error::OutOfBounds)?;
                stack.get_mut(sp .. sp + (imm as usize * 2))
                    .ok_or_else(|| Error::OutOfBounds)?
                    .fill(0x00);

                u16::store(stack, sp, v)?;
            }

            // extendu (u32)
            (0x60, 2, imm) => {
                let v = u32::load(stack, sp)?;

                sp = sp.checked_sub(imm as usize * 4)
                    .ok_or_else(|| Error::OutOfBounds)?;
                stack.get_mut(sp .. sp + (imm as usize * 4))
                    .ok_or_else(|| Error::OutOfBounds)?
                    .fill(0x00);

                u32::store(stack, sp, v)?;
            }

            // extendu (>u32)
            (0x60, _npw2, _imm) => {
                todo!()
            }

            // align (u8)
            (0x70, 0, imm) => {
                // align just moves stack pointer around
                sp = sp.checked_sub(imm as usize * 1)
                    .ok_or_else(|| Error::OutOfBounds)?;
            }

            // align (u16)
            (0x70, 1, imm) => {
                // align just moves stack pointer around
                sp = sp.checked_sub(imm as usize * 2)
                    .ok_or_else(|| Error::OutOfBounds)?;
            }

            // align (u32)
            (0x70, 2, imm) => {
                // align just moves stack pointer around
                sp = sp.checked_sub(imm as usize * 4)
                    .ok_or_else(|| Error::OutOfBounds)?;
            }

            // align (>u32)
            (0x70, _npw2, _imm) => {
                todo!()
            }

            // add (u8)
            (0xf0, 0, 0x0f) => {
                let a = u8::pop(stack, &mut sp)?;
                let b = u8::load(stack, sp)?;
                let v = a.wrapping_add(b);
                u8::store(stack, sp, v)?;
            }

            // add (u16)
            (0xf0, 1, 0x0f) => {
                let a = u16::pop(stack, &mut sp)?;
                let b = u16::load(stack, sp)?;
                let v = a.wrapping_add(b);
                u16::store(stack, sp, v)?;
            }

            // add (u32)
            (0xf0, 2, 0x0f) => {
                let a = u32::pop(stack, &mut sp)?;
                let b = u32::load(stack, sp)?;
                let v = a.wrapping_add(b);
                u32::store(stack, sp, v)?;
            }

            // add (>u32)
            (0xf0, _npw2, 0x0f) => {
                todo!()
            }

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
        print!("  result:");
        for i in 0..result.len() {
            print!(" {:02x}", result[i]);
        }
        println!();
    }
}


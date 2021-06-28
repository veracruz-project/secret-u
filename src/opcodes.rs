
use std::rc::Rc;
use std::fmt::Debug;
use std::mem::size_of;
use std::io;
use std::convert::TryFrom;
use std::fmt;


/// Opcodes emitted as a part of bytecode
///
/// Based on opcodes defined for Wasm, limited to numeric operations
/// with a few extra stack manipulated opcodes since we don't have a
/// system of locals.
#[derive(Debug, Copy, Clone)]
#[repr(u16)]
pub enum Opcode {
    Unreachable = 0x0000,
    Nop         = 0x1000,

    Dup         = 0x2000,
    Truncate    = 0x3000,
    Extends     = 0x4000,
    Extendu     = 0x5000,
    Align       = 0x6000,
    Unalign     = 0x7000,

    Select      = 0xf000,

    Eqz         = 0xf001,
    Eq          = 0xf002,
    Ne          = 0xf003,
    Lts         = 0xf004,
    Ltu         = 0xf005,
    Gts         = 0xf006,
    Gtu         = 0xf007,
    Les         = 0xf008,
    Leu         = 0xf009,
    Ges         = 0xf00a,
    Geu         = 0xf00b,

    Clz         = 0xf00c,
    Ctz         = 0xf00d,
    Popcnt      = 0xf00e,
    Add         = 0xf00f,
    Sub         = 0xf010,
    Mul         = 0xf011,
    Divs        = 0xf012,
    Divu        = 0xf013,
    Rems        = 0xf014,
    Remu        = 0xf015,
    And         = 0xf016,
    Or          = 0xf017,
    Xor         = 0xf018,
    Shl         = 0xf019,
    Shrs        = 0xf01a,
    Shru        = 0xf01b,
    Rotl        = 0xf01c,
    Rotr        = 0xf01d,
}

impl Opcode {
    /// compile down to byte representation
    fn emit(
        &self,
        npw2: u8,
        imm: u8,
        bytecode: &mut dyn io::Write,
    ) -> Result<(), io::Error> {
        let opcode = (*self as u16) | ((npw2 as u16) << 8) | (imm as u16);
        bytecode.write_all(&opcode.to_le_bytes())?;
        Ok(())
    }

    /// has immediate?
    fn has_imm(&self) -> bool {
        (*self as u16) < 0x8000
    }

    /// parse from bytecode
    // TODO error?
    fn decode(
        bytecode: &mut dyn io::Read
    ) -> Result<(Opcode, u8, u8), io::Error> {
        let mut buf = [0; 2];
        bytecode.read_exact(&mut buf)?;
        let opcode = u16::from_le_bytes(buf);
        let npw2 = ((opcode & 0x0f00) >> 8) as u8;
        let imm = (opcode & 0x00ff) as u8;

        let opcode = match opcode & 0xf000 {
            0x0000 => Opcode::Unreachable,
            0x1000 => Opcode::Nop,
            0x2000 => Opcode::Dup,
            0x3000 => Opcode::Truncate,
            0x4000 => Opcode::Extends,
            0x5000 => Opcode::Extendu,
            0x6000 => Opcode::Align,
            0x7000 => Opcode::Unalign,
            0xf000 => match opcode & 0x00ff {
                0x00 => Opcode::Select,
                0x01 => Opcode::Eqz,
                0x02 => Opcode::Eq,
                0x03 => Opcode::Ne,
                0x04 => Opcode::Lts,
                0x05 => Opcode::Ltu,
                0x06 => Opcode::Gts,
                0x07 => Opcode::Gtu,
                0x08 => Opcode::Les,
                0x09 => Opcode::Leu,
                0x0a => Opcode::Ges,
                0x0b => Opcode::Geu,
                0x0c => Opcode::Clz,
                0x0d => Opcode::Ctz,
                0x0e => Opcode::Popcnt,
                0x0f => Opcode::Add,
                0x10 => Opcode::Sub,
                0x11 => Opcode::Mul,
                0x12 => Opcode::Divs,
                0x13 => Opcode::Divu,
                0x14 => Opcode::Rems,
                0x15 => Opcode::Remu,
                0x16 => Opcode::And,
                0x17 => Opcode::Or,
                0x18 => Opcode::Xor,
                0x19 => Opcode::Shl,
                0x1a => Opcode::Shrs,
                0x1b => Opcode::Shru,
                0x1c => Opcode::Rotl,
                0x1d => Opcode::Rotr,
                // TODO error
                _ => panic!("unknown opcode"),
            },
            // TODO error
            _ => panic!("unknown opcode"),
        };
        Ok((opcode, npw2, imm))
    }

    /// debuggable name
    fn name(&self) -> &'static str {
        match self {
            Opcode::Unreachable => "unreachable",
            Opcode::Nop         => "nop",
            Opcode::Dup         => "dup",
            Opcode::Truncate    => "truncate",
            Opcode::Extends     => "extends",
            Opcode::Extendu     => "extendu",
            Opcode::Align       => "align",
            Opcode::Unalign     => "unalign",
            Opcode::Select      => "select",
            Opcode::Eqz         => "eqz",
            Opcode::Eq          => "eq",
            Opcode::Ne          => "ne",
            Opcode::Lts         => "lts",
            Opcode::Ltu         => "ltu",
            Opcode::Gts         => "gts",
            Opcode::Gtu         => "gtu",
            Opcode::Les         => "les",
            Opcode::Leu         => "leu",
            Opcode::Ges         => "ges",
            Opcode::Geu         => "geu",
            Opcode::Clz         => "clz",
            Opcode::Ctz         => "ctz",
            Opcode::Popcnt      => "popcnt",
            Opcode::Add         => "add",
            Opcode::Sub         => "sub",
            Opcode::Mul         => "mul",
            Opcode::Divs        => "divs",
            Opcode::Divu        => "divu",
            Opcode::Rems        => "rems",
            Opcode::Remu        => "remu",
            Opcode::And         => "and",
            Opcode::Or          => "or",
            Opcode::Xor         => "xor",
            Opcode::Shl         => "shl",
            Opcode::Shrs        => "shrs",
            Opcode::Shru        => "shru",
            Opcode::Rotl        => "rotl",
            Opcode::Rotr        => "rotr",
        }
    }

    fn disas(
        bytecode: &mut dyn io::Read
    ) -> Result<String, io::Error> {
        let (opcode, npw2, imm) = Opcode::decode(bytecode)?;
        if opcode.has_imm() {
            Ok(format!("{} u{} {}", opcode, 8 * 2u32.pow(npw2 as u32), imm))
        } else {
            Ok(format!("{} u{}", opcode, 8 * 2u32.pow(npw2 as u32)))
        }
    }
}

impl fmt::Display for Opcode {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(fmt, "{}", self.name())
    }
}

/// helper function for debugging
pub fn disas(
    bytecode: &[u8],
    stdout: &mut dyn io::Write
) -> Result<(), io::Error> {
    let mut bytecode = bytecode;
    while bytecode.len() > 0 {
        writeln!(stdout, "    {}", Opcode::disas(&mut bytecode)?)?;
    }

    Ok(())
}

/// Trait for types that can be compiled
pub trait Optype: Debug + Copy + Clone + From<bool> {
    /// width in bytes, emitted as part of bytecode
    const WIDTH: u8;
    const NPW2: u8;

    /// write into stack as bytes
    fn emit(&self, stack: &mut dyn io::Write) -> Result<(), io::Error>;

    // eval operations, unsafe as these are not necessarily constant time
    unsafe fn eqz(&self) -> bool;
    unsafe fn eq(&self, other: &Self) -> bool;
    unsafe fn ne(&self, other: &Self) -> bool;
    unsafe fn lts(&self, other: &Self) -> bool;
    unsafe fn ltu(&self, other: &Self) -> bool;
    unsafe fn gts(&self, other: &Self) -> bool;
    unsafe fn gtu(&self, other: &Self) -> bool;
    unsafe fn les(&self, other: &Self) -> bool;
    unsafe fn leu(&self, other: &Self) -> bool;
    unsafe fn ges(&self, other: &Self) -> bool;
    unsafe fn geu(&self, other: &Self) -> bool;

    unsafe fn clz(&self) -> Self;
    unsafe fn ctz(&self) -> Self;
    unsafe fn popcnt(&self) -> Self;
    unsafe fn add(&self, other: &Self) -> Self;
    unsafe fn sub(&self, other: &Self) -> Self;
    unsafe fn mul(&self, other: &Self) -> Self;
    unsafe fn divs(&self, other: &Self) -> Self;
    unsafe fn divu(&self, other: &Self) -> Self;
    unsafe fn rems(&self, other: &Self) -> Self;
    unsafe fn remu(&self, other: &Self) -> Self;
    unsafe fn and(&self, other: &Self) -> Self;
    unsafe fn or(&self, other: &Self) -> Self;
    unsafe fn xor(&self, other: &Self) -> Self;
    unsafe fn shl(&self, other: &Self) -> Self;
    unsafe fn shrs(&self, other: &Self) -> Self;
    unsafe fn shru(&self, other: &Self) -> Self;
    unsafe fn rotl(&self, other: &Self) -> Self;
    unsafe fn rotr(&self, other: &Self) -> Self;

    unsafe fn truncate_u8(&self) -> u8;
    unsafe fn truncate_u16(&self) -> u16;
    unsafe fn truncate_u32(&self) -> u32;
    unsafe fn truncate_u64(&self) -> u64;
    unsafe fn extend_u16(&self) -> u16;
    unsafe fn extend_u32(&self) -> u32;
    unsafe fn extend_u64(&self) -> u64;
    unsafe fn extend_u128(&self) -> u128;
    unsafe fn extend_i16(&self) -> i16;
    unsafe fn extend_i32(&self) -> i32;
    unsafe fn extend_i64(&self) -> i64;
    unsafe fn extend_i128(&self) -> i128;
}

macro_rules! optype_truncate_impl {
    ($name:ident, $f:ty => $t:ty) => {
        unsafe fn $name(&self) -> $t {
            if size_of::<$t>() < size_of::<$f>() {
                *self as $t
            } else {
                panic!("truncating to larger size")
            }
        }
    }
}

macro_rules! optype_extendu_impl {
    ($name:ident, $f:ty => $t:ty) => {
        unsafe fn $name(&self) -> $t {
            if size_of::<$t>() > size_of::<$f>() {
                *self as $t
            } else {
                panic!("extending to smaller size")
            }
        }
    }
}

macro_rules! optype_extends_impl {
    ($name:ident, $f:ty, $s:ty => $t:ty) => {
        unsafe fn $name(&self) -> $t {
            if size_of::<$t>() < size_of::<$f>() {
                (*self as $s) as $t
            } else {
                panic!("extending to smaller size")
            }
        }
    }
}

macro_rules! optype_impl {
    ($t:ty, $s:ty, $w:expr, $p:expr) => {
        impl Optype for $t {
            const WIDTH: u8 = $w;
            const NPW2: u8 = $p;

            fn emit(&self, stack: &mut dyn io::Write) -> Result<(), io::Error> {
                stack.write_all(&self.to_le_bytes())
            }

            unsafe fn eqz(&self) -> bool                { *self == 0 }
            unsafe fn eq(&self, other: &Self) -> bool   { *self == *other }
            unsafe fn ne(&self, other: &Self) -> bool   { *self != *other }
            unsafe fn lts(&self, other: &Self) -> bool  { *self as $s < *other as $s }
            unsafe fn ltu(&self, other: &Self) -> bool  { *self < *other }
            unsafe fn gts(&self, other: &Self) -> bool  { *self as $s > *other as $s }
            unsafe fn gtu(&self, other: &Self) -> bool  { *self > *other }
            unsafe fn les(&self, other: &Self) -> bool  { *self as $s <= *other as $s }
            unsafe fn leu(&self, other: &Self) -> bool  { *self <= *other }
            unsafe fn ges(&self, other: &Self) -> bool  { *self as $s >= *other as $s }
            unsafe fn geu(&self, other: &Self) -> bool  { *self >= *other }

            unsafe fn clz(&self) -> Self                { self.leading_zeros() as $t }
            unsafe fn ctz(&self) -> Self                { self.trailing_zeros() as $t }
            unsafe fn popcnt(&self) -> Self             { self.count_ones() as $t }
            unsafe fn add(&self, other: &Self) -> Self  { *self + *other }
            unsafe fn sub(&self, other: &Self) -> Self  { *self - *other }
            unsafe fn mul(&self, other: &Self) -> Self  { *self * *other }
            unsafe fn divs(&self, other: &Self) -> Self { (*self as $s / *other as $s) as $t }
            unsafe fn divu(&self, other: &Self) -> Self { *self / *other }
            unsafe fn rems(&self, other: &Self) -> Self { (*self as $s % *other as $s) as $t }
            unsafe fn remu(&self, other: &Self) -> Self { *self & *other }
            unsafe fn and(&self, other: &Self) -> Self  { *self & *other }
            unsafe fn or(&self, other: &Self) -> Self   { *self | *other }
            unsafe fn xor(&self, other: &Self) -> Self  { *self ^ *other }
            unsafe fn shl(&self, other: &Self) -> Self  { *self << *other }
            unsafe fn shrs(&self, other: &Self) -> Self { (*self as $s >> *other as $s) as $t }
            unsafe fn shru(&self, other: &Self) -> Self { *self >> *other }
            unsafe fn rotl(&self, other: &Self) -> Self { self.rotate_left(*other as u32) }
            unsafe fn rotr(&self, other: &Self) -> Self { self.rotate_right(*other as u32) }

            optype_truncate_impl! { truncate_u8, $t => u8 }
            optype_truncate_impl! { truncate_u16, $t => u16 }
            optype_truncate_impl! { truncate_u32, $t => u32 }
            optype_truncate_impl! { truncate_u64, $t => u64 }
            optype_extendu_impl! { extend_u16, $t => u16 }
            optype_extendu_impl! { extend_u32, $t => u32 }
            optype_extendu_impl! { extend_u64, $t => u64 }
            optype_extendu_impl! { extend_u128, $t => u128 }
            optype_extends_impl! { extend_i16, $t, $s => i16 }
            optype_extends_impl! { extend_i32, $t, $s => i32 }
            optype_extends_impl! { extend_i64, $t, $s => i64 }
            optype_extends_impl! { extend_i128, $t, $s => i128 }
        }
    }
}

optype_impl! { u8,   i8,    1,  0 }
optype_impl! { u16,  i16,   2,  1 }
optype_impl! { u32,  i32,   4,  2 }
optype_impl! { u64,  i64,   8,  3 }
optype_impl! { u128, i128,  16, 4 }

/// Any Op, captures ops where type does not matter
pub trait AnyOp: Debug {
    /// width in bytes, needed for determining cast sizes
    fn width(&self) -> u8;

    /// primitive type, npw2(width)
    fn npw2(&self) -> u8;

    /// low-level compile, note this has multiple outputs, all
    /// outputs can be computed in one pass, or a NullWrite can be
    /// use to ignore unneeded output
    fn emit(
        &self,
        bytecode: &mut dyn io::Write,
        stack: &mut dyn io::Write,
        imms: &mut usize,
        sp: &mut usize,
        max_sp: &mut usize,
    ) -> Result<(), io::Error>;

//    // eval operations, unsafe as these are not necessarily constant time
//    unsafe fn eval_eqz(&self) -> bool;
//    unsafe fn eval_truncate_u8(&self) -> u8;
//    unsafe fn eval_truncate_u16(&self) -> u16;
//    unsafe fn eval_truncate_u32(&self) -> u32;
//    unsafe fn eval_truncate_u64(&self) -> u64;
//    unsafe fn eval_extend_u16(&self) -> u16;
//    unsafe fn eval_extend_u32(&self) -> u32;
//    unsafe fn eval_extend_u64(&self) -> u64;
//    unsafe fn eval_extend_u128(&self) -> u128;
//    unsafe fn eval_extend_i16(&self) -> i16;
//    unsafe fn eval_extend_i32(&self) -> i32;
//    unsafe fn eval_extend_i64(&self) -> i64;
//    unsafe fn eval_extend_i128(&self) -> i128;
}

/// Tree of operations
#[derive(Debug, Clone)]
pub enum Op<T: Optype> {
    Imm(T),
    Truncate(Rc<dyn AnyOp>),
    Extends(Rc<dyn AnyOp>),
    Extendu(Rc<dyn AnyOp>),
    Select(Rc<Op<T>>, Rc<Op<T>>, Rc<Op<T>>),

    Eqz(Rc<Op<T>>),
    Eq(Rc<Op<T>>, Rc<Op<T>>),
    Ne(Rc<Op<T>>, Rc<Op<T>>),
    Lts(Rc<Op<T>>, Rc<Op<T>>),
    Ltu(Rc<Op<T>>, Rc<Op<T>>),
    Gts(Rc<Op<T>>, Rc<Op<T>>),
    Gtu(Rc<Op<T>>, Rc<Op<T>>),
    Les(Rc<Op<T>>, Rc<Op<T>>),
    Leu(Rc<Op<T>>, Rc<Op<T>>),
    Ges(Rc<Op<T>>, Rc<Op<T>>),
    Geu(Rc<Op<T>>, Rc<Op<T>>),

    Clz(Rc<Op<T>>),
    Ctz(Rc<Op<T>>),
    Popcnt(Rc<Op<T>>),
    Add(Rc<Op<T>>, Rc<Op<T>>),
    Sub(Rc<Op<T>>, Rc<Op<T>>),
    Mul(Rc<Op<T>>, Rc<Op<T>>),
    Divs(Rc<Op<T>>, Rc<Op<T>>),
    Divu(Rc<Op<T>>, Rc<Op<T>>),
    Rems(Rc<Op<T>>, Rc<Op<T>>),
    Remu(Rc<Op<T>>, Rc<Op<T>>),
    And(Rc<Op<T>>, Rc<Op<T>>),
    Or(Rc<Op<T>>, Rc<Op<T>>),
    Xor(Rc<Op<T>>, Rc<Op<T>>),
    Shl(Rc<Op<T>>, Rc<Op<T>>),
    Shrs(Rc<Op<T>>, Rc<Op<T>>),
    Shru(Rc<Op<T>>, Rc<Op<T>>),
    Rotl(Rc<Op<T>>, Rc<Op<T>>),
    Rotr(Rc<Op<T>>, Rc<Op<T>>),
}

impl<T: Optype> Op<T> {
    /// high-level compile
    pub fn compile(&self) -> (Vec<u8>, Vec<u8>, usize) {
        let mut bytecode = vec![];
        let mut stack = vec![];
        let mut imms = 0usize;
        let mut sp = 0usize;
        let mut max_sp = 0usize;

        self.emit(&mut bytecode, &mut stack, &mut imms, &mut sp, &mut max_sp)
            .expect("vector write resulted in io::error?");

        // at this point stack contains imms, but we also need space for
        // the working stack
        stack.resize(imms + max_sp, 0);

        // emit bytecode to cleanup immediates at the end
        // TODO what if immediates are unaligned?
        assert!(imms % (T::WIDTH as usize) == 0, "unaligned imms?");
        let cleanup = u8::try_from(imms / (T::WIDTH as usize)).expect("overflow in cleanup");
        Opcode::Unalign.emit(T::NPW2, cleanup, &mut bytecode)
            .expect("vector write resulted in io::error?");

        // imms is now the initial stack pointer
        (bytecode, stack, imms)
    }
}

impl<T: Optype> AnyOp for Op<T> {
    /// width in bytes, emitted as part of bytecode
    fn width(&self) -> u8 {
        T::WIDTH
    }

    /// primitive type, npw2(width)
    fn npw2(&self) -> u8 {
        T::NPW2
    }

    /// compile down to bytecode
    fn emit(
        &self,
        bytecode: &mut dyn io::Write,
        stack: &mut dyn io::Write,
        imms: &mut usize,
        sp: &mut usize,
        max_sp: &mut usize,
    ) -> Result<(), io::Error> {
        // helper functions for compile
        fn adjust_sp<T: Optype>(sp: &mut usize, max_sp: &mut usize, delta: isize) {
            let delta = delta * (T::WIDTH as isize);

            *sp = (*sp as isize + delta) as usize;
            if *sp > *max_sp {
                *max_sp = *sp;
            }
        }

        match self {
            Op::Imm(v) => {
                // align imms as necessary
                while *imms % (T::WIDTH as usize) != 0 {
                    stack.write_all(&[0])?;
                    *imms += 1;
                }

                // write imms to the bottom of the stack
                v.emit(stack)?;
                *imms += T::WIDTH as usize;

                // align top of stack as necessary
                if *sp % (T::WIDTH as usize) != 0 {
                    let align = T::WIDTH as usize - (*sp % (T::WIDTH as usize));
                    let align = u8::try_from(align).expect("immediate overflow in unalign");
                    Opcode::Extendu.emit(0, align, bytecode)?;
                    adjust_sp::<u8>(sp, max_sp, align as isize);
                }

                // dup imm to top of stack
                assert!(*imms % (T::WIDTH as usize) == 0, "imms not aligned?");
                let imm = *imms/(T::WIDTH as usize) - 1;
                let imm = u8::try_from(imm).expect("immedate overflow in dup");
                Opcode::Dup.emit(T::NPW2, imm, bytecode)?;
                adjust_sp::<T>(sp, max_sp, 1);
            }

            Op::Truncate(a) => {
                // keep track of original sp to unalign if needed
                let expected_sp = *sp + T::WIDTH as usize;

                a.emit(bytecode, stack, imms, sp, max_sp)?;
                let delta = a.width() - T::WIDTH;
                assert!(delta % T::WIDTH == 0, "unaligned truncate?");
                let delta = delta / T::WIDTH;
                Opcode::Truncate.emit(T::NPW2, delta, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -(delta as isize));

                // unalign?
                if *sp > expected_sp {
                    let align = *sp - expected_sp;
                    assert!(align % (T::WIDTH as usize) == 0, "unaligned unalign?");
                    let align = align / (T::WIDTH as usize);
                    let align = u8::try_from(align).expect("immediate overflow in unalign");
                    Opcode::Unalign.emit(T::NPW2, align, bytecode)?;
                    adjust_sp::<T>(sp, max_sp, -(align as isize));
                }
            }

            Op::Extends(a) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;

                // align as necessary
                if (*sp - a.width() as usize) % (T::WIDTH as usize) != 0 {
                    let align = T::WIDTH as usize - ((*sp - a.width() as usize) % (T::WIDTH as usize));
                    assert!(align % (a.width() as usize) == 0, "unaligned align?");
                    let align = align / a.width() as usize;
                    let align = u8::try_from(align).expect("immediate overflow in align");
                    Opcode::Align.emit(a.npw2(), align, bytecode)?;
                    adjust_sp::<u8>(sp, max_sp, align as isize * a.width() as isize);
                }

                let delta = T::WIDTH - a.width();
                assert!(delta % a.width() == 0, "unaligned extends?");
                Opcode::Extends.emit(a.npw2(), delta / a.width(), bytecode)?;
                adjust_sp::<u8>(sp, max_sp, delta as isize * a.width() as isize);
            }

            Op::Extendu(a) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;

                // align as necessary
                if (*sp - a.width() as usize) % (T::WIDTH as usize) != 0 {
                    let align = T::WIDTH as usize - ((*sp - a.width() as usize) % (T::WIDTH as usize));
                    assert!(align % (a.width() as usize) == 0, "unaligned align?");
                    let align = align / a.width() as usize;
                    let align = u8::try_from(align).expect("immediate overflow in align");
                    Opcode::Align.emit(a.npw2(), align, bytecode)?;
                    adjust_sp::<u8>(sp, max_sp, align as isize * a.width() as isize);
                }

                let delta = T::WIDTH - a.width();
                assert!(delta % a.width() == 0, "unaligned extendu?");
                Opcode::Extendu.emit(a.npw2(), delta / a.width(), bytecode)?;
                adjust_sp::<u8>(sp, max_sp, delta as isize * a.width() as isize);
            }

            Op::Select(p, a, b) => {
                p.emit(bytecode, stack, imms, sp, max_sp)?;
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Select.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -2);
            }

            Op::Eqz(a) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Eqz.emit(T::NPW2, 0, bytecode)?;
            }

            Op::Eq(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Eq.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            Op::Ne(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Ne.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            Op::Lts(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Lts.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            Op::Ltu(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Ltu.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            Op::Gts(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Gts.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            Op::Gtu(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Gtu.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            Op::Les(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Les.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            Op::Leu(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Leu.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            Op::Ges(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Ges.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            Op::Geu(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Geu.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            Op::Clz(a) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Clz.emit(T::NPW2, 0, bytecode)?;
            }

            Op::Ctz(a) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Clz.emit(T::NPW2, 0, bytecode)?;
            }

            Op::Popcnt(a) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Clz.emit(T::NPW2, 0, bytecode)?;
            }

            Op::Add(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Add.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            Op::Sub(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Sub.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            Op::Mul(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Mul.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            Op::Divs(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Divs.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            Op::Divu(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Divu.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            Op::Rems(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Rems.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            Op::Remu(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Remu.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            Op::And(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::And.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            Op::Or(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Or.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            Op::Xor(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Xor.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            Op::Shl(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Shl.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            Op::Shrs(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Shrs.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            Op::Shru(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Shru.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            Op::Rotl(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Rotl.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            Op::Rotr(a, b) => {
                a.emit(bytecode, stack, imms, sp, max_sp)?;
                b.emit(bytecode, stack, imms, sp, max_sp)?;
                Opcode::Rotr.emit(T::NPW2, 0, bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }
        }

        Ok(())
    }


//    // eval operations, unsafe as these are not necessarily constant time
//    unsafe fn eval_eqz(&self) -> bool { self.eval().eqz() }
//    unsafe fn eval_truncate_u8(&self) -> u8 { self.eval().truncate_u8() }
//    unsafe fn eval_truncate_u16(&self) -> u16 { self.eval().truncate_u16() }
//    unsafe fn eval_truncate_u32(&self) -> u32 { self.eval().truncate_u32() }
//    unsafe fn eval_truncate_u64(&self) -> u64 { self.eval().truncate_u64() }
//    unsafe fn eval_extend_u16(&self) -> u16 { self.eval().extend_u16() }
//    unsafe fn eval_extend_u32(&self) -> u32 { self.eval().extend_u32() }
//    unsafe fn eval_extend_u64(&self) -> u64 { self.eval().extend_u64() }
//    unsafe fn eval_extend_u128(&self) -> u128 { self.eval().extend_u128() }
//    unsafe fn eval_extend_i16(&self) -> i16 { self.eval().extend_i16() }
//    unsafe fn eval_extend_i32(&self) -> i32 { self.eval().extend_i32() }
//    unsafe fn eval_extend_i64(&self) -> i64 { self.eval().extend_i64() }
//    unsafe fn eval_extend_i128(&self) -> i128 { self.eval().extend_i128() }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compile_add() {
        let example = Op::<u32>::Add(
            Rc::new(Op::<u32>::Imm(1)),
            Rc::new(Op::<u32>::Imm(2))
        );

        println!();
        println!("input: {:?}", example);
        let (bytecode, stack, sp) = example.compile();
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
        println!("  sp: {}", sp);

        assert_eq!(bytecode.len(), 4*2);
        assert_eq!(stack.len(), 4*4);
        assert_eq!(sp, 2*4);
    }

    #[test]
    fn compile_alignment() {
        let example = Op::<u16>::Add(
            Rc::new(Op::<u16>::Extends(
                Rc::new(Op::<u8>::Imm(2))
            )),
            Rc::new(Op::<u16>::Truncate(
                Rc::new(Op::<u32>::Imm(1)),
            )),
        );

        println!();
        println!("input: {:?}", example);
        let (bytecode, stack, sp) = example.compile();
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
        println!("  sp: {}", sp);

        assert_eq!(bytecode.len(), 8*2);
        assert_eq!(stack.len(), 4*4);
        assert_eq!(sp, 2*4);
    }

    #[test]
    fn compile_pythag() {
        let a = Rc::new(Op::<u32>::Imm(3));
        let b = Rc::new(Op::<u32>::Imm(4));
        let c = Rc::new(Op::<u32>::Imm(5));
        let example = Op::<u32>::Eq(
            Rc::new(Op::<u32>::Add(
                Rc::new(Op::<u32>::Mul(a.clone(), a)),
                Rc::new(Op::<u32>::Mul(b.clone(), b))
            )),
            Rc::new(Op::<u32>::Mul(c.clone(), c))
        );

        println!();
        println!("input: {:?}", example);
        let (bytecode, stack, sp) = example.compile();
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
        println!("  sp: {}", sp);

        assert_eq!(bytecode.len(), 12*2);
        assert_eq!(stack.len(), 9*4);
        assert_eq!(sp, 6*4);
    }
}

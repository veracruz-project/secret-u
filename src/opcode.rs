
use std::rc::Rc;
use std::fmt::Debug;
use std::io;
use std::convert::TryFrom;
use std::fmt;
use std::mem;
use crate::error::Error;


/// OpCodes emitted as a part of bytecode
///
/// Based on opcodes defined for Wasm, limited to numeric operations
/// with a few extra stack manipulated opcodes since we don't have a
/// system of locals.
#[derive(Debug, Copy, Clone)]
#[repr(u16)]
pub enum OpCode {
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

impl OpCode {
    pub fn has_imm(&self) -> bool {
        (*self as u16) < 0x8000
    }
}

impl fmt::Display for OpCode {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let name = match self {
            OpCode::Unreachable => "unreachable",
            OpCode::Nop         => "nop",
            OpCode::Dup         => "dup",
            OpCode::Truncate    => "truncate",
            OpCode::Extends     => "extends",
            OpCode::Extendu     => "extendu",
            OpCode::Align       => "align",
            OpCode::Unalign     => "unalign",
            OpCode::Select      => "select",
            OpCode::Eqz         => "eqz",
            OpCode::Eq          => "eq",
            OpCode::Ne          => "ne",
            OpCode::Lts         => "lts",
            OpCode::Ltu         => "ltu",
            OpCode::Gts         => "gts",
            OpCode::Gtu         => "gtu",
            OpCode::Les         => "les",
            OpCode::Leu         => "leu",
            OpCode::Ges         => "ges",
            OpCode::Geu         => "geu",
            OpCode::Clz         => "clz",
            OpCode::Ctz         => "ctz",
            OpCode::Popcnt      => "popcnt",
            OpCode::Add         => "add",
            OpCode::Sub         => "sub",
            OpCode::Mul         => "mul",
            OpCode::Divs        => "divs",
            OpCode::Divu        => "divu",
            OpCode::Rems        => "rems",
            OpCode::Remu        => "remu",
            OpCode::And         => "and",
            OpCode::Or          => "or",
            OpCode::Xor         => "xor",
            OpCode::Shl         => "shl",
            OpCode::Shrs        => "shrs",
            OpCode::Shru        => "shru",
            OpCode::Rotl        => "rotl",
            OpCode::Rotr        => "rotr",
        };
        write!(fmt, "{}", name)
    }
}

/// An encoded instruction
#[derive(Debug, Copy, Clone)]
pub struct Op(u16);

impl Op {
    /// Create a new op from its components
    pub const fn new(opcode: OpCode, npw2: u8, imm: u8) -> Op {
        Op((opcode as u16) | ((npw2 as u16) << 8) | (imm as u16))
    }

    pub fn has_imm(&self) -> bool {
        self.0 < 0x8000
    }

    pub fn opcode(&self) -> OpCode {
        let opcode = if self.has_imm() {
            self.0 & 0xf000
        } else {
            self.0 & 0xf0ff
        };

        // we check for OpCode validity on every function that can build
        // an Op, so this should only result in valid OpCodes
        unsafe { mem::transmute(opcode) }
    }

    pub fn npw2(&self) -> u8 {
        ((self.0 & 0x0f00) >> 8) as u8
    }

    pub fn width(&self) -> usize {
        1usize << self.npw2()
    }

    pub fn imm(&self) -> u8 {
        (self.0 & 0x00ff) as u8
    }

    /// compile down to bytecode
    pub fn encode(
        &self,
        bytecode: &mut dyn io::Write
    ) -> Result<(), io::Error> {
        bytecode.write_all(&self.0.to_le_bytes())?;
        Ok(())
    }

    /// decode from bytecode
    pub fn decode(
        bytecode: &mut dyn io::Read
    ) -> Result<Result<Op, Error>, io::Error> {
        let mut buf = [0; 2];
        bytecode.read_exact(&mut buf)?;
        let op = u16::from_le_bytes(buf);
        Ok(Self::try_from(op))
    }
}

impl TryFrom<u16> for Op {
    type Error = Error;

    fn try_from(op: u16) -> Result<Self, Self::Error> {
        let npw2 = ((op & 0x0f00) >> 8) as u8;
        let imm = (op & 0x00ff) as u8;

        let opcode = match op & 0xf000 {
            0x0000 => OpCode::Unreachable,
            0x1000 => OpCode::Nop,
            0x2000 => OpCode::Dup,
            0x3000 => OpCode::Truncate,
            0x4000 => OpCode::Extends,
            0x5000 => OpCode::Extendu,
            0x6000 => OpCode::Align,
            0x7000 => OpCode::Unalign,
            0xf000 => match op & 0x00ff {
                0x00 => OpCode::Select,
                0x01 => OpCode::Eqz,
                0x02 => OpCode::Eq,
                0x03 => OpCode::Ne,
                0x04 => OpCode::Lts,
                0x05 => OpCode::Ltu,
                0x06 => OpCode::Gts,
                0x07 => OpCode::Gtu,
                0x08 => OpCode::Les,
                0x09 => OpCode::Leu,
                0x0a => OpCode::Ges,
                0x0b => OpCode::Geu,
                0x0c => OpCode::Clz,
                0x0d => OpCode::Ctz,
                0x0e => OpCode::Popcnt,
                0x0f => OpCode::Add,
                0x10 => OpCode::Sub,
                0x11 => OpCode::Mul,
                0x12 => OpCode::Divs,
                0x13 => OpCode::Divu,
                0x14 => OpCode::Rems,
                0x15 => OpCode::Remu,
                0x16 => OpCode::And,
                0x17 => OpCode::Or,
                0x18 => OpCode::Xor,
                0x19 => OpCode::Shl,
                0x1a => OpCode::Shrs,
                0x1b => OpCode::Shru,
                0x1c => OpCode::Rotl,
                0x1d => OpCode::Rotr,
                _ => Err(Error::InvalidOpcode(op))?,
            },
            _ => Err(Error::InvalidOpcode(op))?,
        };

        Ok(Self::new(opcode, npw2, imm))
    }
}

impl fmt::Display for Op {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        if self.has_imm() {
            write!(fmt, "{} u{} {}", self.opcode(), 8*self.width(), self.imm())
        } else {
            write!(fmt, "{} u{}", self.opcode(), 8*self.width())
        }
    }
}

/// helper function for debugging
pub fn disas(
    bytecode: &[u8],
    stdout: &mut dyn io::Write
) -> Result<(), io::Error> {
    let mut bytecode = bytecode;
    while bytecode.len() > 0 {
        match Op::decode(&mut bytecode)? {
            Ok(opcode) => {
                writeln!(stdout, "    {}", opcode)?;
            }
            Err(Error::InvalidOpcode(op)) => {
                writeln!(stdout, "    unknown {:#04x}", op)?;
            }
        }
    }

    Ok(())
}

/// Trait for types that can be compiled
pub trait OpType: Debug + Copy + Clone + From<bool> {
    /// width in bytes, emitted as part of bytecode
    const WIDTH: u8;

    /// npw2(width), used in instruction encoding
    const NPW2: u8;

    /// write into stack as bytes
    fn encode(&self, stack: &mut dyn io::Write) -> Result<(), io::Error>;
}

macro_rules! optype_impl {
    ($t:ty, $s:ty, $w:expr, $p:expr) => {
        impl OpType for $t {
            const WIDTH: u8 = $w;
            const NPW2: u8 = $p;

            fn encode(
                &self,
                stack: &mut dyn io::Write
            ) -> Result<(), io::Error> {
                stack.write_all(&self.to_le_bytes())
            }
        }
    }
}

optype_impl! { u8,   i8,    1,  0 }
optype_impl! { u16,  i16,   2,  1 }
optype_impl! { u32,  i32,   4,  2 }
optype_impl! { u64,  i64,   8,  3 }
optype_impl! { u128, i128,  16, 4 }

/// Any OpTree, captures ops where type does not matter
pub trait AnyOpTree: Debug {
    /// width in bytes, needed for determining cast sizes
    fn width(&self) -> u8;

    /// primitive type, npw2(width)
    fn npw2(&self) -> u8;

    /// low-level compile, note this has multiple outputs, all
    /// outputs can be computed in one pass, or a NullWrite can be
    /// use to ignore unneeded output
    fn encode(
        &self,
        bytecode: &mut dyn io::Write,
        stack: &mut dyn io::Write,
        imms: &mut usize,
        sp: &mut usize,
        max_sp: &mut usize,
    ) -> Result<(), io::Error>;
}

/// Tree of operations
#[derive(Debug, Clone)]
pub enum OpTree<T: OpType> {
    Imm(T),
    Truncate(Rc<dyn AnyOpTree>),
    Extends(Rc<dyn AnyOpTree>),
    Extendu(Rc<dyn AnyOpTree>),
    Select(Rc<OpTree<T>>, Rc<OpTree<T>>, Rc<OpTree<T>>),

    Eqz(Rc<OpTree<T>>),
    Eq(Rc<OpTree<T>>, Rc<OpTree<T>>),
    Ne(Rc<OpTree<T>>, Rc<OpTree<T>>),
    Lts(Rc<OpTree<T>>, Rc<OpTree<T>>),
    Ltu(Rc<OpTree<T>>, Rc<OpTree<T>>),
    Gts(Rc<OpTree<T>>, Rc<OpTree<T>>),
    Gtu(Rc<OpTree<T>>, Rc<OpTree<T>>),
    Les(Rc<OpTree<T>>, Rc<OpTree<T>>),
    Leu(Rc<OpTree<T>>, Rc<OpTree<T>>),
    Ges(Rc<OpTree<T>>, Rc<OpTree<T>>),
    Geu(Rc<OpTree<T>>, Rc<OpTree<T>>),

    Clz(Rc<OpTree<T>>),
    Ctz(Rc<OpTree<T>>),
    Popcnt(Rc<OpTree<T>>),
    Add(Rc<OpTree<T>>, Rc<OpTree<T>>),
    Sub(Rc<OpTree<T>>, Rc<OpTree<T>>),
    Mul(Rc<OpTree<T>>, Rc<OpTree<T>>),
    Divs(Rc<OpTree<T>>, Rc<OpTree<T>>),
    Divu(Rc<OpTree<T>>, Rc<OpTree<T>>),
    Rems(Rc<OpTree<T>>, Rc<OpTree<T>>),
    Remu(Rc<OpTree<T>>, Rc<OpTree<T>>),
    And(Rc<OpTree<T>>, Rc<OpTree<T>>),
    Or(Rc<OpTree<T>>, Rc<OpTree<T>>),
    Xor(Rc<OpTree<T>>, Rc<OpTree<T>>),
    Shl(Rc<OpTree<T>>, Rc<OpTree<T>>),
    Shrs(Rc<OpTree<T>>, Rc<OpTree<T>>),
    Shru(Rc<OpTree<T>>, Rc<OpTree<T>>),
    Rotl(Rc<OpTree<T>>, Rc<OpTree<T>>),
    Rotr(Rc<OpTree<T>>, Rc<OpTree<T>>),
}

impl<T: OpType> OpTree<T> {
    /// high-level compile
    pub fn compile(&self) -> (Vec<u8>, Vec<u8>, usize) {
        let mut bytecode = vec![];
        let mut stack = vec![];
        let mut imms = 0usize;
        let mut sp = 0usize;
        let mut max_sp = 0usize;

        self.encode(&mut bytecode, &mut stack, &mut imms, &mut sp, &mut max_sp)
            .expect("vector write resulted in io::error?");

        // at this point stack contains imms, but we also need space for
        // the working stack
        stack.resize(imms + max_sp, 0);

        // emit bytecode to cleanup immediates at the end
        // TODO what if immediates are unaligned?
        assert!(imms % (T::WIDTH as usize) == 0, "unaligned imms?");
        let cleanup = u8::try_from(imms / (T::WIDTH as usize)).expect("overflow in cleanup");
        Op::new(OpCode::Unalign, T::NPW2, cleanup).encode(&mut bytecode)
            .expect("vector write resulted in io::error?");

        // imms is now the initial stack pointer
        (bytecode, stack, imms)
    }
}

impl<T: OpType> AnyOpTree for OpTree<T> {
    /// width in bytes, emitted as part of bytecode
    fn width(&self) -> u8 {
        T::WIDTH
    }

    /// primitive type, npw2(width)
    fn npw2(&self) -> u8 {
        T::NPW2
    }

    /// compile down to bytecode
    fn encode(
        &self,
        bytecode: &mut dyn io::Write,
        stack: &mut dyn io::Write,
        imms: &mut usize,
        sp: &mut usize,
        max_sp: &mut usize,
    ) -> Result<(), io::Error> {
        // helper functions for compile
        fn adjust_sp<T: OpType>(sp: &mut usize, max_sp: &mut usize, delta: isize) {
            let delta = delta * (T::WIDTH as isize);

            *sp = (*sp as isize + delta) as usize;
            if *sp > *max_sp {
                *max_sp = *sp;
            }
        }

        match self {
            OpTree::Imm(v) => {
                // align imms as necessary
                while *imms % (T::WIDTH as usize) != 0 {
                    stack.write_all(&[0])?;
                    *imms += 1;
                }

                // write imms to the bottom of the stack
                v.encode(stack)?;
                *imms += T::WIDTH as usize;

                // align top of stack as necessary
                if *sp % (T::WIDTH as usize) != 0 {
                    let align = T::WIDTH as usize - (*sp % (T::WIDTH as usize));
                    let align = u8::try_from(align).expect("immediate overflow in unalign");
                    Op::new(OpCode::Extendu, 0, align).encode(bytecode)?;
                    adjust_sp::<u8>(sp, max_sp, align as isize);
                }

                // dup imm to top of stack
                assert!(*imms % (T::WIDTH as usize) == 0, "imms not aligned?");
                let imm = *imms/(T::WIDTH as usize) - 1;
                let imm = u8::try_from(imm).expect("immedate overflow in dup");
                Op::new(OpCode::Dup, T::NPW2, imm).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, 1);
            }

            OpTree::Truncate(a) => {
                // keep track of original sp to unalign if needed
                let expected_sp = *sp + T::WIDTH as usize;

                a.encode(bytecode, stack, imms, sp, max_sp)?;
                let delta = a.width() - T::WIDTH;
                assert!(delta % T::WIDTH == 0, "unaligned truncate?");
                let delta = delta / T::WIDTH;
                Op::new(OpCode::Truncate, T::NPW2, delta).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -(delta as isize));

                // unalign?
                if *sp > expected_sp {
                    let align = *sp - expected_sp;
                    assert!(align % (T::WIDTH as usize) == 0, "unaligned unalign?");
                    let align = align / (T::WIDTH as usize);
                    let align = u8::try_from(align).expect("immediate overflow in unalign");
                    Op::new(OpCode::Unalign, T::NPW2, align).encode(bytecode)?;
                    adjust_sp::<T>(sp, max_sp, -(align as isize));
                }
            }

            OpTree::Extends(a) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;

                // align as necessary
                if (*sp - a.width() as usize) % (T::WIDTH as usize) != 0 {
                    let align = T::WIDTH as usize - ((*sp - a.width() as usize) % (T::WIDTH as usize));
                    assert!(align % (a.width() as usize) == 0, "unaligned align?");
                    let align = align / a.width() as usize;
                    let align = u8::try_from(align).expect("immediate overflow in align");
                    Op::new(OpCode::Align, a.npw2(), align).encode(bytecode)?;
                    adjust_sp::<u8>(sp, max_sp, align as isize * a.width() as isize);
                }

                let delta = T::WIDTH - a.width();
                assert!(delta % a.width() == 0, "unaligned extends?");
                Op::new(OpCode::Extends, a.npw2(), delta / a.width()).encode(bytecode)?;
                adjust_sp::<u8>(sp, max_sp, delta as isize * a.width() as isize);
            }

            OpTree::Extendu(a) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;

                // align as necessary
                if (*sp - a.width() as usize) % (T::WIDTH as usize) != 0 {
                    let align = T::WIDTH as usize - ((*sp - a.width() as usize) % (T::WIDTH as usize));
                    assert!(align % (a.width() as usize) == 0, "unaligned align?");
                    let align = align / a.width() as usize;
                    let align = u8::try_from(align).expect("immediate overflow in align");
                    Op::new(OpCode::Align, a.npw2(), align).encode(bytecode)?;
                    adjust_sp::<u8>(sp, max_sp, align as isize * a.width() as isize);
                }

                let delta = T::WIDTH - a.width();
                assert!(delta % a.width() == 0, "unaligned extendu?");
                Op::new(OpCode::Extendu, a.npw2(), delta / a.width()).encode(bytecode)?;
                adjust_sp::<u8>(sp, max_sp, delta as isize * a.width() as isize);
            }

            OpTree::Select(p, a, b) => {
                p.encode(bytecode, stack, imms, sp, max_sp)?;
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Select, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -2);
            }

            OpTree::Eqz(a) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Eqz, T::NPW2, 0).encode(bytecode)?;
            }

            OpTree::Eq(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Eq, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            OpTree::Ne(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Ne, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            OpTree::Lts(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Lts, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            OpTree::Ltu(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Ltu, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            OpTree::Gts(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Gts, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            OpTree::Gtu(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Gtu, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            OpTree::Les(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Les, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            OpTree::Leu(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Leu, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            OpTree::Ges(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Ges, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            OpTree::Geu(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Geu, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            OpTree::Clz(a) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Clz, T::NPW2, 0).encode(bytecode)?;
            }

            OpTree::Ctz(a) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Clz, T::NPW2, 0).encode(bytecode)?;
            }

            OpTree::Popcnt(a) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Clz, T::NPW2, 0).encode(bytecode)?;
            }

            OpTree::Add(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Add, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            OpTree::Sub(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Sub, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            OpTree::Mul(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Mul, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            OpTree::Divs(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Divs, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            OpTree::Divu(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Divu, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            OpTree::Rems(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Rems, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            OpTree::Remu(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Remu, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            OpTree::And(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::And, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            OpTree::Or(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Or, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            OpTree::Xor(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Xor, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            OpTree::Shl(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Shl, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            OpTree::Shrs(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Shrs, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            OpTree::Shru(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Shru, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            OpTree::Rotl(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Rotl, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }

            OpTree::Rotr(a, b) => {
                a.encode(bytecode, stack, imms, sp, max_sp)?;
                b.encode(bytecode, stack, imms, sp, max_sp)?;
                Op::new(OpCode::Rotr, T::NPW2, 0).encode(bytecode)?;
                adjust_sp::<T>(sp, max_sp, -1);
            }
        }

        Ok(())
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compile_add() {
        let example = OpTree::<u32>::Add(
            Rc::new(OpTree::<u32>::Imm(1)),
            Rc::new(OpTree::<u32>::Imm(2))
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
        let example = OpTree::<u16>::Add(
            Rc::new(OpTree::<u16>::Extends(
                Rc::new(OpTree::<u8>::Imm(2))
            )),
            Rc::new(OpTree::<u16>::Truncate(
                Rc::new(OpTree::<u32>::Imm(1)),
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
        let a = Rc::new(OpTree::<u32>::Imm(3));
        let b = Rc::new(OpTree::<u32>::Imm(4));
        let c = Rc::new(OpTree::<u32>::Imm(5));
        let example = OpTree::<u32>::Eq(
            Rc::new(OpTree::<u32>::Add(
                Rc::new(OpTree::<u32>::Mul(a.clone(), a)),
                Rc::new(OpTree::<u32>::Mul(b.clone(), b))
            )),
            Rc::new(OpTree::<u32>::Mul(c.clone(), c))
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

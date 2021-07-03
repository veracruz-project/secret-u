
use std::rc::Rc;
use std::fmt::Debug;
use std::io;
use std::convert::TryFrom;
use std::fmt;
use std::mem;
use crate::error::Error;
use std::cell::Cell;
use crate::Secret;


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

    Get         = 0x2000,
    Set         = 0x3000,
    Truncate    = 0x4000,
    Extends     = 0x5000,
    Extendu     = 0x6000,
    Align       = 0x7000,

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
            OpCode::Get         => "get",
            OpCode::Set         => "set",
            OpCode::Truncate    => "truncate",
            OpCode::Extends     => "extends",
            OpCode::Extendu     => "extendu",
            OpCode::Align       => "align",
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
            0x2000 => OpCode::Get,
            0x3000 => OpCode::Set,
            0x4000 => OpCode::Truncate,
            0x5000 => OpCode::Extends,
            0x6000 => OpCode::Extendu,
            0x7000 => OpCode::Align,
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
            Err(_) => {
                panic!("unexpected error in disas?");
            }
        }
    }

    Ok(())
}

/// Trait for types that can be compiled
pub trait OpType: Debug + Copy + Clone + From<bool> {
    /// width in bytes, emitted as part of bytecode
    const WIDTH: usize;

    /// npw2(width), used in instruction encoding
    const NPW2: u8;

    /// write into stack as bytes
    fn encode(&self, stack: &mut dyn io::Write) -> Result<(), io::Error>;
}

macro_rules! optype_impl {
    ($t:ty, $s:ty, $w:expr, $p:expr) => {
        impl OpType for $t {
            const WIDTH: usize = $w;
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

/// Kinds of operations in tree
#[derive(Debug, Clone)]
pub enum OpKind<T: OpType> {
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

/// Tree of operations, including metadata to deduplicate
/// common branches
#[derive(Debug, Clone)]
pub struct OpTree<T: OpType> {
    kind: OpKind<T>,
    refs: Cell<u32>,
    slot: Cell<Option<u8>>,
}

impl<T: OpType> OpTree<T> {
    pub fn new(kind: OpKind<T>) -> OpTree<T> {
        OpTree {
            kind: kind,
            refs: Cell::new(0),
            slot: Cell::new(None),
        }
    }

    /// high-level compile into bytecode, stack, and initial stack pointer
    pub fn compile(&self) -> (Vec<u8>, Secret<Vec<u8>>) {
        // NOTE! We make sure to zero all refs from pass1 to pass2, this is
        // rather fragile and requires all passes to always be run as a pair,
        // we can't interrupt between passes without needing to reset all
        // internal reference counts

        // first pass to find number of immediates and deduplicate branches
        let mut stack = Vec::new();
        let mut imms = 0usize;
        self.compile_pass1(
            &mut stack,
            &mut imms
        ).expect("vector write resulted in io::error?");

        // second pass now to compile the bytecode and stack, note sp now points
        // to end of immediates
        let mut bytecode = Vec::new();
        let mut sp = 0usize;
        let mut max_sp = 0usize;
        self.compile_pass2(
            &mut bytecode,
            &mut imms,
            &mut sp,
            &mut max_sp
        ).expect("vector write resulted in io::error?");

        // at this point stack contains imms, but we also need space for
        // the working stack
        stack.resize(imms + max_sp, 0);

        // imms is now the initial stack pointer
        (bytecode, Secret::new(stack))
    }
}

// TODO what the heck should this visibility be? we don't want compile
// passes exposed, but rustc sure does like to complain otherwise
pub trait AnyOpTree: Debug + fmt::Display {
    /// type's width in bytes, needed for determining cast sizes
    fn width(&self) -> usize;

    /// npw2(width), used as a part of instruction encoding
    fn npw2(&self) -> u8;

    /// First compile pass, used to find the number of immediates
    /// for offset calculation, and local reference counting to
    /// deduplicate branches.
    fn compile_pass1(
        &self,
        stack: &mut dyn io::Write,
        imms: &mut usize,
    ) -> Result<(), io::Error>;

    /// Second compile pass, used to actually compile both the
    /// immediates and bytecode. Since both bytecode and stack are
    /// generic writers, a null writer could be used if either are
    /// not needed.
    fn compile_pass2(
        &self,
        bytecode: &mut dyn io::Write,
        imms: &mut usize,
        sp: &mut usize,
        max_sp: &mut usize,
    ) -> Result<(), io::Error>;
}

impl<T: OpType> AnyOpTree for OpTree<T> {
    fn width(&self) -> usize {
        T::WIDTH
    }

    fn npw2(&self) -> u8 {
        T::NPW2
    }

    fn compile_pass1(
        &self,
        stack: &mut dyn io::Write,
        imms: &mut usize,
    ) -> Result<(), io::Error> {
        // mark node as seen
        let prefs = self.refs.get();
        self.refs.set(prefs + 1);
        if prefs > 0 {
            // already visited?
            return Ok(());
        }

        // make sure slots left over from previous calculation are reset
        self.slot.set(None);

        match &self.kind {
            OpKind::Imm(v) => {
                // align imms?
                while *imms % T::WIDTH != 0 {
                    stack.write_all(&[0])?;
                    *imms += 1;
                }

                // save slot
                assert!(*imms % T::WIDTH == 0, "unaligned slot");
                let slot = *imms / T::WIDTH;
                let slot = u8::try_from(slot).expect("slot overflow");
                self.slot.set(Some(slot));

                // write imm to stack
                v.encode(stack)?;

                // update imms
                *imms += T::WIDTH;
            }

            OpKind::Truncate(a) => {
                a.compile_pass1(stack, imms)?;
            }

            OpKind::Extends(a) => {
                a.compile_pass1(stack, imms)?;
            }

            OpKind::Extendu(a) => {
                a.compile_pass1(stack, imms)?;
            }

            OpKind::Select(p, a, b) => {
                p.compile_pass1(stack, imms)?;
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::Eqz(a) => {
                a.compile_pass1(stack, imms)?;
            }

            OpKind::Eq(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::Ne(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::Lts(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::Ltu(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::Gts(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::Gtu(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::Les(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::Leu(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::Ges(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::Geu(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::Clz(a) => {
                a.compile_pass1(stack, imms)?;
            }

            OpKind::Ctz(a) => {
                a.compile_pass1(stack, imms)?;
            }

            OpKind::Popcnt(a) => {
                a.compile_pass1(stack, imms)?;
            }

            OpKind::Add(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::Sub(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::Mul(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::Divs(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::Divu(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::Rems(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::Remu(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::And(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::Or(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::Xor(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::Shl(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::Shrs(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::Shru(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::Rotl(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }

            OpKind::Rotr(a, b) => {
                a.compile_pass1(stack, imms)?;
                b.compile_pass1(stack, imms)?;
            }
        }

        Ok(())
    }

    fn compile_pass2(
        &self,
        bytecode: &mut dyn io::Write,
        imms: &mut usize,
        sp: &mut usize,
        max_sp: &mut usize,
    ) -> Result<(), io::Error> {
        // helper functions
        fn adjust_sp(
            sp: &mut usize,
            max_sp: &mut usize,
            delta: isize,
            width: usize,
        ) {
            let delta = delta * width as isize;

            *sp = (*sp as isize + delta) as usize;
            if *sp > *max_sp {
                *max_sp = *sp;
            }
        }

        // is node shared?
        let prefs = self.refs.get();
        self.refs.set(prefs - 1);

        // already computed?
        let slot = self.slot.get();
        if let Some(slot) = slot {
            // align stack?
            if *sp % T::WIDTH != 0 {
                let align = T::WIDTH - (*sp % T::WIDTH);
                let align = u8::try_from(align).expect("align overflow");
                Op::new(OpCode::Align, 0, align).encode(bytecode)?;
                adjust_sp(sp, max_sp, align as isize, 1);
            }

            // get slot
            Op::new(OpCode::Get, T::NPW2, slot).encode(bytecode)?;
            adjust_sp(sp, max_sp, 1, T::WIDTH);
            return Ok(());
        }

        match &self.kind {
            OpKind::Imm(_) => {
                // should be entirely handled in first pass
                unreachable!()
            }

            OpKind::Truncate(a) => {
                // keep track of original sp to unalign if needed
                let expected_sp = *sp + T::WIDTH;

                a.compile_pass2(bytecode, imms, sp, max_sp)?;

                // truncate, including unalignment
                let truncate = *sp - expected_sp;
                assert!(truncate % T::WIDTH == 0, "unaligned truncate");
                let truncate = truncate / T::WIDTH;
                let truncate = u8::try_from(truncate).expect("truncate overflow");
                Op::new(OpCode::Truncate, T::NPW2, truncate).encode(bytecode)?;
                adjust_sp(sp, max_sp, -(truncate as isize), T::WIDTH);
            }

            OpKind::Extends(a) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;

                // align as necessary
                let align = if (*sp - a.width()) % T::WIDTH != 0 {
                    T::WIDTH - ((*sp - a.width()) % T::WIDTH)
                } else {
                    0
                };

                let extends = (T::WIDTH - a.width()) + align;
                assert!(extends % a.width() == 0, "unaligned extends");
                let extends = extends / a.width();
                let extends = u8::try_from(extends).expect("extends overflow");
                Op::new(OpCode::Extends, a.npw2(), extends).encode(bytecode)?;
                adjust_sp(sp, max_sp, extends as isize, a.width());
            }

            OpKind::Extendu(a) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;

                // align as necessary
                let align = if (*sp - a.width()) % T::WIDTH != 0 {
                    T::WIDTH - ((*sp - a.width()) % T::WIDTH)
                } else {
                    0
                };

                let extendu = (T::WIDTH - a.width()) + align;
                assert!(extendu % a.width() == 0, "unaligned extendu");
                let extendu = extendu / a.width();
                let extendu = u8::try_from(extendu).expect("extendu overflow");
                Op::new(OpCode::Extendu, a.npw2(), extendu).encode(bytecode)?;
                adjust_sp(sp, max_sp, extendu as isize, a.width());
            }

            OpKind::Select(p, a, b) => {
                p.compile_pass2(bytecode, imms, sp, max_sp)?;
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Select, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -2, T::WIDTH);
            }

            OpKind::Eqz(a) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Eqz, T::NPW2, 0).encode(bytecode)?;
            }

            OpKind::Eq(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Eq, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }

            OpKind::Ne(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Ne, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }

            OpKind::Lts(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Lts, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }

            OpKind::Ltu(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Ltu, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }

            OpKind::Gts(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Gts, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }

            OpKind::Gtu(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Gtu, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }

            OpKind::Les(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Les, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }

            OpKind::Leu(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Leu, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }

            OpKind::Ges(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Ges, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }

            OpKind::Geu(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Geu, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }

            OpKind::Clz(a) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Clz, T::NPW2, 0).encode(bytecode)?;
            }

            OpKind::Ctz(a) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Ctz, T::NPW2, 0).encode(bytecode)?;
            }

            OpKind::Popcnt(a) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Popcnt, T::NPW2, 0).encode(bytecode)?;
            }

            OpKind::Add(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Add, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }

            OpKind::Sub(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Sub, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }

            OpKind::Mul(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Mul, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }

            OpKind::Divs(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Divs, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }

            OpKind::Divu(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Divu, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }

            OpKind::Rems(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Rems, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }

            OpKind::Remu(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Remu, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }

            OpKind::And(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::And, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }

            OpKind::Or(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Or, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }

            OpKind::Xor(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Xor, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }

            OpKind::Shl(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Shl, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }

            OpKind::Shrs(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Shrs, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }

            OpKind::Shru(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Shru, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }

            OpKind::Rotl(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Rotl, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }

            OpKind::Rotr(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp)?;
                b.compile_pass2(bytecode, imms, sp, max_sp)?;
                Op::new(OpCode::Rotr, T::NPW2, 0).encode(bytecode)?;
                adjust_sp(sp, max_sp, -1, T::WIDTH);
            }
        }

        // save for later computations?
        if prefs > 1 {
            // align imms?
            if *imms % T::WIDTH != 0 {
                *imms += T::WIDTH - (*imms % T::WIDTH);
            }

            // set slot and save for later
            assert!(*imms % T::WIDTH == 0, "unaligned slot");
            let slot = *imms / T::WIDTH;
            let slot = u8::try_from(slot).expect("slot overflow");
            Op::new(OpCode::Set, T::NPW2, slot).encode(bytecode)?;
            self.slot.set(Some(slot));

            // update imms
            *imms += T::WIDTH;
        }

        Ok(())
    }
}

impl<T: OpType> fmt::Display for OpTree<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match &self.kind {
            OpKind::Imm(v)          => write!(fmt, "(imm {:?})", v),
            OpKind::Truncate(a)     => write!(fmt, "(truncate {})", a),
            OpKind::Extends(a)      => write!(fmt, "(extends {})", a),
            OpKind::Extendu(a)      => write!(fmt, "(extendu {})", a),
            OpKind::Select(p, a, b) => write!(fmt, "(select {} {} {})", p, a, b),
            OpKind::Eqz(a)          => write!(fmt, "(eqz {})", a),
            OpKind::Eq(a, b)        => write!(fmt, "(eq {} {})", a, b),
            OpKind::Ne(a, b)        => write!(fmt, "(ne {} {})", a, b),
            OpKind::Lts(a, b)       => write!(fmt, "(lts {} {})", a, b),
            OpKind::Ltu(a, b)       => write!(fmt, "(ltu {} {})", a, b),
            OpKind::Gts(a, b)       => write!(fmt, "(gts {} {})", a, b),
            OpKind::Gtu(a, b)       => write!(fmt, "(gtu {} {})", a, b),
            OpKind::Les(a, b)       => write!(fmt, "(les {} {})", a, b),
            OpKind::Leu(a, b)       => write!(fmt, "(leu {} {})", a, b),
            OpKind::Ges(a, b)       => write!(fmt, "(ges {} {})", a, b),
            OpKind::Geu(a, b)       => write!(fmt, "(geu {} {})", a, b),
            OpKind::Clz(a)          => write!(fmt, "(clz {})", a),
            OpKind::Ctz(a)          => write!(fmt, "(ctz {})", a),
            OpKind::Popcnt(a)       => write!(fmt, "(popcnt {})", a),
            OpKind::Add(a, b)       => write!(fmt, "(add {} {})", a, b),
            OpKind::Sub(a, b)       => write!(fmt, "(sub {} {})", a, b),
            OpKind::Mul(a, b)       => write!(fmt, "(mul {} {})", a, b),
            OpKind::Divs(a, b)      => write!(fmt, "(divs {} {})", a, b),
            OpKind::Divu(a, b)      => write!(fmt, "(divu {} {})", a, b),
            OpKind::Rems(a, b)      => write!(fmt, "(rems {} {})", a, b),
            OpKind::Remu(a, b)      => write!(fmt, "(remu {} {})", a, b),
            OpKind::And(a, b)       => write!(fmt, "(and {} {})", a, b),
            OpKind::Or(a, b)        => write!(fmt, "(or {} {})", a, b),
            OpKind::Xor(a, b)       => write!(fmt, "(xor {} {})", a, b),
            OpKind::Shl(a, b)       => write!(fmt, "(shl {} {})", a, b),
            OpKind::Shrs(a, b)      => write!(fmt, "(shrs {} {})", a, b),
            OpKind::Shru(a, b)      => write!(fmt, "(shru {} {})", a, b),
            OpKind::Rotl(a, b)      => write!(fmt, "(rotl {} {})", a, b),
            OpKind::Rotr(a, b)      => write!(fmt, "(rotr {} {})", a, b),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compile_add() {
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
    }

    #[test]
    fn compile_alignment() {
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
    }

    #[test]
    fn compile_dag() {
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
    }

    #[test]
    fn compile_pythag() {
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
    }
}

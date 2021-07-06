//! opcode/bytecode definitions

use std::rc::Rc;
use std::fmt::Debug;
use std::io;
use std::convert::TryFrom;
use std::fmt;
use std::mem::transmute;
use crate::error::Error;
use std::cell::Cell;
use crate::vm::exec;


/// OpCodes emitted as a part of bytecode
///
/// Based on opcodes defined for Wasm, limited to numeric operations
/// with a few extra stack manipulated opcodes since we don't have a
/// system of locals.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[repr(u16)]
pub enum OpCode {
    Get         = 0x1000,
    Set         = 0x2000,
    Truncate    = 0x3000,
    Extends     = 0x4000,
    Extendu     = 0x5000,
    Unalign     = 0x6000,

    Return      = 0xf000,
    Select      = 0xf001,

    Eqz         = 0xf002,
    Eq          = 0xf003,
    Ne          = 0xf004,
    Lts         = 0xf005,
    Ltu         = 0xf006,
    Gts         = 0xf007,
    Gtu         = 0xf008,
    Les         = 0xf009,
    Leu         = 0xf00a,
    Ges         = 0xf00b,
    Geu         = 0xf00c,

    Clz         = 0xf00d,
    Ctz         = 0xf00e,
    Popcnt      = 0xf00f,
    Add         = 0xf010,
    Sub         = 0xf011,
    Mul         = 0xf012,
    Divs        = 0xf013,
    Divu        = 0xf014,
    Rems        = 0xf015,
    Remu        = 0xf016,
    And         = 0xf017,
    Or          = 0xf018,
    Xor         = 0xf019,
    Shl         = 0xf01a,
    Shrs        = 0xf01b,
    Shru        = 0xf01c,
    Rotl        = 0xf01d,
    Rotr        = 0xf01e,
}

impl OpCode {
    pub fn has_imm(&self) -> bool {
        (*self as u16) < 0x8000
    }
}

impl fmt::Display for OpCode {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let name = match self {
            OpCode::Get         => "get",
            OpCode::Set         => "set",
            OpCode::Truncate    => "truncate",
            OpCode::Extends     => "extends",
            OpCode::Extendu     => "extendu",
            OpCode::Unalign     => "unalign",
            OpCode::Return      => "return",
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
        unsafe { transmute(opcode) }
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
            0x1000 => OpCode::Get,
            0x2000 => OpCode::Set,
            0x3000 => OpCode::Truncate,
            0x4000 => OpCode::Extends,
            0x5000 => OpCode::Extendu,
            0x6000 => OpCode::Unalign,
            0xf000 => match op & 0x00ff {
                0x00 => OpCode::Return,
                0x01 => OpCode::Select,
                0x02 => OpCode::Eqz,
                0x03 => OpCode::Eq,
                0x04 => OpCode::Ne,
                0x05 => OpCode::Lts,
                0x06 => OpCode::Ltu,
                0x07 => OpCode::Gts,
                0x08 => OpCode::Gtu,
                0x09 => OpCode::Les,
                0x0a => OpCode::Leu,
                0x0b => OpCode::Ges,
                0x0c => OpCode::Geu,
                0x0d => OpCode::Clz,
                0x0e => OpCode::Ctz,
                0x0f => OpCode::Popcnt,
                0x10 => OpCode::Add,
                0x11 => OpCode::Sub,
                0x12 => OpCode::Mul,
                0x13 => OpCode::Divs,
                0x14 => OpCode::Divu,
                0x15 => OpCode::Rems,
                0x16 => OpCode::Remu,
                0x17 => OpCode::And,
                0x18 => OpCode::Or,
                0x19 => OpCode::Xor,
                0x1a => OpCode::Shl,
                0x1b => OpCode::Shrs,
                0x1c => OpCode::Shru,
                0x1d => OpCode::Rotl,
                0x1e => OpCode::Rotr,
                _ => Err(Error::InvalidOpcode(op))?,
            },
            _ => Err(Error::InvalidOpcode(op))?,
        };

        Ok(Self::new(opcode, npw2, imm))
    }
}

impl fmt::Display for Op {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self.opcode() {
            OpCode::Truncate | OpCode::Extends | OpCode::Extendu => {
                write!(fmt, "{} u{} u{}",
                    self.opcode(),
                    8*self.width(),
                    8*(1 << self.imm())
                )
            }
            _ if self.has_imm() => {
                write!(fmt, "{} u{} {}",
                    self.opcode(),
                    8*self.width(),
                    self.imm()
                )
            }
            _ => {
                write!(fmt, "{} u{}",
                    self.opcode(),
                    8*self.width()
                )
            }
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
pub trait OpType: Copy + Clone + Default + Debug {
    /// width in bytes, emitted as part of bytecode
    const WIDTH: usize;

    /// npw2(width), used in instruction encoding
    const NPW2: u8;

    /// write into stack as bytes
    fn encode(&self, stack: &mut dyn io::Write) -> Result<(), io::Error>;

    /// read from stack
    fn decode(stack: &mut dyn io::Read) -> Result<Self, io::Error>;

    // constant OpTree pool
    fn zero() -> Rc<OpTree<Self>>;
    fn one()  -> Rc<OpTree<Self>>;
    fn ones() -> Rc<OpTree<Self>>;
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

            fn decode(
                stack: &mut dyn io::Read
            ) -> Result<Self, io::Error> {
                let mut buf = [0; $w];
                stack.read_exact(&mut buf)?;
                Ok(<$t>::from_le_bytes(buf))
            }

            // Common constants, since these are reference counted and deduplicated,
            // having a pool of constants can help reduce duplicate immediates, though
            // note these should only be used if they are not a secret

            // These must be declared here since thread-local storage can't depend on
            // generic types

            fn zero() -> Rc<OpTree<Self>> {
                thread_local! {
                    static ZERO: Rc<OpTree<$t>> = Rc::new(OpTree::new(OpKind::Imm(0)));
                }
                ZERO.with(|v| v.clone())
            }

            fn one() -> Rc<OpTree<Self>> {
                thread_local! {
                    static ONE: Rc<OpTree<$t>> = Rc::new(OpTree::new(OpKind::Imm(1)));
                }
                ONE.with(|v| v.clone())
            }

            fn ones() -> Rc<OpTree<Self>> {
                thread_local! {
                    static ONES: Rc<OpTree<$t>> = Rc::new(OpTree::new(OpKind::Imm(<$t>::MAX)));
                }
                ONES.with(|v| v.clone())
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

    // Common constants, since these are reference counted and deduplicated,
    // having a pool of constants can help reduce duplicate immediates, though
    // note these should only be used if they are not a secret
    pub fn zero() -> Rc<Self> {
        T::zero()
    }

    pub fn one() -> Rc<Self> {
        T::one()
    }

    pub fn ones() -> Rc<Self> {
        T::ones()
    }

    /// high-level compile into bytecode, stack, and initial stack pointer
    pub fn compile(&self) -> (Vec<u8>, Vec<u8>) {
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
        let mut max_align = 0usize;
        self.compile_pass2(
            &mut bytecode,
            &mut imms,
            &mut sp,
            &mut max_sp,
            &mut max_align
        ).expect("vector write resulted in io::error?");

        // add return instruction to type-check the result
        Op::new(OpCode::Return, T::NPW2, 0).encode(&mut bytecode)
            .expect("vector write resulted in io::error?");

        // at this point stack contains imms, but we also need space for
        // the working stack
        let imms = imms + max_align-1;
        let imms = imms - (imms % max_align);
        stack.resize(imms + max_sp, 0);

        // imms is now the initial stack pointer
        (bytecode, stack)
    }

    /// try to get immediate value if we are a flat value
    pub fn imm(&self) -> Option<T> {
        match self.kind {
            OpKind::Imm(v) => Some(v),
            _              => None,
        }
    }

    /// compile and execute if value is not an immediate already
    pub fn eval(&self) -> Result<T, Error> {
        match self.imm() {
            Some(v) => Ok(v),
            None => {
                let (bytecode, mut stack) = self.compile();
                let mut res = exec(&bytecode, &mut stack)?;
                let v = T::decode(&mut res).map_err(|_| Error::InvalidReturn)?;
                Ok(v)
            }
        }
    }
}

impl<T: OpType> From<T> for OpTree<T> {
    fn from(t: T) -> OpTree<T> {
        OpTree::new(OpKind::Imm(t))
    }
}

impl<T: OpType> Default for OpTree<T> {
    fn default() -> OpTree<T> {
        OpTree::new(OpKind::Imm(T::default()))
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
        max_align: &mut usize,
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
        max_align: &mut usize,
    ) -> Result<(), io::Error> {
        // helper functions
        fn sp_push(
            sp: &mut usize,
            max_sp: &mut usize,
            delta: usize,
            width: usize,
        ) {
            let x = *sp + (delta * width);
            *sp = x;
            if x > *max_sp {
                *max_sp = x;
            }
        }

        fn sp_pop(
            sp: &mut usize,
            _max_sp: &mut usize,
            delta: usize,
            width: usize,
        ) {
            let x = *sp - (delta * width);
            *sp = x;
        }

        fn sp_align(
            sp: &mut usize,
            max_align: &mut usize,
            width: usize,
        ) {
            // align up, we assume sp_align is followed by sp_push,
            // so we leave it to sp_push to check max_sp
            let x = *sp;
            let x = x + width-1;
            let x = x - (x % width);
            *sp = x;

            // all pushes onto the stack go through a sp_align, so
            // this is where we can also find the max_align
            if width > *max_align {
                *max_align = width;
            }
        }

        // is node shared?
        let prefs = self.refs.get();
        self.refs.set(prefs - 1);

        // already computed?
        let slot = self.slot.get();
        if let Some(slot) = slot {
            // get slot and align
            Op::new(OpCode::Get, T::NPW2, slot).encode(bytecode)?;
            sp_align(sp, max_align, T::WIDTH);
            sp_push(sp, max_sp, 1, T::WIDTH);
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

                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;

                // truncate
                Op::new(OpCode::Truncate, T::NPW2, a.npw2()).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, a.width());
                sp_push(sp, max_sp, 1, T::WIDTH);

                // manually unalign?
                if *sp > expected_sp {
                    let diff = *sp - expected_sp;
                    assert!(diff % T::WIDTH == 0, "unaligned truncate");
                    let diff = diff / T::WIDTH;
                    let diff = u8::try_from(diff).expect("unalign overflow");
                    Op::new(OpCode::Unalign, T::NPW2, diff).encode(bytecode)?;
                    sp_pop(sp, max_sp, diff as usize, T::WIDTH);
                }
            }

            OpKind::Extends(a) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;

                // extends and align
                Op::new(OpCode::Extends, a.npw2(), T::NPW2).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, a.width());
                sp_align(sp, max_align, T::WIDTH);
                sp_push(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Extendu(a) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;

                // extendu and align
                Op::new(OpCode::Extendu, a.npw2(), T::NPW2).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, a.width());
                sp_align(sp, max_align, T::WIDTH);
                sp_push(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Select(p, a, b) => {
                p.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Select, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 2, T::WIDTH);
            }

            OpKind::Eqz(a) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Eqz, T::NPW2, 0).encode(bytecode)?;
            }

            OpKind::Eq(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Eq, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Ne(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Ne, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Lts(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Lts, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Ltu(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Ltu, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Gts(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Gts, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Gtu(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Gtu, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Les(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Les, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Leu(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Leu, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Ges(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Ges, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Geu(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Geu, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Clz(a) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Clz, T::NPW2, 0).encode(bytecode)?;
            }

            OpKind::Ctz(a) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Ctz, T::NPW2, 0).encode(bytecode)?;
            }

            OpKind::Popcnt(a) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Popcnt, T::NPW2, 0).encode(bytecode)?;
            }

            OpKind::Add(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Add, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Sub(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Sub, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Mul(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Mul, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Divs(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Divs, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Divu(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Divu, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Rems(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Rems, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Remu(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Remu, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::And(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::And, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Or(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Or, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Xor(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Xor, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Shl(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Shl, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Shrs(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Shrs, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Shru(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Shru, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Rotl(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Rotl, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
            }

            OpKind::Rotr(a, b) => {
                a.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                b.compile_pass2(bytecode, imms, sp, max_sp, max_align)?;
                Op::new(OpCode::Rotr, T::NPW2, 0).encode(bytecode)?;
                sp_pop(sp, max_sp, 1, T::WIDTH);
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

        assert_eq!(bytecode.len(), 4*2);
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

        assert_eq!(bytecode.len(), 7*2);
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

        assert_eq!(bytecode.len(), 15*2);
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

        assert_eq!(bytecode.len(), 12*2);
        assert_eq!(stack.len(), 6*4);
    }
}

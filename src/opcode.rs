//! opcode/bytecode definitions

use std::rc::Rc;
use std::rc::Weak;
use std::fmt::Debug;
use std::io;
use std::convert::TryFrom;
use std::fmt;
use std::mem::transmute;
use crate::error::Error;
use std::cell::Cell;
use crate::vm::exec;
use std::cmp::max;
use std::collections::HashMap;
use std::cell::RefCell;


/// OpCodes emitted as a part of bytecode
///
/// Based on opcodes defined for Wasm, limited to numeric operations
/// with a few extra stack manipulated opcodes since we don't have a
/// system of locals.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[repr(u16)]
pub enum OpCode {
    Get         = 0x100,
    Set         = 0x200,
    Truncate    = 0x300,
    Extends     = 0x400,
    Extendu     = 0x500,
    Unalign     = 0x600,

    Return      = 0xf00,
    Select      = 0xf01,

    Eqz         = 0xf02,
    Eq          = 0xf03,
    Ne          = 0xf04,
    Lts         = 0xf05,
    Ltu         = 0xf06,
    Gts         = 0xf07,
    Gtu         = 0xf08,
    Les         = 0xf09,
    Leu         = 0xf0a,
    Ges         = 0xf0b,
    Geu         = 0xf0c,

    Clz         = 0xf0d,
    Ctz         = 0xf0e,
    Popcnt      = 0xf0f,
    Add         = 0xf10,
    Sub         = 0xf11,
    Mul         = 0xf12,
    Divs        = 0xf13,
    Divu        = 0xf14,
    Rems        = 0xf15,
    Remu        = 0xf16,
    And         = 0xf17,
    Or          = 0xf18,
    Xor         = 0xf19,
    Shl         = 0xf1a,
    Shrs        = 0xf1b,
    Shru        = 0xf1c,
    Rotl        = 0xf1d,
    Rotr        = 0xf1e,
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
        Op(((npw2 as u16) << 12) | (opcode as u16) | (imm as u16))
    }

    pub fn has_imm(&self) -> bool {
        self.0 & 0x800 == 0x000
    }

    pub fn opcode(&self) -> OpCode {
        let opcode = if self.has_imm() {
            self.0 & 0xf00
        } else {
            self.0 & 0xfff
        };

        // we check for OpCode validity on every function that can build
        // an Op, so this should only result in valid OpCodes
        unsafe { transmute(opcode) }
    }

    pub fn npw2(&self) -> u8 {
        (self.0 >> 12) as u8
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
        let npw2 = (op >> 12) as u8;
        let imm = (op & 0x00ff) as u8;

        let opcode = match op & 0x0f00 {
            0x100 => OpCode::Get,
            0x200 => OpCode::Set,
            0x300 => OpCode::Truncate,
            0x400 => OpCode::Extends,
            0x500 => OpCode::Extendu,
            0x600 => OpCode::Unalign,
            0xf00 => match op & 0x00ff {
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
                write!(fmt, "u{}.{} u{}",
                    8*self.width(),
                    self.opcode(),
                    8*(1 << self.imm())
                )
            }
            _ if self.has_imm() => {
                write!(fmt, "u{}.{} {}",
                    8*self.width(),
                    self.opcode(),
                    self.imm()
                )
            }
            _ => {
                write!(fmt, "u{}.{}",
                    8*self.width(),
                    self.opcode()
                )
            }
        }
    }
}

/// helper function for debugging
pub fn disas<W: io::Write>(
    bytecode: &[u8],
    mut out: W
) -> Result<(), io::Error> {
    let mut bytecode = bytecode;
    while bytecode.len() > 0 {
        match Op::decode(&mut bytecode)? {
            Ok(opcode) => {
                writeln!(out, "    {}", opcode)?;
            }
            Err(Error::InvalidOpcode(op)) => {
                writeln!(out, "    unknown {:#06x}", op)?;
            }
            Err(_) => {
                panic!("unexpected error in disas?");
            }
        }
    }

    Ok(())
}


/// Trait for types that can be compiled
pub trait OpType: Copy + Clone + Default + Debug + 'static {
    /// width in bytes, emitted as part of bytecode
    const WIDTH: usize;

    /// npw2(width), used in instruction encoding
    const NPW2: u8;

    /// write into stack as bytes
    fn encode(&self, stack: &mut dyn io::Write) -> Result<(), io::Error>;

    /// read from stack
    fn decode(stack: &mut dyn io::Read) -> Result<Self, io::Error>;

    /// Register a const in this OpType's constant pool
    ///
    /// Note, this needs to be here since thread-local storage can't
    /// depend on generic types
    fn constant(v: Self) -> Rc<OpTree<Self>>;
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

            fn constant(v: Self) -> Rc<OpTree<Self>> {
                thread_local! {
                    static CONSTANTS: RefCell<HashMap<$t, Weak<OpTree<$t>>>> = {
                        RefCell::new(HashMap::new())
                    };
                }

                CONSTANTS.with(|map| {
                    let mut map = map.borrow_mut();

                    let c = map.get(&v).and_then(|c| c.upgrade());
                    if let Some(c) = c {
                        c
                    } else {
                        let c = Rc::new(OpTree::new(OpKind::Imm(v)));
                        map.insert(v, Rc::downgrade(&c));
                        c
                    }
                })
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
    Sym(&'static str),

    Truncate(Rc<dyn DynOpTree>),
    Extends(Rc<dyn DynOpTree>),
    Extendu(Rc<dyn DynOpTree>),
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

/// Compilation state
pub struct OpCompile<'a> {
    bytecode: &'a mut dyn io::Write,
    stack: &'a mut dyn io::Write,

    imms: usize,
    sp: usize,
    max_sp: usize,
    max_align: usize,

    slot_pool: Option<Vec<(u8, u8)>>,
}

impl OpCompile<'_> {
    fn new<'a>(
        bytecode: &'a mut dyn io::Write,
        stack: &'a mut dyn io::Write,
        opt: bool,
    ) -> OpCompile<'a> {
        OpCompile {
            bytecode: bytecode,
            stack: stack,

            imms: 0,
            sp: 0,
            max_sp: 0,
            max_align: 0,

            slot_pool: opt.then(|| Vec::new()),
        }
    }

    // helper functions
    fn sp_push(
        &mut self,
        delta: usize,
        width: usize,
    ) {
        let x = self.sp + (delta * width);
        self.sp = x;
        self.max_sp = max(self.max_sp, x);
    }

    fn sp_pop(
        &mut self,
        delta: usize,
        width: usize,
    ) {
        let x = self.sp - (delta * width);
        self.sp = x;
    }

    fn sp_align(
        &mut self,
        width: usize,
    ) {
        // align up, we assume sp_align is followed by sp_push,
        // so we leave it to sp_push to check max_sp
        let x = self.sp;
        let x = x + width-1;
        let x = x - (x % width);
        self.sp = x;

        // all pushes onto the stack go through a sp_align, so
        // this is where we can also find the max_align
        self.max_align = max(self.max_align, width);
    }
}

impl<T: OpType> OpTree<T> {
    pub fn new(kind: OpKind<T>) -> OpTree<T> {
        OpTree {
            kind: kind,
            refs: Cell::new(0),
            slot: Cell::new(None),
        }
    }

    /// Register a const in this OpType's constant pool
    pub fn constant(v: T) -> Rc<Self> {
        T::constant(v)
    }

    /// high-level compile into bytecode, stack, and initial stack pointer
    pub fn compile(&self, opt: bool) -> (Vec<u8>, Vec<u8>) {
        // NOTE! We make sure to zero all refs from pass1 to pass2, this is
        // rather fragile and requires all passes to always be run as a pair,
        // we can't interrupt between passes without needing to reset all
        // internal reference counts

        let mut bytecode = Vec::new();
        let mut stack = Vec::new();
        let mut state = OpCompile::new(&mut bytecode, &mut stack, opt);

        // first pass to find number of immediates and deduplicate branches
        self.compile_pass1(&mut state)
            .expect("vector write resulted in io::error?");

        // second pass now to compile the bytecode and stack, note sp now points
        // to end of immediates
        self.compile_pass2(&mut state)
            .expect("vector write resulted in io::error?");

        // at this point stack contains imms, but we also need space for
        // the working stack
        let imms = state.imms + state.max_align-1;
        let imms = imms - (imms % state.max_align);
        let imms = imms + state.max_sp;
        stack.resize(imms, 0);

        // add return instruction to type-check the result
        Op::new(OpCode::Return, T::NPW2, 0).encode(&mut bytecode)
            .expect("vector write resulted in io::error?");

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
                let (bytecode, mut stack) = self.compile(false);
                let mut res = exec(&bytecode, &mut stack)?;
                let v = T::decode(&mut res).map_err(|_| Error::InvalidReturn)?;
                Ok(v)
            }
        }
    }

    /// Assuming we are Sym, patch the stack during a call
    pub fn patch(&self, v: T, stack: &mut [u8]) {
        assert!(
            match self.kind {
                OpKind::Sym(_) => true,
                _              => false,
            },
            "patching non-sym?"
        );

        let slot = self.slot.get().expect("patching with no slot?");
        let mut slice = &mut stack[
            slot as usize * T::WIDTH
                .. slot as usize * T::WIDTH + T::WIDTH
        ];
        v.encode(&mut slice).expect("slice write resulted in io::error?");
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
            // don't bother showing truncate if it's used as a nop,
            // it won't be emitted
            OpKind::Truncate(a) if a.width() == T::WIDTH => {
                return write!(fmt, "{}", a)
            }
            _ => {}
        }

        let w = 8*T::WIDTH;
        match &self.kind {
            OpKind::Imm(v)          => write!(fmt, "(u{}.imm {:?})", w, v),
            OpKind::Sym(s)          => write!(fmt, "(u{}.sym {:?})", w, s),
            OpKind::Truncate(a)     => write!(fmt, "(u{}.truncate {})", w, a),
            OpKind::Extends(a)      => write!(fmt, "(u{}.extends {})", w, a),
            OpKind::Extendu(a)      => write!(fmt, "(u{}.extendu {})", w, a),
            OpKind::Select(p, a, b) => write!(fmt, "(u{}.select {} {} {})", w, p, a, b),
            OpKind::Eqz(a)          => write!(fmt, "(u{}.eqz {})", w, a),
            OpKind::Eq(a, b)        => write!(fmt, "(u{}.eq {} {})", w, a, b),
            OpKind::Ne(a, b)        => write!(fmt, "(u{}.ne {} {})", w, a, b),
            OpKind::Lts(a, b)       => write!(fmt, "(u{}.lts {} {})", w, a, b),
            OpKind::Ltu(a, b)       => write!(fmt, "(u{}.ltu {} {})", w, a, b),
            OpKind::Gts(a, b)       => write!(fmt, "(u{}.gts {} {})", w, a, b),
            OpKind::Gtu(a, b)       => write!(fmt, "(u{}.gtu {} {})", w, a, b),
            OpKind::Les(a, b)       => write!(fmt, "(u{}.les {} {})", w, a, b),
            OpKind::Leu(a, b)       => write!(fmt, "(u{}.leu {} {})", w, a, b),
            OpKind::Ges(a, b)       => write!(fmt, "(u{}.ges {} {})", w, a, b),
            OpKind::Geu(a, b)       => write!(fmt, "(u{}.geu {} {})", w, a, b),
            OpKind::Clz(a)          => write!(fmt, "(u{}.clz {})", w, a),
            OpKind::Ctz(a)          => write!(fmt, "(u{}.ctz {})", w, a),
            OpKind::Popcnt(a)       => write!(fmt, "(u{}.popcnt {})", w, a),
            OpKind::Add(a, b)       => write!(fmt, "(u{}.add {} {})", w, a, b),
            OpKind::Sub(a, b)       => write!(fmt, "(u{}.sub {} {})", w, a, b),
            OpKind::Mul(a, b)       => write!(fmt, "(u{}.mul {} {})", w, a, b),
            OpKind::Divs(a, b)      => write!(fmt, "(u{}.divs {} {})", w, a, b),
            OpKind::Divu(a, b)      => write!(fmt, "(u{}.divu {} {})", w, a, b),
            OpKind::Rems(a, b)      => write!(fmt, "(u{}.rems {} {})", w, a, b),
            OpKind::Remu(a, b)      => write!(fmt, "(u{}.remu {} {})", w, a, b),
            OpKind::And(a, b)       => write!(fmt, "(u{}.and {} {})", w, a, b),
            OpKind::Or(a, b)        => write!(fmt, "(u{}.or {} {})", w, a, b),
            OpKind::Xor(a, b)       => write!(fmt, "(u{}.xor {} {})", w, a, b),
            OpKind::Shl(a, b)       => write!(fmt, "(u{}.shl {} {})", w, a, b),
            OpKind::Shrs(a, b)      => write!(fmt, "(u{}.shrs {} {})", w, a, b),
            OpKind::Shru(a, b)      => write!(fmt, "(u{}.shru {} {})", w, a, b),
            OpKind::Rotl(a, b)      => write!(fmt, "(u{}.rotl {} {})", w, a, b),
            OpKind::Rotr(a, b)      => write!(fmt, "(u{}.rotr {} {})", w, a, b),
        }
    }
}


// dyn-compatible wrapping trait
pub trait DynOpTree: Debug + fmt::Display {
    /// type's width in bytes, needed for determining cast sizes
    fn width(&self) -> usize;

    /// npw2(width), used as a part of instruction encoding
    fn npw2(&self) -> u8;

    /// hook to enable eqz without known type
    fn eqz(&self) -> &'static dyn Fn(Rc<dyn DynOpTree>) -> Rc<dyn DynOpTree>;

    /// First compile pass, used to find the number of immediates
    /// for offset calculation, and local reference counting to
    /// deduplicate branches.
    fn compile_pass1(&self, state: &mut OpCompile) -> Result<(), io::Error>;

    /// Second compile pass, used to actually compile both the
    /// immediates and bytecode. Since both bytecode and stack are
    /// generic writers, a null writer could be used if either are
    /// not needed.
    fn compile_pass2(&self, state: &mut OpCompile) -> Result<(), io::Error>;
}

impl<T: OpType> DynOpTree for OpTree<T> {
    fn width(&self) -> usize {
        T::WIDTH
    }

    fn npw2(&self) -> u8 {
        T::NPW2
    }

    fn eqz(&self) -> &'static dyn Fn(Rc<dyn DynOpTree>) -> Rc<dyn DynOpTree> {
        // bit messy but this works
        // unfortunately this only works when there is a single argument
        fn eqz<T: OpType>(tree: Rc<dyn DynOpTree>) -> Rc<dyn DynOpTree> {
            Rc::new(OpTree::<T>::new(OpKind::<T>::Eqz(
                // truncate here is a nop
                Rc::new(OpTree::<T>::new(OpKind::<T>::Truncate(tree)))
            )))
        }
        &eqz::<T>
    }

    fn compile_pass1(&self, state: &mut OpCompile) -> Result<(), io::Error> {
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
                while state.imms % T::WIDTH != 0 {
                    state.stack.write_all(&[0])?;
                    state.imms += 1;
                }

                // save slot
                assert!(state.imms % T::WIDTH == 0, "unaligned slot");
                let slot = state.imms / T::WIDTH;
                let slot = u8::try_from(slot).expect("slot overflow");
                self.slot.set(Some(slot));

                // write imm to stack
                v.encode(state.stack)?;

                // update imms
                state.imms += T::WIDTH;
            }

            OpKind::Sym(_) => {
                // align imms?
                while state.imms % T::WIDTH != 0 {
                    state.stack.write_all(&[0])?;
                    state.imms += 1;
                }

                // save slot
                assert!(state.imms % T::WIDTH == 0, "unaligned slot");
                let slot = state.imms / T::WIDTH;
                let slot = u8::try_from(slot).expect("slot overflow");
                self.slot.set(Some(slot));

                // we'll fill this in later, use an arbitrary constant
                // to hopefully help debugging
                for _ in 0..T::WIDTH {
                    state.stack.write_all(&[0xcc])?;
                }

                // update imms
                state.imms += T::WIDTH;
            }

            OpKind::Truncate(a) => {
                a.compile_pass1(state)?;
            }

            OpKind::Extends(a) => {
                a.compile_pass1(state)?;
            }

            OpKind::Extendu(a) => {
                a.compile_pass1(state)?;
            }

            OpKind::Select(p, a, b) => {
                p.compile_pass1(state)?;
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::Eqz(a) => {
                a.compile_pass1(state)?;
            }

            OpKind::Eq(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::Ne(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::Lts(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::Ltu(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::Gts(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::Gtu(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::Les(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::Leu(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::Ges(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::Geu(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::Clz(a) => {
                a.compile_pass1(state)?;
            }

            OpKind::Ctz(a) => {
                a.compile_pass1(state)?;
            }

            OpKind::Popcnt(a) => {
                a.compile_pass1(state)?;
            }

            OpKind::Add(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::Sub(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::Mul(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::Divs(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::Divu(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::Rems(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::Remu(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::And(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::Or(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::Xor(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::Shl(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::Shrs(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::Shru(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::Rotl(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }

            OpKind::Rotr(a, b) => {
                a.compile_pass1(state)?;
                b.compile_pass1(state)?;
            }
        }

        Ok(())
    }

    fn compile_pass2(&self, state: &mut OpCompile) -> Result<(), io::Error> {
        // is node shared?
        let prefs = self.refs.get();
        self.refs.set(prefs - 1);

        // already computed?
        let slot = self.slot.get();
        if let Some(slot) = slot {
            // get slot and align
            Op::new(OpCode::Get, T::NPW2, slot).encode(state.bytecode)?;
            state.sp_align(T::WIDTH);
            state.sp_push(1, T::WIDTH);

            // are we done with slot? contribute to slot_pool
            if prefs == 1 {
                if let Some(pool) = state.slot_pool.as_mut() {
                    pool.push((T::NPW2, slot));
                }
            }

            return Ok(());
        }

        match &self.kind {
            OpKind::Imm(_) => {
                // should be entirely handled in first pass
                unreachable!()
            }

            OpKind::Sym(_) => {
                // should be entirely handled in first pass
                unreachable!()
            }

            OpKind::Truncate(a) => {
                // keep track of original sp to unalign if needed
                let expected_sp = state.sp + T::WIDTH;

                a.compile_pass2(state)?;

                // nop if size does not change
                if a.width() != T::WIDTH {
                    // truncate
                    Op::new(OpCode::Truncate, T::NPW2, a.npw2()).encode(state.bytecode)?;
                    state.sp_pop(1, a.width());
                    state.sp_push(1, T::WIDTH);
                }

                // manually unalign?
                if state.sp > expected_sp {
                    let diff = state.sp - expected_sp;
                    assert!(diff % T::WIDTH == 0, "unaligned truncate");
                    let diff = diff / T::WIDTH;
                    let diff = u8::try_from(diff).expect("unalign overflow");
                    Op::new(OpCode::Unalign, T::NPW2, diff).encode(state.bytecode)?;
                    state.sp_pop(diff as usize, T::WIDTH);
                }
            }

            OpKind::Extends(a) => {
                a.compile_pass2(state)?;

                // extends and align
                Op::new(OpCode::Extends, a.npw2(), T::NPW2).encode(state.bytecode)?;
                state.sp_pop(1, a.width());
                state.sp_align(T::WIDTH);
                state.sp_push(1, T::WIDTH);
            }

            OpKind::Extendu(a) => {
                a.compile_pass2(state)?;

                // extendu and align
                Op::new(OpCode::Extendu, a.npw2(), T::NPW2).encode(state.bytecode)?;
                state.sp_pop(1, a.width());
                state.sp_align(T::WIDTH);
                state.sp_push(1, T::WIDTH);
            }

            OpKind::Select(p, a, b) => {
                p.compile_pass2(state)?;
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Select, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(2, T::WIDTH);
            }

            OpKind::Eqz(a) => {
                a.compile_pass2(state)?;
                Op::new(OpCode::Eqz, T::NPW2, 0).encode(state.bytecode)?;
            }

            OpKind::Eq(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Eq, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }

            OpKind::Ne(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Ne, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }

            OpKind::Lts(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Lts, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }

            OpKind::Ltu(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Ltu, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }

            OpKind::Gts(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Gts, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }

            OpKind::Gtu(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Gtu, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }

            OpKind::Les(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Les, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }

            OpKind::Leu(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Leu, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }

            OpKind::Ges(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Ges, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }

            OpKind::Geu(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Geu, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }

            OpKind::Clz(a) => {
                a.compile_pass2(state)?;
                Op::new(OpCode::Clz, T::NPW2, 0).encode(state.bytecode)?;
            }

            OpKind::Ctz(a) => {
                a.compile_pass2(state)?;
                Op::new(OpCode::Ctz, T::NPW2, 0).encode(state.bytecode)?;
            }

            OpKind::Popcnt(a) => {
                a.compile_pass2(state)?;
                Op::new(OpCode::Popcnt, T::NPW2, 0).encode(state.bytecode)?;
            }

            OpKind::Add(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Add, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }

            OpKind::Sub(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Sub, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }

            OpKind::Mul(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Mul, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }

            OpKind::Divs(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Divs, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }

            OpKind::Divu(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Divu, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }

            OpKind::Rems(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Rems, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }

            OpKind::Remu(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Remu, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }

            OpKind::And(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::And, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }

            OpKind::Or(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Or, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }

            OpKind::Xor(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Xor, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }

            OpKind::Shl(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Shl, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }

            OpKind::Shrs(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Shrs, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }

            OpKind::Shru(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Shru, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }

            OpKind::Rotl(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Rotl, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }

            OpKind::Rotr(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Rotr, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::WIDTH);
            }
        }

        // save for later computations?
        if prefs > 1 {
            // can we reuse a slot in the slot pool?
            let slot = state.slot_pool.as_mut().and_then(|pool| {
                let slot = pool.iter().copied()
                    .enumerate()
                    .filter(|(_, (npw2, _))| *npw2 >= T::NPW2)
                    .min_by_key(|(_, (npw2, _))| *npw2);
                if let Some((i, (_, slot))) = slot {
                    pool.remove(i);
                    Some(slot)
                } else {
                    None
                }
            });

            // fallback to allocating an immediate
            let slot = slot.unwrap_or_else(|| {
                // align imms?
                if state.imms % T::WIDTH != 0 {
                    state.imms += T::WIDTH - (state.imms % T::WIDTH);
                }

                assert!(state.imms % T::WIDTH == 0, "unaligned slot");
                let slot = state.imms / T::WIDTH;
                let slot = u8::try_from(slot).expect("slot overflow");

                // update imms
                state.imms += T::WIDTH;

                slot
            });

            // set slot and save for later
            Op::new(OpCode::Set, T::NPW2, slot).encode(state.bytecode)?;
            self.slot.set(Some(slot));
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
        let (bytecode, stack) = example.compile(true);
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
        let (bytecode, stack) = example.compile(true);
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
        let (bytecode, stack) = example.compile(true);
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
        assert_eq!(stack.len(), 6*4);
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
        let (bytecode, stack) = example.compile(true);
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

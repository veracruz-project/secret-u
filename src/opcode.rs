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

use aligned_utils::bytes::AlignedBytes;


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

    pub fn size(&self) -> usize {
        1usize << self.npw2()
    }

    pub fn width(&self) -> usize {
        8*self.size()
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
                    self.width(),
                    self.opcode(),
                    8*(1 << self.imm())
                )
            }
            _ if self.has_imm() => {
                write!(fmt, "u{}.{} {}",
                    self.width(),
                    self.opcode(),
                    self.imm()
                )
            }
            _ => {
                write!(fmt, "u{}.{}",
                    self.width(),
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
pub trait OpType: Copy + Clone + Debug + 'static {
    /// size in bytes
    const SIZE: usize;

    /// width in bits
    const WIDTH: usize;

    /// npw2(size), used in instruction encoding
    const NPW2: u8;

    /// workaround for lack of array default impls
    fn default() -> Self;

    /// write into stack as bytes
    fn encode(&self, stack: &mut dyn io::Write) -> Result<(), io::Error>;

    /// read from stack
    fn decode(stack: &mut dyn io::Read) -> Result<Self, io::Error>;

    /// A constant, non-secret 0
    ///
    /// Note, this needs to be here since thread-local storage can't
    /// depend on generic types
    fn zero() -> Rc<OpTree<Self>>;

    /// A constant, non-secret 1
    ///
    /// Note, this needs to be here since thread-local storage can't
    /// depend on generic types
    fn one() -> Rc<OpTree<Self>>;

    /// A constant with all bits set to 1, non-secret
    ///
    /// Note, this needs to be here since thread-local storage can't
    /// depend on generic types
    fn ones() -> Rc<OpTree<Self>>;

    /// Register a const in this OpType's constant pool
    ///
    /// Note, this needs to be here since thread-local storage can't
    /// depend on generic types
    fn const_(v: Self) -> Rc<OpTree<Self>>;

    /// Test if self is zero
    fn is_zero(&self) -> bool;

    /// Test if self is one
    fn is_one(&self) -> bool;

    /// Test if self is ones
    fn is_ones(&self) -> bool;
}

macro_rules! optype_impl {
    ([u8; $n:literal ($p:literal)]) => {
        impl OpType for [u8;$n] {
            const SIZE: usize = $n;
            const WIDTH: usize = 8*$n;
            const NPW2: u8 = $p;

            fn default() -> Self {
                [0; $n]
            }

            fn encode(
                &self,
                stack: &mut dyn io::Write
            ) -> Result<(), io::Error> {
                stack.write_all(self)
            }

            fn decode(
                stack: &mut dyn io::Read
            ) -> Result<Self, io::Error> {
                let mut buf = [0; $n];
                stack.read_exact(&mut buf)?;
                Ok(buf)
            }

            fn zero() -> Rc<OpTree<Self>> {
                // Hold an Rc here so this is never freed
                thread_local! {
                    static ZERO: RefCell<Option<Rc<OpTree<[u8;$n]>>>> = RefCell::new(None);
                }

                ZERO.with(|v| {
                    v.borrow_mut()
                        .get_or_insert_with(|| Self::const_([0; $n]))
                        .clone()
                })
            }

            fn one() -> Rc<OpTree<Self>> {
                // Hold an Rc here so this is never freed
                thread_local! {
                    static ONE: RefCell<Option<Rc<OpTree<[u8;$n]>>>> = RefCell::new(None);
                }

                ONE.with(|v| {
                    v.borrow_mut()
                        .get_or_insert_with(|| {
                            // don't know an easier way to build this
                            let mut one = [0; $n];
                            one[0] = 1;
                            Self::const_(one)
                        })
                        .clone()
                })
            }

            fn ones() -> Rc<OpTree<Self>> {
                // Hold an Rc here so this is never freed
                thread_local! {
                    static ONES: RefCell<Option<Rc<OpTree<[u8;$n]>>>> = RefCell::new(None);
                }

                ONES.with(|v| {
                    v.borrow_mut()
                        .get_or_insert_with(|| Self::const_([0xff; $n]))
                        .clone()
                })
            }

            fn const_(v: Self) -> Rc<OpTree<Self>> {
                thread_local! {
                    static CONSTANTS: RefCell<HashMap<[u8;$n], Weak<OpTree<[u8;$n]>>>> = {
                        RefCell::new(HashMap::new())
                    };
                }

                CONSTANTS.with(|map| {
                    let mut map = map.borrow_mut();

                    let c = map.get(&v).and_then(|c| c.upgrade());
                    if let Some(c) = c {
                        c
                    } else {
                        let c = Rc::new(OpTree::new(OpKind::Imm(v), true));
                        map.insert(v, Rc::downgrade(&c));
                        c
                    }
                })
            }

            fn is_zero(&self) -> bool {
                self == &[0; $n]
            }

            fn is_one(&self) -> bool {
                // don't know an easier way to build this
                let mut one = [0; $n];
                one[0] = 1;
                self == &one
            }

            fn is_ones(&self) -> bool {
                self == &[0xff; $n]
            }
        }
    };

}

optype_impl! { [u8; 1   (0)] }
optype_impl! { [u8; 2   (1)] }
optype_impl! { [u8; 4   (2)] }
optype_impl! { [u8; 8   (3)] }
optype_impl! { [u8; 16  (4)] }
optype_impl! { [u8; 32  (5)] }
optype_impl! { [u8; 64  (6)] }
optype_impl! { [u8; 128 (7)] }




/// Kinds of operations in tree
#[derive(Debug)]
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
#[derive(Debug)]
pub struct OpTree<T: OpType> {
    kind: OpKind<T>,
    refs: Cell<u32>,
    slot: Cell<Option<u8>>,
    const_: bool,
    #[cfg(feature="opt-const-folding")]
    folded: RefCell<Option<Option<Rc<OpTree<T>>>>>,
}

/// Compilation state
pub struct OpCompile<'a> {
    bytecode: &'a mut dyn io::Write,
    stack: &'a mut dyn io::Write,

    imms: usize,
    sp: usize,
    max_sp: usize,
    max_align: usize,

    #[cfg(feature="opt-register-coloring")]
    slot_pool: Option<Vec<(u8, u8)>>,
}

impl OpCompile<'_> {
    fn new<'a>(
        bytecode: &'a mut dyn io::Write,
        stack: &'a mut dyn io::Write,
        #[allow(unused)]
        opt: bool,
    ) -> OpCompile<'a> {
        OpCompile {
            bytecode: bytecode,
            stack: stack,

            imms: 0,
            sp: 0,
            max_sp: 0,
            max_align: 0,

            #[cfg(feature="opt-register-coloring")]
            slot_pool: opt.then(|| Vec::new()),
        }
    }

    // helper functions
    fn sp_push(
        &mut self,
        delta: usize,
        size: usize,
    ) {
        let x = self.sp + (delta * size);
        self.sp = x;
        self.max_sp = max(self.max_sp, x);
    }

    fn sp_pop(
        &mut self,
        delta: usize,
        size: usize,
    ) {
        let x = self.sp - (delta * size);
        self.sp = x;
    }

    fn sp_align(
        &mut self,
        size: usize,
    ) {
        // align up, we assume sp_align is followed by sp_push,
        // so we leave it to sp_push to check max_sp
        let x = self.sp;
        let x = x + size-1;
        let x = x - (x % size);
        self.sp = x;

        // all pushes onto the stack go through a sp_align, so
        // this is where we can also find the max_align
        self.max_align = max(self.max_align, size);
    }
}

/// Core OpTree type
impl<T: OpType> OpTree<T> {
    fn new(kind: OpKind<T>, const_: bool) -> OpTree<T> {
        OpTree {
            kind: kind,
            refs: Cell::new(0),
            slot: Cell::new(None),
            const_: const_,
            #[cfg(feature="opt-const-folding")]
            folded: RefCell::new(None),
        }
    }

    /// A constant 0
    pub fn zero() -> Rc<Self> {
        T::zero()
    }

    /// A constant 1
    pub fn one() -> Rc<Self> {
        T::one()
    }

    /// A constant with all bits set to 1
    pub fn ones() -> Rc<Self> {
        T::ones()
    }

    /// Register a const in this OpType's constant pool
    pub fn const_(v: T) -> Rc<Self> {
        T::const_(v)
    }

    /// Create an immediate, secret value
    pub fn imm(v: T) -> Rc<Self> {
        Rc::new(Self::new(OpKind::Imm(v), false))
    }

    // Constructors for other tree nodes, note that
    // constant-ness is propogated
    pub fn sym(name: &'static str) -> Rc<Self> {
        Rc::new(Self::new(OpKind::Sym(name), false))
    }

    pub fn truncate(a: Rc<dyn DynOpTree>) -> Rc<Self> {
        let const_ = a.is_const();
        Rc::new(Self::new(OpKind::Truncate(a), const_))
    }

    pub fn extends(a: Rc<dyn DynOpTree>) -> Rc<Self> {
        let const_ = a.is_const();
        Rc::new(Self::new(OpKind::Extends(a), const_))
    }

    pub fn extendu(a: Rc<dyn DynOpTree>) -> Rc<Self> {
        let const_ = a.is_const();
        Rc::new(Self::new(OpKind::Extendu(a), const_))
    }

    pub fn select(a: Rc<Self>, b: Rc<Self>, c: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const() && c.is_const();
        Rc::new(Self::new(OpKind::Select(a, b, c), const_))
    }

    pub fn eqz(a: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const();
        Rc::new(Self::new(OpKind::Eqz(a), const_))
    }

    pub fn eq(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::Eq(a, b), const_))
    }

    pub fn ne(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::Ne(a, b), const_))
    }

    pub fn lts(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::Lts(a, b), const_))
    }

    pub fn ltu(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::Ltu(a, b), const_))
    }

    pub fn gts(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::Gts(a, b), const_))
    }

    pub fn gtu(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::Gtu(a, b), const_))
    }

    pub fn les(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::Les(a, b), const_))
    }

    pub fn leu(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::Leu(a, b), const_))
    }

    pub fn ges(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::Ges(a, b), const_))
    }

    pub fn geu(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::Geu(a, b), const_))
    }

    pub fn clz(a: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const();
        Rc::new(Self::new(OpKind::Clz(a), const_))
    }

    pub fn ctz(a: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const();
        Rc::new(Self::new(OpKind::Ctz(a), const_))
    }

    pub fn popcnt(a: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const();
        Rc::new(Self::new(OpKind::Popcnt(a), const_))
    }

    pub fn add(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::Add(a, b), const_))
    }

    pub fn sub(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::Sub(a, b), const_))
    }

    pub fn mul(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::Mul(a, b), const_))
    }

    pub fn divs(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::Divs(a, b), const_))
    }

    pub fn divu(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::Divu(a, b), const_))
    }

    pub fn rems(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::Rems(a, b), const_))
    }

    pub fn remu(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::Remu(a, b), const_))
    }

    pub fn and(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::And(a, b), const_))
    }

    pub fn or(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::Or(a, b), const_))
    }

    pub fn xor(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::Xor(a, b), const_))
    }

    pub fn shl(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::Shl(a, b), const_))
    }

    pub fn shrs(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::Shrs(a, b), const_))
    }

    pub fn shru(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::Shru(a, b), const_))
    }

    pub fn rotl(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::Rotl(a, b), const_))
    }

    pub fn rotr(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        Rc::new(Self::new(OpKind::Rotr(a, b), const_))
    }

    /// Downcast a generic OpTree, panicing if types do not match
    pub fn downcast(a: Rc<dyn DynOpTree>) -> Rc<OpTree<T>> {
        assert!(a.width() == T::WIDTH);
        // based on Rc::downcast impl
        unsafe {
            Rc::from_raw(Rc::into_raw(a) as _)
        }
    }

    /// high-level compile into bytecode, stack, and initial stack pointer
    pub fn compile(&self, opt: bool) -> (AlignedBytes, AlignedBytes) {
        // should we do a constant folding pass?
        #[cfg(feature="opt-const-folding")]
        if opt {
            self.fold_consts();
        }

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

        // extract so we can drop OpCompile (due to lifetime messiness)
        let imms = state.imms;
        let max_sp = state.max_sp;
        let max_align = state.max_align;

        // add return instruction to type-check the result
        Op::new(OpCode::Return, T::NPW2, 0).encode(&mut bytecode)
            .expect("vector write resulted in io::error?");

        // align bytecode
        // TODO we should internally use a u16 and transmute this
        let aligned_bytecode = AlignedBytes::new_from_slice(&bytecode, 4);

        // at this point stack contains imms, but we need to make space for
        // the working stack, also align the stack
        let imms = imms + max_align-1;          // align imms
        let imms = imms - (imms % max_align);
        let imms = imms + max_sp;               // add space for stack
        let imms = imms + max_align-1;          // align stack
        let imms = imms - (imms % max_align);

        let mut aligned_stack = AlignedBytes::new_zeroed(imms, max_align);
        aligned_stack[..stack.len()].copy_from_slice(&stack);

        // imms is now the initial stack pointer
        (aligned_bytecode, aligned_stack)
    }

    /// compile and execute if value is not an immediate or constant already
    pub fn eval(&self) -> Result<T, Error> {
        match self.kind {
            OpKind::Imm(v) => Ok(v),
            _ => {
                let (bytecode, mut stack) = self.compile(false);
                let mut res = exec(&bytecode, &mut stack)?;
                let v = T::decode(&mut res).map_err(|_| Error::InvalidReturn)?;
                Ok(v)
            }
        }
    }

    /// Assuming we are Sym, patch the stack during a call
    pub fn patch(&self, v: T, stack: &mut [u8]) {
        assert!(self.is_sym(), "patching non-sym?");

        let slot = self.slot.get().expect("patching with no slot?");
        let mut slice = &mut stack[
            slot as usize * T::SIZE
                .. slot as usize * T::SIZE + T::SIZE
        ];
        v.encode(&mut slice).expect("slice write resulted in io::error?");
    }
}

impl<T: OpType> fmt::Display for OpTree<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let w = T::WIDTH;
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
    /// type's size in bytes, needed for determining cast sizes
    fn size(&self) -> usize;

    /// type's width in bits
    fn width(&self) -> usize;

    /// npw2(size), used as a part of instruction encoding
    fn npw2(&self) -> u8;

    /// is expression an immediate?
    fn is_imm(&self) -> bool;

    /// is expression a symbol?
    fn is_sym(&self) -> bool;

    /// is expression const?
    fn is_const(&self) -> bool;

    /// checks if expression is const and is zero
    fn is_zero(&self) -> bool;

    /// checks if expression is const and is one
    fn is_one(&self) -> bool;

    /// checks if expression is const and is ones
    fn is_ones(&self) -> bool;

    /// hook to enable eqz without known type
    fn dyn_eqz(&self) -> &'static dyn Fn(Rc<dyn DynOpTree>) -> Rc<dyn DynOpTree>;

    /// An optional pass to fold consts in the tree
    #[cfg(feature="opt-const-folding")]
    fn fold_consts(&self);

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
    fn size(&self) -> usize {
        T::SIZE
    }

    fn width(&self) -> usize {
        T::WIDTH
    }

    fn npw2(&self) -> u8 {
        T::NPW2
    }

    fn is_imm(&self) -> bool {
        match self.kind {
            OpKind::Imm(_) => true,
            _ => false,
        }
    }

    fn is_sym(&self) -> bool {
        match self.kind {
            OpKind::Sym(_) => true,
            _ => false,
        }
    }

    fn is_const(&self) -> bool {
        self.const_
    }

    fn is_zero(&self) -> bool {
        #[cfg(feature="opt-const-folding")]
        match (self.is_const(), &self.kind, &*self.folded.borrow()) {
            (true, OpKind::Imm(v), _            ) => v.is_zero(),
            (true, _,              Some(Some(x))) => x.is_zero(),
            _                                     => false,
        }
        #[cfg(not(feature="opt-const-folding"))]
        match (self.is_const(), &self.kind) {
            (true, OpKind::Imm(v)) => v.is_zero(),
            _                      => false,
        }
    }

    fn is_one(&self) -> bool {
        #[cfg(feature="opt-const-folding")]
        match (self.is_const(), &self.kind, &*self.folded.borrow()) {
            (true, OpKind::Imm(v), _            ) => v.is_one(),
            (true, _,              Some(Some(x))) => x.is_one(),
            _                                     => false,
        }
        #[cfg(not(feature="opt-const-folding"))]
        match (self.is_const(), &self.kind) {
            (true, OpKind::Imm(v)) => v.is_one(),
            _                      => false,
        }
    }

    fn is_ones(&self) -> bool {
        #[cfg(feature="opt-const-folding")]
        match (self.is_const(), &self.kind, &*self.folded.borrow()) {
            (true, OpKind::Imm(v), _            ) => v.is_ones(),
            (true, _,              Some(Some(x))) => x.is_ones(),
            _                                     => false,
        }
        #[cfg(not(feature="opt-const-folding"))]
        match (self.is_const(), &self.kind) {
            (true, OpKind::Imm(v)) => v.is_ones(),
            _                      => false,
        }
    }

    fn dyn_eqz(&self) -> &'static dyn Fn(Rc<dyn DynOpTree>) -> Rc<dyn DynOpTree> {
        // bit messy but this works
        // unfortunately this only works when there is a single argument
        fn eqz<T: OpType>(tree: Rc<dyn DynOpTree>) -> Rc<dyn DynOpTree> {
            OpTree::eqz(OpTree::<T>::downcast(tree))
        }
        &eqz::<T>
    }

    #[cfg(feature="opt-const-folding")]
    fn fold_consts(&self) {
        // already folded?
        if self.folded.borrow().is_some() {
            return;
        }
        self.folded.replace(Some(None));
        
        if !self.is_imm() && self.is_const() {
            // oh hey, we're const
            //
            // note this recursively triggers another compilation
            // + execution, so be careful
            //
            // if this fails we just bail on the const folding so the error
            // can be reported at runtime
            if let Ok(v) = self.eval() {
                self.folded.replace(Some(Some(Self::const_(v))));
                return;
            }
        }

        match &self.kind {
            OpKind::Imm(_) => {},
            OpKind::Sym(_) => {},

            OpKind::Truncate(a) => {
                a.fold_consts();
            }

            OpKind::Extends(a) => {
                a.fold_consts();
            }

            OpKind::Extendu(a) => {
                a.fold_consts();
            }

            OpKind::Select(p, a, b) => {
                p.fold_consts();
                a.fold_consts();
                b.fold_consts();
            }

            OpKind::Eqz(a) => {
                a.fold_consts();
            }

            OpKind::Eq(a, b) => {
                a.fold_consts();
                b.fold_consts();
            }

            OpKind::Ne(a, b) => {
                a.fold_consts();
                b.fold_consts();
            }

            OpKind::Lts(a, b) => {
                a.fold_consts();
                b.fold_consts();
            }

            OpKind::Ltu(a, b) => {
                a.fold_consts();
                b.fold_consts();
            }

            OpKind::Gts(a, b) => {
                a.fold_consts();
                b.fold_consts();
            }

            OpKind::Gtu(a, b) => {
                a.fold_consts();
                b.fold_consts();
            }

            OpKind::Les(a, b) => {
                a.fold_consts();
                b.fold_consts();
            }

            OpKind::Leu(a, b) => {
                a.fold_consts();
                b.fold_consts();
            }

            OpKind::Ges(a, b) => {
                a.fold_consts();
                b.fold_consts();
            }

            OpKind::Geu(a, b) => {
                a.fold_consts();
                b.fold_consts();
            }

            OpKind::Clz(a) => {
                a.fold_consts();
            }

            OpKind::Ctz(a) => {
                a.fold_consts();
            }

            OpKind::Popcnt(a) => {
                a.fold_consts();
            }

            OpKind::Add(a, b) => {
                a.fold_consts();
                b.fold_consts();
                if a.is_zero() {
                    self.folded.replace(Some(Some(b.clone())));
                } else if b.is_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }

            OpKind::Sub(a, b) => {
                a.fold_consts();
                b.fold_consts();
                if b.is_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }

            OpKind::Mul(a, b) => {
                a.fold_consts();
                b.fold_consts();
                if a.is_one() {
                    self.folded.replace(Some(Some(b.clone())));
                } else if b.is_one() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }

            OpKind::Divs(a, b) => {
                a.fold_consts();
                b.fold_consts();
                if b.is_one() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }

            OpKind::Divu(a, b) => {
                a.fold_consts();
                b.fold_consts();
                if b.is_one() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }

            OpKind::Rems(a, b) => {
                a.fold_consts();
                b.fold_consts();
            }

            OpKind::Remu(a, b) => {
                a.fold_consts();
                b.fold_consts();
            }

            OpKind::And(a, b) => {
                a.fold_consts();
                b.fold_consts();
                if a.is_ones() {
                    self.folded.replace(Some(Some(b.clone())));
                } else if b.is_ones() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }

            OpKind::Or(a, b) => {
                a.fold_consts();
                b.fold_consts();
                if a.is_zero() {
                    self.folded.replace(Some(Some(b.clone())));
                } else if b.is_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }

            OpKind::Xor(a, b) => {
                a.fold_consts();
                b.fold_consts();
                if a.is_zero() {
                    self.folded.replace(Some(Some(b.clone())));
                } else if b.is_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }

            OpKind::Shl(a, b) => {
                a.fold_consts();
                b.fold_consts();
                if b.is_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }

            OpKind::Shrs(a, b) => {
                a.fold_consts();
                b.fold_consts();
                if b.is_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }

            OpKind::Shru(a, b) => {
                a.fold_consts();
                b.fold_consts();
                if b.is_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }

            OpKind::Rotl(a, b) => {
                a.fold_consts();
                b.fold_consts();
                if b.is_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }

            OpKind::Rotr(a, b) => {
                a.fold_consts();
                b.fold_consts();
                if b.is_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
        }
    }

    fn compile_pass1(&self, state: &mut OpCompile) -> Result<(), io::Error> {
        // prefer folded tree
        #[cfg(feature="opt-const-folding")]
        if let Some(Some(folded)) = &*self.folded.borrow() {
            return folded.compile_pass1(state);
        }

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
                while state.imms % T::SIZE != 0 {
                    state.stack.write_all(&[0])?;
                    state.imms += 1;
                }

                // save slot
                assert!(state.imms % T::SIZE == 0, "unaligned slot");
                let slot = state.imms / T::SIZE;
                let slot = u8::try_from(slot).expect("slot overflow");
                self.slot.set(Some(slot));

                // write imm to stack
                v.encode(state.stack)?;

                // update imms
                state.imms += T::SIZE;
            }

            OpKind::Sym(_) => {
                // align imms?
                while state.imms % T::SIZE != 0 {
                    state.stack.write_all(&[0])?;
                    state.imms += 1;
                }

                // save slot
                assert!(state.imms % T::SIZE == 0, "unaligned slot");
                let slot = state.imms / T::SIZE;
                let slot = u8::try_from(slot).expect("slot overflow");
                self.slot.set(Some(slot));

                // we'll fill this in later, use an arbitrary constant
                // to hopefully help debugging
                for _ in 0..T::SIZE {
                    state.stack.write_all(&[0xcc])?;
                }

                // update imms
                state.imms += T::SIZE;
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
        // prefer folded tree
        #[cfg(feature="opt-const-folding")]
        if let Some(Some(folded)) = &*self.folded.borrow() {
            return folded.compile_pass2(state);
        }

        // is node shared?
        let prefs = self.refs.get();
        self.refs.set(prefs - 1);

        // already computed?
        let slot = self.slot.get();
        if let Some(slot) = slot {
            // get slot and align
            Op::new(OpCode::Get, T::NPW2, slot).encode(state.bytecode)?;
            state.sp_align(T::SIZE);
            state.sp_push(1, T::SIZE);

            // are we done with slot? contribute to slot_pool
            #[cfg(feature="opt-register-coloring")]
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
                let expected_sp = state.sp + T::SIZE;

                a.compile_pass2(state)?;

                // truncate
                Op::new(OpCode::Truncate, T::NPW2, a.npw2()).encode(state.bytecode)?;
                state.sp_pop(1, a.size());
                state.sp_push(1, T::SIZE);

                // manually unalign?
                if state.sp > expected_sp {
                    let diff = state.sp - expected_sp;
                    assert!(diff % T::SIZE == 0, "unaligned truncate");
                    let diff = diff / T::SIZE;
                    let diff = u8::try_from(diff).expect("unalign overflow");
                    Op::new(OpCode::Unalign, T::NPW2, diff).encode(state.bytecode)?;
                    state.sp_pop(diff as usize, T::SIZE);
                }
            }

            OpKind::Extends(a) => {
                a.compile_pass2(state)?;

                // extends and align
                Op::new(OpCode::Extends, a.npw2(), T::NPW2).encode(state.bytecode)?;
                state.sp_pop(1, a.size());
                state.sp_align(T::SIZE);
                state.sp_push(1, T::SIZE);
            }

            OpKind::Extendu(a) => {
                a.compile_pass2(state)?;

                // extendu and align
                Op::new(OpCode::Extendu, a.npw2(), T::NPW2).encode(state.bytecode)?;
                state.sp_pop(1, a.size());
                state.sp_align(T::SIZE);
                state.sp_push(1, T::SIZE);
            }

            OpKind::Select(p, a, b) => {
                p.compile_pass2(state)?;
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Select, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(2, T::SIZE);
            }

            OpKind::Eqz(a) => {
                a.compile_pass2(state)?;
                Op::new(OpCode::Eqz, T::NPW2, 0).encode(state.bytecode)?;
            }

            OpKind::Eq(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Eq, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::SIZE);
            }

            OpKind::Ne(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Ne, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::SIZE);
            }

            OpKind::Lts(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Lts, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::SIZE);
            }

            OpKind::Ltu(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Ltu, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::SIZE);
            }

            OpKind::Gts(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Gts, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::SIZE);
            }

            OpKind::Gtu(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Gtu, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::SIZE);
            }

            OpKind::Les(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Les, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::SIZE);
            }

            OpKind::Leu(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Leu, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::SIZE);
            }

            OpKind::Ges(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Ges, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::SIZE);
            }

            OpKind::Geu(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Geu, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::SIZE);
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
                state.sp_pop(1, T::SIZE);
            }

            OpKind::Sub(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Sub, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::SIZE);
            }

            OpKind::Mul(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Mul, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::SIZE);
            }

            OpKind::Divs(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Divs, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::SIZE);
            }

            OpKind::Divu(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Divu, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::SIZE);
            }

            OpKind::Rems(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Rems, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::SIZE);
            }

            OpKind::Remu(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Remu, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::SIZE);
            }

            OpKind::And(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::And, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::SIZE);
            }

            OpKind::Or(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Or, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::SIZE);
            }

            OpKind::Xor(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Xor, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::SIZE);
            }

            OpKind::Shl(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Shl, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::SIZE);
            }

            OpKind::Shrs(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Shrs, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::SIZE);
            }

            OpKind::Shru(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Shru, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::SIZE);
            }

            OpKind::Rotl(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Rotl, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::SIZE);
            }

            OpKind::Rotr(a, b) => {
                a.compile_pass2(state)?;
                b.compile_pass2(state)?;
                Op::new(OpCode::Rotr, T::NPW2, 0).encode(state.bytecode)?;
                state.sp_pop(1, T::SIZE);
            }
        }

        // save for later computations?
        if prefs > 1 {
            // can we reuse a slot in the slot pool?
            #[cfg(feature="opt-register-coloring")]
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
            #[cfg(not(feature="opt-register-coloring"))]
            let slot = None;

            // fallback to allocating an immediate
            let slot = slot.unwrap_or_else(|| {
                // align imms?
                if state.imms % T::SIZE != 0 {
                    state.imms += T::SIZE - (state.imms % T::SIZE);
                }

                assert!(state.imms % T::SIZE == 0, "unaligned slot");
                let slot = state.imms / T::SIZE;
                let slot = u8::try_from(slot).expect("slot overflow");

                // update imms
                state.imms += T::SIZE;

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
        let example = OpTree::add(
            OpTree::imm(1u32.to_le_bytes()),
            OpTree::imm(2u32.to_le_bytes())
        );

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

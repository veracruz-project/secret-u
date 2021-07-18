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
use std::collections::BTreeSet;
use std::cell::RefCell;
use std::io::Write;

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

impl From<Op> for u16 {
    fn from(op: Op) -> u16 {
        op.0
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

fn arbitrary_names() -> impl Iterator<Item=String> {
    let alphabet = "abcdefghijklmnopqrstuvwxyz";
    // a..z
    alphabet.chars()
        .map(move |c| String::from(c))
        .chain(
            // a2..z2, a3..z3, ...
            (2..).map(move |n| {
                    alphabet.chars()
                        .map(move |c| format!("{}{}", c, n))
                })
                .flatten()
        )
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
                writeln!(out, "    {:04x} {}", u16::from(opcode), opcode)?;
            }
            Err(Error::InvalidOpcode(op)) => {
                writeln!(out, "    {:04x} unknown {:#06x}", op, op)?;
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

    /// Display as hex, used for debugging
    fn hex(&self) -> String;
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
                        let c = Rc::new(OpTree::new(OpKind::Imm(v), true, false));
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

            /// Display as hex, used for debugging
            fn hex(&self) -> String {
                let mut buf = vec![b'0', b'x'];
                for b in self.iter().rev() {
                    write!(buf, "{:02x}", b).unwrap();
                }
                String::from_utf8(buf).unwrap()
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
    sym: bool,
    #[cfg(feature="opt-const-folding")]
    folded: RefCell<Option<Option<Rc<OpTree<T>>>>>,
}

/// Pool for allocating/reusing slots in a fictional blob of bytes
#[derive(Debug)]
struct SlotPool {
    // pool of deallocated slots, note the reversed
    // order so that we are sorted first by slot size,
    // and second by decreasing slot numbers
    pool: BTreeSet<(u8, i16)>,
    //              ^   ^- negative slot number
    //              '----- slot npw2

    // current end of blob
    size: usize,
}

impl SlotPool {
    /// Create a new empty slot pool
    fn new() -> SlotPool {
        SlotPool {
            pool: BTreeSet::new(),
            size: 0,
        }
    }

    /// Get the size of the slot pool
    fn size(&self) -> usize {
        self.size
    }

    /// Allocate a slot with the required npw2 size,
    /// note it's possible to run out of slots here
    fn alloc(&mut self, npw2: u8) -> Result<u8, Error> {
        // The allocation scheme here is a bit complicated.
        // 
        // Slots of all sizes share a common buffer, which means
        // smaller slots have a smaller addressable range than larger
        // slots.
        //
        //  .--------- u32 slot 0
        //  v       v- u32 slot 1
        // [ | | | | | | | | ...
        //  ^-^------- u8 slot 0
        //    '------- u8 slot 1
        //
        // An optimal algorithm would probably allocate all slots and
        // then sort by size, but since we're only doing this in one pass
        // we just try to avoid the lower ranges of slots as much as possible.
        //
        // This includes:
        // 1. Reusing slots from the largest already-allocated slot of a
        //    give size
        // 2. Limiting slot 0 to u8 slots
        //

        // find smallest slot where size >= npw2 but slot*size < 256
        let best_slot = self.pool.range((npw2, i16::MIN)..)
            .copied()
            .filter(|(best_npw2, best_islot)| {
                // fits in slot number?
                u8::try_from(
                    (usize::try_from(-best_islot).unwrap() << best_npw2) >> npw2
                ).is_ok()
            })
            .next();
        match best_slot {
            Some((mut best_npw2, best_islot)) => {
                // remove from pool
                self.pool.remove(&(best_npw2, best_islot));
                let mut best_slot = u8::try_from(-best_islot).unwrap();

                // pad
                while best_npw2 > npw2 {
                    best_slot *= 2;
                    best_npw2 -= 1;
                    // return padding into pool
                    if let Some(padding_slot) = best_slot.checked_add(1) {
                        self.dealloc(padding_slot, best_npw2);
                    }
                }

                debug_assert!(best_npw2 == npw2);
                Ok(best_slot)
            }
            None => {
                // skip slot 0?
                if self.size == 0 && npw2 != 0 {
                    self.size += 1;
                    self.dealloc(0, 0);
                }

                // allocate new slot
                while self.size % (1 << npw2) != 0 {
                    let padding_npw2 = self.size.trailing_zeros();
                    let padding_slot = self.size >> padding_npw2;
                    self.size += 1 << padding_npw2;
                    if let Ok(padding_slot) = u8::try_from(padding_slot) {
                        self.dealloc(padding_slot, u8::try_from(padding_npw2).unwrap());
                    }
                }

                match u8::try_from(self.size >> npw2) {
                    Ok(slot) => {
                        self.size += 1 << npw2;
                        Ok(slot)
                    }
                    _ => {
                        Err(Error::OutOfSlots(npw2))
                    }
                }
            }
        }
    }

    /// Return a slot to the pool
    fn dealloc(&mut self, mut slot: u8, mut npw2: u8) {
        // don't defragment slot 0! reserved for a u8, this
        // intentionally fragments the front of our pool, which
        // helps keep us from clobbering smaller slots with one
        // big one
        if slot & !1 != 0 {
            // try to defragment?
            while self.pool.remove(&(npw2, -i16::from(slot ^ 1))) {
                slot /= 2;
                npw2 += 1;
            }
        }

        assert!(
            self.pool.insert((npw2, -i16::from(slot))),
            "Found duplicate slot in pool!? ({}, {})\n{:?}",
            slot, npw2,
            self.pool
        )
    }
}

/// Compilation state
pub struct OpCompile {
    bytecode: Vec<u8>,
    stack: Vec<u8>,

    slot_pool: SlotPool,

    sp: usize,
    max_sp: usize,
    max_npw2: u8,
}

impl OpCompile {
    fn new() -> OpCompile {
        OpCompile {
            bytecode: Vec::new(),
            stack: Vec::new(),

            slot_pool: SlotPool::new(),

            sp: 0,
            max_sp: 0,
            max_npw2: 0,
        }
    }

    // these all just go to the slot_pool, but we also
    // keep track of max_npw2
    fn slot_alloc(&mut self, npw2: u8) -> Result<u8, Error> {
        self.slot_pool.alloc(npw2)
            .map(|slot| {
                self.max_npw2 = max(self.max_npw2, npw2);
                slot
            })
    }

    fn slot_dealloc(&mut self, slot: u8, npw2: u8) {
        self.slot_pool.dealloc(slot, npw2)
    }

    // sp functions
    fn sp_push(
        &mut self,
        delta: usize,
        npw2: u8,
    ) {
        let x = self.sp + (delta << npw2);
        self.sp = x;
        self.max_sp = max(self.max_sp, x);
    }

    fn sp_pop(
        &mut self,
        delta: usize,
        npw2: u8,
    ) {
        let x = self.sp - (delta << npw2);
        self.sp = x;
    }

    fn sp_align(
        &mut self,
        npw2: u8,
    ) {
        // align up, we assume sp_align is followed by sp_push,
        // so we leave it to sp_push to check max_sp
        let x = self.sp;
        let x = x + (1 << npw2)-1;
        let x = x - (x % (1 << npw2));
        self.sp = x;

        // all pushes onto the stack go through a sp_align, so
        // this is where we can also find the max_npw2
        self.max_npw2 = max(self.max_npw2, npw2);
    }
}

/// Core OpTree type
impl<T: OpType> OpTree<T> {
    fn new(kind: OpKind<T>, const_: bool, sym: bool) -> OpTree<T> {
        OpTree {
            kind: kind,
            refs: Cell::new(0),
            slot: Cell::new(None),
            const_: const_,
            sym: sym,
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
        Rc::new(Self::new(OpKind::Imm(v), false, false))
    }

    // Constructors for other tree nodes, note that
    // constant-ness is propogated
    pub fn sym(name: &'static str) -> Rc<Self> {
        Rc::new(Self::new(OpKind::Sym(name), false, true))
    }

    pub fn truncate(a: Rc<dyn DynOpTree>) -> Rc<Self> {
        let const_ = a.is_const();
        let sym    = a.is_sym();
        Rc::new(Self::new(OpKind::Truncate(a), const_, sym))
    }

    pub fn extends(a: Rc<dyn DynOpTree>) -> Rc<Self> {
        let const_ = a.is_const();
        let sym    = a.is_sym();
        Rc::new(Self::new(OpKind::Extends(a), const_, sym))
    }

    pub fn extendu(a: Rc<dyn DynOpTree>) -> Rc<Self> {
        let const_ = a.is_const();
        let sym    = a.is_sym();
        Rc::new(Self::new(OpKind::Extendu(a), const_, sym))
    }

    pub fn select(a: Rc<Self>, b: Rc<Self>, c: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const() && c.is_const();
        let sym    = a.is_sym()   || b.is_sym()   || c.is_sym();
        Rc::new(Self::new(OpKind::Select(a, b, c), const_, sym))
    }

    pub fn eqz(a: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const();
        let sym    = a.is_sym();
        Rc::new(Self::new(OpKind::Eqz(a), const_, sym))
    }

    pub fn eq(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::Eq(a, b), const_, sym))
    }

    pub fn ne(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::Ne(a, b), const_, sym))
    }

    pub fn lts(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::Lts(a, b), const_, sym))
    }

    pub fn ltu(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::Ltu(a, b), const_, sym))
    }

    pub fn gts(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::Gts(a, b), const_, sym))
    }

    pub fn gtu(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::Gtu(a, b), const_, sym))
    }

    pub fn les(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::Les(a, b), const_, sym))
    }

    pub fn leu(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::Leu(a, b), const_, sym))
    }

    pub fn ges(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::Ges(a, b), const_, sym))
    }

    pub fn geu(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::Geu(a, b), const_, sym))
    }

    pub fn clz(a: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const();
        let sym    = a.is_sym();
        Rc::new(Self::new(OpKind::Clz(a), const_, sym))
    }

    pub fn ctz(a: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const();
        let sym    = a.is_sym();
        Rc::new(Self::new(OpKind::Ctz(a), const_, sym))
    }

    pub fn popcnt(a: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const();
        let sym    = a.is_sym();
        Rc::new(Self::new(OpKind::Popcnt(a), const_, sym))
    }

    pub fn add(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::Add(a, b), const_, sym))
    }

    pub fn sub(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::Sub(a, b), const_, sym))
    }

    pub fn mul(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::Mul(a, b), const_, sym))
    }

    pub fn divs(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::Divs(a, b), const_, sym))
    }

    pub fn divu(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::Divu(a, b), const_, sym))
    }

    pub fn rems(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::Rems(a, b), const_, sym))
    }

    pub fn remu(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::Remu(a, b), const_, sym))
    }

    pub fn and(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::And(a, b), const_, sym))
    }

    pub fn or(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::Or(a, b), const_, sym))
    }

    pub fn xor(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::Xor(a, b), const_, sym))
    }

    pub fn shl(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::Shl(a, b), const_, sym))
    }

    pub fn shrs(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::Shrs(a, b), const_, sym))
    }

    pub fn shru(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::Shru(a, b), const_, sym))
    }

    pub fn rotl(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::Rotl(a, b), const_, sym))
    }

    pub fn rotr(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind::Rotr(a, b), const_, sym))
    }

    /// Downcast a generic OpTree, panicing if types do not match
    pub fn downcast(a: Rc<dyn DynOpTree>) -> Rc<OpTree<T>> {
        assert!(a.width() == T::WIDTH);
        // based on Rc::downcast impl
        unsafe {
            Rc::from_raw(Rc::into_raw(a) as _)
        }
    }

    /// display tree for debugging
    pub fn disas<W: io::Write>(&self, mut out: W) -> Result<(), io::Error> {
        // get a source of variable names, these represent
        // deduplicate dag branches
        let mut slot_names = HashMap::new();
        let mut arbitrary_names = arbitrary_names();

        // two passes, since we want to deduplicate the dag, otherwise
        // our debug output gets VERY BIG
        self.disas_pass1();
        let expr = self.disas_pass2(
            &mut slot_names,
            &mut arbitrary_names,
            &mut out
        )?;

        // cleanup last expression
        write!(out, "    {}\n", expr)
    }

    /// high-level compile into bytecode, stack, and initial stack pointer
    pub fn compile(&self, #[allow(unused)] opt: bool) -> (AlignedBytes, AlignedBytes) {
        // should we do a constant folding pass?
        #[cfg(feature="opt-const-folding")]
        if opt {
            self.fold_consts();
        }

        // debug?
        #[cfg(feature="debug-trees")]
        {
            println!("tree:");
            self.disas(io::stdout()).unwrap();
        }

        // NOTE! We make sure to zero all refs from pass1 to pass2, this is
        // rather fragile and requires all passes to always be run as a pair,
        // we can't interrupt between passes without needing to reset all
        // internal reference counts

        let mut state = OpCompile::new();

        // first pass to find number of immediates and deduplicate branches
        self.compile_pass1(&mut state);

        // second pass now to compile the bytecode and stack, note sp now points
        // to end of immediates
        self.compile_pass2(&mut state);

        // add return instruction to type-check the result
        Op::new(OpCode::Return, T::NPW2, 0).encode(&mut state.bytecode).unwrap();

        // align bytecode
        // TODO we should internally use a u16 and transmute this
        let aligned_bytecode = AlignedBytes::new_from_slice(&state.bytecode, 4);

        // at this point stack contains imms, but we need to make space for
        // the working stack and align everything
        let max_align = 1usize << state.max_npw2;
        let imms = state.slot_pool.size() + max_align-1; // align imms
        let imms = imms - (imms % max_align);
        let imms = imms + state.max_sp;                  // add space for stack
        let imms = imms + max_align-1;                   // align stack
        let imms = imms - (imms % max_align);

        let mut aligned_stack = AlignedBytes::new_zeroed(imms, max_align);
        aligned_stack[..state.stack.len()].copy_from_slice(&state.stack);

        #[cfg(feature="debug-bytecode")]
        {
            println!("stack:");
            print!("   ");
            for b in aligned_stack.iter() {
                 print!(" {:02x}", b);
            }
            println!();

            println!("bytecode:");
            disas(&aligned_bytecode, io::stdout()).unwrap();
        }

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
        assert!(
            match self.kind {
                OpKind::Sym(_) => true,
                _              => false,
            },
            "patching non-sym?"
        );

        let slot = self.slot.get().expect("patching with no slot?");
        let mut slice = &mut stack[
            slot as usize * T::SIZE
                .. slot as usize * T::SIZE + T::SIZE
        ];
        v.encode(&mut slice).expect("slice write resulted in io::error?");
    }
}

// dyn-compatible wrapping trait
pub trait DynOpTree: Debug {
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

    /// First pass for debug output
    fn disas_pass1(&self);

    /// Second pass for debug output
    fn disas_pass2(
        &self,
        names: &mut HashMap<usize, String>,
        arbitrary_names: &mut dyn Iterator<Item=String>,
        stmts: &mut dyn io::Write,
    ) -> Result<String, io::Error>;

    /// An optional pass to fold consts in the tree
    #[cfg(feature="opt-const-folding")]
    fn fold_consts(&self);

    /// First compile pass, used to find the number of immediates
    /// for offset calculation, and local reference counting to
    /// deduplicate branches.
    fn compile_pass1(&self, state: &mut OpCompile);

    /// Second compile pass, used to actually compile both the
    /// immediates and bytecode. Since both bytecode and stack are
    /// generic writers, a null writer could be used if either are
    /// not needed.
    fn compile_pass2(&self, state: &mut OpCompile);
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
        self.sym
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

    fn disas_pass1(&self) {
        // prefer folded tree
        #[cfg(feature="opt-const-folding")]
        if let Some(Some(folded)) = &*self.folded.borrow() {
            return folded.disas_pass1();
        }

        // mark node as seen
        let prefs = self.refs.get();
        self.refs.set(prefs + 1);
        if prefs > 0 {
            // already visited?
            return;
        }

        match &self.kind {
            OpKind::Imm(_) => {},
            OpKind::Sym(_) => {},

            OpKind::Truncate(a) => {
                a.disas_pass1();
            }

            OpKind::Extends(a) => {
                a.disas_pass1();
            }

            OpKind::Extendu(a) => {
                a.disas_pass1();
            }

            OpKind::Select(p, a, b) => {
                p.disas_pass1();
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Eqz(a) => {
                a.disas_pass1();
            }

            OpKind::Eq(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Ne(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Lts(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Ltu(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Gts(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Gtu(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Les(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Leu(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Ges(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Geu(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Clz(a) => {
                a.disas_pass1();
            }

            OpKind::Ctz(a) => {
                a.disas_pass1();
            }

            OpKind::Popcnt(a) => {
                a.disas_pass1();
            }

            OpKind::Add(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Sub(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Mul(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Divs(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Divu(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Rems(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Remu(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::And(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Or(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Xor(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Shl(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Shrs(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Shru(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Rotl(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Rotr(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
        }
    }

    fn disas_pass2(
        &self,
        names: &mut HashMap<usize, String>,
        arbitrary_names: &mut dyn Iterator<Item=String>,
        stmts: &mut dyn io::Write,
    ) -> Result<String, io::Error> {
        // prefer folded tree
        #[cfg(feature="opt-const-folding")]
        if let Some(Some(folded)) = &*self.folded.borrow() {
            return folded.disas_pass2(names, arbitrary_names, stmts);
        }

        // is node shared?
        let prefs = self.refs.get();
        self.refs.set(prefs - 1);

        // already computed?
        let name = names.get(&((self as *const _) as usize));
        if let Some(name) = name {
            return Ok(name.clone());
        }

        let expr = match &self.kind {
            OpKind::Imm(v) => format!("(u{}.imm {})", T::WIDTH, v.hex()),
            OpKind::Sym(s) => format!("(u{}.sym {:?})", T::WIDTH, s),

            OpKind::Truncate(a) => format!("(u{}.truncate {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Extends(a) => format!("(u{}.extends {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Extendu(a) => format!("(u{}.extendu {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),

            OpKind::Select(p, a, b) => format!("(u{}.select {} {} {})",
                T::WIDTH,
                p.disas_pass2(names, arbitrary_names, stmts)?,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Eqz(a) => format!("(u{}.eqz {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Eq(a, b) => format!("(u{}.eq {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Ne(a, b) => format!("(u{}.ne {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Lts(a, b) => format!("(u{}.lts {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Ltu(a, b) => format!("(u{}.ltu {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Gts(a, b) => format!("(u{}.gts {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Gtu(a, b) => format!("(u{}.gtu {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Les(a, b) => format!("(u{}.les {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Leu(a, b) => format!("(u{}.leu {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Ges(a, b) => format!("(u{}.ges {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Geu(a, b) => format!("(u{}.geu {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Clz(a) => format!("(u{}.clz {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Ctz(a) => format!("(u{}.ctz {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Popcnt(a) => format!("(u{}.popcnt {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Add(a, b) => format!("(u{}.add {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Sub(a, b) => format!("(u{}.sub {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Mul(a, b) => format!("(u{}.mul {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Divs(a, b) => format!("(u{}.divs {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Divu(a, b) => format!("(u{}.divu {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Rems(a, b) => format!("(u{}.rems {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Remu(a, b) => format!("(u{}.remu {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::And(a, b) => format!("(u{}.and {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Or(a, b) => format!("(u{}.or {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Xor(a, b) => format!("(u{}.xor {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Shl(a, b) => format!("(u{}.shl {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Shrs(a, b) => format!("(u{}.shrs {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Shru(a, b) => format!("(u{}.shru {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Rotl(a, b) => format!("(u{}.rotl {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Rotr(a, b) => format!("(u{}.rotr {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
        };

        // used later? save as stmt?
        if prefs > 1 {
            let name = arbitrary_names.next().unwrap();
            names.insert((self as *const _) as usize, name.clone());
            write!(stmts, "    {} = {}\n", name, expr)?;
            Ok(name)
        } else {
            Ok(expr)
        }
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

    fn compile_pass1(&self, state: &mut OpCompile) {
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
            return;
        }

        // make sure slots left over from previous calculation are reset
        self.slot.set(None);

        match &self.kind {
            OpKind::Imm(v) => {
                // allocate slot
                let slot = state.slot_alloc(T::NPW2).unwrap();
                self.slot.set(Some(slot));

                // write imm to stack
                if state.stack.len() < (usize::from(slot)+1) << T::NPW2 {
                    state.stack.resize((usize::from(slot)+1) << T::NPW2, 0);
                }

                v.encode(&mut &mut state.stack[
                    usize::from(slot) << T::NPW2
                        .. (usize::from(slot)+1) << T::NPW2
                ]).unwrap();
            }

            OpKind::Sym(_) => {
                // allocate slot
                let slot = state.slot_alloc(T::NPW2).unwrap();
                self.slot.set(Some(slot));

                if state.stack.len() < (usize::from(slot)+1) << T::NPW2 {
                    state.stack.resize((usize::from(slot)+1) << T::NPW2, 0);
                }

                // we'll fill this in later, use an arbitrary constant
                // to hopefully help debugging
                state.stack[
                    usize::from(slot) << T::NPW2
                        .. (usize::from(slot)+1) << T::NPW2
                ].fill(0xcc);
            }

            OpKind::Truncate(a) => {
                a.compile_pass1(state);
            }

            OpKind::Extends(a) => {
                a.compile_pass1(state);
            }

            OpKind::Extendu(a) => {
                a.compile_pass1(state);
            }

            OpKind::Select(p, a, b) => {
                p.compile_pass1(state);
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Eqz(a) => {
                a.compile_pass1(state);
            }

            OpKind::Eq(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Ne(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Lts(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Ltu(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Gts(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Gtu(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Les(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Leu(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Ges(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Geu(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Clz(a) => {
                a.compile_pass1(state);
            }

            OpKind::Ctz(a) => {
                a.compile_pass1(state);
            }

            OpKind::Popcnt(a) => {
                a.compile_pass1(state);
            }

            OpKind::Add(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Sub(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Mul(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Divs(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Divu(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Rems(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Remu(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::And(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Or(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Xor(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Shl(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Shrs(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Shru(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Rotl(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Rotr(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
        }
    }

    fn compile_pass2(&self, state: &mut OpCompile) {
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
            Op::new(OpCode::Get, T::NPW2, slot).encode(&mut state.bytecode).unwrap();
            state.sp_align(T::NPW2);
            state.sp_push(1, T::NPW2);

            // are we done with slot? contribute to slot_pool
            if prefs == 1 {
                state.slot_dealloc(slot, T::NPW2);
            }

            return;
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

                a.compile_pass2(state);

                // truncate
                Op::new(OpCode::Truncate, T::NPW2, a.npw2()).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, a.npw2());
                state.sp_push(1, T::NPW2);

                // manually unalign?
                if state.sp > expected_sp {
                    let diff = state.sp - expected_sp;
                    assert!(diff % T::SIZE == 0, "unaligned truncate");
                    let diff = diff / T::SIZE;
                    let diff = u8::try_from(diff).expect("unalign overflow");
                    Op::new(OpCode::Unalign, T::NPW2, diff).encode(&mut state.bytecode).unwrap();
                    state.sp_pop(diff as usize, T::NPW2);
                }
            }

            OpKind::Extends(a) => {
                a.compile_pass2(state);

                // extends and align
                Op::new(OpCode::Extends, a.npw2(), T::NPW2).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, a.npw2());
                state.sp_align(T::NPW2);
                state.sp_push(1, T::NPW2);
            }

            OpKind::Extendu(a) => {
                a.compile_pass2(state);

                // extendu and align
                Op::new(OpCode::Extendu, a.npw2(), T::NPW2).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, a.npw2());
                state.sp_align(T::NPW2);
                state.sp_push(1, T::NPW2);
            }

            OpKind::Select(p, a, b) => {
                p.compile_pass2(state);
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Select, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(2, T::NPW2);
            }

            OpKind::Eqz(a) => {
                a.compile_pass2(state);
                Op::new(OpCode::Eqz, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
            }

            OpKind::Eq(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Eq, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }

            OpKind::Ne(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Ne, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }

            OpKind::Lts(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Lts, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }

            OpKind::Ltu(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Ltu, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }

            OpKind::Gts(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Gts, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }

            OpKind::Gtu(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Gtu, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }

            OpKind::Les(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Les, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }

            OpKind::Leu(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Leu, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }

            OpKind::Ges(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Ges, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }

            OpKind::Geu(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Geu, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }

            OpKind::Clz(a) => {
                a.compile_pass2(state);
                Op::new(OpCode::Clz, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
            }

            OpKind::Ctz(a) => {
                a.compile_pass2(state);
                Op::new(OpCode::Ctz, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
            }

            OpKind::Popcnt(a) => {
                a.compile_pass2(state);
                Op::new(OpCode::Popcnt, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
            }

            OpKind::Add(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Add, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }

            OpKind::Sub(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Sub, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }

            OpKind::Mul(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Mul, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }

            OpKind::Divs(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Divs, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }

            OpKind::Divu(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Divu, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }

            OpKind::Rems(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Rems, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }

            OpKind::Remu(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Remu, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }

            OpKind::And(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::And, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }

            OpKind::Or(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Or, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }

            OpKind::Xor(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Xor, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }

            OpKind::Shl(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Shl, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }

            OpKind::Shrs(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Shrs, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }

            OpKind::Shru(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Shru, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }

            OpKind::Rotl(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Rotl, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }

            OpKind::Rotr(a, b) => {
                a.compile_pass2(state);
                b.compile_pass2(state);
                Op::new(OpCode::Rotr, T::NPW2, 0).encode(&mut state.bytecode).unwrap();
                state.sp_pop(1, T::NPW2);
            }
        }

        // save for later computations?
        if prefs > 1 {
            // allocate slot
            let slot = state.slot_alloc(T::NPW2).unwrap();

            // set slot and save for later
            Op::new(OpCode::Set, T::NPW2, slot).encode(&mut state.bytecode).unwrap();
            self.slot.set(Some(slot));
        }
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
        println!("input:");
        example.disas(io::stdout()).unwrap();
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
        assert_eq!(stack.len(), 5*4);
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
        println!("input:");
        example.disas(io::stdout()).unwrap();
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
        println!("input:");
        example.disas(io::stdout()).unwrap();
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
        assert_eq!(stack.len(), 7*4);
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
        println!("input:");
        example.disas(io::stdout()).unwrap();
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
        assert_eq!(stack.len(), 7*4);
    }

    #[test]
    fn constant_folding() {
        let a = OpTree::const_(3u32.to_le_bytes());
        let b = OpTree::const_(4u32.to_le_bytes());
        let c = OpTree::const_(5u32.to_le_bytes());
        let example = OpTree::eq(
            OpTree::add(
                OpTree::mul(a.clone(), a),
                OpTree::mul(b.clone(), b)
            ),
            OpTree::mul(c.clone(), c)
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
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

        assert_eq!(bytecode.len(), 2*2);
        assert_eq!(stack.len(), 3*4);
    }

    #[test]
    fn compile_slot_defragment() {
        let a = OpTree::imm([1u8; 1]);
        let b = OpTree::imm([2u8; 1]);
        let c = OpTree::imm([3u8; 1]);
        let d = OpTree::imm([4u8; 1]);
        let e = OpTree::imm([5u8; 1]);
        let f = OpTree::imm([6u8; 1]);
        let g = OpTree::imm([7u8; 1]);
        let h = OpTree::imm([8u8; 1]);
        let big = OpTree::<[u8;4]>::extendu(a);
        let i = OpTree::add(
            big.clone(),
            OpTree::add(
                big.clone(),
                OpTree::add(
                    OpTree::<[u8;4]>::extendu(b),
                    OpTree::add(
                        OpTree::<[u8;4]>::extendu(c),
                        OpTree::add(
                            OpTree::<[u8;4]>::extendu(d),
                            OpTree::add(
                                OpTree::<[u8;4]>::extendu(e),
                                OpTree::add(
                                    OpTree::<[u8;4]>::extendu(f),
                                    OpTree::add(
                                        OpTree::<[u8;4]>::extendu(g),
                                        OpTree::<[u8;4]>::extendu(h)
                                    )
                                )
                            )
                        )
                    )
                )
            )
        );
        let example = OpTree::add(i.clone(), OpTree::add(i, big));

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
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

        assert_eq!(bytecode.len(), 32*2);
        assert_eq!(stack.len(), 12*4);
    }
}

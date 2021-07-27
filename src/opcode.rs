//! opcode/bytecode definitions

use std::rc::Rc;
use std::fmt::Debug;
use std::fmt::LowerHex;
use std::io;
use std::convert::TryFrom;
use std::fmt;
use std::mem::transmute;
use crate::error::Error;
use std::cell::Cell;
use crate::engine::exec;
use std::cmp::max;
use std::cmp::min;
use std::mem::size_of;
use std::collections::HashMap;
#[cfg(feature="opt-color-slots")]
use std::collections::BTreeSet;
use std::cell::RefCell;

use aligned_utils::bytes::AlignedBytes;


/// OpCodes emitted as a part of bytecode
///
/// Based originally on the numeric instructions of Wasm, with the
/// noticable omission of the division instructions (uncommon for
/// both SIMD instruction sets and constant-time instruction sets)
/// but extended to larger integer sizes (u8-u512), and with multiple
/// SIMD lanes (u8x2, u16x4, etc).
///
/// Instead of operating on locals/globals with a stack, instructions
/// operate directly on 256 registers (sometimes called "slots"), which
/// share a common blob of memory but must not overlap or be reinterpreted.
///
/// Most instructions follow a 2-register format:
/// 
/// [-3-|-3-|00|--  8  --|--  8  --|--  8  --]
///   ^   ^         ^         ^         ^- 8-bit source slot
///   |   |         |         '----------- 8-bit destination slot
///   |   |         '--------------------- 8-bit opcode
///   |   '------------------------------- 3-bit npw2(lanes)
///   '----------------------------------- 3-bit npw2(size)
///
/// However there are 4 special instruction which use either a 7-bit
/// immediate or 3-register format:
///
/// extract + replace:
/// [-3-|-3-|01-|-- 7  --|--  8  --|--  8  --]
///   ^   ^    ^    ^         ^         ^- 8-bit source slot
///   |   |    |    |         '----------- 8-bit destination slot
///   |   |    |    '--------------------- 7-bit lane number
///   |   |    '-------------------------- 1-bit extract or replace
///   |   '------------------------------- 3-bit npw2(lanes)
///   '----------------------------------- 3-bit npw2(size)
///
/// select + shuffle:
/// [-3-|-3-|1-|--  8  --|--  8  --|--  8  --]
///   ^   ^   ^     ^         ^         ^- 8-bit source slot
///   |   |   |     |         '----------- 8-bit destination slot
///   |   |   |     '--------------------- 8-bit predicate slot
///   |   |   '--------------------------- 1-bit select or shuffle
///   |   '------------------------------- 3-bit npw2(lanes)
///   '----------------------------------- 3-bit npw2(size)
///
/// Most instructions are a fixed 32-bits, except for const instructions
/// which are followed by a 32-bit aligned little-endian immediate in the
/// instruction stream.
///
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[repr(u32)]
pub enum OpCode {
    Extract       = 0x01000000,
    Replace       = 0x01800000,
    Select        = 0x02000000,
    Shuffle       = 0x03000000,

    Arg           = 0x00010000,
    Ret           = 0x00020000,

    ExtendConstU  = 0x00030000,
    ExtendConstS  = 0x00040000,
    SplatConst    = 0x00050000,
    ExtendConst8U = 0x00060000,
    ExtendConst8S = 0x00070000,
    SplatConst8   = 0x00080000,
    ExtendU       = 0x00090000,
    ExtendS       = 0x000a0000,
    Splat         = 0x000b0000,

    None          = 0x000c0000,
    Any           = 0x000d0000,
    All           = 0x000e0000,
    Eq            = 0x000f0000,
    Ne            = 0x00100000,
    LtU           = 0x00110000,
    LtS           = 0x00120000,
    GtU           = 0x00130000,
    GtS           = 0x00140000,
    LeU           = 0x00150000,
    LeS           = 0x00160000,
    GeU           = 0x00170000,
    GeS           = 0x00180000,
    MinU          = 0x00190000,
    MinS          = 0x001a0000,
    MaxU          = 0x001b0000,
    MaxS          = 0x001c0000,

    Neg           = 0x001d0000,
    Abs           = 0x001e0000,
    Not           = 0x001f0000,
    Clz           = 0x00200000,
    Ctz           = 0x00210000,
    Popcnt        = 0x00220000,
    Add           = 0x00230000,
    Sub           = 0x00240000,
    Mul           = 0x00250000,
    And           = 0x00260000,
    Andnot        = 0x00270000,
    Or            = 0x00280000,
    Xor           = 0x00290000,
    Shl           = 0x002a0000,
    ShrU          = 0x002b0000,
    ShrS          = 0x002c0000,
    Rotl          = 0x002d0000,
    Rotr          = 0x002e0000,
}

impl fmt::Display for OpCode {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let name = match self {
            OpCode::Extract       => "extract",
            OpCode::Replace       => "replace",
            OpCode::Select        => "select",
            OpCode::Shuffle       => "shuffle",

            OpCode::Arg           => "arg",
            OpCode::Ret           => "ret",

            OpCode::ExtendConstU  => "extend_const_u",
            OpCode::ExtendConstS  => "extend_const_s",
            OpCode::SplatConst    => "splat_const",
            OpCode::ExtendConst8U => "extend_const8_u",
            OpCode::ExtendConst8S => "extend_const8_s",
            OpCode::SplatConst8   => "splat_const8",
            OpCode::ExtendU       => "extend_u",
            OpCode::ExtendS       => "extend_s",
            OpCode::Splat         => "splat",

            OpCode::None          => "none",
            OpCode::Any           => "any",
            OpCode::All           => "all",
            OpCode::Eq            => "eq",
            OpCode::Ne            => "ne",
            OpCode::LtU           => "lt_u",
            OpCode::LtS           => "lt_s",
            OpCode::GtU           => "gt_u",
            OpCode::GtS           => "gt_s",
            OpCode::LeU           => "le_u",
            OpCode::LeS           => "le_s",
            OpCode::GeU           => "ge_u",
            OpCode::GeS           => "ge_s",
            OpCode::MinU          => "min_u",
            OpCode::MinS          => "min_s",
            OpCode::MaxU          => "max_u",
            OpCode::MaxS          => "max_s",

            OpCode::Neg           => "neg",
            OpCode::Abs           => "abs",
            OpCode::Not           => "not",
            OpCode::Clz           => "clz",
            OpCode::Ctz           => "ctz",
            OpCode::Popcnt        => "popcnt",
            OpCode::Add           => "add",
            OpCode::Sub           => "sub",
            OpCode::Mul           => "mul",
            OpCode::And           => "and",
            OpCode::Andnot        => "andnot",
            OpCode::Or            => "or",
            OpCode::Xor           => "xor",
            OpCode::Shl           => "shl",
            OpCode::ShrU          => "shr_u",
            OpCode::ShrS          => "shr_s",
            OpCode::Rotl          => "rotl",
            OpCode::Rotr          => "rotr",
        };
        write!(fmt, "{}", name)
    }
}


/// An encoded instruction
#[derive(Debug, Copy, Clone)]
pub struct OpIns(u32);

impl OpIns {
    /// Create a new instruction from its components
    #[inline]
    pub const fn new(
        npw2: u8,
        lnpw2: u8,
        opcode: OpCode,
        p: u8,
        a: u8,
        b: u8
    ) -> OpIns {
        OpIns(
            ((npw2 as u32) << 29)
                | ((lnpw2 as u32) << 26)
                | (opcode as u32)
                | ((p as u32) << 16)
                | ((a as u32) << 8)
                | ((b as u32) << 0)
        )
    }

    #[inline]
    pub fn opcode(&self) -> OpCode {
        let opcode = if self.0 & 0x02000000 != 0 {
            self.0 & 0x03000000
        } else if self.0 & 0x01000000 != 0 {
            self.0 & 0x03800000
        } else {
            self.0 & 0x03ff0000
        };

        // we check for OpCode validity on every function that can build
        // an Op, so this should only result in valid OpCodes
        unsafe { transmute(opcode) }
    }

    #[inline]
    pub fn npw2(&self) -> u8 {
        ((self.0 & 0xe0000000) >> 29) as u8
    }

    #[inline]
    pub fn size(&self) -> usize {
        1usize << self.npw2()
    }

    #[inline]
    pub fn width(&self) -> usize {
        8*self.size()
    }

    #[inline]
    pub fn lnpw2(&self) -> u8 {
        ((self.0 & 0x1c000000) >> 26) as u8
    }

    #[inline]
    pub fn lcount(&self) -> usize {
        1usize << self.lnpw2()
    }

    #[inline]
    pub fn lsize(&self) -> usize {
        self.size() >> self.lnpw2()
    }

    #[inline]
    pub fn lwidth(&self) -> usize {
        8*self.lsize()
    }

    #[inline]
    pub fn p(&self) -> u8 {
        (self.0 >> 16) as u8
    }

    #[inline]
    pub fn a(&self) -> u8 {
        (self.0 >> 8) as u8
    }

    #[inline]
    pub fn b(&self) -> u8 {
        (self.0 >> 0) as u8
    }
}

impl From<OpIns> for u32 {
    fn from(ins: OpIns) -> u32 {
        ins.0
    }
}

impl TryFrom<u32> for OpIns {
    type Error = Error;

    fn try_from(ins: u32) -> Result<Self, Self::Error> {
        // ensure opcode is valid
        match (ins & 0x03ff0000) >> 16 {
            0x100..=0x17f => OpCode::Extract,
            0x180..=0x1ff => OpCode::Replace,
            0x200..=0x2ff => OpCode::Select,
            0x300..=0x3ff => OpCode::Shuffle,

            0x001 => OpCode::Arg,
            0x002 => OpCode::Ret,

            0x003 => OpCode::ExtendConstU,
            0x004 => OpCode::ExtendConstS,
            0x005 => OpCode::SplatConst,
            0x006 => OpCode::ExtendConst8U,
            0x007 => OpCode::ExtendConst8S,
            0x008 => OpCode::SplatConst8,
            0x009 => OpCode::ExtendU,
            0x00a => OpCode::ExtendS,
            0x00b => OpCode::Splat,

            0x00c => OpCode::None,
            0x00d => OpCode::Any,
            0x00e => OpCode::All,
            0x00f => OpCode::Eq,
            0x010 => OpCode::Ne,
            0x011 => OpCode::LtU,
            0x012 => OpCode::LtS,
            0x013 => OpCode::GtU,
            0x014 => OpCode::GtS,
            0x015 => OpCode::LeU,
            0x016 => OpCode::LeS,
            0x017 => OpCode::GeU,
            0x018 => OpCode::GeS,
            0x019 => OpCode::MinU,
            0x01a => OpCode::MinS,
            0x01b => OpCode::MaxU,
            0x01c => OpCode::MaxS,

            0x01d => OpCode::Neg,
            0x01f => OpCode::Abs,
            0x01e => OpCode::Not,
            0x020 => OpCode::Clz,
            0x021 => OpCode::Ctz,
            0x022 => OpCode::Popcnt,
            0x023 => OpCode::Add,
            0x024 => OpCode::Sub,
            0x025 => OpCode::Mul,
            0x026 => OpCode::And,
            0x027 => OpCode::Andnot,
            0x028 => OpCode::Or,
            0x029 => OpCode::Xor,
            0x02a => OpCode::Shl,
            0x02b => OpCode::ShrU,
            0x02c => OpCode::ShrS,
            0x02d => OpCode::Rotl,
            0x02e => OpCode::Rotr,

            _ => Err(Error::InvalidOpcode(ins))?,
        };

        Ok(Self(ins))
    }
}

impl fmt::Display for OpIns {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self.opcode() {
            OpCode::Extract => {
                write!(fmt, "u{}.{} r{}, r{}[{}]",
                    prefix(self.npw2(), self.lnpw2()),
                    self.opcode(),
                    self.a(),
                    self.b(),
                    self.p()
                )
            }

            OpCode::Replace => {
                write!(fmt, "u{}.{} r{}[{}], r{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.opcode(),
                    self.a(),
                    self.p(),
                    self.b()
                )
            }

            OpCode::Select | OpCode::Shuffle => {
                write!(fmt, "u{}.{} r{}, r{}, r{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.opcode(),
                    self.p(),
                    self.a(),
                    self.b()
                )
            }


            // special format for moves because they are so common
            OpCode::ExtendConstU if self.lnpw2() == 0 => {
                write!(fmt, "u{}.move_const r{}",
                    self.width(),
                    self.a()
                )
            }

            OpCode::ExtendConstU | OpCode::ExtendConstS | OpCode::SplatConst => {
                write!(fmt, "u{}.{} r{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.opcode(),
                    self.a()
                )
            }

            // special format for moves because they are so common
            OpCode::ExtendConst8U if self.lnpw2() == 0 => {
                write!(fmt, "u{}.move_const8 r{}",
                    self.width(),
                    self.a()
                )
            }

            OpCode::ExtendConst8U | OpCode::ExtendConst8S | OpCode::SplatConst8 => {
                write!(fmt, "u{}.{} r{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.opcode(),
                    self.a()
                )
            }

            // special format for moves because they are so common
            OpCode::ExtendU if self.lnpw2() == 0 => {
                write!(fmt, "u{}.move r{}, r{}",
                    self.width(),
                    self.a(),
                    self.b()
                )
            }

            _ => {
                write!(fmt, "u{}.{} r{}, r{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.opcode(),
                    self.a(),
                    self.b()
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

fn prefix(npw2: u8, lnpw2: u8) -> String {
    if lnpw2 == 0 {
        format!("{}", 8usize << npw2)
    } else {
        format!("{}x{}", (8usize << npw2) >> lnpw2, 1usize << lnpw2)
    }
}

/// helper function for debugging
pub fn disas<W: io::Write>(
    bytecode: &[u32],
    mut out: W
) -> Result<(), io::Error> {
    let mut i = 0;
    while i < bytecode.len() {
        let ins = bytecode[i];
        i += 1;

        match OpIns::try_from(ins) {
            Ok(ins) => {
                match ins.opcode() {
                    OpCode::ExtendConstU | OpCode::ExtendConstS | OpCode::SplatConst => {
                        let const_size = max(1, ins.lsize()/4);
                        write!(out, "    {:08x} {}, 0x", u32::from(ins), ins)?;
                        for j in (0..const_size).rev() {
                            write!(out, "{:0w$x}",
                                &bytecode[i+j],
                                w=2*min(4, ins.lsize())
                            )?;
                        }
                        writeln!(out)?;
                        for _ in 0..const_size {
                            writeln!(out, "    {:08x}", bytecode[i])?;
                            i += 1;
                        }
                    }
                    OpCode::ExtendConst8U | OpCode::ExtendConst8S | OpCode::SplatConst8 => {
                        writeln!(out, "    {:08x} {}, 0x{:02x}", u32::from(ins), ins, ins.b())?;
                    }
                    _ => {
                        writeln!(out, "    {:08x} {}", u32::from(ins), ins)?;
                    }
                }
            }
            Err(Error::InvalidOpcode(ins)) => {
                writeln!(out, "    {:08x} unknown {:#010x}", ins, ins)?;
            }
            Err(err) => {
                panic!("unexpected error in disas: {}", err);
            }
        }
    }

    Ok(())
}

/// Trait for the underlying types
pub trait OpU: Default + Copy + Clone + Debug + LowerHex + Eq + Sized + 'static {
    /// npw2(size)
    const NPW2: u8;

    /// raw byte representation
    type Bytes: AsRef<[u8]> + AsMut<[u8]> + for<'a> TryFrom<&'a [u8]>;

    /// to raw byte representation
    fn to_le_bytes(self) -> Self::Bytes;

    /// from raw byte representation
    fn from_le_bytes(bytes: Self::Bytes) -> Self;

    /// Zero
    fn zero() -> Self;

    /// One
    fn one() -> Self;

    /// All bits set to one
    fn ones() -> Self;

    /// Test if self is zero
    fn is_zero(&self) -> bool {
        self == &Self::ones()
    }

    /// Test if self is one
    fn is_one(&self) -> bool {
        self == &Self::one()
    }

    /// Test if self is ones
    fn is_ones(&self) -> bool {
        self == &Self::ones()
    }

    /// Can we compress into an extend_const_u instruction?
    fn is_extend_u_compressable(&self, npw2: u8) -> bool {
        let bytes = self.to_le_bytes();
        let bytes = bytes.as_ref();
        let width = 1usize << npw2;
        bytes[width..].iter().all(|b| *b == 0)
    }

    /// Can we compress into an extend_const_s instruction?
    fn is_extend_s_compressable(&self, npw2: u8) -> bool {
        let bytes = self.to_le_bytes();
        let bytes = bytes.as_ref();
        let width = 1usize << npw2;
        if bytes[width-1] & 0x80 == 0x80 {
            bytes[width..].iter().all(|b| *b == 0xff)
        } else {
            bytes[width..].iter().all(|b| *b == 0x00)
        }
    }

    /// Can we compress into a splat_const instruction?
    fn is_splat_compressable(&self, npw2: u8) -> bool {
        let bytes = self.to_le_bytes();
        let bytes = bytes.as_ref();
        let width = 1usize << npw2;
        (width..bytes.len())
            .step_by(width)
            .all(|i| &bytes[i..i+width] == &bytes[..width])
    }
}

macro_rules! opu_impl {
    ($u:ident([u8; $n:expr]; $npw2:expr $(; $($prim:ty),*)?)) => {
        #[derive(Copy, Clone, Debug, Eq, PartialEq)]
        pub struct $u([u8; $n]);

        impl From<[u8; $n]> for $u {
            fn from(v: [u8; $n]) -> Self {
                Self::from_le_bytes(v)
            }
        }

        impl From<$u> for [u8; $n] {
            fn from(v: $u) -> [u8; $n] {
                v.to_le_bytes()
            }
        }

        $($(
            impl From<$prim> for $u {
                fn from(v: $prim) -> Self {
                    Self::from_le_bytes(v.to_le_bytes())
                }
            }

            impl From<$u> for $prim {
                fn from(v: $u) -> $prim {
                    <$prim>::from_le_bytes(v.to_le_bytes())
                }
            }
        )*)?

        impl OpU for $u {
            const NPW2: u8 = $npw2;

            /// raw byte representation
            type Bytes = [u8; $n];

            /// to raw byte representation
            fn to_le_bytes(self) -> Self::Bytes {
                self.0
            }

            /// from raw byte representation
            fn from_le_bytes(bytes: Self::Bytes) -> Self {
                Self(bytes)
            }

            /// Zero
            fn zero() -> Self {
                Self([0; $n])
            }

            /// One
            fn one() -> Self {
                let mut one = [0; $n];
                one[0] = 1;
                Self::try_from(one).unwrap()
            }

            /// All bits set to one
            fn ones() -> Self {
                Self([0xff; $n])
            }
        }

        impl Default for $u {
            fn default() -> Self {
                Self::zero()
            }
        }

        impl LowerHex for $u {
            fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
                write!(fmt, "0x")?;
                for b in self.0.iter().rev() {
                    write!(fmt, "{:02x}", b)?;
                }
                Ok(())
            }
        }
    }
}

opu_impl! { U8  ([u8;  1]; 0; u8,   i8  ) }
opu_impl! { U16 ([u8;  2]; 1; u16,  i16 ) }
opu_impl! { U32 ([u8;  4]; 2; u32,  i32 ) }
opu_impl! { U64 ([u8;  8]; 3; u64,  i64 ) }
opu_impl! { U128([u8; 16]; 4; u128, i128) }
opu_impl! { U256([u8; 32]; 5)             }
opu_impl! { U512([u8; 64]; 6)             }


/// Kinds of operations in tree
#[derive(Debug)]
pub enum OpKind<T: OpU> {
    Const(T),
    Imm(T),
    Sym(&'static str),

    Extract(u8, Rc<dyn DynOpNode>),
    Replace(u8, Rc<OpNode<T>>, Rc<dyn DynOpNode>),
    Select(u8, Rc<OpNode<T>>, Rc<OpNode<T>>, Rc<OpNode<T>>),
    Shuffle(u8, Rc<OpNode<T>>, Rc<OpNode<T>>, Rc<OpNode<T>>),

    ExtendU(Rc<dyn DynOpNode>),
    ExtendS(Rc<dyn DynOpNode>),
    Splat(Rc<dyn DynOpNode>),

    None(Rc<OpNode<T>>),
    Any(Rc<OpNode<T>>),
    All(u8, Rc<OpNode<T>>),
    Eq(u8, Rc<OpNode<T>>, Rc<OpNode<T>>),
    Ne(u8, Rc<OpNode<T>>, Rc<OpNode<T>>),
    LtU(u8, Rc<OpNode<T>>, Rc<OpNode<T>>),
    LtS(u8, Rc<OpNode<T>>, Rc<OpNode<T>>),
    GtU(u8, Rc<OpNode<T>>, Rc<OpNode<T>>),
    GtS(u8, Rc<OpNode<T>>, Rc<OpNode<T>>),
    LeU(u8, Rc<OpNode<T>>, Rc<OpNode<T>>),
    LeS(u8, Rc<OpNode<T>>, Rc<OpNode<T>>),
    GeU(u8, Rc<OpNode<T>>, Rc<OpNode<T>>),
    GeS(u8, Rc<OpNode<T>>, Rc<OpNode<T>>),
    MinU(u8, Rc<OpNode<T>>, Rc<OpNode<T>>),
    MinS(u8, Rc<OpNode<T>>, Rc<OpNode<T>>),
    MaxU(u8, Rc<OpNode<T>>, Rc<OpNode<T>>),
    MaxS(u8, Rc<OpNode<T>>, Rc<OpNode<T>>),

    Neg(u8, Rc<OpNode<T>>),
    Abs(u8, Rc<OpNode<T>>),
    Not(Rc<OpNode<T>>),
    Clz(u8, Rc<OpNode<T>>),
    Ctz(u8, Rc<OpNode<T>>),
    Popcnt(u8, Rc<OpNode<T>>),
    Add(u8, Rc<OpNode<T>>, Rc<OpNode<T>>),
    Sub(u8, Rc<OpNode<T>>, Rc<OpNode<T>>),
    Mul(u8, Rc<OpNode<T>>, Rc<OpNode<T>>),
    And(Rc<OpNode<T>>, Rc<OpNode<T>>),
    Andnot(Rc<OpNode<T>>, Rc<OpNode<T>>),
    Or(Rc<OpNode<T>>, Rc<OpNode<T>>),
    Xor(Rc<OpNode<T>>, Rc<OpNode<T>>),
    Shl(u8, Rc<OpNode<T>>, Rc<OpNode<T>>),
    ShrU(u8, Rc<OpNode<T>>, Rc<OpNode<T>>),
    ShrS(u8, Rc<OpNode<T>>, Rc<OpNode<T>>),
    Rotl(u8, Rc<OpNode<T>>, Rc<OpNode<T>>),
    Rotr(u8, Rc<OpNode<T>>, Rc<OpNode<T>>),
}


/// Tree of operations, including metadata to deduplicate
/// common branches
#[derive(Debug)]
pub struct OpNode<T: OpU> {
    kind: OpKind<T>,
    refs: Cell<u32>,
    slot: Cell<Option<u8>>,
    flags: u8,
    depth: u32,
    #[cfg(feature="opt-fold-consts")]
    folded: RefCell<Option<Option<Rc<OpNode<T>>>>>,
}

/// Root OpNode with additional small object optimization, which
/// is useful for avoiding unnecessary allocations
///
/// Note this still participates in DAG deduplication by lazily
/// allocating on demand, the result is a lot of RefCells...
///
/// Also not that Cell is not usable here because Rc does not
/// implement Copy
///
#[derive(Debug)]
pub struct OpTree<T: OpU>(RefCell<OpRoot<T>>);

#[derive(Debug)]
pub enum OpRoot<T: OpU> {
    Const(T),
    Imm(T),
    Tree(Rc<OpNode<T>>),
}

impl<T: OpU> Default for OpTree<T> {
    fn default() -> Self {
        Self::zero()
    }
}

impl<T: OpU> Clone for OpTree<T> {
    // clone defers to tree, which ensures the backing tree is
    // Rc before cloning
    fn clone(&self) -> Self {
        OpTree(RefCell::new(OpRoot::Tree(self.node())))
    }
}



/// Pool for allocating/reusing slots in a fictional blob of bytes
#[derive(Debug)]
struct SlotPool {
    // pool of deallocated slots, note the reversed
    // order so that we are sorted first by slot size,
    // and second by decreasing slot numbers
    #[cfg(feature="opt-color-slots")]
    pool: BTreeSet<(u8, i16)>,
    //              ^   ^- negative slot number
    //              '----- slot npw2

    // current end of blob
    size: usize,

    // aligned of blob
    max_npw2: u8,
}

impl SlotPool {
    /// Create a new empty slot pool
    fn new() -> SlotPool {
        SlotPool {
            #[cfg(feature="opt-color-slots")]
            pool: BTreeSet::new(),
            size: 0,
            max_npw2: 9,
        }
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

        #[cfg(feature="opt-color-slots")]
        {
            // find smallest slot where size >= npw2 but slot*size < 256
            let best_slot = self.pool.range((npw2, i16::MIN)..)
                .copied()
                .filter(|(best_npw2, best_islot)| {
                    // fits in slot number?
                    u8::try_from(
                        (usize::try_from(-best_islot).unwrap() << best_npw2)
                            >> npw2
                    ).is_ok()
                })
                .next();
            if let Some((mut best_npw2, best_islot)) = best_slot {
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
                self.max_npw2 = max(self.max_npw2, npw2);
                return Ok(best_slot)
            }
        }


        // no slot found? fallback to increasing size of our slot pool

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
                self.max_npw2 = max(self.max_npw2, npw2);
                Ok(slot)
            }
            _ => {
                Err(Error::OutOfSlots(npw2))
            }
        }
    }

    /// Return a slot to the pool
    fn dealloc(
        &mut self,
        #[allow(unused)] mut slot: u8,
        #[allow(unused)] mut npw2: u8
    ) {
        // do nothing here if we aren't reusing slots
        #[cfg(feature="opt-color-slots")]
        {
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
}

/// Compilation state
pub struct OpCompile {
    bytecode: Vec<u32>,
    slots: Vec<u8>,

    #[allow(dead_code)]
    opt: bool,
    slot_pool: SlotPool,
}

impl OpCompile {
    fn new(opt: bool) -> OpCompile {
        OpCompile {
            bytecode: Vec::new(),
            slots: Vec::new(),

            opt: opt,
            slot_pool: SlotPool::new(),
        }
    }
}


/// A trait to help with conversions between trees of different types
pub trait DynOpTree {
    /// get NPW2 of the underlying tree
    fn npw2(&self) -> u8;

    /// get the underlying DynOpNode
    fn dyn_node(&self) -> Rc<dyn DynOpNode>;

    // some dyn operations that can avoid casting
    fn dyn_not(&self) -> Rc<dyn DynOpTree>;
    fn dyn_and(&self, other: &dyn DynOpTree) -> Rc<dyn DynOpTree>;
    fn dyn_andnot(&self, other: &dyn DynOpTree) -> Rc<dyn DynOpTree>;
    fn dyn_notand(&self, other: &dyn DynOpTree) -> Rc<dyn DynOpTree>;
    fn dyn_or(&self, other: &dyn DynOpTree) -> Rc<dyn DynOpTree>;
    fn dyn_xor(&self, other: &dyn DynOpTree) -> Rc<dyn DynOpTree>;
}

impl<T: OpU> DynOpTree for OpTree<T> {
    fn npw2(&self) -> u8 {
        T::NPW2
    }

    fn dyn_node(&self) -> Rc<dyn DynOpNode> {
        // node triggers a lazily allocated Rc object here, and then
        // we insert our trait object as we return, neato
        self.node()
    }

    fn dyn_not(&self) -> Rc<dyn DynOpTree> {
        Rc::new(Self::not(self.clone()))
    }

    fn dyn_and(&self, other: &dyn DynOpTree) -> Rc<dyn DynOpTree> {
        // use the smallest type
        if other.npw2() < self.npw2() {
            other.dyn_and(self)
        } else {
            Rc::new(Self::and(self.clone(), OpTree::dyn_cast_s(other)))
        }
    }

    fn dyn_andnot(&self, other: &dyn DynOpTree) -> Rc<dyn DynOpTree> {
        // use the smallest type
        if other.npw2() < self.npw2() {
            other.dyn_notand(self)
        } else {
            Rc::new(Self::andnot(self.clone(), OpTree::dyn_cast_s(other)))
        }
    }

    fn dyn_notand(&self, other: &dyn DynOpTree) -> Rc<dyn DynOpTree> {
        // use the smallest type
        if other.npw2() < self.npw2() {
            other.dyn_andnot(self)
        } else {
            Rc::new(Self::andnot(OpTree::dyn_cast_s(other), self.clone()))
        }
    }

    fn dyn_or(&self, other: &dyn DynOpTree) -> Rc<dyn DynOpTree> {
        // use the smallest type
        if other.npw2() < self.npw2() {
            other.dyn_or(self)
        } else {
            Rc::new(Self::or(self.clone(), OpTree::dyn_cast_s(other)))
        }
    }

    fn dyn_xor(&self, other: &dyn DynOpTree) -> Rc<dyn DynOpTree> {
        // use the smallest type
        if other.npw2() < self.npw2() {
            other.dyn_xor(self)
        } else {
            Rc::new(Self::xor(self.clone(), OpTree::dyn_cast_s(other)))
        }
    }
}


/// Core of the OpTree
impl<T: OpU> OpTree<T> {
    /// Create an immediate, secret value
    pub fn imm<U>(v: U) -> Self
    where
        T: From<U>
    {
        OpTree(RefCell::new(OpRoot::Imm(T::from(v))))
    }

    /// Create a const susceptable to compiler optimizations
    pub fn const_<U>(v: U) -> Self
    where
        T: From<U>
    {
        OpTree(RefCell::new(OpRoot::Const(T::from(v))))
    }

    /// A constant 0
    pub fn zero() -> Self {
        Self::const_(T::zero())
    }

    /// A constant 1
    pub fn one() -> Self {
        Self::const_(T::one())
    }

    /// A constant with all bits set to 1
    pub fn ones() -> Self {
        Self::const_(T::ones())
    }

    /// Create new tree
    fn from_kind(kind: OpKind<T>, flags: u8, depth: u32) -> Self {
        OpTree(RefCell::new(OpRoot::Tree(Rc::new(OpNode::new(kind, flags, depth)))))
    }

    /// Get internal tree, potentially allocating if needed
    fn node(&self) -> Rc<OpNode<T>> {
        let mut tree = self.0.borrow_mut();
        match &*tree {
            OpRoot::Const(v) => {
                // convert to Rc if necessary
                let node = Rc::new(OpNode::new(
                    OpKind::Const(*v), 0, 0
                ));
                *tree = OpRoot::Tree(node.clone());
                node
            }
            OpRoot::Imm(v) => {
                // convert to Rc if necessary
                let node = Rc::new(OpNode::new(
                    OpKind::Imm(*v), OpNode::<T>::SECRET, 0
                ));
                *tree = OpRoot::Tree(node.clone());
                node
            }
            OpRoot::Tree(node) => {
                // can just increment reference count here
                node.clone()
            }
        }
    }

    /// Forcefully downcast into a different OpTree, panicking if types
    /// do not match
    pub fn dyn_downcast(a: &dyn DynOpTree) -> Self {
        assert_eq!(a.npw2(), T::NPW2);
        let b: &Self = unsafe { &*(a as *const dyn DynOpTree as *const Self) };
        b.clone()
    }

    /// Helper for choosing the most efficient cast between trees of
    /// different types, including returning the tree as is with only
    /// the type information stripped
    pub fn dyn_cast_u(a: &dyn DynOpTree) -> Self {
        if T::NPW2 > a.npw2() {
            let a = a.dyn_node();
            let flags = a.flags();
            let depth = a.depth();
            Self::from_kind(OpKind::ExtendU(a), flags, depth)
        } else if T::NPW2 < a.npw2() {
            let a = a.dyn_node();
            let flags = a.flags();
            let depth = a.depth();
            Self::from_kind(OpKind::Extract(0, a), flags, depth)
        } else {
            Self::dyn_downcast(a)
        }
    }

    /// Helper for choosing the most efficient cast between trees of
    /// different types, including returning the tree as is with only
    /// the type information stripped
    pub fn dyn_cast_s(a: &dyn DynOpTree) -> Self {
        if T::NPW2 > a.npw2() {
            let a = a.dyn_node();
            let flags = a.flags();
            let depth = a.depth();
            Self::from_kind(OpKind::ExtendS(a), flags, depth)
        } else if T::NPW2 < a.npw2() {
            let a = a.dyn_node();
            let flags = a.flags();
            let depth = a.depth();
            Self::from_kind(OpKind::Extract(0, a), flags, depth)
        } else {
            Self::dyn_downcast(a)
        }
    }

    /// is expression an immediate?
    pub fn is_imm(&self) -> bool {
        match &*self.0.borrow() {
            OpRoot::Const(_) => true,
            OpRoot::Imm(_) => true,
            OpRoot::Tree(tree) => tree.is_imm(),
        }
    }

    /// is expression a symbol?
    pub fn is_sym(&self) -> bool {
        match &*self.0.borrow() {
            OpRoot::Const(_) => false,
            OpRoot::Imm(_) => false,
            OpRoot::Tree(tree) => tree.is_sym(),
        }
    }

    /// is expression const?
    pub fn is_const(&self) -> bool {
        match &*self.0.borrow() {
            OpRoot::Const(_) => true,
            OpRoot::Imm(_) => false,
            OpRoot::Tree(tree) => tree.is_const(),
        }
    }

    // Constructors for other tree nodes, note that
    // constant-ness is propogated
    pub fn sym(name: &'static str) -> Self {
        Self::from_kind(OpKind::Sym(name), OpNode::<T>::SECRET | OpNode::<T>::SYM, 0)
    }

    pub fn extract<U: OpU>(x: u8, a: OpTree<U>) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Extract(x, a), flags, depth)
    }

    pub fn replace<U: OpU>(x: u8, a: Self, b: OpTree<U>) -> Self {
        let a = a.node();
        let b = b.dyn_node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Replace(x, a, b), flags, depth)
    }

    pub fn select(lnpw2: u8, p: Self, a: Self, b: Self) -> Self {
        let p = p.node();
        let a = a.node();
        let b = b.node();
        let flags = p.flags() | a.flags() | b.flags();
        let depth = max(p.depth(), max(a.depth(), b.depth())).saturating_add(1);
        Self::from_kind(OpKind::Select(lnpw2, p, a, b), flags, depth)
    }

    pub fn shuffle(lnpw2: u8, p: Self, a: Self, b: Self) -> Self {
        let p = p.node();
        let a = a.node();
        let b = b.node();
        let flags = p.flags() | a.flags() | b.flags();
        let depth = max(p.depth(), max(a.depth(), b.depth())).saturating_add(1);
        Self::from_kind(OpKind::Shuffle(lnpw2, p, a, b), flags, depth)
    }

    pub fn extend_u<U: OpU>(a: OpTree<U>) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::ExtendU(a), flags, depth)
    }

    pub fn extend_s<U: OpU>(a: OpTree<U>) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::ExtendS(a), flags, depth)
    }

    pub fn splat<U: OpU>(a: OpTree<U>) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Splat(a), flags, depth)
    }

    pub fn none(a: Self) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::None(a), flags, depth)
    }

    pub fn any(a: Self) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Any(a), flags, depth)
    }

    pub fn all(lnpw2: u8, a: Self) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::All(lnpw2, a), flags, depth)
    }

    pub fn eq(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Eq(lnpw2, a, b), flags, depth)
    }

    pub fn ne(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Ne(lnpw2, a, b), flags, depth)
    }

    pub fn lt_u(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::LtU(lnpw2, a, b), flags, depth)
    }

    pub fn lt_s(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::LtS(lnpw2, a, b), flags, depth)
    }

    pub fn gt_u(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::GtU(lnpw2, a, b), flags, depth)
    }

    pub fn gt_s(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::GtS(lnpw2, a, b), flags, depth)
    }

    pub fn le_u(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::LeU(lnpw2, a, b), flags, depth)
    }

    pub fn le_s(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::LeS(lnpw2, a, b), flags, depth)
    }

    pub fn ge_u(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::GeU(lnpw2, a, b), flags, depth)
    }

    pub fn ge_s(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::GeS(lnpw2, a, b), flags, depth)
    }

    pub fn min_u(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::MinU(lnpw2, a, b), flags, depth)
    }

    pub fn min_s(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::MinS(lnpw2, a, b), flags, depth)
    }

    pub fn max_u(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::MaxU(lnpw2, a, b), flags, depth)
    }

    pub fn max_s(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::MaxS(lnpw2, a, b), flags, depth)
    }

    pub fn neg(lnpw2: u8, a: Self) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Neg(lnpw2, a), flags, depth)
    }

    pub fn abs(lnpw2: u8, a: Self) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Abs(lnpw2, a), flags, depth)
    }

    pub fn not(a: Self) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Not(a), flags, depth)
    }

    pub fn clz(lnpw2: u8, a: Self) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Clz(lnpw2, a), flags, depth)
    }

    pub fn ctz(lnpw2: u8, a: Self) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Ctz(lnpw2, a), flags, depth)
    }

    pub fn popcnt(lnpw2: u8, a: Self) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Popcnt(lnpw2, a), flags, depth)
    }

    pub fn add(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Add(lnpw2, a, b), flags, depth)
    }

    pub fn sub(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Sub(lnpw2, a, b), flags, depth)
    }

    pub fn mul(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Mul(lnpw2, a, b), flags, depth)
    }

    pub fn and(a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::And(a, b), flags, depth)
    }

    pub fn andnot(a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Andnot(a, b), flags, depth)
    }

    pub fn or(a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Or(a, b), flags, depth)
    }

    pub fn xor(a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Xor(a, b), flags, depth)
    }

    pub fn shl(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Shl(lnpw2, a, b), flags, depth)
    }

    pub fn shr_u(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::ShrU(lnpw2, a, b), flags, depth)
    }

    pub fn shr_s(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::ShrS(lnpw2, a, b), flags, depth)
    }

    pub fn rotl(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Rotl(lnpw2, a, b), flags, depth)
    }

    pub fn rotr(lnpw2: u8, a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Rotr(lnpw2, a, b), flags, depth)
    }

    /// display tree for debugging
    pub fn disas<W: io::Write>(&self, mut out: W) -> Result<(), io::Error> {
        match &*self.0.borrow() {
            OpRoot::Const(v) => writeln!(out, "    (u{}.const {:x}", 8 << T::NPW2, v),
            OpRoot::Imm(v)   => writeln!(out, "    (u{}.imm {:x})",  8 << T::NPW2, v),
            OpRoot::Tree(tree) => tree.disas(out),
        }
    }

    /// high-level compile into bytecode, stack, and initial stack pointer
    pub fn compile(&self, opt: bool) -> (Vec<u32>, AlignedBytes) {
        self.node().compile(opt)
    }

    /// Assuming we are Sym, patch the slots during a call
    pub fn patch<U>(&self, slots: &mut [u8], v: U)
    where
        T: From<U>
    {
        match &*self.0.borrow() {
            OpRoot::Tree(tree) => tree.patch(slots, v),
            _ => panic!("patching non-sym?")
        }
    }

    /// execute bytecode, resulting in an immediate OpTree
    pub fn exec(bytecode: &[u32], slots: &mut [u8]) -> Self {
        Self::try_exec(bytecode, slots).unwrap()
    }

    /// execute bytecode, resulting in an immediate OpTree
    pub fn try_exec(bytecode: &[u32], slots: &mut [u8]) -> Result<Self, Error> {
        let res = exec(bytecode, slots)?;
        Ok(OpTree(RefCell::new(OpRoot::Imm(T::from_le_bytes(
            T::Bytes::try_from(res).map_err(|_| Error::InvalidReturn)?
        )))))
    }

    /// compile and execute if OpTree is not already an immediate
    pub fn eval(self) -> Self {
        self.try_eval().unwrap()
    }

    /// compile and execute if OpTree is not already an immediate
    pub fn try_eval(self) -> Result<Self, Error> {
        match self.0.into_inner() {
            OpRoot::Const(v) => Ok(Self::const_(v)),
            OpRoot::Imm(v)   => Ok(Self::imm(v)),
            OpRoot::Tree(tree) => {
                let (bytecode, mut stack) = tree.compile(false);
                Self::try_exec(&bytecode, &mut stack)
            }
        }
    }

    /// retrieve result, panicking if OpTree is not in immediate form
    pub fn result<U>(self) -> U
    where
        U: From<T>
    {
        self.try_result::<U>()
            .expect("attempted to get result from un-evaled tree")
    }

    /// retrieve result, or None
    pub fn try_result<U>(self) -> Option<U>
    where
        U: From<T>
    {
        match self.0.into_inner() {
            OpRoot::Const(v) => Some(U::from(v)),
            OpRoot::Imm(v)   => Some(U::from(v)),
            OpRoot::Tree(_)  => None,
        }
    }
}

/// Core OpNode type
impl<T: OpU> OpNode<T> {
    const SECRET: u8 = 0x1;
    const SYM: u8    = 0x2;

    fn new(kind: OpKind<T>, flags: u8, depth: u32) -> OpNode<T> {
        OpNode {
            kind: kind,
            refs: Cell::new(0),
            slot: Cell::new(None),
            flags: flags,
            depth: depth,
            #[cfg(feature="opt-fold-consts")]
            folded: RefCell::new(None),
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

        #[cfg(feature="debug-check-refs")]
        self.check_refs();

        // cleanup last expression
        write!(out, "    {}\n", expr)
    }

    /// high-level compile into bytecode, stack, and initial stack pointer
    pub fn compile(&self, opt: bool) -> (Vec<u32>, AlignedBytes) {
        // should we do a constant folding pass?
        #[cfg(feature="opt-fold-consts")]
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

        let mut state = OpCompile::new(opt);

        // first pass to find number of immediates and deduplicate branches
        self.compile_pass1(&mut state);

        // second pass now to compile the bytecode and stack, note sp now points
        // to end of immediates
        let (slot, _) = self.compile_pass2(&mut state);

        // to make lifetimes work in order to figure out slot reuse, reference
        // counting for is left up to the caller
        let refs = self.dec_refs();
        debug_assert_eq!(refs, 0);

        #[cfg(feature="debug-check-refs")]
        self.check_refs();

        // add required return instruction
        state.bytecode.push(u32::from(OpIns::new(
            T::NPW2, 0, OpCode::Ret, 0, 0, slot
        )));

        // align slots
        let mut aligned_slots = AlignedBytes::new_zeroed(
            state.slot_pool.size,
            1usize << state.slot_pool.max_npw2
        );
        aligned_slots[..state.slots.len()].copy_from_slice(&state.slots);

        #[cfg(feature="debug-bytecode")]
        {
            println!("slots:");
            print!("   ");
            for b in aligned_slots.iter() {
                 print!(" {:02x}", b);
            }
            println!();

            println!("bytecode:");
            disas(&state.bytecode, io::stdout()).unwrap();
        }

        // imms is now the initial stack pointer
        (state.bytecode, aligned_slots)
    }

    /// Assuming we are Sym, patch the slots during a call
    pub fn patch<U>(&self, slots: &mut [u8], v: U)
    where
        T: From<U>
    {
        assert!(
            match self.kind {
                OpKind::Sym(_) => true,
                _              => false,
            },
            "patching non-sym?"
        );

        let slot = self.slot.get().expect("patching with no slot?");
        slots[
            slot as usize * size_of::<T>()
                .. (slot as usize + 1) * size_of::<T>()
        ].copy_from_slice(T::from(v).to_le_bytes().as_ref());
    }

    /// compile and execute if value is not already an immediate or constant
    pub fn eval(&self) -> T {
        self.try_eval().unwrap()
    }

    /// compile and execute if value is not already an immediate or constant
    pub fn try_eval(&self) -> Result<T, Error> {
        let (bytecode, mut stack) = self.compile(false);
        Ok(OpTree::try_exec(&bytecode, &mut stack)?.result())
    }
}

// dyn-compatible wrapping trait
pub trait DynOpNode: Debug {
    /// npw2(size), used as a part of instruction encoding
    fn npw2(&self) -> u8;

    /// bitwised-or flags from all branches
    fn flags(&self) -> u8;

    /// saturating depth of tree for heuristic purposes
    fn depth(&self) -> u32;

    /// is expression an immediate?
    fn is_imm(&self) -> bool;

    /// is expression a symbol?
    fn is_sym(&self) -> bool;

    /// is expression const?
    fn is_const(&self) -> bool;

    /// checks if expression is const and is zero
    fn is_const_zero(&self) -> bool;

    /// checks if expression is const and is one
    fn is_const_one(&self) -> bool;

    /// checks if expression is const and is ones
    fn is_const_ones(&self) -> bool;

    /// Increment tree-internal reference count
    fn inc_refs(&self) -> u32;

    /// Decrement tree-internal reference count
    fn dec_refs(&self) -> u32;

    /// First pass for debug output
    fn disas_pass1(&self);

    /// Second pass for debug output
    fn disas_pass2(
        &self,
        names: &mut HashMap<usize, String>,
        arbitrary_names: &mut dyn Iterator<Item=String>,
        stmts: &mut dyn io::Write,
    ) -> Result<String, io::Error>;

    /// Optional pass to check that refs return to 0
    ///
    /// Note this is very expensive
    #[cfg(feature="debug-check-refs")]
    fn check_refs(&self);

    /// An optional pass to fold consts in the tree
    #[cfg(feature="opt-fold-consts")]
    fn fold_consts(&self);

    /// First compile pass, used to find the number of immediates
    /// for offset calculation, and local reference counting to
    /// deduplicate branches.
    fn compile_pass1(&self, state: &mut OpCompile);

    /// Second compile pass, used to actually compile both the
    /// immediates and bytecode. Returns the resulting slot + npw2.
    fn compile_pass2(&self, state: &mut OpCompile) -> (u8, u8);
}


// schedule branches in operations in order to minimize slot usage, note this
// macro is only designed for compile_pass2 and if I could put the macro in
// a different scope I would
//
// we don't know the actual slot usage until compilation, so instead we use the
// saturated depth as a heuristic, most of the branches with registers we can save
// are quite small anyways
//
#[cfg(feature="opt-schedule-slots")]
macro_rules! schedule {
    (
        let ($a_slot:ident, $a_npw2:ident) = $a:ident.compile_pass2($a_state:ident);
        let ($b_slot:ident, $b_npw2:ident) = $b:ident.compile_pass2($b_state:ident);
    ) => {
        let a_tuple;
        let b_tuple;
        if $a.depth() > $b.depth() {
            a_tuple = $a.compile_pass2($a_state);
            b_tuple = $b.compile_pass2($b_state);
        } else {
            b_tuple = $b.compile_pass2($b_state);
            a_tuple = $a.compile_pass2($a_state);
        }
        let ($a_slot, $a_npw2) = a_tuple;
        let ($b_slot, $b_npw2) = b_tuple;
    };
    (
        let ($p_slot:ident, $p_npw2:ident) = $p:ident.compile_pass2($p_state:ident);
        let ($a_slot:ident, $a_npw2:ident) = $a:ident.compile_pass2($a_state:ident);
        let ($b_slot:ident, $b_npw2:ident) = $b:ident.compile_pass2($b_state:ident);
    ) => {
        // this isn't perfect, but more efficient than fully sorting
        let a_tuple;
        let b_tuple;
        if $a.depth() > $b.depth() {
            a_tuple = $a.compile_pass2($a_state);
            b_tuple = $b.compile_pass2($b_state);
        } else {
            b_tuple = $b.compile_pass2($b_state);
            a_tuple = $a.compile_pass2($a_state);
        }
        let ($a_slot, $a_npw2) = a_tuple;
        let ($b_slot, $b_npw2) = b_tuple;
        // we're guessing predicates are usually more short lived
        let ($p_slot, $p_npw2) = $p.compile_pass2($p_state);
    };
}
#[cfg(not(feature="opt-schedule-slots"))]
macro_rules! schedule {
    (
        let ($a_slot:ident, $a_npw2:ident) = $a:ident.compile_pass2($a_state:ident);
        let ($b_slot:ident, $b_npw2:ident) = $b:ident.compile_pass2($b_state:ident);
    ) => {
        let ($a_slot, $a_npw2) = $a.compile_pass2($a_state);
        let ($b_slot, $b_npw2) = $b.compile_pass2($b_state);
    };
    (
        let ($p_slot:ident, $p_npw2:ident) = $p:ident.compile_pass2($p_state:ident);
        let ($a_slot:ident, $a_npw2:ident) = $a:ident.compile_pass2($a_state:ident);
        let ($b_slot:ident, $b_npw2:ident) = $b:ident.compile_pass2($b_state:ident);
    ) => {
        let ($a_slot, $a_npw2) = $a.compile_pass2($a_state);
        let ($b_slot, $b_npw2) = $b.compile_pass2($b_state);
        // we're guessing predicates are usually more short lived
        let ($p_slot, $p_npw2) = $p.compile_pass2($p_state);
    };
}

impl<T: OpU> DynOpNode for OpNode<T> {
    fn npw2(&self) -> u8 {
        T::NPW2
    }

    fn flags(&self) -> u8 {
        self.flags
    }

    fn depth(&self) -> u32 {
        // TODO ok we need a different way to handle this
        // prefer folded tree
        #[cfg(feature="opt-fold-consts")]
        if let Some(Some(folded)) = &*self.folded.borrow() {
            return folded.depth();
        }

        self.depth
    }

    fn is_imm(&self) -> bool {
        match self.kind {
            OpKind::Const(_) => true,
            OpKind::Imm(_) => true,
            _ => false,
        }
    }

    fn is_sym(&self) -> bool {
        self.flags & Self::SYM == Self::SYM
    }

    fn is_const(&self) -> bool {
        self.flags & Self::SECRET != Self::SECRET
    }

    fn is_const_zero(&self) -> bool {
        #[cfg(feature="opt-fold-consts")]
        match (self.is_const(), &self.kind, &*self.folded.borrow()) {
            (true, OpKind::Const(v), _            ) => v.is_zero(),
            (true, _,                Some(Some(x))) => x.is_const_zero(),
            _                                       => false,
        }
        #[cfg(not(feature="opt-fold-consts"))]
        match (self.is_const(), &self.kind) {
            (true, OpKind::Const(v)) => v.is_zero(),
            _                        => false,
        }
    }

    fn is_const_one(&self) -> bool {
        #[cfg(feature="opt-fold-consts")]
        match (self.is_const(), &self.kind, &*self.folded.borrow()) {
            (true, OpKind::Const(v), _            ) => v.is_one(),
            (true, _,                Some(Some(x))) => x.is_const_one(),
            _                                       => false,
        }
        #[cfg(not(feature="opt-fold-consts"))]
        match (self.is_const(), &self.kind) {
            (true, OpKind::Const(v)) => v.is_zero(),
            _                        => false,
        }
    }

    fn is_const_ones(&self) -> bool {
        #[cfg(feature="opt-fold-consts")]
        match (self.is_const(), &self.kind, &*self.folded.borrow()) {
            (true, OpKind::Const(v), _            ) => v.is_ones(),
            (true, _,                Some(Some(x))) => x.is_const_ones(),
            _                                       => false,
        }
        #[cfg(not(feature="opt-fold-consts"))]
        match (self.is_const(), &self.kind) {
            (true, OpKind::Const(v)) => v.is_zero(),
            _                        => false,
        }
    }

    fn inc_refs(&self) -> u32 {
        // prefer folded tree
        #[cfg(feature="opt-fold-consts")]
        if let Some(Some(folded)) = &*self.folded.borrow() {
            return folded.inc_refs();
        }

        let refs = self.refs.get() + 1;
        self.refs.set(refs);
        refs
    }

    fn dec_refs(&self) -> u32 {
        // prefer folded tree
        #[cfg(feature="opt-fold-consts")]
        if let Some(Some(folded)) = &*self.folded.borrow() {
            return folded.dec_refs();
        }

        let refs = self.refs.get() - 1;
        self.refs.set(refs);
        refs
    }

    fn disas_pass1(&self) {
        // prefer folded tree
        #[cfg(feature="opt-fold-consts")]
        if let Some(Some(folded)) = &*self.folded.borrow() {
            return folded.disas_pass1();
        }

        // mark node as seen
        let refs = self.inc_refs();
        if refs > 1 {
            // already visited?
            return;
        }

        match &self.kind {
            OpKind::Const(_) => {},
            OpKind::Imm(_) => {},
            OpKind::Sym(_) => {},

            OpKind::Extract(_, a) => {
                a.disas_pass1();
            }
            OpKind::Replace(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind::Select(_, p, a, b) => {
                p.disas_pass1();
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind::Shuffle(_, p, a, b) => {
                p.disas_pass1();
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::ExtendU(a) => {
                a.disas_pass1();
            }
            OpKind::ExtendS(a) => {
                a.disas_pass1();
            }
            OpKind::Splat(a) => {
                a.disas_pass1();
            }

            OpKind::None(a) => {
                a.disas_pass1();
            }
            OpKind::Any(a) => {
                a.disas_pass1();
            }
            OpKind::All(_, a) => {
                a.disas_pass1();
            }
            OpKind::Eq(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind::Ne(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind::LtU(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind::LtS(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind::GtU(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind::GtS(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind::LeU(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind::LeS(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind::GeU(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind::GeS(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind::MinU(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind::MinS(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind::MaxU(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind::MaxS(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind::Neg(_, a) => {
                a.disas_pass1();
            }
            OpKind::Abs(_, a) => {
                a.disas_pass1();
            }
            OpKind::Not(a) => {
                a.disas_pass1();
            }
            OpKind::Clz(_, a) => {
                a.disas_pass1();
            }
            OpKind::Ctz(_, a) => {
                a.disas_pass1();
            }
            OpKind::Popcnt(_, a) => {
                a.disas_pass1();
            }
            OpKind::Add(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind::Sub(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind::Mul(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind::And(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind::Andnot(a, b) => {
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
            OpKind::Shl(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind::ShrU(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind::ShrS(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind::Rotl(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind::Rotr(_, a, b) => {
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
        #[cfg(feature="opt-fold-consts")]
        if let Some(Some(folded)) = &*self.folded.borrow() {
            return folded.disas_pass2(names, arbitrary_names, stmts);
        }

        // is node shared?
        let refs = self.dec_refs();

        // already computed?
        let name = names.get(&((self as *const _) as usize));
        if let Some(name) = name {
            return Ok(name.clone());
        }

        let expr = match &self.kind {
            OpKind::Const(v) => format!("(u{}.const {:x})",
                8 << T::NPW2,
                v
            ),
            OpKind::Imm(v) => format!("(u{}.imm {:x})",
                8 << T::NPW2,
                v
            ),
            OpKind::Sym(s) => format!("(u{}.sym {:?})",
                8 << T::NPW2,
                s
            ),

            OpKind::Extract(x, a) => format!("(u{}.extract {} {})",
                prefix(a.npw2(), a.npw2()-T::NPW2),
                x,
                a.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Replace(x, a, b) => format!("(u{}.replace {} {} {})",
                prefix(T::NPW2, T::NPW2-b.npw2()),
                x,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Select(lnpw2, p, a, b) => format!("(u{}.select {} {} {})",
                prefix(T::NPW2, *lnpw2),
                p.disas_pass2(names, arbitrary_names, stmts)?,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Shuffle(lnpw2, p, a, b) => format!("(u{}.shuffle {} {} {})",
                prefix(T::NPW2, *lnpw2),
                p.disas_pass2(names, arbitrary_names, stmts)?,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?
            ),

            OpKind::ExtendU(a) => format!("(u{}.extend_u {})",
                8 << T::NPW2,
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::ExtendS(a) => format!("(u{}.extend_s {})",
                8 << T::NPW2,
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Splat(a) => format!("(u{}.splat {})",
                8 << T::NPW2,
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),

            OpKind::None(a) => format!("(u{}.none {})",
                8 << T::NPW2,
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Any(a) => format!("(u{}.any {})",
                8 << T::NPW2,
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::All(lnpw2, a) => format!("(u{}.all {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Eq(lnpw2, a, b) => format!("(u{}.eq {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Ne(lnpw2, a, b) => format!("(u{}.ne {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::LtU(lnpw2, a, b) => format!("(u{}.lt_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::LtS(lnpw2, a, b) => format!("(u{}.lt_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::GtU(lnpw2, a, b) => format!("(u{}.gt_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::GtS(lnpw2, a, b) => format!("(u{}.gt_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::LeU(lnpw2, a, b) => format!("(u{}.le_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::LeS(lnpw2, a, b) => format!("(u{}.le_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::GeU(lnpw2, a, b) => format!("(u{}.ge_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::GeS(lnpw2, a, b) => format!("(u{}.ge_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::MinU(lnpw2, a, b) => format!("(u{}.min_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::MinS(lnpw2, a, b) => format!("(u{}.min_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::MaxU(lnpw2, a, b) => format!("(u{}.max_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::MaxS(lnpw2, a, b) => format!("(u{}.max_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),

            OpKind::Neg(lnpw2, a) => format!("(u{}.neg {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Abs(lnpw2, a) => format!("(u{}.abs {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Not(a) => format!("(u{}.not {})",
                8 << T::NPW2,
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Clz(lnpw2, a) => format!("(u{}.clz {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Ctz(lnpw2, a) => format!("(u{}.ctz {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Popcnt(lnpw2, a) => format!("(u{}.popcnt {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Add(lnpw2, a, b) => format!("(u{}.add {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Sub(lnpw2, a, b) => format!("(u{}.sub {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Mul(lnpw2, a, b) => format!("(u{}.mul {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::And(a, b) => format!("(u{}.and {} {})",
                8 << T::NPW2,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Andnot(a, b) => format!("(u{}.andnot {} {})",
                8 << T::NPW2,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Or(a, b) => format!("(u{}.or {} {})",
                8 << T::NPW2,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Xor(a, b) => format!("(u{}.xor {} {})",
                8 << T::NPW2,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Shl(lnpw2, a, b) => format!("(u{}.shl {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::ShrU(lnpw2, a, b) => format!("(u{}.shr_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::ShrS(lnpw2, a, b) => format!("(u{}.shr_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Rotl(lnpw2, a, b) => format!("(u{}.rotl {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Rotr(lnpw2, a, b) => format!("(u{}.rotr {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
        };

        // used later? save as stmt?
        if refs > 0 {
            let name = arbitrary_names.next().unwrap();
            names.insert((self as *const _) as usize, name.clone());
            write!(stmts, "    {} = {}\n", name, expr)?;
            Ok(name)
        } else {
            Ok(expr)
        }
    }

    #[cfg(feature="debug-check-refs")]
    fn check_refs(&self) {
        // prefer folded tree
        #[cfg(feature="opt-fold-consts")]
        if let Some(Some(folded)) = &*self.folded.borrow() {
            return folded.check_refs();
        }

        // refs must equal 0 between multi-pass traversals
        assert_eq!(self.refs.get(), 0);

        match &self.kind {
            OpKind::Const(_) => {},
            OpKind::Imm(_) => {},
            OpKind::Sym(_) => {},

            OpKind::Extract(_, a) => {
                a.check_refs();
            }
            OpKind::Replace(_, a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::Select(_, p, a, b) => {
                p.check_refs();
                a.check_refs();
                b.check_refs();
            }
            OpKind::Shuffle(_, p, a, b) => {
                p.check_refs();
                a.check_refs();
                b.check_refs();
            }

            OpKind::ExtendU(a) => {
                a.check_refs();
            }
            OpKind::ExtendS(a) => {
                a.check_refs();
            }
            OpKind::Splat(a) => {
                a.check_refs();
            }

            OpKind::None(a) => {
                a.check_refs();
            }
            OpKind::Any(a) => {
                a.check_refs();
            }
            OpKind::All(_, a) => {
                a.check_refs();
            }
            OpKind::Eq(_, a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::Ne(_, a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::LtU(_, a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::LtS(_, a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::GtU(_, a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::GtS(_, a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::LeU(_, a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::LeS(_, a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::GeU(_, a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::GeS(_, a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::MinU(_, a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::MinS(_, a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::MaxU(_, a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::MaxS(_, a, b) => {
                a.check_refs();
                b.check_refs();
            }

            OpKind::Neg(_, a) => {
                a.check_refs();
            }
            OpKind::Abs(_, a) => {
                a.check_refs();
            }
            OpKind::Not(a) => {
                a.check_refs();
            }
            OpKind::Clz(_, a) => {
                a.check_refs();
            }
            OpKind::Ctz(_, a) => {
                a.check_refs();
            }
            OpKind::Popcnt(_, a) => {
                a.check_refs();
            }
            OpKind::Add(_, a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::Sub(_, a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::Mul(_, a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::And(a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::Andnot(a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::Or(a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::Xor(a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::Shl(_, a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::ShrU(_, a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::ShrS(_, a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::Rotl(_, a, b) => {
                a.check_refs();
                b.check_refs();
            }
            OpKind::Rotr(_, a, b) => {
                a.check_refs();
                b.check_refs();
            }
        }
    }


    #[cfg(feature="opt-fold-consts")]
    fn fold_consts(&self) {
        // already folded?
        if self.folded.borrow().is_some() {
            return;
        }
        self.folded.replace(Some(None));
        
        if self.is_const() && !self.is_imm() {
            // oh hey, we're const
            //
            // note this recursively triggers another compilation
            // + execution, so be careful
            //
            // if this fails we just bail on the const folding so the error
            // can be reported at runtime
            if let Ok(v) = self.try_eval() {
                self.folded.replace(Some(Some(Rc::new(Self::new(
                    OpKind::Const(v), 0, 0
                )))));
                return;
            }
        }

        match &self.kind {
            OpKind::Const(_) => {},
            OpKind::Imm(_) => {},
            OpKind::Sym(_) => {},

            OpKind::Extract(_, a) => {
                a.fold_consts();
            }
            OpKind::Replace(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind::Select(_, p, a, b) => {
                p.fold_consts();
                a.fold_consts();
                b.fold_consts();
            }
            OpKind::Shuffle(_, p, a, b) => {
                p.fold_consts();
                a.fold_consts();
                b.fold_consts();
            }

            OpKind::ExtendU(a) => {
                a.fold_consts();
            }
            OpKind::ExtendS(a) => {
                a.fold_consts();
            }
            OpKind::Splat(a) => {
                a.fold_consts();
            }

            OpKind::None(a) => {
                a.fold_consts();
            }
            OpKind::Any(a) => {
                a.fold_consts();
            }
            OpKind::All(_, a) => {
                a.fold_consts();
            }
            OpKind::Eq(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind::Ne(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind::LtU(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind::LtS(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind::GtU(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind::GtS(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind::LeU(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind::LeS(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind::GeU(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind::GeS(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind::MinU(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind::MinS(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind::MaxU(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind::MaxS(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }

            OpKind::Neg(_, a) => {
                a.fold_consts();
            }
            OpKind::Abs(_, a) => {
                a.fold_consts();
            }
            OpKind::Not(a) => {
                a.fold_consts();
            }
            OpKind::Clz(_, a) => {
                a.fold_consts();
            }
            OpKind::Ctz(_, a) => {
                a.fold_consts();
            }
            OpKind::Popcnt(_, a) => {
                a.fold_consts();
            }
            OpKind::Add(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
                #[cfg(feature="opt-fold-nops")]
                if a.is_const_zero() {
                    self.folded.replace(Some(Some(b.clone())));
                } else if b.is_const_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
            OpKind::Sub(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
                #[cfg(feature="opt-fold-nops")]
                if b.is_const_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
            OpKind::Mul(x, a, b) => {
                a.fold_consts();
                b.fold_consts();
                #[cfg(feature="opt-fold-nops")]
                if *x == 0 && a.is_const_one() {
                    self.folded.replace(Some(Some(b.clone())));
                } else if *x == 0 && b.is_const_one() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
            OpKind::And(a, b) => {
                a.fold_consts();
                b.fold_consts();
                #[cfg(feature="opt-fold-nops")]
                if a.is_const_ones() {
                    self.folded.replace(Some(Some(b.clone())));
                } else if b.is_const_ones() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
            OpKind::Andnot(a, b) => {
                a.fold_consts();
                b.fold_consts();
                #[cfg(feature="opt-fold-nops")]
                if a.is_const_ones() {
                    self.folded.replace(Some(Some(b.clone())));
                } else if b.is_const_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
            OpKind::Or(a, b) => {
                a.fold_consts();
                b.fold_consts();
                #[cfg(feature="opt-fold-nops")]
                if a.is_const_zero() {
                    self.folded.replace(Some(Some(b.clone())));
                } else if b.is_const_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
            OpKind::Xor(a, b) => {
                a.fold_consts();
                b.fold_consts();
                #[cfg(feature="opt-fold-nops")]
                if a.is_const_zero() {
                    self.folded.replace(Some(Some(b.clone())));
                } else if b.is_const_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
            OpKind::Shl(x, a, b) => {
                a.fold_consts();
                b.fold_consts();
                #[cfg(feature="opt-fold-nops")]
                if *x == 0 && b.is_const_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
            OpKind::ShrU(x, a, b) => {
                a.fold_consts();
                b.fold_consts();
                #[cfg(feature="opt-fold-nops")]
                if *x == 0 && b.is_const_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
            OpKind::ShrS(x, a, b) => {
                a.fold_consts();
                b.fold_consts();
                #[cfg(feature="opt-fold-nops")]
                if *x == 0 && b.is_const_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
            OpKind::Rotl(x, a, b) => {
                a.fold_consts();
                b.fold_consts();
                #[cfg(feature="opt-fold-nops")]
                if *x == 0 && b.is_const_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
            OpKind::Rotr(x, a, b) => {
                a.fold_consts();
                b.fold_consts();
                #[cfg(feature="opt-fold-nops")]
                if *x == 0 && b.is_const_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
        }
    }

    fn compile_pass1(&self, state: &mut OpCompile) {
        // prefer folded tree
        #[cfg(feature="opt-fold-consts")]
        if let Some(Some(folded)) = &*self.folded.borrow() {
            return folded.compile_pass1(state);
        }

        // mark node as seen
        let refs = self.inc_refs();
        if refs > 1 {
            // already visited?
            return;
        }

        // make sure slots left over from previous calculation are reset
        self.slot.set(None);

        match &self.kind {
            OpKind::Const(_) => {
                // handle consts later
            }
            OpKind::Imm(v) => {
                // allocate slot
                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                self.slot.set(Some(slot));

                // write imm to slots
                if state.slots.len() < (usize::from(slot)+1) << T::NPW2 {
                    state.slots.resize((usize::from(slot)+1) << T::NPW2, 0);
                }

                state.slots[
                    usize::from(slot) << T::NPW2
                        .. (usize::from(slot)+1) << T::NPW2
                ].copy_from_slice(v.to_le_bytes().as_ref());

                // initialize arg in bytecode
                state.bytecode.push(u32::from(OpIns::new(
                    T::NPW2, 0, OpCode::Arg, 0, slot, slot
                )));
            }
            OpKind::Sym(_) => {
                assert!(!self.is_const());

                // allocate slot
                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                self.slot.set(Some(slot));

                if state.slots.len() < (usize::from(slot)+1) << T::NPW2 {
                    state.slots.resize((usize::from(slot)+1) << T::NPW2, 0);
                }

                // we'll fill this in later, use an arbitrary constant
                // to hopefully help debugging
                state.slots[
                    usize::from(slot) << T::NPW2
                        .. (usize::from(slot)+1) << T::NPW2
                ].fill(0xcc);

                // initialize arg in bytecode
                state.bytecode.push(u32::from(OpIns::new(
                    T::NPW2, 0, OpCode::Arg, 0, slot, slot
                )));
            }

            OpKind::Extract(_, a) => {
                a.compile_pass1(state);
            }
            OpKind::Replace(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind::Select(_, p, a, b) => {
                p.compile_pass1(state);
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind::Shuffle(_, p, a, b) => {
                p.compile_pass1(state);
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::ExtendU(a) => {
                a.compile_pass1(state);
            }
            OpKind::ExtendS(a) => {
                a.compile_pass1(state);
            }
            OpKind::Splat(a) => {
                a.compile_pass1(state);
            }

            OpKind::None(a) => {
                a.compile_pass1(state);
            }
            OpKind::Any(a) => {
                a.compile_pass1(state);
            }
            OpKind::All(_, a) => {
                a.compile_pass1(state);
            }
            OpKind::Eq(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind::Ne(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind::LtU(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind::LtS(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind::GtU(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind::GtS(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind::LeU(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind::LeS(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind::GeU(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind::GeS(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind::MinU(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind::MinS(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind::MaxU(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind::MaxS(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind::Neg(_, a) => {
                a.compile_pass1(state);
            }
            OpKind::Abs(_, a) => {
                a.compile_pass1(state);
            }
            OpKind::Not(a) => {
                a.compile_pass1(state);
            }
            OpKind::Clz(_, a) => {
                a.compile_pass1(state);
            }
            OpKind::Ctz(_, a) => {
                a.compile_pass1(state);
            }
            OpKind::Popcnt(_, a) => {
                a.compile_pass1(state);
            }
            OpKind::Add(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind::Sub(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind::Mul(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind::And(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind::Andnot(a, b) => {
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
            OpKind::Shl(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind::ShrU(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind::ShrS(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind::Rotl(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind::Rotr(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
        }
    }

    fn compile_pass2(&self, state: &mut OpCompile) -> (u8, u8) {
        // prefer folded tree
        #[cfg(feature="opt-fold-consts")]
        if let Some(Some(folded)) = &*self.folded.borrow() {
            return folded.compile_pass2(state);
        }

        // already computed?
        if let Some(slot) = self.slot.get() {
            return (slot, T::NPW2);
        }

        match &self.kind {
            OpKind::Const(v) => {
                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                #[allow(unused_mut)] let mut best_npw2 = T::NPW2;
                #[allow(unused_mut)] let mut best_ins8 = OpCode::ExtendConst8U;
                #[allow(unused_mut)] let mut best_ins = OpCode::ExtendConstU;

                // can we use a smaller encoding?
                #[cfg(feature="opt-compress-consts")]
                {
                    if state.opt {
                        for npw2 in 0..T::NPW2 {
                            if v.is_extend_u_compressable(npw2) {
                                best_npw2 = npw2;
                                best_ins8 = OpCode::ExtendConst8U;
                                best_ins  = OpCode::ExtendConstU;
                                break;
                            } else if v.is_extend_s_compressable(npw2) {
                                best_npw2 = npw2;
                                best_ins8 = OpCode::ExtendConst8S;
                                best_ins  = OpCode::ExtendConstS;
                                break;
                            } else if v.is_splat_compressable(npw2) {
                                best_npw2 = npw2;
                                best_ins8 = OpCode::SplatConst8;
                                best_ins  = OpCode::SplatConst;
                                break;
                            }
                        }
                    }
                }

                // fall back to uncompressed encodings
                if best_npw2 == 0 {
                    // u8s can fit directly in instruction

                    let mut buf = Vec::from(v.to_le_bytes().as_ref());
                    buf.truncate(1);

                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, T::NPW2, best_ins8, 0, slot, buf[0]
                    )));
                } else {
                    // encode const into bytecode stream
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, T::NPW2 - best_npw2, best_ins, 0, slot, 0
                    )));

                    let mut buf = Vec::from(v.to_le_bytes().as_ref());
                    buf.truncate(1 << best_npw2);
                    buf.resize(max(4, buf.len()), 0);
                    for i in (0..buf.len()).step_by(4) {
                        state.bytecode.push(u32::from_le_bytes(
                            <[u8;4]>::try_from(&buf[i..i+4]).unwrap()
                        ));
                    }
                }

                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Imm(_) => {
                // should be entirely handled in first pass
                unreachable!()
            }
            OpKind::Sym(_) => {
                // should be entirely handled in first pass
                unreachable!()
            }

            OpKind::Select(lnpw2, p, a, b) => {
                schedule! {
                    let (p_slot, p_npw2) = p.compile_pass2(state);
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let p_refs = p.dec_refs();
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Select, p_slot, a_slot, b_slot
                    )));
                    if p_refs == 0 { state.slot_pool.dealloc(p_slot, p_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Select, p_slot, slot, b_slot
                    )));
                    if p_refs == 0 { state.slot_pool.dealloc(p_slot, p_npw2); }
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::Shuffle(lnpw2, p, a, b) => {
                schedule! {
                    let (p_slot, p_npw2) = p.compile_pass2(state);
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let p_refs = p.dec_refs();
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Shuffle, p_slot, a_slot, b_slot
                    )));
                    if p_refs == 0 { state.slot_pool.dealloc(p_slot, p_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Shuffle, p_slot, slot, b_slot
                    )));
                    if p_refs == 0 { state.slot_pool.dealloc(p_slot, p_npw2); }
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::Extract(lane, a) => {
                assert!(T::NPW2 <= a.npw2());
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns::new(
                    a_npw2, a_npw2-T::NPW2, OpCode::Extract, *lane, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Replace(lane, a, b) => {
                assert!(T::NPW2 >= b.npw2());
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, T::NPW2-b_npw2, OpCode::Replace, *lane, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, T::NPW2-b_npw2, OpCode::Replace, *lane, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }

            OpKind::ExtendU(a) => {
                assert!(T::NPW2 >= a.npw2());
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns::new(
                    T::NPW2, T::NPW2-a_npw2, OpCode::ExtendU, 0, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::ExtendS(a) => {
                assert!(T::NPW2 >= a.npw2());
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns::new(
                    T::NPW2, T::NPW2-a_npw2, OpCode::ExtendS, 0, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Splat(a) => {
                assert!(T::NPW2 >= a.npw2());
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns::new(
                    T::NPW2, T::NPW2-a_npw2, OpCode::Splat, 0, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }

            OpKind::None(a) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns::new(
                    T::NPW2, 0, OpCode::None, 0, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Any(a) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns::new(
                    T::NPW2, 0, OpCode::Any, 0, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::All(lnpw2, a) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::All, 0, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Eq(lnpw2, a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Eq, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Eq, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Eq, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::Ne(lnpw2, a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Ne, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Ne, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Ne, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::LtU(lnpw2, a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::LtU, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::GtU, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::LtU, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::LtS(lnpw2, a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::LtS, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::GtS, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::LtS, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::GtU(lnpw2, a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::GtU, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::LtU, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::GtU, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::GtS(lnpw2, a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::GtS, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::LtS, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::GtS, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::LeU(lnpw2, a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::LeU, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::GeU, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::LeU, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::LeS(lnpw2, a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::LeS, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::GeS, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::LeS, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::GeU(lnpw2, a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::GeU, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::LeU, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::GeU, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::GeS(lnpw2, a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::GeS, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::LeS, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::GeS, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::MinU(lnpw2, a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::MinU, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::MinU, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::MinU, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::MinS(lnpw2, a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::MinS, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::MinS, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::MinS, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::MaxU(lnpw2, a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::MaxU, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::MaxU, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::MaxU, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::MaxS(lnpw2, a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::MaxS, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::MaxS, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::MaxS, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::Neg(lnpw2, a) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Neg, 0, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Abs(lnpw2, a) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Abs, 0, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Not(a) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns::new(
                    T::NPW2, 0, OpCode::Not, 0, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Clz(lnpw2, a) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Clz, 0, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Ctz(lnpw2, a) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Ctz, 0, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Popcnt(lnpw2, a) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Popcnt, 0, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Add(lnpw2, a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Add, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Add, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Add, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::Sub(lnpw2, a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Sub, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Sub, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::Mul(lnpw2, a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Mul, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Mul, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Mul, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::And(a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::And, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::And, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::And, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::Andnot(a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::Andnot, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::Andnot, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::Andnot, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::Or(a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::Or, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::Or, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::Or, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::Xor(a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::Xor, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::Xor, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::Xor, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::Shl(lnpw2, a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Shl, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Shl, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::ShrU(lnpw2, a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::ShrU, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::ShrU, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::ShrS(lnpw2, a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::ShrS, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::ShrS, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::Rotl(lnpw2, a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Rotl, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Rotl, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::Rotr(lnpw2, a, b) => {
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Rotr, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, 0, OpCode::ExtendU, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Rotr, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compile_add() {
        let example = OpTree::add(0,
            OpTree::<U32>::imm(1u32),
            OpTree::<U32>::imm(2u32)
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 4);
        assert_eq!(stack.len(), 12);
    }

    #[test]
    fn compile_add_parallel() {
        let example = OpTree::add(2,
            OpTree::<U32>::imm(0x01020304u32),
            OpTree::<U32>::imm(0x0506fffeu32)
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 4);
        assert_eq!(stack.len(), 12);
    }

    #[test]
    fn compile_alignment() {
        let example = OpTree::add(0,
            OpTree::<U16>::extend_s(
                OpTree::<U8>::imm(2u8)
            ),
            OpTree::<U16>::extract(0,
                OpTree::<U32>::imm(1u32),
            ),
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 6);
        assert_eq!(stack.len(), 8);
    }

    #[test]
    fn compile_dag() {
        let two = OpTree::<U32>::imm(2u32);
        let a = OpTree::add(0,
            OpTree::<U32>::imm(1u32),
            OpTree::<U32>::imm(2u32)
        );
        let b = OpTree::shr_s(0,
            a.clone(), two.clone()
        );
        let c = OpTree::shl(0,
            a.clone(), two.clone()
        );
        let example = OpTree::eq(0,
            OpTree::add(0,
                OpTree::mul(0, b, two),
                c,
            ),
            a,
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 12);
        assert_eq!(stack.len(), 5*4);
    }

    #[test]
    fn compile_pythag() {
        let a = OpTree::<U32>::imm(3u32);
        let b = OpTree::<U32>::imm(4u32);
        let c = OpTree::<U32>::imm(5u32);
        let example = OpTree::eq(0,
            OpTree::add(0,
                OpTree::mul(0, a.clone(), a),
                OpTree::mul(0, b.clone(), b)
            ),
            OpTree::mul(0, c.clone(), c)
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 9);
        assert_eq!(stack.len(), 16);
    }

    #[test]
    fn compile_too_many_casts() {
        // this intentionally has an obnoxious amount of casting
        let a = OpTree::<U8>::imm(1u8);
        let b = OpTree::<U16>::imm(1u16);
        let c = OpTree::<U32>::imm(2u32);
        let d = OpTree::<U64>::imm(3u64);
        let e = OpTree::<U128>::imm(5u128);
        let fib_3 = OpTree::add(0,
            OpTree::<U32>::extend_u(b.clone()), OpTree::<U32>::extend_u(a.clone())
        );
        let fib_4 = OpTree::add(0,
            OpTree::<U64>::extend_u(fib_3.clone()), OpTree::<U64>::extend_u(b.clone())
        );
        let fib_5 = OpTree::add(0,
            OpTree::<U128>::extend_u(fib_4.clone()), OpTree::<U128>::extend_u(fib_3.clone())
        );
        let example = OpTree::and(
            OpTree::and(
                OpTree::<U8>::extract(0, OpTree::eq(0, fib_3.clone(), c)),
                OpTree::<U8>::extract(0, OpTree::eq(0, fib_4.clone(), d))
            ),
            OpTree::<U8>::extract(0, OpTree::eq(0, fib_5.clone(), e))
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 23);
        assert_eq!(stack.len(), 80);
    }

    #[test]
    fn constant_folding() {
        let a = OpTree::<U32>::const_(3u32);
        let b = OpTree::<U32>::const_(4u32);
        let c = OpTree::<U32>::const_(5u32);
        let example = OpTree::eq(0,
            OpTree::add(0,
                OpTree::mul(0, a.clone(), a),
                OpTree::mul(0, b.clone(), b)
            ),
            OpTree::mul(0, c.clone(), c)
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 2);
        assert_eq!(stack.len(), 8);
    }

    #[test]
    fn constant_more_folding() {
        // this intentionally has an obnoxious amount of casting
        let a = OpTree::<U8>::const_(1u8);
        let b = OpTree::<U16>::const_(1u16);
        let c = OpTree::<U32>::const_(2u32);
        let d = OpTree::<U64>::const_(3u64);
        let e = OpTree::<U128>::const_(5u128);
        let fib_3 = OpTree::add(0,
            OpTree::<U32>::extend_u(b.clone()), OpTree::<U32>::extend_u(a.clone())
        );
        let fib_4 = OpTree::add(0,
            OpTree::<U64>::extend_u(fib_3.clone()), OpTree::<U64>::extend_u(b.clone())
        );
        let fib_5 = OpTree::add(0,
            OpTree::<U128>::extend_u(fib_4.clone()), OpTree::<U128>::extend_u(fib_3.clone())
        );
        let example = OpTree::and(
            OpTree::and(
                OpTree::<U8>::extract(0, OpTree::eq(0, fib_3.clone(), c)),
                OpTree::<U8>::extract(0, OpTree::eq(0, fib_4.clone(), d))
            ),
            OpTree::<U8>::extract(0, OpTree::eq(0, fib_5.clone(), e))
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 2);
        assert_eq!(stack.len(), 1);
    }

    #[test]
    fn compile_slot_defragment() {
        let a = OpTree::<U8>::imm(1u8);
        let b = OpTree::<U8>::imm(2u8);
        let c = OpTree::<U8>::imm(3u8);
        let d = OpTree::<U8>::imm(4u8);
        let e = OpTree::<U8>::imm(5u8);
        let f = OpTree::<U8>::imm(6u8);
        let g = OpTree::<U8>::imm(7u8);
        let h = OpTree::<U8>::imm(8u8);
        let big = OpTree::<U32>::extend_u(a);
        let i = OpTree::add(0,
            big.clone(),
            OpTree::add(0,
                big.clone(),
                OpTree::add(0,
                    OpTree::<U32>::extend_u(b),
                    OpTree::add(0,
                        OpTree::<U32>::extend_u(c),
                        OpTree::add(0,
                            OpTree::<U32>::extend_u(d),
                            OpTree::add(0,
                                OpTree::<U32>::extend_u(e),
                                OpTree::add(0,
                                    OpTree::<U32>::extend_u(f),
                                    OpTree::add(0,
                                        OpTree::<U32>::extend_u(g),
                                        OpTree::<U32>::extend_u(h)
                                    )
                                )
                            )
                        )
                    )
                )
            )
        );
        let example = OpTree::add(0, i.clone(), OpTree::add(0, i, big));

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 27);
        #[cfg(feature="opt-schedule-slots")]
        assert_eq!(stack.len(), 16);
        #[cfg(not(feature="opt-schedule-slots"))]
        assert_eq!(stack.len(), 36);
    }

    #[test]
    fn compile_compressed_consts() {
        let a = OpTree::<U128>::imm([1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]);
        let b = OpTree::<U128>::const_([1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]);
        let a = OpTree::<U128>::add(0, a, b);
        let b = OpTree::<U128>::const_([0xfe,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff]);
        let a = OpTree::<U128>::add(0, a, b);
        let b = OpTree::<U128>::const_([0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab]);
        let a = OpTree::<U128>::add(0, a, b);
        let b = OpTree::<U128>::const_([2,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0]);
        let a = OpTree::<U128>::add(0, a, b);
        let b = OpTree::<U128>::const_([0xfd,0xfe,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff]);
        let a = OpTree::<U128>::add(0, a, b);
        let b = OpTree::<U128>::const_([0xab,0xcd,0xab,0xcd,0xab,0xcd,0xab,0xcd,0xab,0xcd,0xab,0xcd,0xab,0xcd,0xab,0xcd]);
        let example = OpTree::add(0, a, b);

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 17);
        assert_eq!(stack.len(), 48);
    }
}

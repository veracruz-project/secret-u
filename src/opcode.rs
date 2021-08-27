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
use std::ops::Deref;
use std::ops::DerefMut;
use std::borrow::Cow;

use aligned_utils::bytes::AlignedBytes;

use secret_u_macros::for_secret_t;


/// OpCodes emitted as a part of bytecode
///
/// Based originally on the numeric instructions of Wasm, with the
/// noticable omission of the division instructions (uncommon for
/// both SIMD instruction sets and constant-time instruction sets)
/// but extended to larger integer sizes (u8-u262144), and with multiple
/// SIMD lanes (u8x2, u16x4, etc). (Ok things got a bit out of hand).
///
/// Instead of operating on locals/globals with a stack, instructions
/// operate directly on up to 65536 registers (sometimes called "slots" in
/// this code), which share a common blob of memory but must not overlap or be
/// reinterpreted.
///
/// Instructions follow a 3-register format:
///
/// [4|4|- 8 -|--  16  --|--  16  --|--  16  --]
///  ^ ^   ^        ^          ^          ^-- 16-bit ra
///  | |   |        |          '------------- 16-bit rb
///  | |   |        '------------------------ 16-bit rd
///  | |   '--------------------------------- 8-bit opcode
///  | '------------------------------------- 4-bit npw2(lanes)
///  '--------------------------------------- 4-bit npw2(size)
///
/// Despite the massive 64-bit instruction size, the instruction encoding is
/// still rather tight thanks to needing to encode the integer geometry and
/// large register file.
///
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[repr(u8)]
pub enum OpCode {
    Arg             = 0x01,
    Ret             = 0x02,

    ExtendU         = 0x03,
    ExtendS         = 0x04,
    Truncate        = 0x05,
    Splat           = 0x06,
    SplatConst      = 0x07,
    SplatLongConst  = 0x08,

    Extract         = 0x0a,
    Replace         = 0x0b,
    Select          = 0x0c,
    Shuffle         = 0x0d,

    None            = 0x0f,
    All             = 0x10,
    Eq              = 0x11,
    Ne              = 0x12,
    LtU             = 0x13,
    LtS             = 0x14,
    GtU             = 0x15,
    GtS             = 0x16,
    LeU             = 0x17,
    LeS             = 0x18,
    GeU             = 0x19,
    GeS             = 0x1a,
    MinU            = 0x1b,
    MinS            = 0x1c,
    MaxU            = 0x1d,
    MaxS            = 0x1e,

    Neg             = 0x1f,
    Abs             = 0x20,
    Not             = 0x21,
    Clz             = 0x22,
    Ctz             = 0x23,
    Popcnt          = 0x24,
    Add             = 0x25,
    Sub             = 0x26,
    Mul             = 0x27,
    And             = 0x28,
    Andnot          = 0x29,
    Or              = 0x2a,
    Xor             = 0x2b,
    Shl             = 0x2c,
    ShrU            = 0x2d,
    ShrS            = 0x2e,
    Rotl            = 0x2f,
    Rotr            = 0x30,
}

impl fmt::Display for OpCode {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let name = match self {
            OpCode::Arg             => "arg",
            OpCode::Ret             => "ret",

            OpCode::ExtendU         => "extend_u",
            OpCode::ExtendS         => "extend_s",
            OpCode::Truncate        => "truncate",
            OpCode::Splat           => "splat",
            OpCode::SplatConst      => "splat",
            OpCode::SplatLongConst  => "splat",

            OpCode::Extract         => "extract",
            OpCode::Replace         => "replace",
            OpCode::Select          => "select",
            OpCode::Shuffle         => "shuffle",

            OpCode::None            => "none",
            OpCode::All             => "all",
            OpCode::Eq              => "eq",
            OpCode::Ne              => "ne",
            OpCode::LtU             => "lt_u",
            OpCode::LtS             => "lt_s",
            OpCode::GtU             => "gt_u",
            OpCode::GtS             => "gt_s",
            OpCode::LeU             => "le_u",
            OpCode::LeS             => "le_s",
            OpCode::GeU             => "ge_u",
            OpCode::GeS             => "ge_s",
            OpCode::MinU            => "min_u",
            OpCode::MinS            => "min_s",
            OpCode::MaxU            => "max_u",
            OpCode::MaxS            => "max_s",

            OpCode::Neg             => "neg",
            OpCode::Abs             => "abs",
            OpCode::Not             => "not",
            OpCode::Clz             => "clz",
            OpCode::Ctz             => "ctz",
            OpCode::Popcnt          => "popcnt",
            OpCode::Add             => "add",
            OpCode::Sub             => "sub",
            OpCode::Mul             => "mul",
            OpCode::And             => "and",
            OpCode::Andnot          => "andnot",
            OpCode::Or              => "or",
            OpCode::Xor             => "xor",
            OpCode::Shl             => "shl",
            OpCode::ShrU            => "shr_u",
            OpCode::ShrS            => "shr_s",
            OpCode::Rotl            => "rotl",
            OpCode::Rotr            => "rotr",
        };
        write!(fmt, "{}", name)
    }
}


/// An encoded instruction
#[derive(Debug, Copy, Clone)]
pub struct OpIns(u64);

impl OpIns {
    /// Create a new instruction from its components
    #[inline]
    pub const fn new(
        npw2: u8,
        lnpw2: u8,
        opcode: OpCode,
        d: u16,
        a: u16,
        b: u16
    ) -> OpIns {
        OpIns(
            ((npw2 as u64) << 60)
                | ((lnpw2 as u64) << 56)
                | ((opcode as u64) << 48)
                | ((d as u64) << 32)
                | ((a as u64) << 16)
                | ((b as u64) << 0)
        )
    }

    pub const fn with_ab(
        npw2: u8,
        lnpw2: u8,
        opcode: OpCode,
        d: u16,
        ab: u32
    ) -> OpIns {
        OpIns::new(npw2, lnpw2, opcode, d, (ab >> 16) as u16, ab as u16)
    }

    #[inline]
    pub fn opcode(&self) -> OpCode {
        let opcode = ((self.0 & 0x00ff000000000000) >> 48) as u8;

        // we check for OpCode validity on every function that can build
        // an Op, so this should only result in valid OpCodes
        unsafe { transmute(opcode) }
    }

    #[inline]
    pub fn npw2(&self) -> u8 {
        ((self.0 & 0xf000000000000000) >> 60) as u8
    }

    #[inline]
    pub fn lnpw2(&self) -> u8 {
        ((self.0 & 0x0f00000000000000) >> 56) as u8
    }

    #[inline]
    pub fn lane_npw2(&self) -> u8 {
        self.npw2() - self.lnpw2()
    }

    #[inline]
    pub fn d(&self) -> u16 {
        ((self.0 & 0x0000ffff00000000) >> 32) as u16
    }

    #[inline]
    pub fn a(&self) -> u16 {
        ((self.0 & 0x00000000ffff0000) >> 16) as u16
    }

    #[inline]
    pub fn b(&self) -> u16 {
        ((self.0 & 0x000000000000ffff) >>  0) as u16
    }

    #[inline]
    pub fn ab(&self) -> u32 {
        ((self.0 & 0x00000000ffffffff) >>  0) as u32
    }

    #[inline]
    pub fn b_npw2(&self) -> u8 {
        self.b() as u8
    }

    #[inline]
    pub fn b_lane_npw2(&self) -> u8 {
        self.b_npw2() - self.lnpw2()
    }
}

impl From<OpIns> for u64 {
    fn from(ins: OpIns) -> u64 {
        ins.0
    }
}

impl TryFrom<u64> for OpIns {
    type Error = Error;

    fn try_from(ins: u64) -> Result<Self, Self::Error> {
        // ensure opcode is valid
        match ((ins & 0x00ff000000000000) >> 48) as u8 {
            0x01 => OpCode::Arg,
            0x02 => OpCode::Ret,

            0x03 => OpCode::ExtendU,
            0x04 => OpCode::ExtendS,
            0x05 => OpCode::Truncate,
            0x06 => OpCode::Splat,
            0x07 => OpCode::SplatConst,
            0x08 => OpCode::SplatLongConst,

            0x0a => OpCode::Extract,
            0x0b => OpCode::Replace,
            0x0c => OpCode::Select,
            0x0d => OpCode::Shuffle,

            0x0f => OpCode::None,
            0x10 => OpCode::All,
            0x11 => OpCode::Eq,
            0x12 => OpCode::Ne,
            0x13 => OpCode::LtU,
            0x14 => OpCode::LtS,
            0x15 => OpCode::GtU,
            0x16 => OpCode::GtS,
            0x17 => OpCode::LeU,
            0x18 => OpCode::LeS,
            0x19 => OpCode::GeU,
            0x1a => OpCode::GeS,
            0x1b => OpCode::MinU,
            0x1c => OpCode::MinS,
            0x1d => OpCode::MaxU,
            0x1e => OpCode::MaxS,

            0x1f => OpCode::Neg,
            0x21 => OpCode::Abs,
            0x20 => OpCode::Not,
            0x22 => OpCode::Clz,
            0x23 => OpCode::Ctz,
            0x24 => OpCode::Popcnt,
            0x25 => OpCode::Add,
            0x26 => OpCode::Sub,
            0x27 => OpCode::Mul,
            0x28 => OpCode::And,
            0x29 => OpCode::Andnot,
            0x2a => OpCode::Or,
            0x2b => OpCode::Xor,
            0x2c => OpCode::Shl,
            0x2d => OpCode::ShrU,
            0x2e => OpCode::ShrS,
            0x2f => OpCode::Rotl,
            0x30 => OpCode::Rotr,

            _ => Err(Error::InvalidOpcode(ins))?,
        };

        Ok(Self(ins))
    }
}

impl fmt::Display for OpIns {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self.opcode() {
            // extract/replace
            OpCode::Extract => {
                write!(fmt, "{}.{} r{}, r{}[{}]",
                    prefix(self.npw2(), self.lnpw2()),
                    self.opcode(),
                    self.d(),
                    self.a(),
                    self.b()
                )
            }

            OpCode::Replace => {
                write!(fmt, "{}.{} r{}[{}], r{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.opcode(),
                    self.d(),
                    self.b(),
                    self.a()
                )
            }

            // conversion ops
            OpCode::ExtendU | OpCode::ExtendS => {
                write!(fmt, "{}.{} r{}, r{}, {}",
                    prefix(self.npw2(), self.b_npw2()),
                    self.opcode(),
                    self.d(),
                    self.a(),
                    prefix(self.lane_npw2(), self.b_npw2())
                )
            }

            OpCode::Truncate => {
                write!(fmt, "{}.{} r{}, r{}, {}",
                    prefix(self.lane_npw2(), self.b_npw2()),
                    self.opcode(),
                    self.d(),
                    self.a(),
                    prefix(self.npw2(), self.b_npw2())
                )
            }

            // splats and moves (synonym)
            OpCode::Splat if self.lnpw2() == 0 => {
                write!(fmt, "{}.move r{}, r{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.d(),
                    self.a()
                )
            }

            OpCode::Splat => {
                write!(fmt, "{}.{} r{}, r{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.opcode(),
                    self.d(),
                    self.a(),
                )
            }

            OpCode::SplatConst if self.lnpw2() == 0 => {
                write!(fmt, "{}.move r{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.d()
                )
            }

            OpCode::SplatConst => {
                write!(fmt, "{}.{} r{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.opcode(),
                    self.d()
                )
            }

            OpCode::SplatLongConst if self.lnpw2() == 0 => {
                write!(fmt, "{}.move r{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.d()
                )
            }

            OpCode::SplatLongConst => {
                write!(fmt, "{}.{} r{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.opcode(),
                    self.d()
                )
            }

            // unops
            OpCode::Arg
                | OpCode::Ret
                | OpCode::None
                | OpCode::All
                | OpCode::Neg
                | OpCode::Abs
                | OpCode::Not
                | OpCode::Clz
                | OpCode::Ctz
                | OpCode::Popcnt
                => {
                write!(fmt, "{}.{} r{}, r{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.opcode(),
                    self.d(),
                    self.a()
                )
            }

            // binops/triops
            OpCode::Select
                | OpCode::Shuffle
                | OpCode::Eq
                | OpCode::Ne
                | OpCode::LtU
                | OpCode::LtS
                | OpCode::GtU
                | OpCode::GtS
                | OpCode::LeU
                | OpCode::LeS
                | OpCode::GeU
                | OpCode::GeS
                | OpCode::MinU
                | OpCode::MinS
                | OpCode::MaxU
                | OpCode::MaxS
                | OpCode::Add
                | OpCode::Sub
                | OpCode::Mul
                | OpCode::And
                | OpCode::Andnot
                | OpCode::Or
                | OpCode::Xor
                | OpCode::Shl
                | OpCode::ShrU
                | OpCode::ShrS
                | OpCode::Rotl
                | OpCode::Rotr
                => {
                write!(fmt, "{}.{} r{}, r{}, r{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.opcode(),
                    self.d(),
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
        format!("u{}", 8usize << npw2)
    } else {
        format!("u{}x{}", (8usize << npw2) >> lnpw2, 1usize << lnpw2)
    }
}

/// helper function for debugging
pub fn disas<W: io::Write>(
    bytecode: &[u64],
    mut out: W
) -> Result<(), io::Error> {
    let mut i = 0;
    while i < bytecode.len() {
        let ins = bytecode[i];
        i += 1;

        match OpIns::try_from(ins) {
            Ok(ins) => {
                match ins.opcode() {
                    OpCode::SplatConst => {
                        write!(out, "    {:016x} {}, 0x", u64::from(ins), ins)?;
                        writeln!(out, "{:0w$x}",
                            ins.ab()
                                & 1u32.checked_shl(8*(1 << ins.lane_npw2()))
                                    .map(|mask| mask-1)
                                    .unwrap_or(u32::MAX),
                            w=2*min(4, 1 << ins.lane_npw2())
                        )?;
                    }
                    OpCode::SplatLongConst => {
                        write!(out, "    {:016x} {}, 0x", u64::from(ins), ins)?;
                        // fetch from instruction stream
                        for j in (0 .. (1 << ins.b_npw2())/8).rev() {
                            write!(out, "{:016x}", bytecode[i+j])?;
                        }
                        writeln!(out)?;
                        for _ in 0 .. (1 << ins.b_npw2())/8 {
                            writeln!(out, "    {:016x}", bytecode[i])?;
                            i += 1;
                        }
                    }
                    _ => {
                        writeln!(out, "    {:016x} {}", u64::from(ins), ins)?;
                    }
                }
            }
            Err(Error::InvalidOpcode(ins)) => {
                writeln!(out, "    {:016x} unknown {:#018x}", ins, ins)?;
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

    /// Unsign-extend a smaller type
    fn extend_u<U: OpU>(other: U) -> Self;

    /// Sign-extend a smaller type
    fn extend_s<U: OpU>(other: U) -> Self;

    /// Splat a smaller type
    fn splat<U: OpU>(other: U) -> Self;

    /// Test if self is zero
    fn is_zero(&self) -> bool {
        self == &Self::zero()
    }

    /// Test if self is one
    fn is_one(&self) -> bool {
        self == &Self::one()
    }

    /// Test if self is ones
    fn is_ones(&self) -> bool {
        self == &Self::ones()
    }

    /// Can we compress into a sign-extend followed by a splat?
    fn is_extend_splat(&self, extend_npw2: u8, splat_npw2: u8) -> bool {
        let bytes = self.to_le_bytes();
        let bytes = bytes.as_ref();
        let splat_width = 1usize << splat_npw2;
        let extend_width = 1usize << extend_npw2;

        // is extend?
        (splat_width..bytes.len())
            .step_by(splat_width)
            .all(|i| &bytes[i..i+splat_width] == &bytes[..splat_width])
            // is extend?
            && if bytes[extend_width-1] & 0x80 == 0x80 {
                bytes[extend_width..splat_width].iter().all(|b| *b == 0xff)
            } else {
                bytes[extend_width..splat_width].iter().all(|b| *b == 0x00)
            }
    }

    /// Find the smallest sign-extend splat representation
    fn find_extend_splat(&self) -> (u8, u8) {
        // find best splat
        for splat_npw2 in 0..=Self::NPW2 {
            if self.is_extend_splat(splat_npw2, splat_npw2) {
                // find best extend-splat
                for extend_npw2 in 0..=splat_npw2 {
                    if self.is_extend_splat(extend_npw2, splat_npw2) {
                        return (extend_npw2, splat_npw2);
                    }
                }
            }
        }

        unreachable!();
    }
}

for_secret_t! {
    __if(__t == "u") {
        #[derive(Copy, Clone, Debug, Eq, PartialEq)]
        pub struct __U([u8; __size]);

        impl From<[u8; __size]> for __U {
            fn from(v: [u8; __size]) -> Self {
                Self::from_le_bytes(v)
            }
        }

        impl From<__U> for [u8; __size] {
            fn from(v: __U) -> [u8; __size] {
                v.to_le_bytes()
            }
        }

        __if(__has_prim) {
            impl From<__prim_u> for __U {
                fn from(v: __prim_u) -> Self {
                    Self::from_le_bytes(v.to_le_bytes())
                }
            }

            impl From<__U> for __prim_u {
                fn from(v: __U) -> __prim_u {
                    <__prim_u>::from_le_bytes(v.to_le_bytes())
                }
            }

            impl From<__prim_i> for __U {
                fn from(v: __prim_i) -> Self {
                    Self::from_le_bytes(v.to_le_bytes())
                }
            }

            impl From<__U> for __prim_i {
                fn from(v: __U) -> __prim_i {
                    <__prim_i>::from_le_bytes(v.to_le_bytes())
                }
            }
        }

        impl OpU for __U {
            const NPW2: u8 = __npw2;

            type Bytes = [u8; __size];

            fn to_le_bytes(self) -> Self::Bytes {
                self.0
            }

            fn from_le_bytes(bytes: Self::Bytes) -> Self {
                Self(bytes)
            }

            fn zero() -> Self {
                Self([0; __size])
            }

            fn one() -> Self {
                let mut bytes = [0; __size];
                bytes[0] = 1;
                Self(bytes)
            }

            fn ones() -> Self {
                Self([0xff; __size])
            }

            fn extend_u<U: OpU>(other: U) -> Self {
                let slice = other.to_le_bytes();
                let slice = slice.as_ref();
                let mut bytes = [0; __size];
                bytes[..slice.len()].copy_from_slice(slice);
                Self(bytes)
            }

            fn extend_s<U: OpU>(other: U) -> Self {
                let slice = other.to_le_bytes();
                let slice = slice.as_ref();
                let mut bytes = if slice[slice.len()-1] & 0x80 == 0x80 {
                    [0xff; __size]
                } else {
                    [0x00; __size]
                };
                bytes[..slice.len()].copy_from_slice(slice);
                Self(bytes)
            }

            fn splat<U: OpU>(other: U) -> Self {
                let slice = other.to_le_bytes();
                let slice = slice.as_ref();
                let mut bytes = [0; __size];
                for i in (0..__size).step_by(slice.len()) {
                    bytes[i..i+slice.len()].copy_from_slice(slice);
                }
                Self(bytes)
            }
        }

        impl Default for __U {
            fn default() -> Self {
                Self::zero()
            }
        }

        impl LowerHex for __U {
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


/// Kinds of operations in tree
#[derive(Debug)]
pub enum OpKind<T: OpU> {
    Const(T),
    Imm(T),
    Sym(&'static str),

    Extract(u16, RefCell<Rc<dyn DynOpNode>>),
    Replace(u16, RefCell<Rc<OpNode<T>>>, RefCell<Rc<dyn DynOpNode>>),
    Select(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    Shuffle(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),

    ExtendU(u8, RefCell<Rc<dyn DynOpNode>>),
    ExtendS(u8, RefCell<Rc<dyn DynOpNode>>),
    Truncate(u8, RefCell<Rc<dyn DynOpNode>>),
    Splat(RefCell<Rc<dyn DynOpNode>>),

    None(RefCell<Rc<OpNode<T>>>),
    All(u8, RefCell<Rc<OpNode<T>>>),
    Eq(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    Ne(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    LtU(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    LtS(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    GtU(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    GtS(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    LeU(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    LeS(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    GeU(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    GeS(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    MinU(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    MinS(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    MaxU(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    MaxS(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),

    Neg(u8, RefCell<Rc<OpNode<T>>>),
    Abs(u8, RefCell<Rc<OpNode<T>>>),
    Not(RefCell<Rc<OpNode<T>>>),
    Clz(u8, RefCell<Rc<OpNode<T>>>),
    Ctz(u8, RefCell<Rc<OpNode<T>>>),
    Popcnt(u8, RefCell<Rc<OpNode<T>>>),
    Add(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    Sub(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    Mul(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    And(RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    Andnot(RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    Or(RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    Xor(RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    Shl(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    ShrU(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    ShrS(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    Rotl(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
    Rotr(u8, RefCell<Rc<OpNode<T>>>, RefCell<Rc<OpNode<T>>>),
}


/// Tree of operations, including metadata to deduplicate
/// common branches
#[derive(Debug)]
pub struct OpNode<T: OpU> {
    kind: OpKind<T>,
    refs: Cell<u32>,
    slot: Cell<Option<u16>>,
    flags: u8,
    #[cfg(feature="opt-schedule-slots")]
    depth: u32,
    #[cfg(feature="opt-fold-consts")]
    folded: Cell<bool>,
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
    pool: BTreeSet<(u8, i32)>,
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
            max_npw2: 0,
        }
    }

    /// Allocate a slot with the required npw2 size,
    /// note it's possible to run out of slots here
    fn alloc(&mut self, npw2: u8) -> Result<u16, Error> {
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
            let best_slot = self.pool.range((npw2, i32::MIN)..)
                .copied()
                .filter(|(best_npw2, best_islot)| {
                    // fits in slot number?
                    u16::try_from(
                        (usize::try_from(-best_islot).unwrap() << best_npw2)
                            >> npw2
                    ).is_ok()
                })
                .next();
            if let Some((mut best_npw2, best_islot)) = best_slot {
                // remove from pool
                self.pool.remove(&(best_npw2, best_islot));
                let mut best_slot = u16::try_from(-best_islot).unwrap();

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
            if let Ok(padding_slot) = u16::try_from(padding_slot) {
                self.dealloc(padding_slot, u8::try_from(padding_npw2).unwrap());
            }
        }

        match u16::try_from(self.size >> npw2) {
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
        #[allow(unused)] mut slot: u16,
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
                while self.pool.remove(&(npw2, -i32::from(slot ^ 1))) {
                    slot /= 2;
                    npw2 += 1;
                }
            }

            assert!(
                self.pool.insert((npw2, -i32::from(slot))),
                "Found duplicate slot in pool!? ({}, {})\n{:?}",
                slot, npw2,
                self.pool
            )
        }
    }
}

/// Compilation state
pub struct OpCompile {
    bytecode: Vec<u64>,
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
            Rc::new(Self::and(self.clone(), OpTree::dyn_cast_s(other).into_owned()))
        }
    }

    fn dyn_andnot(&self, other: &dyn DynOpTree) -> Rc<dyn DynOpTree> {
        // use the smallest type
        if other.npw2() < self.npw2() {
            other.dyn_notand(self)
        } else {
            Rc::new(Self::andnot(self.clone(), OpTree::dyn_cast_s(other).into_owned()))
        }
    }

    fn dyn_notand(&self, other: &dyn DynOpTree) -> Rc<dyn DynOpTree> {
        // use the smallest type
        if other.npw2() < self.npw2() {
            other.dyn_andnot(self)
        } else {
            Rc::new(Self::andnot(OpTree::dyn_cast_s(other).into_owned(), self.clone()))
        }
    }

    fn dyn_or(&self, other: &dyn DynOpTree) -> Rc<dyn DynOpTree> {
        // use the smallest type
        if other.npw2() < self.npw2() {
            other.dyn_or(self)
        } else {
            Rc::new(Self::or(self.clone(), OpTree::dyn_cast_s(other).into_owned()))
        }
    }

    fn dyn_xor(&self, other: &dyn DynOpTree) -> Rc<dyn DynOpTree> {
        // use the smallest type
        if other.npw2() < self.npw2() {
            other.dyn_xor(self)
        } else {
            Rc::new(Self::xor(self.clone(), OpTree::dyn_cast_s(other).into_owned()))
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
        OpTree(RefCell::new(OpRoot::Tree(Rc::new(
            OpNode::new(kind, flags, depth)
        ))))
    }

    /// Get internal tree, potentially allocating if needed
    fn node(&self) -> Rc<OpNode<T>> {
        let mut tree = self.0.borrow_mut();
        match tree.deref() {
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
    pub fn dyn_downcast<'a>(a: &'a dyn DynOpTree) -> &'a Self {
        assert_eq!(a.npw2(), T::NPW2);
        unsafe { &*(a as *const dyn DynOpTree as *const Self) }
    }

    /// Helper for choosing the most efficient cast between trees of
    /// different types, including returning the tree as is with only
    /// the type information stripped
    pub fn dyn_cast_u<'a>(a: &'a dyn DynOpTree) -> Cow<'a, Self> {
        if T::NPW2 > a.npw2() {
            let a = a.dyn_node();
            let flags = a.flags();
            let depth = a.depth();
            Cow::Owned(Self::from_kind(OpKind::ExtendU(0, RefCell::new(a)), flags, depth))
        } else if T::NPW2 < a.npw2() {
            let a = a.dyn_node();
            let flags = a.flags();
            let depth = a.depth();
            Cow::Owned(Self::from_kind(OpKind::Truncate(0, RefCell::new(a)), flags, depth))
        } else {
            Cow::Borrowed(Self::dyn_downcast(a))
        }
    }

    /// Helper for choosing the most efficient cast between trees of
    /// different types, including returning the tree as is with only
    /// the type information stripped
    pub fn dyn_cast_s<'a>(a: &'a dyn DynOpTree) -> Cow<'a, Self> {
        if T::NPW2 > a.npw2() {
            let a = a.dyn_node();
            let flags = a.flags();
            let depth = a.depth();
            Cow::Owned(Self::from_kind(OpKind::ExtendS(0, RefCell::new(a)), flags, depth))
        } else if T::NPW2 < a.npw2() {
            let a = a.dyn_node();
            let flags = a.flags();
            let depth = a.depth();
            Cow::Owned(Self::from_kind(OpKind::Truncate(0, RefCell::new(a)), flags, depth))
        } else {
            Cow::Borrowed(Self::dyn_downcast(a))
        }
    }

    /// is expression an immediate?
    pub fn is_imm(&self) -> bool {
        match self.0.borrow().deref() {
            OpRoot::Const(_) => true,
            OpRoot::Imm(_) => true,
            OpRoot::Tree(tree) => tree.is_imm(),
        }
    }

    /// is expression a symbol?
    pub fn is_sym(&self) -> bool {
        match self.0.borrow().deref() {
            OpRoot::Const(_) => false,
            OpRoot::Imm(_) => false,
            OpRoot::Tree(tree) => tree.is_sym(),
        }
    }

    /// is expression const?
    pub fn is_const(&self) -> bool {
        match self.0.borrow().deref() {
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

    pub fn extract<U: OpU>(x: u16, a: OpTree<U>) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Extract(x, RefCell::new(a)), flags, depth)
    }

    pub fn replace<U: OpU>(x: u16, a: Self, b: OpTree<U>) -> Self {
        let a = a.node();
        let b = b.dyn_node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Replace(x, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn select(lnpw2: u8, p: Self, a: Self, b: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let p = p.node();
        let a = a.node();
        let b = b.node();
        let flags = p.flags() | a.flags() | b.flags();
        let depth = max(p.depth(), max(a.depth(), b.depth())).saturating_add(1);
        Self::from_kind(OpKind::Select(lnpw2, RefCell::new(p), RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn shuffle(lnpw2: u8, p: Self, a: Self, b: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let p = p.node();
        let a = a.node();
        let b = b.node();
        let flags = p.flags() | a.flags() | b.flags();
        let depth = max(p.depth(), max(a.depth(), b.depth())).saturating_add(1);
        Self::from_kind(OpKind::Shuffle(lnpw2, RefCell::new(p), RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn extend_u<U: OpU>(lnpw2: u8, a: OpTree<U>) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::ExtendU(lnpw2, RefCell::new(a)), flags, depth)
    }

    pub fn extend_s<U: OpU>(lnpw2: u8, a: OpTree<U>) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::ExtendS(lnpw2, RefCell::new(a)), flags, depth)
    }

    pub fn truncate<U: OpU>(lnpw2: u8, a: OpTree<U>) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Truncate(lnpw2, RefCell::new(a)), flags, depth)
    }

    pub fn splat<U: OpU>(a: OpTree<U>) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Splat(RefCell::new(a)), flags, depth)
    }

    pub fn none(a: Self) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::None(RefCell::new(a)), flags, depth)
    }

    pub fn all(lnpw2: u8, a: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::All(lnpw2, RefCell::new(a)), flags, depth)
    }

    pub fn eq(lnpw2: u8, a: Self, b: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Eq(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn ne(lnpw2: u8, a: Self, b: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Ne(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn lt_u(lnpw2: u8, a: Self, b: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::LtU(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn lt_s(lnpw2: u8, a: Self, b: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::LtS(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn gt_u(lnpw2: u8, a: Self, b: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::GtU(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn gt_s(lnpw2: u8, a: Self, b: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::GtS(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn le_u(lnpw2: u8, a: Self, b: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::LeU(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn le_s(lnpw2: u8, a: Self, b: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::LeS(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn ge_u(lnpw2: u8, a: Self, b: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::GeU(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn ge_s(lnpw2: u8, a: Self, b: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::GeS(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn min_u(lnpw2: u8, a: Self, b: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::MinU(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn min_s(lnpw2: u8, a: Self, b: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::MinS(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn max_u(lnpw2: u8, a: Self, b: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::MaxU(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn max_s(lnpw2: u8, a: Self, b: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::MaxS(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn neg(lnpw2: u8, a: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Neg(lnpw2, RefCell::new(a)), flags, depth)
    }

    pub fn abs(lnpw2: u8, a: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Abs(lnpw2, RefCell::new(a)), flags, depth)
    }

    pub fn not(a: Self) -> Self {
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Not(RefCell::new(a)), flags, depth)
    }

    pub fn clz(lnpw2: u8, a: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Clz(lnpw2, RefCell::new(a)), flags, depth)
    }

    pub fn ctz(lnpw2: u8, a: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Ctz(lnpw2, RefCell::new(a)), flags, depth)
    }

    pub fn popcnt(lnpw2: u8, a: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let flags = a.flags();
        let depth = a.depth();
        Self::from_kind(OpKind::Popcnt(lnpw2, RefCell::new(a)), flags, depth)
    }

    pub fn add(lnpw2: u8, a: Self, b: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Add(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn sub(lnpw2: u8, a: Self, b: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Sub(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn mul(lnpw2: u8, a: Self, b: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Mul(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn and(a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::And(RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn andnot(a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Andnot(RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn or(a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Or(RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn xor(a: Self, b: Self) -> Self {
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Xor(RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn shl(lnpw2: u8, a: Self, b: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Shl(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn shr_u(lnpw2: u8, a: Self, b: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::ShrU(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn shr_s(lnpw2: u8, a: Self, b: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::ShrS(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn rotl(lnpw2: u8, a: Self, b: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Rotl(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    pub fn rotr(lnpw2: u8, a: Self, b: Self) -> Self {
        debug_assert!(lnpw2 <= 6);
        let a = a.node();
        let b = b.node();
        let flags = a.flags() | b.flags();
        let depth = max(a.depth(), b.depth()).saturating_add(1);
        Self::from_kind(OpKind::Rotr(lnpw2, RefCell::new(a), RefCell::new(b)), flags, depth)
    }

    /// display tree for debugging
    pub fn disas<W: io::Write>(&self, mut out: W) -> Result<(), io::Error> {
        match self.0.borrow().deref() {
            OpRoot::Const(v) => writeln!(out, "    (u{}.const {:x}", 8 << T::NPW2, v),
            OpRoot::Imm(v)   => writeln!(out, "    (u{}.imm {:x})",  8 << T::NPW2, v),
            OpRoot::Tree(tree) => tree.disas(out),
        }
    }

    /// high-level compile into bytecode, stack, and initial stack pointer
    pub fn compile(&self, opt: bool) -> (Vec<u64>, AlignedBytes) {
        // force to tree form
        self.node();

        match self.0.borrow_mut().deref_mut() {
            OpRoot::Tree(ref mut tree) => {
                // should we do a constant folding pass? we need to do this here
                // so we can update our root reference
                #[cfg(feature="opt-fold-consts")]
                if opt {
                    if let Some(x) = tree.fold_consts() {
                        *tree = OpNode::<T>::dyn_downcast(x);
                    }
                }

                // compile
                tree.compile(opt)
            }
            _ => panic!("compiling non-tree?"),
        }
    }

    /// Assuming we are Sym, patch the slots during a call
    pub fn patch<U>(&self, slots: &mut [u8], v: U)
    where
        T: From<U>
    {
        match self.0.borrow().deref() {
            OpRoot::Tree(tree) => tree.patch(slots, v),
            _ => panic!("patching non-sym?")
        }
    }

    /// execute bytecode, resulting in an immediate OpTree
    pub fn exec(bytecode: &[u64], slots: &mut [u8]) -> Self {
        Self::try_exec(bytecode, slots).unwrap()
    }

    /// execute bytecode, resulting in an immediate OpTree
    pub fn try_exec(bytecode: &[u64], slots: &mut [u8]) -> Result<Self, Error> {
        let res = exec(bytecode, slots)?;
        Ok(OpTree(RefCell::new(OpRoot::Imm(T::from_le_bytes(
            T::Bytes::try_from(res).map_err(|_| Error::InvalidReturn)?
        )))))
    }

    /// compile and execute if OpTree is not already an immediate
    pub fn eval(&self) -> Self {
        self.try_eval().unwrap()
    }

    /// compile and execute if OpTree is not already an immediate
    pub fn try_eval(&self) -> Result<Self, Error> {
        match self.0.borrow().deref() {
            OpRoot::Const(v) => Ok(Self::const_(*v)),
            OpRoot::Imm(v)   => Ok(Self::imm(*v)),
            OpRoot::Tree(tree) => {
                if tree.is_sym() {
                    Err(Error::DeclassifyInCompile)?;
                }

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

    fn new(kind: OpKind<T>, flags: u8, #[allow(unused)] depth: u32) -> OpNode<T> {
        OpNode {
            kind: kind,
            refs: Cell::new(0),
            slot: Cell::new(None),
            flags: flags,
            #[cfg(feature="opt-schedule-slots")]
            depth: depth,
            #[cfg(feature="opt-fold-consts")]
            folded: Cell::new(false),
        }
    }

    /// Forcefully downcast into a different OpNode, panicking if types
    /// do not match
    pub fn dyn_downcast(a: Rc<dyn DynOpNode>) -> Rc<Self> {
        assert_eq!(a.npw2(), T::NPW2);
        unsafe { Rc::from_raw(Rc::into_raw(a) as _) }
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
    pub fn compile(&self, opt: bool) -> (Vec<u64>, AlignedBytes) {
        // debug?
        #[cfg(feature="debug-ast")]
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
        state.bytecode.push(u64::from(OpIns::new(
            T::NPW2, 0, OpCode::Ret, 0, slot, 0
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
    fn fold_consts(&self) -> Option<Rc<dyn DynOpNode>>;

    /// First compile pass, used to find the number of immediates
    /// for offset calculation, and local reference counting to
    /// deduplicate branches.
    fn compile_pass1(&self, state: &mut OpCompile);

    /// Second compile pass, used to actually compile both the
    /// immediates and bytecode. Returns the resulting slot + npw2.
    fn compile_pass2(&self, state: &mut OpCompile) -> (u16, u8);
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
        #[cfg(feature="opt-schedule-slots")]
        {
            self.depth
        }
        #[cfg(not(feature="opt-schedule-slots"))]
        {
            0
        }
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
        match (self.is_const(), &self.kind) {
            (true, OpKind::Const(v)) => v.is_zero(),
            _                        => false,
        }
    }

    fn is_const_one(&self) -> bool {
        match (self.is_const(), &self.kind) {
            (true, OpKind::Const(v)) => v.is_zero(),
            _                        => false,
        }
    }

    fn is_const_ones(&self) -> bool {
        match (self.is_const(), &self.kind) {
            (true, OpKind::Const(v)) => v.is_zero(),
            _                        => false,
        }
    }

    fn inc_refs(&self) -> u32 {
        let refs = self.refs.get() + 1;
        self.refs.set(refs);
        refs
    }

    fn dec_refs(&self) -> u32 {
        let refs = self.refs.get() - 1;
        self.refs.set(refs);
        refs
    }

    fn disas_pass1(&self) {
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
                a.borrow().disas_pass1();
            }
            OpKind::Replace(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::Select(_, p, a, b) => {
                p.borrow().disas_pass1();
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::Shuffle(_, p, a, b) => {
                p.borrow().disas_pass1();
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }

            OpKind::ExtendU(_, a) => {
                a.borrow().disas_pass1();
            }
            OpKind::ExtendS(_, a) => {
                a.borrow().disas_pass1();
            }
            OpKind::Truncate(_, a) => {
                a.borrow().disas_pass1();
            }
            OpKind::Splat(a) => {
                a.borrow().disas_pass1();
            }

            OpKind::None(a) => {
                a.borrow().disas_pass1();
            }
            OpKind::All(_, a) => {
                a.borrow().disas_pass1();
            }
            OpKind::Eq(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::Ne(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::LtU(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::LtS(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::GtU(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::GtS(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::LeU(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::LeS(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::GeU(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::GeS(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::MinU(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::MinS(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::MaxU(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::MaxS(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }

            OpKind::Neg(_, a) => {
                a.borrow().disas_pass1();
            }
            OpKind::Abs(_, a) => {
                a.borrow().disas_pass1();
            }
            OpKind::Not(a) => {
                a.borrow().disas_pass1();
            }
            OpKind::Clz(_, a) => {
                a.borrow().disas_pass1();
            }
            OpKind::Ctz(_, a) => {
                a.borrow().disas_pass1();
            }
            OpKind::Popcnt(_, a) => {
                a.borrow().disas_pass1();
            }
            OpKind::Add(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::Sub(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::Mul(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::And(a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::Andnot(a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::Or(a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::Xor(a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::Shl(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::ShrU(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::ShrS(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::Rotl(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
            OpKind::Rotr(_, a, b) => {
                a.borrow().disas_pass1();
                b.borrow().disas_pass1();
            }
        }
    }

    fn disas_pass2(
        &self,
        names: &mut HashMap<usize, String>,
        arbitrary_names: &mut dyn Iterator<Item=String>,
        stmts: &mut dyn io::Write,
    ) -> Result<String, io::Error> {
        // is node shared?
        let refs = self.dec_refs();

        // already computed?
        let name = names.get(&((self as *const _) as usize));
        if let Some(name) = name {
            return Ok(name.clone());
        }

        let expr = match &self.kind {
            OpKind::Const(v) => format!("({}.const {:x})",
                prefix(T::NPW2, 0),
                v
            ),
            OpKind::Imm(v) => format!("({}.imm {:x})",
                prefix(T::NPW2, 0),
                v
            ),
            OpKind::Sym(s) => format!("({}.sym {:?})",
                prefix(T::NPW2, 0),
                s
            ),

            OpKind::Extract(x, a) => format!("({}.extract {} {})",
                prefix(a.borrow().npw2(), a.borrow().npw2()-T::NPW2),
                x,
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Replace(x, a, b) => format!("({}.replace {} {} {})",
                prefix(T::NPW2, T::NPW2-b.borrow().npw2()),
                x,
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Select(lnpw2, p, a, b) => format!("({}.select {} {} {})",
                prefix(T::NPW2, *lnpw2),
                p.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Shuffle(lnpw2, p, a, b) => format!("({}.shuffle {} {} {})",
                prefix(T::NPW2, *lnpw2),
                p.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),

            OpKind::ExtendU(lnpw2, a) => format!("({}.extend_u {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::ExtendS(lnpw2, a) => format!("({}.extend_s {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Truncate(lnpw2, a) => format!("({}.truncate {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Splat(a) => format!("({}.splat {})",
                prefix(T::NPW2, T::NPW2-a.borrow().npw2()),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),

            OpKind::None(a) => format!("({}.none {})",
                prefix(T::NPW2, 0),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::All(lnpw2, a) => format!("({}.all {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Eq(lnpw2, a, b) => format!("({}.eq {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Ne(lnpw2, a, b) => format!("({}.ne {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::LtU(lnpw2, a, b) => format!("({}.lt_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::LtS(lnpw2, a, b) => format!("({}.lt_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::GtU(lnpw2, a, b) => format!("({}.gt_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::GtS(lnpw2, a, b) => format!("({}.gt_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::LeU(lnpw2, a, b) => format!("({}.le_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::LeS(lnpw2, a, b) => format!("({}.le_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::GeU(lnpw2, a, b) => format!("({}.ge_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::GeS(lnpw2, a, b) => format!("({}.ge_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::MinU(lnpw2, a, b) => format!("({}.min_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::MinS(lnpw2, a, b) => format!("({}.min_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::MaxU(lnpw2, a, b) => format!("({}.max_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::MaxS(lnpw2, a, b) => format!("({}.max_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),

            OpKind::Neg(lnpw2, a) => format!("({}.neg {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Abs(lnpw2, a) => format!("({}.abs {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Not(a) => format!("({}.not {})",
                8 << T::NPW2,
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Clz(lnpw2, a) => format!("({}.clz {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Ctz(lnpw2, a) => format!("({}.ctz {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Popcnt(lnpw2, a) => format!("({}.popcnt {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind::Add(lnpw2, a, b) => format!("({}.add {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Sub(lnpw2, a, b) => format!("({}.sub {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Mul(lnpw2, a, b) => format!("({}.mul {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::And(a, b) => format!("({}.and {} {})",
                prefix(T::NPW2, 0),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Andnot(a, b) => format!("({}.andnot {} {})",
                prefix(T::NPW2, 0),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Or(a, b) => format!("({}.or {} {})",
                prefix(T::NPW2, 0),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Xor(a, b) => format!("({}.xor {} {})",
                prefix(T::NPW2, 0),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Shl(lnpw2, a, b) => format!("({}.shl {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::ShrU(lnpw2, a, b) => format!("({}.shr_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::ShrS(lnpw2, a, b) => format!("({}.shr_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Rotl(lnpw2, a, b) => format!("({}.rotl {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind::Rotr(lnpw2, a, b) => format!("({}.rotr {} {})",
                prefix(T::NPW2, *lnpw2),
                a.borrow().disas_pass2(names, arbitrary_names, stmts)?,
                b.borrow().disas_pass2(names, arbitrary_names, stmts)?,
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
        // refs must equal 0 between multi-pass traversals
        assert_eq!(self.refs.get(), 0);

        match &self.kind {
            OpKind::Const(_) => {},
            OpKind::Imm(_) => {},
            OpKind::Sym(_) => {},

            OpKind::Extract(_, a) => {
                a.borrow().check_refs();
            }
            OpKind::Replace(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::Select(_, p, a, b) => {
                p.borrow().check_refs();
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::Shuffle(_, p, a, b) => {
                p.borrow().check_refs();
                a.borrow().check_refs();
                b.borrow().check_refs();
            }

            OpKind::ExtendU(_, a) => {
                a.borrow().check_refs();
            }
            OpKind::ExtendS(_, a) => {
                a.borrow().check_refs();
            }
            OpKind::Truncate(_, a) => {
                a.borrow().check_refs();
            }
            OpKind::Splat(a) => {
                a.borrow().check_refs();
            }

            OpKind::None(a) => {
                a.borrow().check_refs();
            }
            OpKind::All(_, a) => {
                a.borrow().check_refs();
            }
            OpKind::Eq(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::Ne(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::LtU(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::LtS(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::GtU(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::GtS(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::LeU(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::LeS(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::GeU(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::GeS(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::MinU(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::MinS(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::MaxU(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::MaxS(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }

            OpKind::Neg(_, a) => {
                a.borrow().check_refs();
            }
            OpKind::Abs(_, a) => {
                a.borrow().check_refs();
            }
            OpKind::Not(a) => {
                a.borrow().check_refs();
            }
            OpKind::Clz(_, a) => {
                a.borrow().check_refs();
            }
            OpKind::Ctz(_, a) => {
                a.borrow().check_refs();
            }
            OpKind::Popcnt(_, a) => {
                a.borrow().check_refs();
            }
            OpKind::Add(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::Sub(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::Mul(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::And(a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::Andnot(a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::Or(a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::Xor(a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::Shl(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::ShrU(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::ShrS(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::Rotl(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
            OpKind::Rotr(_, a, b) => {
                a.borrow().check_refs();
                b.borrow().check_refs();
            }
        }
    }


    #[cfg(feature="opt-fold-consts")]
    fn fold_consts(&self) -> Option<Rc<dyn DynOpNode>> {
        // already folded?
        if self.folded.get() {
            return None;
        }
        self.folded.set(true);

        if self.is_const() && !self.is_imm() {
            // oh hey, we're const
            //
            // note this recursively triggers another compilation
            // + execution, so be careful
            //
            // if this fails we just bail on the const folding so the error
            // can be reported at runtime
            if let Ok(v) = self.try_eval() {
                return Some(Rc::new(Self::new(
                    OpKind::Const(v), 0, 0
                )));
            }
        }

        match &self.kind {
            OpKind::Const(_) => {},
            OpKind::Imm(_) => {},
            OpKind::Sym(_) => {},

            OpKind::Extract(_, a) => {
                let mut a = a.borrow_mut();
                a.fold_consts().map(|x| *a = x);
            }
            OpKind::Replace(_, a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = x);
            }
            OpKind::Select(_, p, a, b) => {
                let mut p = p.borrow_mut();
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                p.fold_consts().map(|x| *p = Self::dyn_downcast(x));
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
            }
            OpKind::Shuffle(_, p, a, b) => {
                let mut p = p.borrow_mut();
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                p.fold_consts().map(|x| *p = Self::dyn_downcast(x));
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
            }

            OpKind::ExtendU(_, a) => {
                let mut a = a.borrow_mut();
                a.fold_consts().map(|x| *a = x);
            }
            OpKind::ExtendS(_, a) => {
                let mut a = a.borrow_mut();
                a.fold_consts().map(|x| *a = x);
            }
            OpKind::Truncate(_, a) => {
                let mut a = a.borrow_mut();
                a.fold_consts().map(|x| *a = x);
            }
            OpKind::Splat(a) => {
                let mut a = a.borrow_mut();
                a.fold_consts().map(|x| *a = x);
            }

            OpKind::None(a) => {
                let mut a = a.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
            }
            OpKind::All(_, a) => {
                let mut a = a.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
            }
            OpKind::Eq(x, a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-simple-reductions")]
                match (&a.kind, &b.kind) {
                    _ if *x == 0 && a.is_const_zero() => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::None(
                                RefCell::new(b.clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    _ if *x == 0 && b.is_const_zero() => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::None(
                                RefCell::new(a.clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    _ => {}
                }
            }
            OpKind::Ne(x, a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-simple-reductions")]
                match (&a.kind, &b.kind) {
                    _ if *x == 0 && a.is_const_zero() => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::All(0,
                                RefCell::new(b.clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    _ if *x == 0 && b.is_const_zero() => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::All(0,
                                RefCell::new(a.clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    _ => {}
                }
            }
            OpKind::LtU(_, a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
            }
            OpKind::LtS(_, a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
            }
            OpKind::GtU(_, a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
            }
            OpKind::GtS(_, a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
            }
            OpKind::LeU(_, a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
            }
            OpKind::LeS(_, a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
            }
            OpKind::GeU(_, a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
            }
            OpKind::GeS(_, a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
            }
            OpKind::MinU(_, a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
            }
            OpKind::MinS(_, a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
            }
            OpKind::MaxU(_, a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
            }
            OpKind::MaxS(_, a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
            }

            OpKind::Neg(_, a) => {
                let mut a = a.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
            }
            OpKind::Abs(_, a) => {
                let mut a = a.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
            }
            OpKind::Not(a) => {
                let mut a = a.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                // not has the most powerful set of reductions, fortunately
                // it is a bit unique in this regard
                #[cfg(feature="opt-simple-reductions")]
                match &a.kind {
                    OpKind::Not(a) => {
                        return Some(a.borrow().clone())
                    }
                    OpKind::None(a)  => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::All(0,
                                RefCell::new(a.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    OpKind::All(0, a) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::None(
                                RefCell::new(a.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    OpKind::Eq(y, a, b) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::Ne(*y,
                                RefCell::new(a.borrow().clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    OpKind::Ne(y, a, b) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::Eq(*y,
                                RefCell::new(a.borrow().clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    OpKind::LtU(y, a, b) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::GeU(*y,
                                RefCell::new(a.borrow().clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    OpKind::LtS(y, a, b) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::GeS(*y,
                                RefCell::new(a.borrow().clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    OpKind::GtU(y, a, b) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::LeU(*y,
                                RefCell::new(a.borrow().clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    OpKind::GtS(y, a, b) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::LeS(*y,
                                RefCell::new(a.borrow().clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    OpKind::LeU(y, a, b) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::GtU(*y,
                                RefCell::new(a.borrow().clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    OpKind::LeS(y, a, b) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::GtS(*y,
                                RefCell::new(a.borrow().clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    OpKind::GeU(y, a, b) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::LtU(*y,
                                RefCell::new(a.borrow().clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    OpKind::GeS(y, a, b) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::LtS(*y,
                                RefCell::new(a.borrow().clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    _ => {}
                }
            }
            OpKind::Clz(_, a) => {
                let mut a = a.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
            }
            OpKind::Ctz(_, a) => {
                let mut a = a.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
            }
            OpKind::Popcnt(_, a) => {
                let mut a = a.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
            }
            OpKind::Add(x, a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-fold-nops")]
                if a.is_const_zero() {
                    return Some(b.clone());
                } else if b.is_const_zero() {
                    return Some(a.clone());
                }
                #[cfg(feature="opt-simple-reductions")]
                match (&a.kind, &b.kind) {
                    (OpKind::Neg(y, a), _) if y == x => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::Sub(*x,
                                RefCell::new(b.clone()),
                                RefCell::new(a.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    (_, OpKind::Neg(y, b)) if y == x => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::Sub(*x,
                                RefCell::new(a.clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    _ => {}
                }
            }
            OpKind::Sub(x, a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-fold-nops")]
                if b.is_const_zero() {
                    return Some(a.clone());
                }
                #[cfg(feature="opt-simple-reductions")]
                match (&a.kind, &b.kind) {
                    (_, OpKind::Neg(y, b)) if y == x => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::Add(*x,
                                RefCell::new(a.clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    _ => {}
                }
            }
            OpKind::Mul(x, a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-fold-nops")]
                if *x == 0 && a.is_const_one() {
                    return Some(b.clone());
                } else if *x == 0 && b.is_const_one() {
                    return Some(a.clone());
                }
            }
            OpKind::And(a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-fold-nops")]
                if a.is_const_ones() {
                    return Some(b.clone());
                } else if b.is_const_ones() {
                    return Some(a.clone());
                }
                #[cfg(feature="opt-simple-reductions")]
                match (&a.kind, &b.kind) {
                    (OpKind::Not(a), OpKind::Not(b)) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::Not(
                                RefCell::new(Rc::new(OpNode::new(
                                    OpKind::Or(
                                        RefCell::new(a.borrow().clone()),
                                        RefCell::new(b.borrow().clone())
                                    ), self.flags, self.depth
                                )))
                            ), self.flags, self.depth
                        )));
                    }
                    (OpKind::Not(a), _) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::Andnot(
                                RefCell::new(b.clone()),
                                RefCell::new(a.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    (_, OpKind::Not(b)) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::Andnot(
                                RefCell::new(a.clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    _ => {}
                }
            }
            OpKind::Andnot(a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-fold-nops")]
                if a.is_const_ones() {
                    return Some(b.clone());
                } else if b.is_const_zero() {
                    return Some(a.clone());
                }
                #[cfg(feature="opt-simple-reductions")]
                match (&a.kind, &b.kind) {
                    (_, OpKind::Not(b)) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::And(
                                RefCell::new(a.clone()),
                                RefCell::new(b.borrow().clone())
                            ),
                            self.flags, self.depth
                        )));
                    }
                    _ => {}
                }
            }
            OpKind::Or(a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-fold-nops")]
                if a.is_const_zero() {
                    return Some(b.clone());
                } else if b.is_const_zero() {
                    return Some(a.clone());
                }
                #[cfg(feature="opt-simple-reductions")]
                match (&a.kind, &b.kind) {
                    (OpKind::Not(a), OpKind::Not(b)) => {
                        return Some(Rc::new(OpNode::new(
                            OpKind::Not(
                                RefCell::new(Rc::new(OpNode::new(
                                    OpKind::And(
                                        RefCell::new(a.borrow().clone()),
                                        RefCell::new(b.borrow().clone())
                                    ), self.flags, self.depth
                                )))
                            ), self.flags, self.depth
                        )));
                    }
                    _ => {}
                }
            }
            OpKind::Xor(a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-fold-nops")]
                if a.is_const_zero() {
                    return Some(b.clone());
                } else if b.is_const_zero() {
                    return Some(a.clone());
                }
            }
            OpKind::Shl(x, a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-fold-nops")]
                if *x == 0 && b.is_const_zero() {
                    return Some(a.clone());
                }
            }
            OpKind::ShrU(x, a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-fold-nops")]
                if *x == 0 && b.is_const_zero() {
                    return Some(a.clone());
                }
            }
            OpKind::ShrS(x, a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-fold-nops")]
                if *x == 0 && b.is_const_zero() {
                    return Some(a.clone());
                }
            }
            OpKind::Rotl(x, a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-fold-nops")]
                if *x == 0 && b.is_const_zero() {
                    return Some(a.clone());
                }
            }
            OpKind::Rotr(x, a, b) => {
                let mut a = a.borrow_mut();
                let mut b = b.borrow_mut();
                a.fold_consts().map(|x| *a = Self::dyn_downcast(x));
                b.fold_consts().map(|x| *b = Self::dyn_downcast(x));
                #[cfg(feature="opt-fold-nops")]
                if *x == 0 && b.is_const_zero() {
                    return Some(a.clone());
                }
            }
        }

        None
    }

    fn compile_pass1(&self, state: &mut OpCompile) {
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
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, 0, OpCode::Arg, slot, slot, 0
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
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, 0, OpCode::Arg, slot, slot, 0
                )));
            }

            OpKind::Extract(_, a) => {
                a.borrow().compile_pass1(state);
            }
            OpKind::Replace(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::Select(_, p, a, b) => {
                p.borrow().compile_pass1(state);
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::Shuffle(_, p, a, b) => {
                p.borrow().compile_pass1(state);
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }

            OpKind::ExtendU(_, a) => {
                a.borrow().compile_pass1(state);
            }
            OpKind::ExtendS(_, a) => {
                a.borrow().compile_pass1(state);
            }
            OpKind::Truncate(_, a) => {
                a.borrow().compile_pass1(state);
            }
            OpKind::Splat(a) => {
                a.borrow().compile_pass1(state);
            }

            OpKind::None(a) => {
                a.borrow().compile_pass1(state);
            }
            OpKind::All(_, a) => {
                a.borrow().compile_pass1(state);
            }
            OpKind::Eq(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::Ne(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::LtU(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::LtS(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::GtU(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::GtS(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::LeU(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::LeS(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::GeU(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::GeS(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::MinU(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::MinS(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::MaxU(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::MaxS(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }

            OpKind::Neg(_, a) => {
                a.borrow().compile_pass1(state);
            }
            OpKind::Abs(_, a) => {
                a.borrow().compile_pass1(state);
            }
            OpKind::Not(a) => {
                a.borrow().compile_pass1(state);
            }
            OpKind::Clz(_, a) => {
                a.borrow().compile_pass1(state);
            }
            OpKind::Ctz(_, a) => {
                a.borrow().compile_pass1(state);
            }
            OpKind::Popcnt(_, a) => {
                a.borrow().compile_pass1(state);
            }
            OpKind::Add(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::Sub(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::Mul(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::And(a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::Andnot(a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::Or(a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::Xor(a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::Shl(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::ShrU(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::ShrS(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::Rotl(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
            OpKind::Rotr(_, a, b) => {
                a.borrow().compile_pass1(state);
                b.borrow().compile_pass1(state);
            }
        }
    }

    fn compile_pass2(&self, state: &mut OpCompile) -> (u16, u8) {
        // already computed?
        if let Some(slot) = self.slot.get() {
            return (slot, T::NPW2);
        }

        match &self.kind {
            OpKind::Const(v) => {
                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                #[allow(unused_mut, unused_assignments)] let mut extend_npw2 = T::NPW2;
                #[allow(unused_mut, unused_assignments)] let mut splat_npw2 = T::NPW2;

                // can we use a smaller encoding?
                #[cfg(feature="opt-compress-consts")]
                {
                    let extend_splat = v.find_extend_splat();
                    extend_npw2 = extend_splat.0;
                    splat_npw2 = extend_splat.1;
                }

                // fall back to uncompressed encodings
                if extend_npw2 <= 2 {
                    // fits in a splat_const (32-bit immediate)
                    let mut buf = Vec::from(v.to_le_bytes().as_ref());
                    buf.truncate(1 << extend_npw2);
                    buf.resize(4, if buf[buf.len()-1] & 0x80 == 0x80 { 0xff } else { 0x00 });

                    state.bytecode.push(u64::from(OpIns::with_ab(
                        T::NPW2, T::NPW2-splat_npw2, OpCode::SplatConst, slot,
                        u32::from_le_bytes(<_>::try_from(&buf[..]).unwrap())
                    )));
                } else {
                    // does not fit, just follows in instruction stream
                    state.bytecode.push(u64::from(OpIns::new(
                        T::NPW2, T::NPW2-splat_npw2, OpCode::SplatLongConst, slot,
                        0, u16::from(extend_npw2), 
                    )));

                    let mut buf = Vec::from(v.to_le_bytes().as_ref());
                    buf.truncate(1 << extend_npw2);
                    for i in (0..buf.len()).step_by(8) {
                        state.bytecode.push(
                            u64::from_le_bytes(<_>::try_from(&buf[i..i+8]).unwrap())
                        );
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
                let p = p.borrow();
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (p_slot, p_npw2) = p.compile_pass2(state);
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let p_refs = p.dec_refs();
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if b_refs == 0 {
                    state.bytecode.push(u64::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Select, b_slot, a_slot, p_slot
                    )));
                    if p_refs == 0 { state.slot_pool.dealloc(p_slot, p_npw2); }
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u64::from(OpIns::new(
                        T::NPW2, 0, OpCode::Splat, slot, b_slot, 0
                    )));
                    state.bytecode.push(u64::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Select, slot, a_slot, p_slot
                    )));
                    if p_refs == 0 { state.slot_pool.dealloc(p_slot, p_npw2); }
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::Shuffle(lnpw2, p, a, b) => {
                let p = p.borrow();
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (p_slot, p_npw2) = p.compile_pass2(state);
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let p_refs = p.dec_refs();
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if b_refs == 0 {
                    state.bytecode.push(u64::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Shuffle, b_slot, a_slot, p_slot
                    )));
                    if p_refs == 0 { state.slot_pool.dealloc(p_slot, p_npw2); }
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u64::from(OpIns::new(
                        T::NPW2, 0, OpCode::Splat, slot, b_slot, 0
                    )));
                    state.bytecode.push(u64::from(OpIns::new(
                        T::NPW2, *lnpw2, OpCode::Shuffle, slot, a_slot, p_slot
                    )));
                    if p_refs == 0 { state.slot_pool.dealloc(p_slot, p_npw2); }
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind::Extract(lane, a) => {
                let a = a.borrow();
                assert!(T::NPW2 <= a.npw2());
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    a_npw2, a_npw2-T::NPW2, OpCode::Extract, slot, a_slot, *lane
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Replace(lane, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                assert!(T::NPW2 >= b.npw2());
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u64::from(OpIns::new(
                        T::NPW2, T::NPW2-b_npw2, OpCode::Replace, a_slot, b_slot, *lane
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u64::from(OpIns::new(
                        T::NPW2, 0, OpCode::Splat, slot, a_slot, 0
                    )));
                    state.bytecode.push(u64::from(OpIns::new(
                        T::NPW2, T::NPW2-b_npw2, OpCode::Replace, slot, b_slot, *lane
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }

            OpKind::ExtendU(lnpw2, a) => {
                let a = a.borrow();
                assert!(T::NPW2 >= a.npw2());
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, T::NPW2-a_npw2, OpCode::ExtendU, slot, a_slot, u16::from(*lnpw2)
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::ExtendS(lnpw2, a) => {
                let a = a.borrow();
                assert!(T::NPW2 >= a.npw2());
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, T::NPW2-a_npw2, OpCode::ExtendS, slot, a_slot, u16::from(*lnpw2)
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Truncate(lnpw2, a) => {
                let a = a.borrow();
                assert!(T::NPW2 <= a.npw2());
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    a_npw2, a_npw2-T::NPW2, OpCode::Truncate, slot, a_slot, u16::from(*lnpw2)
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Splat(a) => {
                let a = a.borrow();
                assert!(T::NPW2 >= a.npw2());
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, T::NPW2-a_npw2, OpCode::Splat, slot, a_slot, 0
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }

            OpKind::None(a) => {
                let a = a.borrow();
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, 0, OpCode::None, slot, a_slot, 0
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::All(lnpw2, a) => {
                let a = a.borrow();
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::All, slot, a_slot, 0
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Eq(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Eq, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Ne(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Ne, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::LtU(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::LtU, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::LtS(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::LtS, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::GtU(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::GtU, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::GtS(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::GtS, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::LeU(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::LeU, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::LeS(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::LeS, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::GeU(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::GeU, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::GeS(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::GeS, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::MinU(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::MinU, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::MinS(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::MinS, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::MaxU(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::MaxU, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::MaxS(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::MaxS, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Neg(lnpw2, a) => {
                let a = a.borrow();
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Neg, slot, a_slot, 0
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Abs(lnpw2, a) => {
                let a = a.borrow();
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Abs, slot, a_slot, 0
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Not(a) => {
                let a = a.borrow();
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, 0, OpCode::Not, slot, a_slot, 0
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Clz(lnpw2, a) => {
                let a = a.borrow();
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Clz, slot, a_slot, 0
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Ctz(lnpw2, a) => {
                let a = a.borrow();
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Ctz, slot, a_slot, 0
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Popcnt(lnpw2, a) => {
                let a = a.borrow();
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Popcnt, slot, a_slot, 0
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Add(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Add, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Sub(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Sub, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Mul(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Mul, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::And(a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, 0, OpCode::And, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Andnot(a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, 0, OpCode::Andnot, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Or(a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, 0, OpCode::Or, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Xor(a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, 0, OpCode::Xor, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Shl(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Shl, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::ShrU(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::ShrU, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::ShrS(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::ShrS, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Rotl(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Rotl, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind::Rotr(lnpw2, a, b) => {
                let a = a.borrow();
                let b = b.borrow();
                schedule! {
                    let (a_slot, a_npw2) = a.compile_pass2(state);
                    let (b_slot, b_npw2) = b.compile_pass2(state);
                }
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u64::from(OpIns::new(
                    T::NPW2, *lnpw2, OpCode::Rotr, slot, a_slot, b_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
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
            OpTree::<U16>::extend_s(0,
                OpTree::<U8>::imm(2u8)
            ),
            OpTree::<U16>::truncate(0,
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

        assert_eq!(bytecode.len(), 10);
        assert_eq!(stack.len(), 16);
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
            OpTree::<U32>::extend_u(0, b.clone()), OpTree::<U32>::extend_u(0, a.clone())
        );
        let fib_4 = OpTree::add(0,
            OpTree::<U64>::extend_u(0, fib_3.clone()), OpTree::<U64>::extend_u(0, b.clone())
        );
        let fib_5 = OpTree::add(0,
            OpTree::<U128>::extend_u(0, fib_4.clone()), OpTree::<U128>::extend_u(0, fib_3.clone())
        );
        let example = OpTree::and(
            OpTree::and(
                OpTree::<U8>::truncate(0, OpTree::eq(0, fib_3.clone(), c)),
                OpTree::<U8>::truncate(0, OpTree::eq(0, fib_4.clone(), d))
            ),
            OpTree::<U8>::truncate(0, OpTree::eq(0, fib_5.clone(), e))
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
        assert_eq!(stack.len(), 96);
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
            OpTree::<U32>::extend_u(0, b.clone()), OpTree::<U32>::extend_u(0, a.clone())
        );
        let fib_4 = OpTree::add(0,
            OpTree::<U64>::extend_u(0, fib_3.clone()), OpTree::<U64>::extend_u(0, b.clone())
        );
        let fib_5 = OpTree::add(0,
            OpTree::<U128>::extend_u(0, fib_4.clone()), OpTree::<U128>::extend_u(0, fib_3.clone())
        );
        let example = OpTree::and(
            OpTree::and(
                OpTree::<U8>::truncate(0, OpTree::eq(0, fib_3.clone(), c)),
                OpTree::<U8>::truncate(0, OpTree::eq(0, fib_4.clone(), d))
            ),
            OpTree::<U8>::truncate(0, OpTree::eq(0, fib_5.clone(), e))
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
        let big = OpTree::<U32>::extend_u(0, a);
        let i = OpTree::add(0,
            big.clone(),
            OpTree::add(0,
                big.clone(),
                OpTree::add(0,
                    OpTree::<U32>::extend_u(0, b),
                    OpTree::add(0,
                        OpTree::<U32>::extend_u(0, c),
                        OpTree::add(0,
                            OpTree::<U32>::extend_u(0, d),
                            OpTree::add(0,
                                OpTree::<U32>::extend_u(0, e),
                                OpTree::add(0,
                                    OpTree::<U32>::extend_u(0, f),
                                    OpTree::add(0,
                                        OpTree::<U32>::extend_u(0, g),
                                        OpTree::<U32>::extend_u(0, h)
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

        assert_eq!(bytecode.len(), 14);
        assert_eq!(stack.len(), 48);
    }
}

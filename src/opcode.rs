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
use crate::vm::exec_;
use std::cmp::max;
use std::cmp::min;
use std::collections::HashMap;
#[cfg(feature="opt-color-slots")]
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
///   |   '------------------------------- 3-bit npw2(lanes) or npw2(source size)
///   '----------------------------------- 3-bit npw2(size)
///
/// However there are 3 special instruction which use a 3-register format
///
/// select:
/// [-3-|-3-|01|--  8  --|--  8  --|--  8  --]
///   ^   ^         ^         ^         ^- 8-bit source slot
///   |   |         |         '----------- 8-bit destination slot
///   |   |         '--------------------- 8-bit predicate slot
///   |   '------------------------------- 3-bit npw2(lanes)
///   '----------------------------------- 3-bit npw2(size)
///
/// extract+replace:
/// [-3-|-3-|1r|--  8  --|--  8  --|--  8  --]
///   ^   ^         ^         ^         ^- 8-bit source slot
///   |   |         |         '----------- 8-bit destination slot
///   |   |         '--------------------- 8-bit lane number
///   |   '------------------------------- 3-bit npw2(lanes)
///   '----------------------------------- 3-bit npw2(size)
///
/// Most instructions are a fixed 32-bits, except for const instructions
/// which are followed by a 32-bit aligned little-endian immediate in the
/// instruction stream.
///
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[repr(u32)]
pub enum OpCode_ {
    Select        = 0x01000000,
    Extract       = 0x02000000,
    Replace       = 0x03000000,

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
    Shuffle       = 0x000c0000,

    None          = 0x000d0000,
    Any           = 0x000e0000,
    All           = 0x000f0000,
    Eq            = 0x00100000,
    Ne            = 0x00110000,
    LtU           = 0x00120000,
    LtS           = 0x00130000,
    GtU           = 0x00140000,
    GtS           = 0x00150000,
    LeU           = 0x00160000,
    LeS           = 0x00170000,
    GeU           = 0x00180000,
    GeS           = 0x00190000,
    MinU          = 0x001a0000,
    MinS          = 0x001b0000,
    MaxU          = 0x001c0000,
    MaxS          = 0x001d0000,

    Neg           = 0x001e0000,
    Abs           = 0x001f0000,
    Not           = 0x00200000,
    Clz           = 0x00210000,
    Ctz           = 0x00220000,
    Popcnt        = 0x00230000,
    Add           = 0x00240000,
    Sub           = 0x00250000,
    Mul           = 0x00260000,
    And           = 0x00270000,
    Andnot        = 0x00280000,
    Or            = 0x00290000,
    Xor           = 0x002a0000,
    Shl           = 0x002b0000,
    ShrU          = 0x002c0000,
    ShrS          = 0x002d0000,
    Rotl          = 0x002e0000,
    Rotr          = 0x002f0000,
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

impl fmt::Display for OpCode_ {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let name = match self {
            OpCode_::Select        => "select",
            OpCode_::Extract       => "extract",
            OpCode_::Replace       => "replace",

            OpCode_::Arg           => "arg",
            OpCode_::Ret           => "ret",

            OpCode_::ExtendConstU  => "extend_const_u",
            OpCode_::ExtendConstS  => "extend_const_s",
            OpCode_::SplatConst    => "splat_const",
            OpCode_::ExtendConst8U => "extend_const8_u",
            OpCode_::ExtendConst8S => "extend_const8_s",
            OpCode_::SplatConst8   => "splat_const8",
            OpCode_::ExtendU       => "extend_u",
            OpCode_::ExtendS       => "extend_s",
            OpCode_::Splat         => "splat",
            OpCode_::Shuffle       => "shuffle",

            OpCode_::None          => "none",
            OpCode_::Any           => "any",
            OpCode_::All           => "all",
            OpCode_::Eq            => "eq",
            OpCode_::Ne            => "ne",
            OpCode_::LtU           => "lt_u",
            OpCode_::LtS           => "lt_s",
            OpCode_::GtU           => "gt_u",
            OpCode_::GtS           => "gt_s",
            OpCode_::LeU           => "le_u",
            OpCode_::LeS           => "le_s",
            OpCode_::GeU           => "ge_u",
            OpCode_::GeS           => "ge_s",
            OpCode_::MinU          => "min_u",
            OpCode_::MinS          => "min_s",
            OpCode_::MaxU          => "max_u",
            OpCode_::MaxS          => "max_s",

            OpCode_::Neg           => "neg",
            OpCode_::Abs           => "abs",
            OpCode_::Not           => "not",
            OpCode_::Clz           => "clz",
            OpCode_::Ctz           => "ctz",
            OpCode_::Popcnt        => "popcnt",
            OpCode_::Add           => "add",
            OpCode_::Sub           => "sub",
            OpCode_::Mul           => "mul",
            OpCode_::And           => "and",
            OpCode_::Andnot        => "andnot",
            OpCode_::Or            => "or",
            OpCode_::Xor           => "xor",
            OpCode_::Shl           => "shl",
            OpCode_::ShrU          => "shr_u",
            OpCode_::ShrS          => "shr_s",
            OpCode_::Rotl          => "rotl",
            OpCode_::Rotr          => "rotr",
        };
        write!(fmt, "{}", name)
    }
}


/// An encoded instruction
#[derive(Debug, Copy, Clone)]
pub struct Op(u16);

/// An encoded instruction
#[derive(Debug, Copy, Clone)]
pub struct OpIns_(u32);

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

impl OpIns_ {
    /// Create a new instruction from its components
    #[inline]
    pub const fn new(
        npw2: u8,
        lnpw2: u8,
        opcode: OpCode_,
        p: u8,
        a: u8,
        b: u8
    ) -> OpIns_ {
        OpIns_(
            ((npw2 as u32) << 29)
                | ((lnpw2 as u32) << 26)
                | (opcode as u32)
                | ((p as u32) << 16)
                | ((a as u32) << 8)
                | ((b as u32) << 0)
        )
    }

    #[inline]
    pub fn opcode(&self) -> OpCode_ {
        let opcode = if self.0 & 0x03000000 != 0 {
            self.0 & 0x03000000
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
    pub fn xsize(&self) -> usize {
        1usize << self.lnpw2()
    }

    #[inline]
    pub fn xwidth(&self) -> usize {
        8*self.xsize()
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

impl From<Op> for u16 {
    fn from(op: Op) -> u16 {
        op.0
    }
}

impl From<OpIns_> for u32 {
    fn from(ins: OpIns_) -> u32 {
        ins.0
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

impl TryFrom<u32> for OpIns_ {
    type Error = Error;

    fn try_from(ins: u32) -> Result<Self, Self::Error> {
        // ensure opcode is valid
        match (ins & 0x03ff0000) >> 16 {
            0x100..=0x1ff => OpCode_::Select,
            0x200..=0x2ff => OpCode_::Extract,
            0x300..=0x3ff => OpCode_::Replace,

            0x001 => OpCode_::Arg,
            0x002 => OpCode_::Ret,

            0x003 => OpCode_::ExtendConstU,
            0x004 => OpCode_::ExtendConstS,
            0x005 => OpCode_::SplatConst,
            0x006 => OpCode_::ExtendConst8U,
            0x007 => OpCode_::ExtendConst8S,
            0x008 => OpCode_::SplatConst8,
            0x009 => OpCode_::ExtendU,
            0x00a => OpCode_::ExtendS,
            0x00b => OpCode_::Splat,
            0x00c => OpCode_::Shuffle,

            0x00d => OpCode_::None,
            0x00e => OpCode_::Any,
            0x00f => OpCode_::All,
            0x010 => OpCode_::Eq,
            0x011 => OpCode_::Ne,
            0x012 => OpCode_::LtU,
            0x013 => OpCode_::LtS,
            0x014 => OpCode_::GtU,
            0x015 => OpCode_::GtS,
            0x016 => OpCode_::LeU,
            0x017 => OpCode_::LeS,
            0x018 => OpCode_::GeU,
            0x019 => OpCode_::GeS,
            0x01a => OpCode_::MinU,
            0x01b => OpCode_::MinS,
            0x01c => OpCode_::MaxU,
            0x01d => OpCode_::MaxS,

            0x01e => OpCode_::Neg,
            0x020 => OpCode_::Abs,
            0x01f => OpCode_::Not,
            0x021 => OpCode_::Clz,
            0x022 => OpCode_::Ctz,
            0x023 => OpCode_::Popcnt,
            0x024 => OpCode_::Add,
            0x025 => OpCode_::Sub,
            0x026 => OpCode_::Mul,
            0x027 => OpCode_::And,
            0x028 => OpCode_::Andnot,
            0x029 => OpCode_::Or,
            0x02a => OpCode_::Xor,
            0x02b => OpCode_::Shl,
            0x02c => OpCode_::ShrU,
            0x02d => OpCode_::ShrS,
            0x02e => OpCode_::Rotl,
            0x02f => OpCode_::Rotr,

            _ => Err(Error::InvalidOpcode_(ins))?,
        };

        Ok(Self(ins))
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

impl fmt::Display for OpIns_ {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self.opcode() {
            OpCode_::Select => {
                write!(fmt, "u{}.{} r{}, r{}, r{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.opcode(),
                    self.p(),
                    self.a(),
                    self.b()
                )
            }

            // special format for moves because they are so common
            OpCode_::Extract if self.lnpw2() == 0 && self.p() == 0 => {
                write!(fmt, "u{}.move r{}, r{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.a(),
                    self.b()
                )
            }

            OpCode_::Extract => {
                write!(fmt, "u{}.{} r{}, r{}[{}]",
                    prefix(self.npw2(), self.lnpw2()),
                    self.opcode(),
                    self.a(),
                    self.b(),
                    self.p()
                )
            }

            OpCode_::Replace => {
                write!(fmt, "u{}.{} r{}[{}], r{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.opcode(),
                    self.a(),
                    self.p(),
                    self.b()
                )
            }

            // special format for moves because they are so common
            OpCode_::ExtendConstU if self.width() == self.xwidth() => {
                write!(fmt, "u{}.move_const r{}",
                    self.width(),
                    self.a()
                )
            }

            OpCode_::ExtendConstU | OpCode_::ExtendConstS | OpCode_::SplatConst => {
                write!(fmt, "u{}u{}.{} r{}",
                    self.width(),
                    self.xwidth(),
                    self.opcode(),
                    self.a()
                )
            }

            // special format for moves because they are so common
            OpCode_::ExtendConst8U if self.width() == self.xwidth() => {
                write!(fmt, "u{}.move_const8 r{}",
                    self.width(),
                    self.a()
                )
            }

            OpCode_::ExtendConst8U | OpCode_::ExtendConst8S | OpCode_::SplatConst8 => {
                write!(fmt, "u{}u{}.{} r{}",
                    self.width(),
                    self.xwidth(),
                    self.opcode(),
                    self.a()
                )
            }

            OpCode_::ExtendU | OpCode_::ExtendS | OpCode_::Splat => {
                write!(fmt, "u{}u{}.{} r{}, r{}",
                    self.width(),
                    self.xwidth(),
                    self.opcode(),
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

/// helper function for debugging
pub fn disas_<W: io::Write>(
    bytecode: &[u32],
    mut out: W
) -> Result<(), io::Error> {
    let mut i = 0;
    while i < bytecode.len() {
        let ins = bytecode[i];
        i += 1;

        match OpIns_::try_from(ins) {
            Ok(ins) => {
                match ins.opcode() {
                    OpCode_::ExtendConstU | OpCode_::ExtendConstS | OpCode_::SplatConst => {
                        let const_size = max(1, ins.xsize()/4);
                        write!(out, "    {:08x} {}, 0x", u32::from(ins), ins)?;
                        for j in (0..const_size).rev() {
                            write!(out, "{:0w$x}",
                                &bytecode[i+j],
                                w=2*min(4, ins.xsize())
                            )?;
                        }
                        writeln!(out)?;
                        for _ in 0..const_size {
                            writeln!(out, "    {:08x}", bytecode[i])?;
                            i += 1;
                        }
                    }
                    OpCode_::ExtendConst8U | OpCode_::ExtendConst8S | OpCode_::SplatConst8 => {
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

    /// Zero
    fn zero_() -> Self;

    /// A constant, non-secret 1
    ///
    /// Note, this needs to be here since thread-local storage can't
    /// depend on generic types
    fn one() -> Rc<OpTree<Self>>;

    /// One
    fn one_() -> Self;

    /// A constant with all bits set to 1, non-secret
    ///
    /// Note, this needs to be here since thread-local storage can't
    /// depend on generic types
    fn ones() -> Rc<OpTree<Self>>;

    /// All bits set to one
    fn ones_() -> Self;

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

    /// Can we compress into an extend_const_u instruction?
    fn is_extend_u_compressable(&self, npw2: u8) -> bool;

    /// Can we compress into an extend_const_s instruction?
    fn is_extend_s_compressable(&self, npw2: u8) -> bool;

    /// Can we compress into a splat_const instruction?
    fn is_splat_compressable(&self, npw2: u8) -> bool;

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

            fn zero_() -> Self {
                [0; $n]
            }

            fn one_() -> Self {
                let mut one = [0; $n];
                one[0] = 1;
                Self::try_from(one).unwrap()
            }

            fn ones_() -> Self {
                [0xff; $n]
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
                self == &Self::zero_()
            }

            fn is_one(&self) -> bool {
                // don't know an easier way to build this
                let mut one = [0; $n];
                one[0] = 1;
                self == &Self::one_()
            }

            fn is_ones(&self) -> bool {
                self == &Self::ones_()
            }

            fn is_extend_u_compressable(&self, npw2: u8) -> bool {
                let width = 1usize << npw2;
                self[width..].iter().all(|b| *b == 0)
            }

            fn is_extend_s_compressable(&self, npw2: u8) -> bool {
                let width = 1usize << npw2;
                if self[width-1] & 0x80 == 0x80 {
                    self[width..].iter().all(|b| *b == 0xff)
                } else {
                    self[width..].iter().all(|b| *b == 0x00)
                }
            }

            fn is_splat_compressable(&self, npw2: u8) -> bool {
                let width = 1usize << npw2;
                (width..$n).step_by(width).all(|i| &self[i..i+width] == &self[..width])
            }

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

/// Kinds of operations in tree
#[derive(Debug)]
pub enum OpKind_<T: OpType> {
    Imm(T),
    Sym(&'static str),

    Select(u8, Rc<OpTree_<T>>, Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    Extract(u8, Rc<dyn DynOpTree_>),
    Replace(u8, Rc<OpTree_<T>>, Rc<dyn DynOpTree_>),

    ExtendU(Rc<dyn DynOpTree_>),
    ExtendS(Rc<dyn DynOpTree_>),
    Splat(Rc<dyn DynOpTree_>),
    Shuffle(u8, Rc<OpTree_<T>>, Rc<OpTree_<T>>),

    None(Rc<OpTree_<T>>),
    Any(Rc<OpTree_<T>>),
    All(u8, Rc<OpTree_<T>>),
    Eq(u8, Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    Ne(u8, Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    LtU(u8, Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    LtS(u8, Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    GtU(u8, Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    GtS(u8, Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    LeU(u8, Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    LeS(u8, Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    GeU(u8, Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    GeS(u8, Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    MinU(u8, Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    MinS(u8, Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    MaxU(u8, Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    MaxS(u8, Rc<OpTree_<T>>, Rc<OpTree_<T>>),

    Neg(u8, Rc<OpTree_<T>>),
    Abs(u8, Rc<OpTree_<T>>),
    Not(Rc<OpTree_<T>>),
    Clz(u8, Rc<OpTree_<T>>),
    Ctz(u8, Rc<OpTree_<T>>),
    Popcnt(u8, Rc<OpTree_<T>>),
    Add(u8, Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    Sub(u8, Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    Mul(u8, Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    And(Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    Andnot(Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    Or(Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    Xor(Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    Shl(u8, Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    ShrU(u8, Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    ShrS(u8, Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    Rotl(u8, Rc<OpTree_<T>>, Rc<OpTree_<T>>),
    Rotr(u8, Rc<OpTree_<T>>, Rc<OpTree_<T>>),
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
    #[cfg(feature="opt-fold-consts")]
    folded: RefCell<Option<Option<Rc<OpTree<T>>>>>,
}

/// Tree of operations, including metadata to deduplicate
/// common branches
#[derive(Debug)]
pub struct OpTree_<T: OpType> {
    kind: OpKind_<T>,
    refs: Cell<u32>,
    slot: Cell<Option<u8>>,
    const_: bool,
    sym: bool,
    #[cfg(feature="opt-fold-consts")]
    folded: RefCell<Option<Option<Rc<OpTree_<T>>>>>,
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
    bytecode: Vec<u8>,
    stack: Vec<u8>,

    slot_pool: SlotPool,

    sp: usize,
    max_sp: usize,
    max_npw2: u8,
}

/// Compilation state
pub struct OpCompile_ {
    bytecode: Vec<u32>,
    slots: Vec<u8>,

    #[allow(dead_code)]
    opt: bool,
    slot_pool: SlotPool,
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

impl OpCompile_ {
    fn new(opt: bool) -> OpCompile_ {
        OpCompile_ {
            bytecode: Vec::new(),
            slots: Vec::new(),

            opt: opt,
            slot_pool: SlotPool::new(),
        }
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
            #[cfg(feature="opt-fold-consts")]
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
                // TODO use decode?
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

/// Core OpTree type
impl<T: OpType> OpTree_<T> {
    fn new(kind: OpKind_<T>, const_: bool, sym: bool) -> OpTree_<T> {
        OpTree_ {
            kind: kind,
            refs: Cell::new(0),
            slot: Cell::new(None),
            const_: const_,
            sym: sym,
            #[cfg(feature="opt-fold-consts")]
            folded: RefCell::new(None),
        }
    }

    /// Create an immediate, secret value
    pub fn imm(v: T) -> Rc<Self> {
        Rc::new(Self::new(OpKind_::Imm(v), false, false))
    }

    /// Create a const susceptable to compiler optimizations
    pub fn const_(v: T) -> Rc<Self> {
        Rc::new(Self::new(OpKind_::Imm(v), true, false))
    }

    /// A constant 0
    pub fn zero() -> Rc<Self> {
        Self::const_(T::zero_())
    }

    /// A constant 1
    pub fn one() -> Rc<Self> {
        Self::const_(T::one_())
    }

    /// A constant with all bits set to 1
    pub fn ones() -> Rc<Self> {
        Self::const_(T::ones_())
    }

    // Constructors for other tree nodes, note that
    // constant-ness is propogated
    pub fn sym(name: &'static str) -> Rc<Self> {
        Rc::new(Self::new(OpKind_::Sym(name), false, true))
    }

    pub fn select(lnpw2: u8, p: Rc<Self>, a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = p.is_const() && a.is_const() && b.is_const();
        let sym    = p.is_sym()   || a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::Select(lnpw2, p, a, b), const_, sym))
    }

    pub fn extract(x: u8, a: Rc<dyn DynOpTree_>) -> Rc<Self> {
        let const_ = a.is_const();
        let sym    = a.is_sym();
        Rc::new(Self::new(OpKind_::Extract(x, a), const_, sym))
    }

    pub fn replace(x: u8, a: Rc<Self>, b: Rc<dyn DynOpTree_>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || a.is_sym();
        Rc::new(Self::new(OpKind_::Replace(x, a, b), const_, sym))
    }

    pub fn extend_u(a: Rc<dyn DynOpTree_>) -> Rc<Self> {
        let const_ = a.is_const();
        let sym    = a.is_sym();
        Rc::new(Self::new(OpKind_::ExtendU(a), const_, sym))
    }

    pub fn extend_s(a: Rc<dyn DynOpTree_>) -> Rc<Self> {
        let const_ = a.is_const();
        let sym    = a.is_sym();
        Rc::new(Self::new(OpKind_::ExtendS(a), const_, sym))
    }

    pub fn splat(a: Rc<dyn DynOpTree_>) -> Rc<Self> {
        let const_ = a.is_const();
        let sym    = a.is_sym();
        Rc::new(Self::new(OpKind_::Splat(a), const_, sym))
    }

    pub fn shuffle(lnpw2: u8, a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::Shuffle(lnpw2, a, b), const_, sym))
    }

    pub fn none(a: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const();
        let sym    = a.is_sym();
        Rc::new(Self::new(OpKind_::None(a), const_, sym))
    }

    pub fn any(a: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const();
        let sym    = a.is_sym();
        Rc::new(Self::new(OpKind_::Any(a), const_, sym))
    }

    pub fn all(lnpw2: u8, a: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const();
        let sym    = a.is_sym();
        Rc::new(Self::new(OpKind_::All(lnpw2, a), const_, sym))
    }

    pub fn eq(lnpw2: u8, a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::Eq(lnpw2, a, b), const_, sym))
    }

    pub fn ne(lnpw2: u8, a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::Ne(lnpw2, a, b), const_, sym))
    }

    pub fn lt_u(lnpw2: u8, a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::LtU(lnpw2, a, b), const_, sym))
    }

    pub fn lt_s(lnpw2: u8, a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::LtS(lnpw2, a, b), const_, sym))
    }

    pub fn gt_u(lnpw2: u8, a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::GtU(lnpw2, a, b), const_, sym))
    }

    pub fn gt_s(lnpw2: u8, a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::GtS(lnpw2, a, b), const_, sym))
    }

    pub fn le_u(lnpw2: u8, a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::LeU(lnpw2, a, b), const_, sym))
    }

    pub fn le_s(lnpw2: u8, a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::LeS(lnpw2, a, b), const_, sym))
    }

    pub fn ge_u(lnpw2: u8, a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::GeU(lnpw2, a, b), const_, sym))
    }

    pub fn ge_s(lnpw2: u8, a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::GeS(lnpw2, a, b), const_, sym))
    }

    pub fn min_u(lnpw2: u8, a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::MinU(lnpw2, a, b), const_, sym))
    }

    pub fn min_s(lnpw2: u8, a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::MinS(lnpw2, a, b), const_, sym))
    }

    pub fn max_u(lnpw2: u8, a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::MaxU(lnpw2, a, b), const_, sym))
    }

    pub fn max_s(lnpw2: u8, a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::MaxS(lnpw2, a, b), const_, sym))
    }

    pub fn neg(lnpw2: u8, a: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const();
        let sym    = a.is_sym();
        Rc::new(Self::new(OpKind_::Neg(lnpw2, a), const_, sym))
    }

    pub fn abs(lnpw2: u8, a: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const();
        let sym    = a.is_sym();
        Rc::new(Self::new(OpKind_::Abs(lnpw2, a), const_, sym))
    }

    pub fn not(a: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const();
        let sym    = a.is_sym();
        Rc::new(Self::new(OpKind_::Not(a), const_, sym))
    }

    pub fn clz(lnpw2: u8, a: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const();
        let sym    = a.is_sym();
        Rc::new(Self::new(OpKind_::Clz(lnpw2, a), const_, sym))
    }

    pub fn ctz(lnpw2: u8, a: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const();
        let sym    = a.is_sym();
        Rc::new(Self::new(OpKind_::Ctz(lnpw2, a), const_, sym))
    }

    pub fn popcnt(lnpw2: u8, a: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const();
        let sym    = a.is_sym();
        Rc::new(Self::new(OpKind_::Popcnt(lnpw2, a), const_, sym))
    }

    pub fn add(lnpw2: u8, a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::Add(lnpw2, a, b), const_, sym))
    }

    pub fn sub(lnpw2: u8, a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::Sub(lnpw2, a, b), const_, sym))
    }

    pub fn mul(lnpw2: u8, a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::Mul(lnpw2, a, b), const_, sym))
    }

    pub fn and(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::And(a, b), const_, sym))
    }

    pub fn andnot(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::Andnot(a, b), const_, sym))
    }

    pub fn or(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::Or(a, b), const_, sym))
    }

    pub fn xor(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::Xor(a, b), const_, sym))
    }

    pub fn shl(lnpw2: u8, a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::Shl(lnpw2, a, b), const_, sym))
    }

    pub fn shr_u(lnpw2: u8, a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::ShrU(lnpw2, a, b), const_, sym))
    }

    pub fn shr_s(lnpw2: u8, a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::ShrS(lnpw2, a, b), const_, sym))
    }

    pub fn rotl(lnpw2: u8, a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::Rotl(lnpw2, a, b), const_, sym))
    }

    pub fn rotr(lnpw2: u8, a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        let const_ = a.is_const() && b.is_const();
        let sym    = a.is_sym()   || b.is_sym();
        Rc::new(Self::new(OpKind_::Rotr(lnpw2, a, b), const_, sym))
    }

    /// Downcast a generic OpTree, panicing if types do not match
    pub fn downcast(a: Rc<dyn DynOpTree_>) -> Rc<OpTree_<T>> {
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
    pub fn compile(&self, opt: bool) -> (Vec<u32>, AlignedBytes) {
        // should we do a constant folding pass?
        #[cfg(feature="opt-fold-consts")]
        if opt {
            self.fold_consts();
        }

        // debug?
        #[cfg(feature="debug-trees")]
        if opt {
            println!("tree:");
            self.disas(io::stdout()).unwrap();
        }

        // NOTE! We make sure to zero all refs from pass1 to pass2, this is
        // rather fragile and requires all passes to always be run as a pair,
        // we can't interrupt between passes without needing to reset all
        // internal reference counts

        let mut state = OpCompile_::new(opt);

        // first pass to find number of immediates and deduplicate branches
        self.compile_pass1(&mut state);

        // second pass now to compile the bytecode and stack, note sp now points
        // to end of immediates
        let (slot, _) = self.compile_pass2(&mut state);

        // to make lifetimes work in order to figure out slot reuse, reference
        // counting for is left up to the caller
        let refs = self.dec_refs();
        debug_assert_eq!(refs, 0);

        // add required return instruction
        state.bytecode.push(u32::from(OpIns_::new(
            T::NPW2, 0, OpCode_::Ret, 0, 0, slot
        )));

        // align bytecode
//        // TODO could we transmute this somehow?
//        let mut aligned_bytecode = AlignedBytes::new_zeroed(4*state.bytecode.len(), 4);
//        for i in 0..state.bytecode.len() {
//            aligned_bytecode[4*i..4*i+4].copy_from_slice(
//                &state.bytecode[i].to_le_bytes()
//            );
//        }

        // align slots
        let mut aligned_slots = AlignedBytes::new_zeroed(
            state.slot_pool.size,
            1usize << state.slot_pool.max_npw2
        );
        aligned_slots[..state.slots.len()].copy_from_slice(&state.slots);

        #[cfg(feature="debug-bytecode")]
        if opt {
            println!("slots:");
            print!("   ");
            for b in aligned_slots.iter() {
                 print!(" {:02x}", b);
            }
            println!();

            println!("bytecode:");
            disas_(&state.bytecode, io::stdout()).unwrap();
        }

        // imms is now the initial stack pointer
        (state.bytecode, aligned_slots)
    }

    /// compile and execute if value is not an immediate or constant already
    pub fn eval(&self) -> Result<T, Error> {
        match self.kind {
            OpKind_::Imm(v) => Ok(v),
            _ => {
                let (bytecode, mut stack) = self.compile(false);
                let mut res = exec_(&bytecode, &mut stack)?;
                let v = T::decode(&mut res).map_err(|_| Error::InvalidReturn)?;
                Ok(v)
            }
        }
    }

    /// Assuming we are Sym, patch the stack during a call
    pub fn patch(&self, v: T, stack: &mut [u8]) {
        assert!(
            match self.kind {
                OpKind_::Sym(_) => true,
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
    #[cfg(feature="opt-fold-consts")]
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

// dyn-compatible wrapping trait
pub trait DynOpTree_: Debug {
    /// npw2(size), used as a part of instruction encoding
    fn npw2(&self) -> u8;

    /// type's size in bytes, needed for determining cast sizes
    fn size(&self) -> usize;

    /// type's width in bits
    fn width(&self) -> usize;

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

    /// hook to enable none without known type
    fn dyn_not(&self) -> &'static dyn Fn(Rc<dyn DynOpTree_>) -> Rc<dyn DynOpTree_>;

    /// hook to enable none without known type
    fn dyn_none(&self) -> &'static dyn Fn(Rc<dyn DynOpTree_>) -> Rc<dyn DynOpTree_>;

    /// hook to enable any without known type
    fn dyn_any(&self) -> &'static dyn Fn(Rc<dyn DynOpTree_>) -> Rc<dyn DynOpTree_>;

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

    /// An optional pass to fold consts in the tree
    #[cfg(feature="opt-fold-consts")]
    fn fold_consts(&self);

    /// First compile pass, used to find the number of immediates
    /// for offset calculation, and local reference counting to
    /// deduplicate branches.
    fn compile_pass1(&self, state: &mut OpCompile_);

    /// Second compile pass, used to actually compile both the
    /// immediates and bytecode. Returns the resulting slot + npw2.
    fn compile_pass2(&self, state: &mut OpCompile_) -> (u8, u8);
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
        #[cfg(feature="opt-fold-consts")]
        match (self.is_const(), &self.kind, &*self.folded.borrow()) {
            (true, OpKind::Imm(v), _            ) => v.is_zero(),
            (true, _,              Some(Some(x))) => x.is_zero(),
            _                                     => false,
        }
        #[cfg(not(feature="opt-fold-consts"))]
        match (self.is_const(), &self.kind) {
            (true, OpKind::Imm(v)) => v.is_zero(),
            _                      => false,
        }
    }

    fn is_one(&self) -> bool {
        #[cfg(feature="opt-fold-consts")]
        match (self.is_const(), &self.kind, &*self.folded.borrow()) {
            (true, OpKind::Imm(v), _            ) => v.is_one(),
            (true, _,              Some(Some(x))) => x.is_one(),
            _                                     => false,
        }
        #[cfg(not(feature="opt-fold-consts"))]
        match (self.is_const(), &self.kind) {
            (true, OpKind::Imm(v)) => v.is_one(),
            _                      => false,
        }
    }

    fn is_ones(&self) -> bool {
        #[cfg(feature="opt-fold-consts")]
        match (self.is_const(), &self.kind, &*self.folded.borrow()) {
            (true, OpKind::Imm(v), _            ) => v.is_ones(),
            (true, _,              Some(Some(x))) => x.is_ones(),
            _                                     => false,
        }
        #[cfg(not(feature="opt-fold-consts"))]
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
        #[cfg(feature="opt-fold-consts")]
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
        #[cfg(feature="opt-fold-consts")]
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

    #[cfg(feature="opt-fold-consts")]
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
        #[cfg(feature="opt-fold-consts")]
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
        #[cfg(feature="opt-fold-consts")]
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

impl<T: OpType> DynOpTree_ for OpTree_<T> {
    fn npw2(&self) -> u8 {
        T::NPW2
    }

    fn size(&self) -> usize {
        T::SIZE
    }

    fn width(&self) -> usize {
        T::WIDTH
    }

    fn is_imm(&self) -> bool {
        match self.kind {
            OpKind_::Imm(_) => true,
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
        #[cfg(feature="opt-fold-consts")]
        match (self.is_const(), &self.kind, &*self.folded.borrow()) {
            (true, OpKind_::Imm(v), _            ) => v.is_zero(),
            (true, _,               Some(Some(x))) => x.is_zero(),
            _                                     => false,
        }
        #[cfg(not(feature="opt-fold-consts"))]
        match (self.is_const(), &self.kind) {
            (true, OpKind_::Imm(v)) => v.is_zero(),
            _                       => false,
        }
    }

    fn is_one(&self) -> bool {
        #[cfg(feature="opt-fold-consts")]
        match (self.is_const(), &self.kind, &*self.folded.borrow()) {
            (true, OpKind_::Imm(v), _            ) => v.is_one(),
            (true, _,               Some(Some(x))) => x.is_one(),
            _                                     => false,
        }
        #[cfg(not(feature="opt-fold-consts"))]
        match (self.is_const(), &self.kind) {
            (true, OpKind_::Imm(v)) => v.is_zero(),
            _                       => false,
        }
    }

    fn is_ones(&self) -> bool {
        #[cfg(feature="opt-fold-consts")]
        match (self.is_const(), &self.kind, &*self.folded.borrow()) {
            (true, OpKind_::Imm(v), _            ) => v.is_ones(),
            (true, _,               Some(Some(x))) => x.is_ones(),
            _                                      => false,
        }
        #[cfg(not(feature="opt-fold-consts"))]
        match (self.is_const(), &self.kind) {
            (true, OpKind_::Imm(v)) => v.is_zero(),
            _                       => false,
        }
    }

    fn dyn_not(&self) -> &'static dyn Fn(Rc<dyn DynOpTree_>) -> Rc<dyn DynOpTree_> {
        // bit messy but this works
        // unfortunately this only works when there is a single argument
        fn not<T: OpType>(tree: Rc<dyn DynOpTree_>) -> Rc<dyn DynOpTree_> {
            OpTree_::not(OpTree_::<T>::downcast(tree))
        }
        &not::<T>
    }

    // TODO do we still need these? should we have these for all unops?
    fn dyn_none(&self) -> &'static dyn Fn(Rc<dyn DynOpTree_>) -> Rc<dyn DynOpTree_> {
        // bit messy but this works
        // unfortunately this only works when there is a single argument
        fn none<T: OpType>(tree: Rc<dyn DynOpTree_>) -> Rc<dyn DynOpTree_> {
            OpTree_::none(OpTree_::<T>::downcast(tree))
        }
        &none::<T>
    }

    fn dyn_any(&self) -> &'static dyn Fn(Rc<dyn DynOpTree_>) -> Rc<dyn DynOpTree_> {
        // bit messy but this works
        // unfortunately this only works when there is a single argument
        fn any<T: OpType>(tree: Rc<dyn DynOpTree_>) -> Rc<dyn DynOpTree_> {
            OpTree_::any(OpTree_::<T>::downcast(tree))
        }
        &any::<T>
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
            OpKind_::Imm(_) => {},
            OpKind_::Sym(_) => {},

            OpKind_::Select(_, p, a, b) => {
                p.disas_pass1();
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::Extract(_, a) => {
                a.disas_pass1();
            }
            OpKind_::Replace(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind_::ExtendU(a) => {
                a.disas_pass1();
            }
            OpKind_::ExtendS(a) => {
                a.disas_pass1();
            }
            OpKind_::Splat(a) => {
                a.disas_pass1();
            }
            OpKind_::Shuffle(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind_::None(a) => {
                a.disas_pass1();
            }
            OpKind_::Any(a) => {
                a.disas_pass1();
            }
            OpKind_::All(_, a) => {
                a.disas_pass1();
            }
            OpKind_::Eq(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::Ne(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::LtU(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::LtS(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::GtU(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::GtS(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::LeU(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::LeS(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::GeU(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::GeS(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::MinU(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::MinS(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::MaxU(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::MaxS(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }

            OpKind_::Neg(_, a) => {
                a.disas_pass1();
            }
            OpKind_::Abs(_, a) => {
                a.disas_pass1();
            }
            OpKind_::Not(a) => {
                a.disas_pass1();
            }
            OpKind_::Clz(_, a) => {
                a.disas_pass1();
            }
            OpKind_::Ctz(_, a) => {
                a.disas_pass1();
            }
            OpKind_::Popcnt(_, a) => {
                a.disas_pass1();
            }
            OpKind_::Add(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::Sub(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::Mul(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::And(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::Andnot(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::Or(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::Xor(a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::Shl(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::ShrU(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::ShrS(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::Rotl(_, a, b) => {
                a.disas_pass1();
                b.disas_pass1();
            }
            OpKind_::Rotr(_, a, b) => {
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
            OpKind_::Imm(v) if self.is_const() => format!("(u{}.const {})",
                T::WIDTH,
                v.hex()
            ),
            OpKind_::Imm(v) => format!("(u{}.imm {})",
                T::WIDTH,
                v.hex()
            ),
            OpKind_::Sym(s) => format!("(u{}.sym {:?})",
                T::WIDTH,
                s
            ),

            OpKind_::Select(lnpw2, p, a, b) => format!("(u{}.select {} {} {})",
                prefix(T::NPW2, *lnpw2),
                p.disas_pass2(names, arbitrary_names, stmts)?,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind_::Extract(x, a) => format!("(u{}.extract {} {})",
                prefix(a.npw2(), a.npw2()-T::NPW2),
                x,
                a.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind_::Replace(x, a, b) => format!("(u{}.replace {} {} {})",
                prefix(T::NPW2, T::NPW2-b.npw2()),
                x,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?
            ),

            OpKind_::ExtendU(a) => format!("(u{}.extend_u {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind_::ExtendS(a) => format!("(u{}.extend_s {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind_::Splat(a) => format!("(u{}.splat {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind_::Shuffle(lnpw2, a, b) => format!("(u{}.shuffle {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?
            ),

            OpKind_::None(a) => format!("(u{}.none {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind_::Any(a) => format!("(u{}.any {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind_::All(lnpw2, a) => format!("(u{}.all {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind_::Eq(lnpw2, a, b) => format!("(u{}.eq {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind_::Ne(lnpw2, a, b) => format!("(u{}.ne {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind_::LtU(lnpw2, a, b) => format!("(u{}.lt_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind_::LtS(lnpw2, a, b) => format!("(u{}.lt_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind_::GtU(lnpw2, a, b) => format!("(u{}.gt_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind_::GtS(lnpw2, a, b) => format!("(u{}.gt_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind_::LeU(lnpw2, a, b) => format!("(u{}.le_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind_::LeS(lnpw2, a, b) => format!("(u{}.le_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind_::GeU(lnpw2, a, b) => format!("(u{}.ge_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind_::GeS(lnpw2, a, b) => format!("(u{}.ge_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind_::MinU(lnpw2, a, b) => format!("(u{}.min_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind_::MinS(lnpw2, a, b) => format!("(u{}.min_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind_::MaxU(lnpw2, a, b) => format!("(u{}.max_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind_::MaxS(lnpw2, a, b) => format!("(u{}.max_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),

            OpKind_::Neg(lnpw2, a) => format!("(u{}.neg {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind_::Abs(lnpw2, a) => format!("(u{}.abs {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind_::Not(a) => format!("(u{}.not {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind_::Clz(lnpw2, a) => format!("(u{}.clz {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind_::Ctz(lnpw2, a) => format!("(u{}.ctz {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind_::Popcnt(lnpw2, a) => format!("(u{}.popcnt {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?
            ),
            OpKind_::Add(lnpw2, a, b) => format!("(u{}.add {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind_::Sub(lnpw2, a, b) => format!("(u{}.sub {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind_::Mul(lnpw2, a, b) => format!("(u{}.mul {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind_::And(a, b) => format!("(u{}.and {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind_::Andnot(a, b) => format!("(u{}.andnot {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind_::Or(a, b) => format!("(u{}.or {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind_::Xor(a, b) => format!("(u{}.xor {} {})",
                T::WIDTH,
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind_::Shl(lnpw2, a, b) => format!("(u{}.shl {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind_::ShrU(lnpw2, a, b) => format!("(u{}.shr_u {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind_::ShrS(lnpw2, a, b) => format!("(u{}.shr_s {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind_::Rotl(lnpw2, a, b) => format!("(u{}.rotl {} {})",
                prefix(T::NPW2, *lnpw2),
                a.disas_pass2(names, arbitrary_names, stmts)?,
                b.disas_pass2(names, arbitrary_names, stmts)?,
            ),
            OpKind_::Rotr(lnpw2, a, b) => format!("(u{}.rotr {} {})",
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

    #[cfg(feature="opt-fold-consts")]
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
            OpKind_::Imm(_) => {},
            OpKind_::Sym(_) => {},

            OpKind_::Select(_, p, a, b) => {
                p.fold_consts();
                a.fold_consts();
                b.fold_consts();
            }
            OpKind_::Extract(_, a) => {
                a.fold_consts();
            }
            OpKind_::Replace(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }

            OpKind_::ExtendU(a) => {
                a.fold_consts();
            }
            OpKind_::ExtendS(a) => {
                a.fold_consts();
            }
            OpKind_::Splat(a) => {
                a.fold_consts();
            }
            OpKind_::Shuffle(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }

            OpKind_::None(a) => {
                a.fold_consts();
            }
            OpKind_::Any(a) => {
                a.fold_consts();
            }
            OpKind_::All(_, a) => {
                a.fold_consts();
            }
            OpKind_::Eq(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind_::Ne(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind_::LtU(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind_::LtS(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind_::GtU(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind_::GtS(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind_::LeU(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind_::LeS(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind_::GeU(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind_::GeS(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind_::MinU(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind_::MinS(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind_::MaxU(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }
            OpKind_::MaxS(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
            }

            OpKind_::Neg(_, a) => {
                a.fold_consts();
            }
            OpKind_::Abs(_, a) => {
                a.fold_consts();
            }
            OpKind_::Not(a) => {
                a.fold_consts();
            }
            OpKind_::Clz(_, a) => {
                a.fold_consts();
            }
            OpKind_::Ctz(_, a) => {
                a.fold_consts();
            }
            OpKind_::Popcnt(_, a) => {
                a.fold_consts();
            }
            OpKind_::Add(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
                #[cfg(feature="opt-fold-nops")]
                if a.is_zero() {
                    self.folded.replace(Some(Some(b.clone())));
                } else if b.is_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
            OpKind_::Sub(_, a, b) => {
                a.fold_consts();
                b.fold_consts();
                #[cfg(feature="opt-fold-nops")]
                if b.is_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
            OpKind_::Mul(x, a, b) => {
                a.fold_consts();
                b.fold_consts();
                #[cfg(feature="opt-fold-nops")]
                if *x == 0 && a.is_one() {
                    self.folded.replace(Some(Some(b.clone())));
                } else if *x == 0 && b.is_one() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
            OpKind_::And(a, b) => {
                a.fold_consts();
                b.fold_consts();
                #[cfg(feature="opt-fold-nops")]
                if a.is_ones() {
                    self.folded.replace(Some(Some(b.clone())));
                } else if b.is_ones() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
            OpKind_::Andnot(a, b) => {
                a.fold_consts();
                b.fold_consts();
                #[cfg(feature="opt-fold-nops")]
                if a.is_ones() {
                    self.folded.replace(Some(Some(b.clone())));
                } else if b.is_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
            OpKind_::Or(a, b) => {
                a.fold_consts();
                b.fold_consts();
                #[cfg(feature="opt-fold-nops")]
                if a.is_zero() {
                    self.folded.replace(Some(Some(b.clone())));
                } else if b.is_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
            OpKind_::Xor(a, b) => {
                a.fold_consts();
                b.fold_consts();
                #[cfg(feature="opt-fold-nops")]
                if a.is_zero() {
                    self.folded.replace(Some(Some(b.clone())));
                } else if b.is_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
            OpKind_::Shl(x, a, b) => {
                a.fold_consts();
                b.fold_consts();
                #[cfg(feature="opt-fold-nops")]
                if *x == 0 && b.is_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
            OpKind_::ShrU(x, a, b) => {
                a.fold_consts();
                b.fold_consts();
                #[cfg(feature="opt-fold-nops")]
                if *x == 0 && b.is_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
            OpKind_::ShrS(x, a, b) => {
                a.fold_consts();
                b.fold_consts();
                #[cfg(feature="opt-fold-nops")]
                if *x == 0 && b.is_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
            OpKind_::Rotl(x, a, b) => {
                a.fold_consts();
                b.fold_consts();
                #[cfg(feature="opt-fold-nops")]
                if *x == 0 && b.is_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
            OpKind_::Rotr(x, a, b) => {
                a.fold_consts();
                b.fold_consts();
                #[cfg(feature="opt-fold-nops")]
                if *x == 0 && b.is_zero() {
                    self.folded.replace(Some(Some(a.clone())));
                }
            }
        }
    }

    fn compile_pass1(&self, state: &mut OpCompile_) {
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
            OpKind_::Imm(v) => {
                if self.const_ {
                    // handle consts later
                    return;
                }

                // allocate slot
                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                self.slot.set(Some(slot));

                // write imm to slots
                if state.slots.len() < (usize::from(slot)+1) << T::NPW2 {
                    state.slots.resize((usize::from(slot)+1) << T::NPW2, 0);
                }

                v.encode(&mut &mut state.slots[
                    usize::from(slot) << T::NPW2
                        .. (usize::from(slot)+1) << T::NPW2
                ]).unwrap();

                // initialize arg in bytecode
                state.bytecode.push(u32::from(OpIns_::new(
                    T::NPW2, 0, OpCode_::Arg, 0, slot, slot
                )));
            }
            OpKind_::Sym(_) => {
                assert!(!self.const_);

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
                state.bytecode.push(u32::from(OpIns_::new(
                    T::NPW2, 0, OpCode_::Arg, 0, slot, slot
                )));
            }

            OpKind_::Select(_, p, a, b) => {
                p.compile_pass1(state);
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::Extract(_, a) => {
                a.compile_pass1(state);
            }
            OpKind_::Replace(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind_::ExtendU(a) => {
                a.compile_pass1(state);
            }
            OpKind_::ExtendS(a) => {
                a.compile_pass1(state);
            }
            OpKind_::Splat(a) => {
                a.compile_pass1(state);
            }
            OpKind_::Shuffle(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind_::None(a) => {
                a.compile_pass1(state);
            }
            OpKind_::Any(a) => {
                a.compile_pass1(state);
            }
            OpKind_::All(_, a) => {
                a.compile_pass1(state);
            }
            OpKind_::Eq(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::Ne(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::LtU(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::LtS(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::GtU(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::GtS(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::LeU(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::LeS(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::GeU(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::GeS(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::MinU(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::MinS(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::MaxU(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::MaxS(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }

            OpKind_::Neg(_, a) => {
                a.compile_pass1(state);
            }
            OpKind_::Abs(_, a) => {
                a.compile_pass1(state);
            }
            OpKind_::Not(a) => {
                a.compile_pass1(state);
            }
            OpKind_::Clz(_, a) => {
                a.compile_pass1(state);
            }
            OpKind_::Ctz(_, a) => {
                a.compile_pass1(state);
            }
            OpKind_::Popcnt(_, a) => {
                a.compile_pass1(state);
            }
            OpKind_::Add(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::Sub(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::Mul(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::And(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::Andnot(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::Or(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::Xor(a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::Shl(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::ShrU(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::ShrS(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::Rotl(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
            OpKind_::Rotr(_, a, b) => {
                a.compile_pass1(state);
                b.compile_pass1(state);
            }
        }
    }

    fn compile_pass2(&self, state: &mut OpCompile_) -> (u8, u8) {
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
            OpKind_::Imm(v) => {
                // variable imms handled on first pass
                assert!(self.const_);

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                #[allow(unused_mut)] let mut best_npw2 = T::NPW2;
                #[allow(unused_mut)] let mut best_ins8 = OpCode_::ExtendConst8U;
                #[allow(unused_mut)] let mut best_ins = OpCode_::ExtendConstU;

                // can we use a smaller encoding?
                #[cfg(feature="opt-compress-consts")]
                {
                    if state.opt {
                        for npw2 in 0..T::NPW2 {
                            if v.is_extend_u_compressable(npw2) {
                                best_npw2 = npw2;
                                best_ins8 = OpCode_::ExtendConst8U;
                                best_ins  = OpCode_::ExtendConstU;
                                break;
                            } else if v.is_extend_s_compressable(npw2) {
                                best_npw2 = npw2;
                                best_ins8 = OpCode_::ExtendConst8S;
                                best_ins  = OpCode_::ExtendConstS;
                                break;
                            } else if v.is_splat_compressable(npw2) {
                                best_npw2 = npw2;
                                best_ins8 = OpCode_::SplatConst8;
                                best_ins  = OpCode_::SplatConst;
                                break;
                            }
                        }
                    }
                }

                // fall back to uncompressed encodings
                if best_npw2 == 0 {
                    // u8s can fit directly in instruction

                    // TODO can this be more efficient (and less ugly)
                    let mut buf = Vec::new();
                    v.encode(&mut buf).unwrap();
                    buf.truncate(1 << best_npw2);
                    debug_assert!(buf.len() == 1);

                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, best_ins8, 0, slot, buf[0]
                    )));
                } else {
                    // encode const into bytecode stream
                    // TODO compressed encoding schemes?
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, best_npw2, best_ins, 0, slot, 0
                    )));

                    // TODO can this be more efficient
                    let mut buf = Vec::new();
                    v.encode(&mut buf).unwrap();
                    buf.truncate(1 << best_npw2);
                    buf.resize(max(4, buf.len()), 0);
                    for i in (0..buf.len()).step_by(4) {
                        state.bytecode.push(u32::from_le_bytes(
                            <[u8;4]>::try_from(&buf[i..i+4]).unwrap()
                        ));
                    }
                }

                (slot, T::NPW2)
            }
            OpKind_::Sym(_) => {
                // should be entirely handled in first pass
                unreachable!()
            }

            OpKind_::Select(lnpw2, p, a, b) => {
                let (p_slot, p_npw2) = p.compile_pass2(state);
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let p_refs = p.dec_refs();
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::Select, p_slot, a_slot, b_slot
                    )));
                    if p_refs == 0 { state.slot_pool.dealloc(p_slot, p_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::Select, p_slot, slot, b_slot
                    )));
                    if p_refs == 0 { state.slot_pool.dealloc(p_slot, p_npw2); }
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::Extract(lane, a) => {
                assert!(T::NPW2 <= a.npw2());
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns_::new(
                    a_npw2, a_npw2-T::NPW2, OpCode_::Extract, *lane, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind_::Replace(lane, a, b) => {
                assert!(T::NPW2 >= b.npw2());
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, T::NPW2-b_npw2, OpCode_::Replace, *lane, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, T::NPW2-b_npw2, OpCode_::Replace, *lane, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }

            OpKind_::ExtendU(a) => {
                assert!(T::NPW2 >= a.npw2());
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns_::new(
                    T::NPW2, a_npw2, OpCode_::ExtendU, 0, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind_::ExtendS(a) => {
                assert!(T::NPW2 >= a.npw2());
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns_::new(
                    T::NPW2, a_npw2, OpCode_::ExtendS, 0, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind_::Splat(a) => {
                assert!(T::NPW2 >= a.npw2());
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns_::new(
                    T::NPW2, a_npw2, OpCode_::Splat, 0, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind_::Shuffle(lnpw2, a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::Shuffle, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::Shuffle, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }

            OpKind_::None(a) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns_::new(
                    T::NPW2, 0, OpCode_::None, 0, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind_::Any(a) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns_::new(
                    T::NPW2, 0, OpCode_::Any, 0, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind_::All(lnpw2, a) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns_::new(
                    T::NPW2, *lnpw2, OpCode_::All, 0, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind_::Eq(lnpw2, a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::Eq, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::Eq, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::Eq, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::Ne(lnpw2, a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::Ne, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::Ne, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::Ne, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::LtU(lnpw2, a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::LtU, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::GtU, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::LtU, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::LtS(lnpw2, a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::LtS, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::GtS, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::LtS, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::GtU(lnpw2, a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::GtU, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::LtU, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::GtU, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::GtS(lnpw2, a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::GtS, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::LtS, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::GtS, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::LeU(lnpw2, a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::LeU, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::GeU, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::LeU, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::LeS(lnpw2, a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::LeS, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::GeS, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::LeS, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::GeU(lnpw2, a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::GeU, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::LeU, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::GeU, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::GeS(lnpw2, a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::GeS, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::LeS, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::GeS, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::MinU(lnpw2, a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::MinU, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::MinU, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::MinU, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::MinS(lnpw2, a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::MinS, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::MinS, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::MinS, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::MaxU(lnpw2, a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::MaxU, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::MaxU, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::MaxU, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::MaxS(lnpw2, a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::MaxS, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::MaxS, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::MaxS, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::Neg(lnpw2, a) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns_::new(
                    T::NPW2, *lnpw2, OpCode_::Neg, 0, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind_::Abs(lnpw2, a) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns_::new(
                    T::NPW2, *lnpw2, OpCode_::Abs, 0, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind_::Not(a) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns_::new(
                    T::NPW2, 0, OpCode_::Not, 0, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind_::Clz(lnpw2, a) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns_::new(
                    T::NPW2, *lnpw2, OpCode_::Clz, 0, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind_::Ctz(lnpw2, a) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns_::new(
                    T::NPW2, *lnpw2, OpCode_::Ctz, 0, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind_::Popcnt(lnpw2, a) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let a_refs = a.dec_refs();
                if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }

                let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                state.bytecode.push(u32::from(OpIns_::new(
                    T::NPW2, *lnpw2, OpCode_::Popcnt, 0, slot, a_slot
                )));
                self.slot.set(Some(slot));
                (slot, T::NPW2)
            }
            OpKind_::Add(lnpw2, a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::Add, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::Add, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::Add, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::Sub(lnpw2, a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::Sub, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::Sub, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::Mul(lnpw2, a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::Mul, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::Mul, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::Mul, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::And(a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::And, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::And, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2)
                        .map_err(|e| {
                            disas_(&state.bytecode, io::stdout());
                            e
                        })
                        .unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::And, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::Andnot(a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Andnot, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Andnot, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Andnot, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::Or(a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Or, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Or, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Or, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::Xor(a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Xor, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else if b_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Xor, 0, b_slot, a_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    self.slot.set(Some(b_slot));
                    (b_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Xor, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::Shl(lnpw2, a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::Shl, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::Shl, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::ShrU(lnpw2, a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::ShrU, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::ShrU, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::ShrS(lnpw2, a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::ShrS, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::ShrS, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::Rotl(lnpw2, a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::Rotl, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::Rotl, 0, slot, b_slot
                    )));
                    if a_refs == 0 { state.slot_pool.dealloc(a_slot, a_npw2); }
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(slot));
                    (slot, T::NPW2)
                }
            }
            OpKind_::Rotr(lnpw2, a, b) => {
                let (a_slot, a_npw2) = a.compile_pass2(state);
                let (b_slot, b_npw2) = b.compile_pass2(state);
                let a_refs = a.dec_refs();
                let b_refs = b.dec_refs();

                // can we reuse slots?
                if a_refs == 0 {
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::Rotr, 0, a_slot, b_slot
                    )));
                    if b_refs == 0 { state.slot_pool.dealloc(b_slot, b_npw2); }
                    self.slot.set(Some(a_slot));
                    (a_slot, T::NPW2)
                } else {
                    let slot = state.slot_pool.alloc(T::NPW2).unwrap();
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, 0, OpCode_::Extract, 0, slot, a_slot
                    )));
                    state.bytecode.push(u32::from(OpIns_::new(
                        T::NPW2, *lnpw2, OpCode_::Rotr, 0, slot, b_slot
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
        let example = OpTree_::add(0,
            OpTree_::imm(1u32.to_le_bytes()),
            OpTree_::imm(2u32.to_le_bytes())
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas_(&bytecode, io::stdout()).unwrap();
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
        let example = OpTree_::add(2,
            OpTree_::imm(0x01020304u32.to_le_bytes()),
            OpTree_::imm(0x0506fffeu32.to_le_bytes())
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas_(&bytecode, io::stdout()).unwrap();
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
        let example = OpTree_::add(0,
            OpTree_::<[u8;2]>::extend_s(
                OpTree_::imm(2u8.to_le_bytes())
            ),
            OpTree_::<[u8;2]>::extract(0,
                OpTree_::imm(1u32.to_le_bytes()),
            ),
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas_(&bytecode, io::stdout()).unwrap();
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
        let two = OpTree_::imm(2u32.to_le_bytes());
        let a = OpTree_::add(0,
            OpTree_::imm(1u32.to_le_bytes()),
            OpTree_::imm(2u32.to_le_bytes())
        );
        let b = OpTree_::shr_s(0,
            a.clone(), two.clone()
        );
        let c = OpTree_::shl(0,
            a.clone(), two.clone()
        );
        let example = OpTree_::eq(0,
            OpTree_::add(0,
                OpTree_::mul(0, b, two),
                c,
            ),
            a,
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas_(&bytecode, io::stdout()).unwrap();
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
        let a = OpTree_::imm(3u32.to_le_bytes());
        let b = OpTree_::imm(4u32.to_le_bytes());
        let c = OpTree_::imm(5u32.to_le_bytes());
        let example = OpTree_::eq(0,
            OpTree_::add(0,
                OpTree_::mul(0, a.clone(), a),
                OpTree_::mul(0, b.clone(), b)
            ),
            OpTree_::mul(0, c.clone(), c)
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas_(&bytecode, io::stdout()).unwrap();
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
        let a = OpTree_::imm(1u8.to_le_bytes());
        let b = OpTree_::imm(1u16.to_le_bytes());
        let c = OpTree_::imm(2u32.to_le_bytes());
        let d = OpTree_::imm(3u64.to_le_bytes());
        let e = OpTree_::imm(5u128.to_le_bytes());
        let fib_3 = OpTree_::add(0,
            OpTree_::<[u8;4]>::extend_u(b.clone()), OpTree_::<[u8;4]>::extend_u(a.clone())
        );
        let fib_4 = OpTree_::add(0,
            OpTree_::<[u8;8]>::extend_u(fib_3.clone()), OpTree_::<[u8;8]>::extend_u(b.clone())
        );
        let fib_5 = OpTree_::add(0,
            OpTree_::<[u8;16]>::extend_u(fib_4.clone()), OpTree_::<[u8;16]>::extend_u(fib_3.clone())
        );
        let example = OpTree_::and(
            OpTree_::and(
                OpTree_::<[u8;1]>::extract(0, OpTree_::eq(0, fib_3.clone(), c)),
                OpTree_::<[u8;1]>::extract(0, OpTree_::eq(0, fib_4.clone(), d))
            ),
            OpTree_::<[u8;1]>::extract(0, OpTree_::eq(0, fib_5.clone(), e))
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas_(&bytecode, io::stdout()).unwrap();
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
        let a = OpTree_::const_(3u32.to_le_bytes());
        let b = OpTree_::const_(4u32.to_le_bytes());
        let c = OpTree_::const_(5u32.to_le_bytes());
        let example = OpTree_::eq(0,
            OpTree_::add(0,
                OpTree_::mul(0, a.clone(), a),
                OpTree_::mul(0, b.clone(), b)
            ),
            OpTree_::mul(0, c.clone(), c)
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas_(&bytecode, io::stdout()).unwrap();
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
        let a = OpTree_::const_(1u8.to_le_bytes());
        let b = OpTree_::const_(1u16.to_le_bytes());
        let c = OpTree_::const_(2u32.to_le_bytes());
        let d = OpTree_::const_(3u64.to_le_bytes());
        let e = OpTree_::const_(5u128.to_le_bytes());
        let fib_3 = OpTree_::add(0,
            OpTree_::<[u8;4]>::extend_u(b.clone()), OpTree_::<[u8;4]>::extend_u(a.clone())
        );
        let fib_4 = OpTree_::add(0,
            OpTree_::<[u8;8]>::extend_u(fib_3.clone()), OpTree_::<[u8;8]>::extend_u(b.clone())
        );
        let fib_5 = OpTree_::add(0,
            OpTree_::<[u8;16]>::extend_u(fib_4.clone()), OpTree_::<[u8;16]>::extend_u(fib_3.clone())
        );
        let example = OpTree_::and(
            OpTree_::and(
                OpTree_::<[u8;1]>::extract(0, OpTree_::eq(0, fib_3.clone(), c)),
                OpTree_::<[u8;1]>::extract(0, OpTree_::eq(0, fib_4.clone(), d))
            ),
            OpTree_::<[u8;1]>::extract(0, OpTree_::eq(0, fib_5.clone(), e))
        );

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas_(&bytecode, io::stdout()).unwrap();
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
        let a = OpTree_::imm([1u8; 1]);
        let b = OpTree_::imm([2u8; 1]);
        let c = OpTree_::imm([3u8; 1]);
        let d = OpTree_::imm([4u8; 1]);
        let e = OpTree_::imm([5u8; 1]);
        let f = OpTree_::imm([6u8; 1]);
        let g = OpTree_::imm([7u8; 1]);
        let h = OpTree_::imm([8u8; 1]);
        let big = OpTree_::<[u8;4]>::extend_u(a);
        let i = OpTree_::add(0,
            big.clone(),
            OpTree_::add(0,
                big.clone(),
                OpTree_::add(0,
                    OpTree_::<[u8;4]>::extend_u(b),
                    OpTree_::add(0,
                        OpTree_::<[u8;4]>::extend_u(c),
                        OpTree_::add(0,
                            OpTree_::<[u8;4]>::extend_u(d),
                            OpTree_::add(0,
                                OpTree_::<[u8;4]>::extend_u(e),
                                OpTree_::add(0,
                                    OpTree_::<[u8;4]>::extend_u(f),
                                    OpTree_::add(0,
                                        OpTree_::<[u8;4]>::extend_u(g),
                                        OpTree_::<[u8;4]>::extend_u(h)
                                    )
                                )
                            )
                        )
                    )
                )
            )
        );
        let example = OpTree_::add(0, i.clone(), OpTree_::add(0, i, big));

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas_(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 27);
        assert_eq!(stack.len(), 36);
    }

    #[test]
    fn compile_compressed_consts() {
        let a = OpTree_::imm([1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]);
        let b = OpTree_::const_([1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]);
        let a = OpTree_::add(0, a, b);
        let b = OpTree_::const_([0xfe,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff]);
        let a = OpTree_::add(0, a, b);
        let b = OpTree_::const_([0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab,0xab]);
        let a = OpTree_::add(0, a, b);
        let b = OpTree_::const_([2,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0]);
        let a = OpTree_::add(0, a, b);
        let b = OpTree_::const_([0xfd,0xfe,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff]);
        let a = OpTree_::add(0, a, b);
        let b = OpTree_::const_([0xab,0xcd,0xab,0xcd,0xab,0xcd,0xab,0xcd,0xab,0xcd,0xab,0xcd,0xab,0xcd,0xab,0xcd]);
        let example = OpTree_::add(0, a, b);

        println!();
        println!("input:");
        example.disas(io::stdout()).unwrap();
        let (bytecode, stack) = example.compile(true);
        println!("  bytecode:");
        disas_(&bytecode, io::stdout()).unwrap();
        print!("  stack:");
        for i in 0..stack.len() {
            print!(" {:02x}", stack[i]);
        }
        println!();

        assert_eq!(bytecode.len(), 17);
        assert_eq!(stack.len(), 48);
    }
}

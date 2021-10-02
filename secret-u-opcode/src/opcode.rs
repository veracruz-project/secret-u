//! opcode/bytecode definitions

use std::fmt::Debug;
use std::io;
use std::convert::TryFrom;
use std::fmt;
use std::mem::transmute;
use crate::error::Error;
use std::cmp::min;


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
    Arg         = 0x01,
    Ret         = 0x02,

    ExtendU     = 0x03,
    ExtendS     = 0x04,
    Truncate    = 0x05,
    Splat       = 0x06,
    SplatC      = 0x07,
    SplatLongC  = 0x08,

    Extract     = 0x09,
    Replace     = 0x0a,
    Select      = 0x0b,
    Shuffle     = 0x0c,

    Eq          = 0x0d,
    EqC         = 0x0e,
    Ne          = 0x0f,
    NeC         = 0x10,
    LtU         = 0x11,
    LtUC        = 0x12,
    LtS         = 0x13,
    LtSC        = 0x14,
    GtU         = 0x15,
    GtUC        = 0x16,
    GtS         = 0x17,
    GtSC        = 0x18,
    LeU         = 0x19,
    LeUC        = 0x1a,
    LeS         = 0x1b,
    LeSC        = 0x1c,
    GeU         = 0x1d,
    GeUC        = 0x1e,
    GeS         = 0x1f,
    GeSC        = 0x20,
    MinU        = 0x21,
    MinUC       = 0x22,
    MinS        = 0x23,
    MinSC       = 0x24,
    MaxU        = 0x25,
    MaxUC       = 0x26,
    MaxS        = 0x27,
    MaxSC       = 0x28,

    Neg         = 0x29,
    Abs         = 0x2a,
    Not         = 0x2b,
    Clz         = 0x2c,
    Ctz         = 0x2d,
    Popcnt      = 0x2e,
    Add         = 0x2f,
    AddC        = 0x30,
    Sub         = 0x31,
    SubC        = 0x32,
    Mul         = 0x33,
    MulC        = 0x34,
    And         = 0x35,
    AndC        = 0x36,
    Andnot      = 0x37,
    AndnotC     = 0x38,
    Or          = 0x39,
    OrC         = 0x3a,
    Xor         = 0x3b,
    XorC        = 0x3c,
    Xmul        = 0x3d,
    XmulC       = 0x3e,
    Shl         = 0x3f,
    ShlC        = 0x40,
    ShrU        = 0x41,
    ShrUC       = 0x42,
    ShrS        = 0x43,
    ShrSC       = 0x44,
    Rotl        = 0x45,
    RotlC       = 0x46,
    Rotr        = 0x47,
    RotrC       = 0x48,
}

impl fmt::Display for OpCode {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let name = match self {
            OpCode::Arg         => "arg",
            OpCode::Ret         => "ret",

            OpCode::ExtendU     => "extend_u",
            OpCode::ExtendS     => "extend_s",
            OpCode::Truncate    => "truncate",
            OpCode::Splat       => "splat",
            OpCode::SplatC      => "splat",
            OpCode::SplatLongC  => "splat",

            OpCode::Extract     => "extract",
            OpCode::Replace     => "replace",
            OpCode::Select      => "select",
            OpCode::Shuffle     => "shuffle",

            OpCode::Eq          => "eq",
            OpCode::EqC         => "eq",
            OpCode::Ne          => "ne",
            OpCode::NeC         => "ne",
            OpCode::LtU         => "lt_u",
            OpCode::LtUC        => "lt_u",
            OpCode::LtS         => "lt_s",
            OpCode::LtSC        => "lt_s",
            OpCode::GtU         => "gt_u",
            OpCode::GtUC        => "gt_u",
            OpCode::GtS         => "gt_s",
            OpCode::GtSC        => "gt_s",
            OpCode::LeU         => "le_u",
            OpCode::LeUC        => "le_u",
            OpCode::LeS         => "le_s",
            OpCode::LeSC        => "le_s",
            OpCode::GeU         => "ge_u",
            OpCode::GeUC        => "ge_u",
            OpCode::GeS         => "ge_s",
            OpCode::GeSC        => "ge_s",
            OpCode::MinU        => "min_u",
            OpCode::MinUC       => "min_u",
            OpCode::MinS        => "min_s",
            OpCode::MinSC       => "min_s",
            OpCode::MaxU        => "max_u",
            OpCode::MaxUC       => "max_u",
            OpCode::MaxS        => "max_s",
            OpCode::MaxSC       => "max_s",

            OpCode::Neg         => "neg",
            OpCode::Abs         => "abs",
            OpCode::Not         => "not",
            OpCode::Clz         => "clz",
            OpCode::Ctz         => "ctz",
            OpCode::Popcnt      => "popcnt",
            OpCode::Add         => "add",
            OpCode::AddC        => "add",
            OpCode::Sub         => "sub",
            OpCode::SubC        => "sub",
            OpCode::Mul         => "mul",
            OpCode::MulC        => "mul",
            OpCode::And         => "and",
            OpCode::AndC        => "and",
            OpCode::Andnot      => "andnot",
            OpCode::AndnotC     => "andnot",
            OpCode::Or          => "or",
            OpCode::OrC         => "or",
            OpCode::Xor         => "xor",
            OpCode::XorC        => "xor",
            OpCode::Xmul        => "xmul",
            OpCode::XmulC       => "xmul",
            OpCode::Shl         => "shl",
            OpCode::ShlC        => "shl",
            OpCode::ShrU        => "shr_u",
            OpCode::ShrUC       => "shr_u",
            OpCode::ShrS        => "shr_s",
            OpCode::ShrSC       => "shr_s",
            OpCode::Rotl        => "rotl",
            OpCode::RotlC       => "rotl",
            OpCode::Rotr        => "rotr",
            OpCode::RotrC       => "rotr",
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
            0x07 => OpCode::SplatC,
            0x08 => OpCode::SplatLongC,

            0x09 => OpCode::Extract,
            0x0a => OpCode::Replace,
            0x0b => OpCode::Select,
            0x0c => OpCode::Shuffle,

            0x0d => OpCode::Eq,
            0x0e => OpCode::EqC,
            0x0f => OpCode::Ne,
            0x10 => OpCode::NeC,
            0x11 => OpCode::LtU,
            0x12 => OpCode::LtUC,
            0x13 => OpCode::LtS,
            0x14 => OpCode::LtSC,
            0x15 => OpCode::GtU,
            0x16 => OpCode::GtUC,
            0x17 => OpCode::GtS,
            0x18 => OpCode::GtSC,
            0x19 => OpCode::LeU,
            0x1a => OpCode::LeUC,
            0x1b => OpCode::LeS,
            0x1c => OpCode::LeSC,
            0x1d => OpCode::GeU,
            0x1e => OpCode::GeUC,
            0x1f => OpCode::GeS,
            0x20 => OpCode::GeSC,
            0x21 => OpCode::MinU,
            0x22 => OpCode::MinUC,
            0x23 => OpCode::MinS,
            0x24 => OpCode::MinSC,
            0x25 => OpCode::MaxU,
            0x26 => OpCode::MaxUC,
            0x27 => OpCode::MaxS,
            0x28 => OpCode::MaxSC,

            0x29 => OpCode::Neg,
            0x2a => OpCode::Abs,
            0x2b => OpCode::Not,
            0x2c => OpCode::Clz,
            0x2d => OpCode::Ctz,
            0x2e => OpCode::Popcnt,
            0x2f => OpCode::Add,
            0x30 => OpCode::AddC,
            0x31 => OpCode::Sub,
            0x32 => OpCode::SubC,
            0x33 => OpCode::Mul,
            0x34 => OpCode::MulC,
            0x35 => OpCode::And,
            0x36 => OpCode::AndC,
            0x37 => OpCode::Andnot,
            0x38 => OpCode::AndnotC,
            0x39 => OpCode::Or,
            0x3a => OpCode::OrC,
            0x3b => OpCode::Xor,
            0x3c => OpCode::XorC,
            0x3d => OpCode::Xmul,
            0x3e => OpCode::XmulC,
            0x3f => OpCode::Shl,
            0x40 => OpCode::ShlC,
            0x41 => OpCode::ShrU,
            0x42 => OpCode::ShrUC,
            0x43 => OpCode::ShrS,
            0x44 => OpCode::ShrSC,
            0x45 => OpCode::Rotl,
            0x46 => OpCode::RotlC,
            0x47 => OpCode::Rotr,
            0x48 => OpCode::RotrC,

            _ => Err(Error::InvalidOpcode(ins))?,
        };

        Ok(Self(ins))
    }
}

pub fn prefix(npw2: u8, lnpw2: u8) -> String {
    if lnpw2 == 0 {
        format!("u{}", 8usize << npw2)
    } else {
        format!("u{}x{}", (8usize << npw2) >> lnpw2, 1usize << lnpw2)
    }
}

impl fmt::Display for OpIns {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self.opcode() {
            // extract/replace
            OpCode::Extract => {
                write!(fmt, "{}.{} s{}, s{}[{}]",
                    prefix(self.npw2(), self.lnpw2()),
                    self.opcode(),
                    self.d() << (self.npw2()-self.lnpw2()),
                    self.a() << self.npw2(),
                    self.b()
                )
            }

            OpCode::Replace => {
                write!(fmt, "{}.{} s{}[{}], s{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.opcode(),
                    self.d() << self.npw2(),
                    self.b(),
                    self.a() << (self.npw2()-self.lnpw2())
                )
            }

            // conversion ops
            OpCode::ExtendU | OpCode::ExtendS => {
                write!(fmt, "{}.{} s{}, s{}, {}",
                    prefix(self.npw2(), self.b_npw2()),
                    self.opcode(),
                    self.d() << self.npw2(),
                    self.a() << (self.npw2()-self.lnpw2()),
                    prefix(self.lane_npw2(), self.b_npw2())
                )
            }

            OpCode::Truncate => {
                write!(fmt, "{}.{} s{}, s{}, {}",
                    prefix(self.lane_npw2(), self.b_npw2()),
                    self.opcode(),
                    self.d() << (self.npw2()-self.lnpw2()),
                    self.a() << self.npw2(),
                    prefix(self.npw2(), self.b_npw2())
                )
            }

            // splats and moves (synonym)
            OpCode::Splat if self.lnpw2() == 0 => {
                write!(fmt, "{}.move s{}, s{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.d() << self.npw2(),
                    self.a() << (self.npw2() - self.lnpw2())
                )
            }

            OpCode::Splat => {
                write!(fmt, "{}.{} s{}, s{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.opcode(),
                    self.d() << self.npw2(),
                    self.a() << (self.npw2() - self.lnpw2()),
                )
            }

            OpCode::SplatC if self.lnpw2() == 0 => {
                write!(fmt, "{}.move s{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.d() << self.npw2()
                )
            }

            OpCode::SplatC => {
                write!(fmt, "{}.{} s{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.opcode(),
                    self.d() << self.npw2()
                )
            }

            OpCode::SplatLongC if self.lnpw2() == 0 => {
                write!(fmt, "{}.move s{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.d() << self.npw2()
                )
            }

            OpCode::SplatLongC => {
                write!(fmt, "{}.{} s{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.opcode(),
                    self.d() << self.npw2()
                )
            }

            // unops
            OpCode::Arg
                | OpCode::Ret
                | OpCode::Neg
                | OpCode::Abs
                | OpCode::Not
                | OpCode::Clz
                | OpCode::Ctz
                | OpCode::Popcnt
                => {
                write!(fmt, "{}.{} s{}, s{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.opcode(),
                    self.d() << self.npw2(),
                    self.a() << self.npw2()
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
                | OpCode::Xmul
                | OpCode::Shl
                | OpCode::ShrU
                | OpCode::ShrS
                | OpCode::Rotl
                | OpCode::Rotr
                => {
                write!(fmt, "{}.{} s{}, s{}, s{}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.opcode(),
                    self.d() << self.npw2(),
                    self.a() << self.npw2(),
                    self.b() << self.npw2()
                )
            }

            // binops with consts
            OpCode::EqC
                | OpCode::NeC
                | OpCode::LtUC
                | OpCode::LtSC
                | OpCode::GtUC
                | OpCode::GtSC
                | OpCode::LeUC
                | OpCode::LeSC
                | OpCode::GeUC
                | OpCode::GeSC
                | OpCode::MinUC
                | OpCode::MinSC
                | OpCode::MaxUC
                | OpCode::MaxSC
                | OpCode::AddC
                | OpCode::SubC
                | OpCode::MulC
                | OpCode::AndC
                | OpCode::AndnotC
                | OpCode::OrC
                | OpCode::XorC
                | OpCode::XmulC
                | OpCode::ShlC
                | OpCode::ShrUC
                | OpCode::ShrSC
                | OpCode::RotlC
                | OpCode::RotrC
                => {
                write!(fmt, "{}.{} s{}, s{}, 0x{:0w$x}",
                    prefix(self.npw2(), self.lnpw2()),
                    self.opcode(),
                    self.d() << self.npw2(),
                    self.a() << self.npw2(),
                    self.b()
                        & 1u16.checked_shl(8*(1 << self.lane_npw2()))
                            .map(|mask| mask-1)
                            .unwrap_or(u16::MAX),
                    w=2*min(2, 1 << self.lane_npw2())
                )
            }
        }
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

        // note we decode splat immediates here, these are long and may require
        // decoding multiple u64s from the instruction stream, so not a good fit
        // for OpIns::display
        match OpIns::try_from(ins) {
            Ok(ins) => {
                match ins.opcode() {
                    OpCode::SplatC => {
                        write!(out, "    {:016x} {}, 0x", u64::from(ins), ins)?;
                        writeln!(out, "{:0w$x}",
                            ins.ab()
                                & 1u32.checked_shl(8*(1 << ins.lane_npw2()))
                                    .map(|mask| mask-1)
                                    .unwrap_or(u32::MAX),
                            w=2*min(4, 1 << ins.lane_npw2())
                        )?;
                    }
                    OpCode::SplatLongC => {
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


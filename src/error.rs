
use thiserror::Error;

#[derive(Error, Debug)]
#[non_exhaustive]
pub enum Error {
    #[error("Invalid opcode {0:#010x}")]
    InvalidOpcode(u32),
    #[error("Invalid return")]
    InvalidReturn,
    #[error("Unaligned access")]
    Unaligned,
    #[error("Out of bounds access")]
    OutOfBounds,
    #[error("Divide by zero")]
    DivideByZero,
    #[error("Attempted to declassify in compile block")]
    DeclassifyInCompile,
    #[error("Exceeded 256 slots for u{}", 8 << _0)]
    OutOfSlots(u8),
}

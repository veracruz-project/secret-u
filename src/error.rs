
use thiserror::Error;

#[derive(Error, Debug)]
#[non_exhaustive]
pub enum Error {
    #[error("Invalid opcode {0:#04x}")]
    InvalidOpcode(u16),
    #[error("Invalid opcode {0:#08x}")]
    InvalidOpcode_(u32),
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
}

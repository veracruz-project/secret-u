
use thiserror::Error;

#[derive(Error, Debug)]
#[non_exhaustive]
pub enum Error {
    #[error("Invalid opcode {0}")]
    InvalidOpcode(u16),
    #[error("Unreachable")]
    Unreachable,
    #[error("Unaligned access")]
    Unaligned,
    #[error("Out of bounds access")]
    OutOfBounds,
}

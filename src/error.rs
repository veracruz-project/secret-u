
use thiserror::Error;

#[derive(Error, Debug)]
#[non_exhaustive]
pub enum Error {
    #[error("Invalid opcode {0}")]
    InvalidOpcode(u16)
}

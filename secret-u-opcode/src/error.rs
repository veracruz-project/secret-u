//!
//! Copyright (c) 2021 Veracruz, a series of LF Projects, LLC.
//! SPDX-License-Identifier: MIT

use thiserror::Error;

#[derive(Error, Debug)]
#[non_exhaustive]
pub enum Error {
    #[error("Invalid opcode {0:#018x}")]
    InvalidOpcode(u64),
    #[error("Invalid return")]
    InvalidReturn,
    #[error("Unaligned access")]
    Unaligned,
    #[error("Out of bounds access")]
    OutOfBounds,
    #[error("Attempted to declassify in compile block")]
    DeclassifyInCompile,
    #[error("Exceeded 65536 slots for u{}", 8 << _0)]
    OutOfSlots(u8),
}

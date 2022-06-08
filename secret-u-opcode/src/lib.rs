//! Common instruction/error definitions
//!
//! Copyright (c) 2021 Veracruz, a series of LF Projects, LLC.
//! SPDX-License-Identifier: MIT

pub mod error;
pub mod opcode;

pub use error::Error;
pub use opcode::OpCode;
pub use opcode::OpIns;
pub use opcode::prefix;
pub use opcode::disas;

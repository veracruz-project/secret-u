//! Common instruction/error definitions

pub mod error;
pub mod opcode;

pub use error::Error;
pub use opcode::OpCode;
pub use opcode::OpIns;
pub use opcode::prefix;
pub use opcode::disas;

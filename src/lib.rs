//! Definitions of secret integers

pub mod error;
pub mod opcode;
pub mod engine;
pub mod traits;
pub mod num;
pub mod lambda;
pub mod table;

pub use error::*;
pub use num::*;
pub use lambda::*;

// introduce traits, but prefix to avoid names collisions, this
// is useful if all of the crate is imported
pub use traits::Eq as SecretEq;
pub use traits::Ord as SecretOrd;
pub use traits::Select as SecretSelect;
pub use traits::Shuffle as SecretShuffle;
pub use traits::Cast as SecretCast;
pub use traits::Eval as SecretEval;


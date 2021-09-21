//! Definitions of secret integers

pub mod error;
pub mod engine;
pub mod opcode;
pub mod optree;
pub mod traits;
pub mod types;
pub mod lambda;
pub mod table;

pub use error::*;
pub use types::*;
pub use lambda::*;

// introduce traits, but prefix to avoid names collisions, this
// is useful if all of the crate is imported
pub use traits::Eq as SecretEq;
pub use traits::Ord as SecretOrd;
pub use traits::Select as SecretSelect;
pub use traits::Shuffle as SecretShuffle;
pub use traits::Shuffle2 as SecretShuffle2;
pub use traits::Cast as SecretCast;
pub use traits::FromCast as SecretFromCast;
pub use traits::Eval as SecretEval;


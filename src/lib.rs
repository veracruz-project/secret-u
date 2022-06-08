//! Definitions of secret integers
//!
//! Copyright (c) 2021 Veracruz, a series of LF Projects, LLC.
//! SPDX-License-Identifier: MIT

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
pub use traits::Classify as SecretClassify;
pub use traits::TryClassify as SecretTryClassify;
pub use traits::FromDeclassify as SecretFromDeclassify;
pub use traits::ClassifyLeBytes as SecretClassifyLeBytes;
pub use traits::TryClassifyLeBytes as SecretTryClassifyLeBytes;
pub use traits::FromDeclassifyLeBytes as SecretFromDeclassifyLeBytes;
pub use traits::ClassifyBeBytes as SecretClassifyBeBytes;
pub use traits::TryClassifyBeBytes as SecretTryClassifyBeBytes;
pub use traits::FromDeclassifyBeBytes as SecretFromDeclassifyBeBytes;
pub use traits::ClassifyNeBytes as SecretClassifyNeBytes;
pub use traits::TryClassifyNeBytes as SecretTryClassifyNeBytes;
pub use traits::FromDeclassifyNeBytes as SecretFromDeclassifyNeBytes;
pub use traits::Eq as SecretEq;
pub use traits::Ord as SecretOrd;
pub use traits::Select as SecretSelect;
pub use traits::Shuffle as SecretShuffle;
pub use traits::Shuffle2 as SecretShuffle2;
pub use traits::Cast as SecretCast;
pub use traits::FromCast as SecretFromCast;
pub use traits::Eval as SecretEval;


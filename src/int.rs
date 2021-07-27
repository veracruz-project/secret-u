//! Definitions of secret integers

use crate::opcode::*;
use crate::error::Error;
use std::rc::Rc;

use std::ops::Not;
use std::ops::BitAnd;
use std::ops::BitAndAssign;
use std::ops::BitOr;
use std::ops::BitOrAssign;
use std::ops::BitXor;
use std::ops::BitXorAssign;
use std::ops::Neg;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Sub;
use std::ops::SubAssign;
use std::ops::Mul;
use std::ops::MulAssign;
use std::ops::Shl;
use std::ops::ShlAssign;
use std::ops::Shr;
use std::ops::ShrAssign;


/// A trait for types that can eq as long as the result remains secret
pub trait SecretEq {
    fn eq(self, other: Self) -> SecretBool;
    fn ne(self, other: Self) -> SecretBool;
}

/// A trait for types that can be compared as long as the result remains secret
pub trait SecretOrd {
    fn lt(self, other: Self) -> SecretBool;
    fn le(self, other: Self) -> SecretBool;
    fn gt(self, other: Self) -> SecretBool;
    fn ge(self, other: Self) -> SecretBool;

    // convenience functions
    fn max(self, other: Self) -> Self;
    fn min(self, other: Self) -> Self;

    fn clamp(self, min: Self, max: Self) -> Self
    where
        Self: Sized
    {
        self.max(min).min(max)
    }
}

/// A trait for objects that can be selected between
pub trait SecretSelect<T> {
    fn select(pred: T, a: Self, b: Self) -> Self;
}

/// A trait for objects that can be flattened to reduce tree size
pub trait SecretEval: Sized {
    /// Evaluate to immediate form
    ///
    /// Normally eval is internally called by declassify,
    /// but this can be useful for flattening the internal
    /// tree manually to avoid growing too larger during a
    /// computation
    fn eval(self) -> Self {
        self.try_eval().unwrap()
    }

    /// Same as eval but propagating internal VM errors
    fn try_eval(self) -> Result<Self, Error>;
}

/// A trait for objects backed by an internal OpTree, this is used
/// for compiling down to bytecode
pub trait SecretTree: Sized {
    /// Internal tree representation
    type Tree;

    /// Build from internal tree
    fn from_tree(tree: Self::Tree) -> Self;

    /// Get internal tree, we can do this without worry
    /// since we internally ensure the value is only ever zeros or ones
    fn tree(self) -> Self::Tree;
}

/// A trait that capture potentially-truncating conversions
///
/// This is equivalent to the "as" keyword used on integer types normally
pub trait Cast<T> {
    fn cast(t: T) -> Self;
}

impl<T, U> Cast<U> for T
where
    T: From<U>,
{
    fn cast(u: U) -> T {
        T::from(u)
    }
}


//// SecretBool ////

/// A secret bool who's value is ensured to not be leaked by Rust's type-system
///
/// Secret bool is a bit different than other secret types, dynamically
/// preserving the original type until needed as this reduces unnecessary
/// casting
///
/// Note, like the underlying Rc type, clone is relatively cheap, but
/// not a bytewise copy, which means we can't implement the Copy trait
#[derive(Clone)]
pub struct SecretBool(DeferredTree);

#[derive(Clone)]
enum DeferredTree {
    Resolved(OpTree<U8>),
    Deferred(Rc<dyn DynOpTree>),
}

impl From<bool> for SecretBool {
    fn from(v: bool) -> SecretBool {
        Self::classify(v)
    }
}

impl Default for SecretBool {
    fn default() -> Self {
        Self::const_(false)
    }
}

impl SecretBool {
    /// Wraps a non-secret value as a secret value
    pub fn classify(v: bool) -> SecretBool {
        Self::from_tree(OpTree::<U8>::imm(if v { 0xffu8 } else { 0x00u8 }))
    }

    /// Extracts the secret value into a non-secret value, this
    /// effectively "leaks" the secret value, but is necessary
    /// to actually do anything
    pub fn declassify(self) -> bool {
        self.try_declassify().unwrap()
    }

    /// Same as declassify but propagating internal VM errors
    pub fn try_declassify(self) -> Result<bool, Error> {
        Ok(self.resolve::<U8>().try_eval()?.result::<u8>() != 0)
    }

    /// Wraps a non-secret value as a secret value
    pub fn new(v: bool) -> SecretBool {
        Self::classify(v)
    }

    /// Create a non-secret constant value, these are available for
    /// more optimizations than secret values
    pub fn const_(v: bool) -> SecretBool {
        Self::from_tree(if v { OpTree::<U8>::ones() } else { OpTree::<U8>::zero() })
    }

    /// Create a deferred SecretBool, the actual type will resolved until
    /// needed to avoid unecessary truncates/extends
    fn defer(tree: Rc<dyn DynOpTree>) -> Self {
        Self(DeferredTree::Deferred(tree))
    }

    /// Force into deferred SecretBool
    fn deferred<'a>(&'a self) -> &'a dyn DynOpTree {
        match &self.0 {
            DeferredTree::Resolved(tree) => tree,
            DeferredTree::Deferred(tree) => tree.as_ref(),
        }
    }

    /// Reduce a deferred SecretBool down into a U8 if necessary
    fn resolve<U: OpU>(self) -> OpTree<U> {
        OpTree::dyn_cast_s(self.deferred())
    }

    /// Select operation for secrecy-preserving conditionals
    pub fn select<T>(self, a: T, b: T) -> T
    where
        T: SecretSelect<SecretBool>
    {
        T::select(self, a, b)
    }
}

impl SecretEval for SecretBool {
    fn try_eval(self) -> Result<Self, Error> {
        let tree = self.resolve::<U8>();
        if tree.is_sym() {
            return Err(Error::DeclassifyInCompile);
        }

        Ok(Self::from_tree(tree.try_eval()?))
    }
}

impl SecretTree for SecretBool {
    type Tree = OpTree<U8>;

    fn from_tree(tree: OpTree<U8>) -> Self {
        Self(DeferredTree::Resolved(tree))
    }

    fn tree(self) -> OpTree<U8> {
        self.resolve::<U8>()
    }
}

impl Not for SecretBool {
    type Output = SecretBool;
    fn not(self) -> SecretBool {
        match self.0 {
            DeferredTree::Resolved(tree) => Self::from_tree(OpTree::not(tree)),
            DeferredTree::Deferred(tree) => Self::defer(tree.dyn_not()),
        }
    }
}

impl BitAnd for SecretBool {
    type Output = SecretBool;
    fn bitand(self, other: SecretBool) -> SecretBool {
        Self::defer(self.deferred().dyn_and(other.deferred()))
    }
}

impl BitAndAssign for SecretBool {
    fn bitand_assign(&mut self, other: SecretBool) {
        *self = self.clone().bitand(other)
    }
}

impl BitOr for SecretBool {
    type Output = SecretBool;
    fn bitor(self, other: SecretBool) -> SecretBool {
        Self::defer(self.deferred().dyn_or(other.deferred()))
    }
}

impl BitOrAssign for SecretBool {
    fn bitor_assign(&mut self, other: SecretBool) {
        *self = self.clone().bitor(other)
    }
}

impl BitXor for SecretBool {
    type Output = SecretBool;
    fn bitxor(self, other: SecretBool) -> SecretBool {
        Self::defer(self.deferred().dyn_xor(other.deferred()))
    }
}

impl BitXorAssign for SecretBool {
    fn bitxor_assign(&mut self, other: SecretBool) {
        *self = self.clone().bitxor(other)
    }
}

impl SecretEq for SecretBool {
    fn eq(self, other: Self) -> SecretBool {
        SecretBool::from_tree(OpTree::eq(0, self.resolve::<U8>(), other.resolve::<U8>()))
    }

    fn ne(self, other: Self) -> SecretBool {
        SecretBool::from_tree(OpTree::ne(0, self.resolve::<U8>(), other.resolve::<U8>()))
    }
}

impl SecretSelect<SecretBool> for SecretBool {
    fn select(p: SecretBool, a: Self, b: Self) -> Self {
        Self::from_tree(OpTree::select(0,
            p.resolve::<U8>(),
            a.resolve::<U8>(),
            b.resolve::<U8>()
        ))
    }
}


//// SecretU* ////

macro_rules! secret_impl {
    ($t:ident($U:ty; [u8; $n:literal]; $($p:ty)?, $($u:ty)?, $($i:ty)?)) => {
        /// A secret integer who's value is ensured to not be leaked by Rust's type-system
        ///
        /// Note, like the underlying Rc type, clone is relatively cheap, but
        /// not a bytewise copy, which means we can't implement the Copy trait
        #[derive(Clone)]
        pub struct $t(OpTree<$U>);

        $(
            impl From<$p> for $t {
                fn from(v: $p) -> $t {
                    Self::classify(v)
                }
            }
        )?

        impl Default for $t {
            fn default() -> Self {
                Self::zero()
            }
        }

        impl $t {
            /// Wraps a non-secret value as a secret value
            pub fn classify_le_bytes(v: [u8; $n]) -> Self {
                Self(OpTree::imm(v))
            }

            /// Extracts the secret value into a non-secret value, this
            /// effectively "leaks" the secret value, but is necessary
            /// to actually do anything
            pub fn declassify_le_bytes(self) -> [u8; $n] {
                self.try_declassify_le_bytes().unwrap()
            }

            /// Same as declassify but propagating internal VM errors
            pub fn try_declassify_le_bytes(self) -> Result<[u8; $n], Error> {
                Ok(self.try_eval()?.0.result())
            }

            /// Wraps a non-secret value as a secret value
            pub fn from_le_bytes(v: [u8; $n]) -> Self {
                Self::classify_le_bytes(v)
            }

            /// Create a non-secret constant value, these are available
            /// for more optimizations than secret values
            pub fn const_le_bytes(v: [u8; $n]) -> Self {
                Self(OpTree::const_(v))
            }

            $(
                /// Wraps a non-secret value as a secret value
                pub fn classify(v: $p) -> Self {
                    Self(OpTree::imm(v.to_le_bytes()))
                }

                /// Extracts the secret value into a non-secret value, this
                /// effectively "leaks" the secret value, but is necessary
                /// to actually do anything
                pub fn declassify(self) -> $p {
                    self.try_declassify().unwrap()
                }

                /// Same as declassify but propagating internal VM errors
                pub fn try_declassify(self) -> Result<$p, Error> {
                    Ok(self.try_eval()?.0.result())
                }

                /// Wraps a non-secret value as a secret value
                pub fn new(v: $p) -> Self {
                    Self::classify(v)
                }

                /// Create a non-secret constant value, these are available
                /// for more optimizations than secret values
                pub fn const_(v: $p) -> Self {
                    Self::const_le_bytes(v.to_le_bytes())
                }
            )?

            /// A constant, non-secret 0
            pub fn zero() -> Self {
                Self(OpTree::zero())
            }

            /// A constant, non-secret 1
            pub fn one() -> Self {
                Self(OpTree::one())
            }

            /// A constant with all bits set to 1, non-secret
            pub fn ones() -> Self {
                Self(OpTree::ones())
            }

            // abs only available on signed types
            $(
                pub fn abs(self) -> Self {
                    let _: $i;
                    Self(OpTree::abs(0, self.0))
                }
            )?

            // other non-trait operations
            pub fn trailing_zeros(self) -> $t {
                Self(OpTree::ctz(0, self.0))
            }

            pub fn trailing_ones(self) -> $t {
                (!self).trailing_zeros()
            }

            pub fn leading_zeros(self) -> $t {
                Self(OpTree::clz(0, self.0))
            }

            pub fn leading_ones(self) -> $t {
                (!self).leading_zeros()
            }

            pub fn count_zeros(self) -> $t {
                (!self).count_ones()
            }

            pub fn count_ones(self) -> $t {
                Self(OpTree::popcnt(0, self.0))
            }

            // ipw2/npw2 only available on unsigned types
            $(
                pub fn is_power_of_two(self) -> SecretBool {
                    let _: $u;
                    self.count_ones().eq(Self::one())
                }

                pub fn next_power_of_two(self) -> $t {
                    let _: $u;
                    // based on implementation in rust core
                    self.clone().le(Self::one()).select(
                        // special case if <= 1
                        Self::zero(),
                        // next_power_of_two_minus_1
                        Self::ones() >> (self - Self::one()).leading_zeros()
                    ) + Self::one()
                }
            )?

            pub fn rotate_left(self, other: $t) -> $t {
                Self(OpTree::rotl(0, self.0, other.0))
            }

            pub fn rotate_right(self, other: $t) -> $t {
                Self(OpTree::rotr(0, self.0, other.0))
            }
        }

        impl SecretEval for $t {
            fn try_eval(self) -> Result<Self, Error> {
                if self.0.is_sym() {
                    return Err(Error::DeclassifyInCompile);
                }

                Ok(Self::from_tree(self.tree().try_eval()?))
            }
        }

        impl SecretTree for $t {
            type Tree = OpTree<$U>;

            fn from_tree(tree: OpTree<$U>) -> Self {
                Self(tree)
            }

            fn tree(self) -> OpTree<$U> {
                self.0
            }
        }

        impl Not for $t {
            type Output = $t;
            fn not(self) -> $t {
                Self(OpTree::not(self.0))
            }
        }

        impl BitAnd for $t {
            type Output = $t;
            fn bitand(self, other: $t) -> $t {
                Self(OpTree::and(self.0, other.0))
            }
        }

        impl BitAndAssign for $t {
            fn bitand_assign(&mut self, other: $t) {
                *self = self.clone().bitand(other)
            }
        }

        impl BitOr for $t {
            type Output = $t;
            fn bitor(self, other: $t) -> $t {
                Self(OpTree::or(self.0, other.0))
            }
        }

        impl BitOrAssign for $t {
            fn bitor_assign(&mut self, other: $t) {
                *self = self.clone().bitor(other)
            }
        }

        impl BitXor for $t {
            type Output = $t;
            fn bitxor(self, other: $t) -> $t {
                Self(OpTree::xor(self.0, other.0))
            }
        }

        impl BitXorAssign for $t {
            fn bitxor_assign(&mut self, other: $t) {
                *self = self.clone().bitxor(other)
            }
        }

        // negate only available for signed types
        $(
            impl Neg for $t {
                type Output = $t;
                fn neg(self) -> $t {
                    let _: $i;
                    Self(OpTree::neg(0, self.0))
                }
            }
        )?

        impl Add for $t {
            type Output = $t;
            fn add(self, other: $t) -> $t {
                Self(OpTree::add(0, self.0, other.0))
            }
        }

        impl AddAssign for $t {
            fn add_assign(&mut self, other: $t) {
                *self = self.clone().add(other)
            }
        }

        impl Sub for $t {
            type Output = $t;
            fn sub(self, other: $t) -> $t {
                Self(OpTree::sub(0, self.0, other.0))
            }
        }

        impl SubAssign for $t {
            fn sub_assign(&mut self, other: $t) {
                *self = self.clone().sub(other)
            }
        }

        impl Mul for $t {
            type Output = $t;
            fn mul(self, other: $t) -> $t {
                Self(OpTree::mul(0, self.0, other.0))
            }
        }

        impl MulAssign for $t {
            fn mul_assign(&mut self, other: $t) {
                *self = self.clone().mul(other)
            }
        }

        impl Shl for $t {
            type Output = $t;
            fn shl(self, other: $t) -> $t {
                Self(OpTree::shl(0, self.0, other.0))
            }
        }

        impl ShlAssign for $t {
            fn shl_assign(&mut self, other: $t) {
                *self = self.clone().shl(other)
            }
        }

        impl Shr for $t {
            type Output = $t;
            fn shr(self, other: $t) -> $t {
                $(
                    let _: $u;
                    Self(OpTree::shr_u(0, self.0, other.0))
                )?
                $(
                    let _: $i;
                    Self(OpTree::shr_s(0, self.0, other.0))
                )?
            }
        }

        impl ShrAssign for $t {
            fn shr_assign(&mut self, other: $t) {
                *self = self.clone().shr(other)
            }
        }

        impl SecretEq for $t {
            fn eq(self, other: Self) -> SecretBool {
                SecretBool::defer(Rc::new(OpTree::eq(0, self.0, other.0)))
            }

            fn ne(self, other: Self) -> SecretBool {
                SecretBool::defer(Rc::new(OpTree::ne(0, self.0, other.0)))
            }
        }

        impl SecretOrd for $t {
            $(
                fn lt(self, other: Self) -> SecretBool {
                    let _: $u;
                    SecretBool::defer(Rc::new(OpTree::lt_u(0, self.0, other.0)))
                }

                fn le(self, other: Self) -> SecretBool {
                    let _: $u;
                    SecretBool::defer(Rc::new(OpTree::le_u(0, self.0, other.0)))
                }

                fn gt(self, other: Self) -> SecretBool {
                    let _: $u;
                    SecretBool::defer(Rc::new(OpTree::gt_u(0, self.0, other.0)))
                }

                fn ge(self, other: Self) -> SecretBool {
                    let _: $u;
                    SecretBool::defer(Rc::new(OpTree::ge_u(0, self.0, other.0)))
                }

                fn min(self, other: Self) -> Self {
                    let _: $u;
                    Self(OpTree::min_u(0, self.0, other.0))
                }

                fn max(self, other: Self) -> Self {
                    let _: $u;
                    Self(OpTree::max_u(0, self.0, other.0))
                }
            )?
            $(
                fn lt(self, other: Self) -> SecretBool {
                    let _: $i;
                    SecretBool::defer(Rc::new(OpTree::lt_s(0, self.0, other.0)))
                }

                fn le(self, other: Self) -> SecretBool {
                    let _: $i;
                    SecretBool::defer(Rc::new(OpTree::le_s(0, self.0, other.0)))
                }

                fn gt(self, other: Self) -> SecretBool {
                    let _: $i;
                    SecretBool::defer(Rc::new(OpTree::gt_s(0, self.0, other.0)))
                }

                fn ge(self, other: Self) -> SecretBool {
                    let _: $i;
                    SecretBool::defer(Rc::new(OpTree::ge_s(0, self.0, other.0)))
                }

                fn min(self, other: Self) -> Self {
                    let _: $i;
                    Self(OpTree::min_s(0, self.0, other.0))
                }

                fn max(self, other: Self) -> Self {
                    let _: $i;
                    Self(OpTree::max_s(0, self.0, other.0))
                }
            )?
        }

        impl SecretSelect<SecretBool> for $t {
            fn select(p: SecretBool, a: Self, b: Self) -> Self {
                Self(OpTree::select(0,
                    p.resolve(),
                    a.0,
                    b.0
                ))
            }
        }
    }
}

secret_impl! { SecretU8  (U8;   [u8;  1]; u8,   u8,       ) }
secret_impl! { SecretU16 (U16;  [u8;  2]; u16,  u16,      ) }
secret_impl! { SecretU32 (U32;  [u8;  4]; u32,  u32,      ) }
secret_impl! { SecretU64 (U64;  [u8;  8]; u64,  u64,      ) }
secret_impl! { SecretU128(U128; [u8; 16]; u128, u128,     ) }
secret_impl! { SecretU256(U256; [u8; 32]; ,     (),       ) }
secret_impl! { SecretU512(U512; [u8; 64]; ,     (),       ) }
secret_impl! { SecretI8  (U8;   [u8;  1]; i8,   ,     i8  ) }
secret_impl! { SecretI16 (U16;  [u8;  2]; i16,  ,     i16 ) }
secret_impl! { SecretI32 (U32;  [u8;  4]; i32,  ,     i32 ) }
secret_impl! { SecretI64 (U64;  [u8;  8]; i64,  ,     i64 ) }
secret_impl! { SecretI128(U128; [u8; 16]; i128, ,     i128) }
secret_impl! { SecretI256(U256; [u8; 32]; ,     ,     ()  ) }
secret_impl! { SecretI512(U512; [u8; 64]; ,     ,     ()  ) }


//// Conversions U* <-> U* ////

// these are really tedius, so we use a really heavy-weight macro here
macro_rules! from_impl {
    // bool extending (bool -> u32)
    (@from FB $from:ident for $to:ident) => {
        impl From<$from> for $to {
            fn from(v: $from) -> $to {
                v.select(<$to>::one(), <$to>::zero())
            }
        }
    };
    // unsigned extending (u8 -> u32)
    (@from FU $from:ident for $to:ident) => {
        impl From<$from> for $to {
            fn from(v: $from) -> $to {
                Self(OpTree::extend_u(v.0))
            }
        }
    };
    // signed extending (i8 -> i32)
    (@from FS $from:ident for $to:ident) => {
        impl From<$from> for $to {
            fn from(v: $from) -> $to {
                Self(OpTree::extend_s(v.0))
            }
        }
    };
    // truncating (i32 -> i8)
    (@from CT $from:ident for $to:ident) => {
        impl Cast<$from> for $to {
            fn cast(v: $from) -> $to {
                Self(OpTree::extract(0, v.0))
            }
        }
    };
    // sign conversion (u32 -> i32)
    (@from CS $from:ident for $to:ident) => {
        impl Cast<$from> for $to {
            fn cast(v: $from) -> $to {
                Self(v.0)
            }
        }
    };
    // base case
    ($to:ident($($op:ident $from:ident),*$(,)?)) => {
        $(
            from_impl! { @from $op $from for $to }
        )*
    };
}

// unsigned from bools
from_impl! { SecretU8  (FB SecretBool) }
from_impl! { SecretU16 (FB SecretBool) }
from_impl! { SecretU32 (FB SecretBool) }
from_impl! { SecretU64 (FB SecretBool) }
from_impl! { SecretU128(FB SecretBool) }
from_impl! { SecretU256(FB SecretBool) }
from_impl! { SecretU512(FB SecretBool) }

// signed from bools
from_impl! { SecretI8  (FB SecretBool) }
from_impl! { SecretI16 (FB SecretBool) }
from_impl! { SecretI32 (FB SecretBool) }
from_impl! { SecretI64 (FB SecretBool) }
from_impl! { SecretI128(FB SecretBool) }
from_impl! { SecretI256(FB SecretBool) }
from_impl! { SecretI512(FB SecretBool) }

// unsigned from unsigned
from_impl! { SecretU8  (             CT SecretU16, CT SecretU32, CT SecretU64, CT SecretU128, CT SecretU256, CT SecretU512) }
from_impl! { SecretU16 (FU SecretU8,               CT SecretU32, CT SecretU64, CT SecretU128, CT SecretU256, CT SecretU512) }
from_impl! { SecretU32 (FU SecretU8, FU SecretU16,               CT SecretU64, CT SecretU128, CT SecretU256, CT SecretU512) }
from_impl! { SecretU64 (FU SecretU8, FU SecretU16, FU SecretU32,               CT SecretU128, CT SecretU256, CT SecretU512) }
from_impl! { SecretU128(FU SecretU8, FU SecretU16, FU SecretU32, FU SecretU64,                CT SecretU256, CT SecretU512) }
from_impl! { SecretU256(FU SecretU8, FU SecretU16, FU SecretU32, FU SecretU64, FU SecretU128,                CT SecretU512) }
from_impl! { SecretU512(FU SecretU8, FU SecretU16, FU SecretU32, FU SecretU64, FU SecretU128, FU SecretU256,              ) }

// unsigned from signed
from_impl! { SecretU8  (CS SecretI8,                                                                                      ) }
from_impl! { SecretU16 (             CS SecretI16,                                                                        ) }
from_impl! { SecretU32 (                           CS SecretI32,                                                          ) }
from_impl! { SecretU64 (                                         CS SecretI64,                                            ) }
from_impl! { SecretU128(                                                       CS SecretI128,                             ) }
from_impl! { SecretU256(                                                                      CS SecretI256,              ) }
from_impl! { SecretU512(                                                                                     CS SecretI512) }

// signed from signed
from_impl! { SecretI8  (             CT SecretI16, CT SecretI32, CT SecretI64, CT SecretI128, CT SecretI256, CT SecretI512) }
from_impl! { SecretI16 (FS SecretI8,               CT SecretI32, CT SecretI64, CT SecretI128, CT SecretI256, CT SecretI512) }
from_impl! { SecretI32 (FS SecretI8, FS SecretI16,               CT SecretI64, CT SecretI128, CT SecretI256, CT SecretI512) }
from_impl! { SecretI64 (FS SecretI8, FS SecretI16, FS SecretI32,               CT SecretI128, CT SecretI256, CT SecretI512) }
from_impl! { SecretI128(FS SecretI8, FS SecretI16, FS SecretI32, FS SecretI64,                CT SecretI256, CT SecretI512) }
from_impl! { SecretI256(FS SecretI8, FS SecretI16, FS SecretI32, FS SecretI64, FS SecretI128,                CT SecretI512) }
from_impl! { SecretI512(FS SecretI8, FS SecretI16, FS SecretI32, FS SecretI64, FS SecretI128, FS SecretI256,              ) }

// signed from unsigned
from_impl! { SecretI8  (CS SecretU8,                                                                                      ) }
from_impl! { SecretI16 (FU SecretU8, CS SecretU16,                                                                        ) }
from_impl! { SecretI32 (FU SecretU8, FU SecretU16, CS SecretU32,                                                          ) }
from_impl! { SecretI64 (FU SecretU8, FU SecretU16, FU SecretU32, CS SecretU64,                                            ) }
from_impl! { SecretI128(FU SecretU8, FU SecretU16, FU SecretU32, FU SecretU64, CS SecretU128,                             ) }
from_impl! { SecretI256(FU SecretU8, FU SecretU16, FU SecretU32, FU SecretU64, FU SecretU128, CS SecretU256,              ) }
from_impl! { SecretI512(FU SecretU8, FU SecretU16, FU SecretU32, FU SecretU64, FU SecretU128, FU SecretU256, CS SecretU512) }


#[cfg(test)]
mod tests {
    use super::*;
    use std::io;

    #[test]
    fn int_bool1() {
        println!();
        let a = SecretBool::new(true);
        let b = SecretBool::new(true);
        let x = (a.clone() & b.clone()).eq(a | b);
        x.clone().tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, true);
    }

    #[test]
    fn int_bool2() {
        println!();
        let a = SecretBool::new(true);
        let b = SecretBool::new(false);
        let x = (a.clone() | b.clone()).select(a, b);
        x.clone().tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, true);
    }

    #[test]
    fn int_eqz() {
        println!();
        let a = SecretU32::new(100);
        let b = SecretU32::new(10);
        let x = !a.clone().gt(b.clone());

        x.clone().tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, false);

        let x = (!a.clone().gt(b.clone())).select(a, b);
        x.clone().tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, 10);
    }

    #[test]
    fn int_abs() {
        println!();
        let a = SecretI32::new(-100);
        let x = a.abs();
        x.clone().tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, 100);
    }

    #[test]
    fn int_u32() {
        println!();
        let a = SecretU32::new(3);
        let b = SecretU32::new(4);
        let c = SecretU32::new(5);
        let x = (a.clone()*a + b.clone()*b) - (c.clone()*c);
        x.clone().tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, 0);
    }

    #[test]
    fn int_i32() {
        println!();
        let a = SecretI32::new(-3);
        let b = SecretI32::new(-4);
        let c = SecretI32::new(-5);
        let x = (a.clone()*a + b.clone()*b) - (c.clone()*c);
        x.clone().tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, 0);
    }

    #[test]
    fn int_ord() {
        println!();

        fn test_ord(a: u32, b: u32, c: u32) {
            let sa = SecretU32::new(a);
            let sb = SecretU32::new(b);
            let sc = SecretU32::new(c);
            let x = sb.clone().lt(sc.clone());
            x.clone().tree().disas(io::stdout()).unwrap();
            let v = x.declassify();
            println!("{}", v);
            assert_eq!(v, b < c);

            let x = sa.clamp(sb, sc);
            x.clone().tree().disas(io::stdout()).unwrap();
            let v = x.declassify();
            println!("{}", v);
            assert_eq!(v, a.clamp(b, c));
        }

        test_ord(0, 1, 3);
        test_ord(2, 1, 3);
        test_ord(4, 1, 3);
    }

    #[test]
    fn int_clz() {
        println!();

        fn test_clz(n: u32) {
            let a = SecretU32::new(n);
            let x = a.clone().leading_zeros();
            x.clone().tree().disas(io::stdout()).unwrap();
            let v = x.declassify();
            println!("{}", v);
            assert_eq!(v, n.leading_zeros());

            let x = a.clone().is_power_of_two();
            x.clone().tree().disas(io::stdout()).unwrap();
            let v = x.declassify();
            println!("{}", v);
            assert_eq!(v, n.is_power_of_two());

            let x = a.next_power_of_two();
            x.clone().tree().disas(io::stdout()).unwrap();
            let v = x.declassify();
            println!("{}", v);
            assert_eq!(v, n.next_power_of_two());
        }

        test_clz(0);
        test_clz(1);
        test_clz(2);
        test_clz(3);
    }
}


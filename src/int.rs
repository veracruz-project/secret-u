//! Definitions of secret integers

use crate::opcode::OpTree;
use crate::opcode::OpType;
use crate::opcode::DynOpTree;
use crate::engine::exec;
use crate::error::Error;
use std::rc::Rc;
use std::convert::TryFrom;

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


/// A trait to facilitate type-unaware movement between OpTrees
pub trait SecretType
where
    Self: Sized,
    Self::TreeType: OpType
{
    /// Declassified representation
    type PrimType;

    /// In-tree representation
    type TreeType;

    /// Wraps a non-secret value as a secret value
    fn classify(n: Self::PrimType) -> Self;

    /// Extracts the secret value into a non-secret value, this
    /// effectively "leaks" the secret value, but is necessary
    /// to actually do anything
    fn declassify(self) -> Self::PrimType {
        self.try_declassify().unwrap()
    }

    /// Same as declassify but propagating internal VM errors
    ///
    /// Useful for catching things like divide-by-zero
    fn try_declassify(self) -> Result<Self::PrimType, Error>;

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
    ///
    /// Useful for catching things like divide-by-zero
    fn try_eval(self) -> Result<Self, Error> {
        Ok(Self::from_tree(OpTree::imm(self.tree().eval()?)))
    }

    /// Evaluate precompiled-bytecode to immediate form
    fn eval_bytecode(bytecode: &[u32], stack: &mut [u8]) -> Self::PrimType {
        Self::try_eval_bytecode(bytecode, stack).unwrap()
    }

    /// Same as eval_bytecode but propagating internal VM errors
    ///
    /// Useful for catching things like divide-by-zero
    fn try_eval_bytecode(bytecode: &[u32], stack: &mut [u8]) -> Result<Self::PrimType, Error>;

    /// Build from tree
    fn from_tree(tree: Rc<OpTree<Self::TreeType>>) -> Self;

    /// Get underlying tree
    fn tree(self) -> Rc<OpTree<Self::TreeType>>;
}

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
    fn max(self, other: Self) -> Self
    where
        Self: Clone + SecretType + From<SecretBool>
    {
        self.clone().gt(other.clone()).select(self, other)
    }

    fn min(self, other: Self) -> Self
    where
        Self: Clone + SecretType + From<SecretBool>
    {
        self.clone().lt(other.clone()).select(self, other)
    }

    fn clamp(self, min: Self, max: Self) -> Self
    where
        Self: Clone + SecretType + From<SecretBool>
    {
        self.max(min).min(max)
    }
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
/// Secret bool is a bit different than other SecretTypes, dynamically
/// preserving the original type until needed as this reduces unnecessary
/// casting
///
/// Note, like the underlying Rc type, clone is relatively cheap, but
/// not a bytewise copy, which means we can't implement the Copy trait
#[derive(Clone)]
pub struct SecretBool(Rc<dyn DynOpTree>);

impl SecretType for SecretBool {
    type PrimType = bool;
    type TreeType = [u8;1];

    fn classify(v: bool) -> SecretBool {
        SecretBool(OpTree::imm([v as u8]))
    }

    fn try_declassify(self) -> Result<bool, Error> {
        if self.0.is_sym() {
            return Err(Error::DeclassifyInCompile);
        }

        Ok(self.truncated_tree::<[u8;1]>().eval()?[0] != 0)
    }

    fn try_eval_bytecode(bytecode: &[u32], stack: &mut [u8]) -> Result<bool, Error> {
        let res = exec(bytecode, stack)?;
        let v = <u8>::from_le_bytes(
            <[u8;1]>::try_from(res).map_err(|_| Error::InvalidReturn)?
        );
        Ok(v != 0)
    }

    fn from_tree(tree: Rc<OpTree<Self::TreeType>>) -> Self {
        Self(tree)
    }

    fn tree(self) -> Rc<OpTree<Self::TreeType>> {
        self.truncated_tree()
    }
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
    pub fn new(v: bool) -> SecretBool {
        Self::classify(v)
    }

    /// Create a non-secret constant value, these are available for
    /// more optimizations than secret values
    pub fn const_(v: bool) -> SecretBool {
        Self(if v {
            OpTree::<[u8;1]>::one()
        } else {
            OpTree::<[u8;1]>::zero()
        })
    }

    /// Helper to convert to any type, we can do this without worry
    /// since we internally ensure the value is only ever zero or one
    fn truncated_tree<T: OpType>(self) -> Rc<OpTree<T>> {
        if T::SIZE > self.0.size() {
            OpTree::extend_s(self.0)
        } else if T::SIZE < self.0.size() {
            OpTree::extract(0, self.0)
        } else {
            OpTree::downcast(self.0)
        }
    }

    /// Select operation for secrecy-preserving conditionals
    pub fn select<T>(self, a: T, b: T) -> T
    where
        T: SecretType + From<SecretBool>
    {
        T::from_tree(OpTree::select(0,
            T::from(self).tree(),
            a.tree(),
            b.tree()
        ))
    }
}

impl Not for SecretBool {
    type Output = SecretBool;
    fn not(self) -> SecretBool {
        Self(self.0.dyn_not()(self.0))
    }
}

impl BitAnd for SecretBool {
    type Output = SecretBool;
    fn bitand(self, other: SecretBool) -> SecretBool {
        Self(OpTree::and(
            self.truncated_tree::<[u8;1]>(),
            other.truncated_tree::<[u8;1]>()
        ))
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
        Self(OpTree::or(
            self.truncated_tree::<[u8;1]>(),
            other.truncated_tree::<[u8;1]>()
        ))
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
        Self(OpTree::xor(
            self.truncated_tree::<[u8;1]>(),
            other.truncated_tree::<[u8;1]>()
        ))
    }
}

impl BitXorAssign for SecretBool {
    fn bitxor_assign(&mut self, other: SecretBool) {
        *self = self.clone().bitxor(other)
    }
}

impl SecretEq for SecretBool {
    fn eq(self, other: Self) -> SecretBool {
        SecretBool(OpTree::eq(0,
            self.truncated_tree::<[u8;1]>(),
            other.truncated_tree::<[u8;1]>()
        ))
    }

    fn ne(self, other: Self) -> SecretBool {
        SecretBool(OpTree::ne(0,
            self.truncated_tree::<[u8;1]>(),
            other.truncated_tree::<[u8;1]>()
        ))
    }
}


//// SecretU* ////

macro_rules! match_sig {
    (s { s => {$($a:tt)*} u => {$($b:tt)*} }) => {
        $($a)*
    };
    (u { s => {$($a:tt)*} u => {$($b:tt)*} }) => {
        $($b)*
    };
    (sa { s => {$($a:tt)*} u => {$($b:tt)*} }) => {
        $($a)*
    };
    (ua { s => {$($a:tt)*} u => {$($b:tt)*} }) => {
        $($b)*
    };
}

macro_rules! match_arr {
    (s { _ => {$($a:tt)*} a => {$($b:tt)*} }) => {
        $($a)*
    };
    (u { _ => {$($a:tt)*} a => {$($b:tt)*} }) => {
        $($a)*
    };
    (sa { _ => {$($a:tt)*} a => {$($b:tt)*} }) => {
        $($b)*
    };
    (ua { _ => {$($a:tt)*} a => {$($b:tt)*} }) => {
        $($b)*
    };
}

macro_rules! secret_impl {
    ($t:ident, $u:ty, $n:literal, $s:ident) => {
        /// A secret integer who's value is ensured to not be leaked by Rust's type-system
        ///
        /// Note, like the underlying Rc type, clone is relatively cheap, but
        /// not a bytewise copy, which means we can't implement the Copy trait
        #[derive(Clone)]
        pub struct $t(Rc<OpTree<[u8;$n]>>);

        impl SecretType for $t {
            type TreeType = [u8;$n];
            type PrimType = $u;

            fn classify(n: $u) -> Self {
                match_arr! { $s {
                    _ => {
                        Self(OpTree::imm(n.to_le_bytes()))
                    }
                    a => {
                        Self(OpTree::imm(n))
                    }
                }}
            }

            fn try_declassify(self) -> Result<$u, Error> {
                if self.0.is_sym() {
                    return Err(Error::DeclassifyInCompile);
                }

                match_arr! { $s {
                    _ => {
                        Ok(<$u>::from_le_bytes(self.0.eval()?))
                    }
                    a => {
                        Ok(self.0.eval()?)
                    }
                }}
            }

            fn try_eval_bytecode(bytecode: &[u32], stack: &mut [u8]) -> Result<$u, Error> {
                let res = exec(bytecode, stack)?;
                match_arr! { $s {
                    _ => {
                        Ok(<$u>::from_le_bytes(
                            <[u8;$n]>::try_from(res).map_err(|_| Error::InvalidReturn)?
                        ))
                    }
                    a => {
                        Ok(
                            <[u8;$n]>::try_from(res).map_err(|_| Error::InvalidReturn)?
                        )
                    }
                }}
            }

            fn from_tree(tree: Rc<OpTree<Self::TreeType>>) -> Self {
                Self(tree)
            }

            fn tree(self) -> Rc<OpTree<Self::TreeType>> {
                self.0
            }
        }

        impl From<$u> for $t {
            fn from(v: $u) -> $t {
                Self::classify(v)
            }
        }

        impl Default for $t {
            fn default() -> Self {
                Self::zero()
            }
        }

        impl $t {
            /// Wraps a non-secret value as a secret value
            pub fn new(v: $u) -> Self {
                Self::classify(v)
            }

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

            /// Create a non-secret constant value, these are available for
            /// more optimizations than secret values
            pub fn const_(v: $u) -> Self {
                match_arr! { $s {
                    _ => {
                        Self(OpTree::const_(v.to_le_bytes()))
                    }
                    a => {
                        Self(OpTree::const_(v))
                    }
                }
            }}

            // abs only available on signed types
            match_sig! { $s {
                s => {
                    pub fn abs(self) -> Self {
                        Self(OpTree::abs(0, self.0))
                    }
                }
                u => {}
            }}

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
            match_sig! { $s {
                s => {}
                u => {
                    pub fn is_power_of_two(self) -> SecretBool {
                        self.count_ones().eq(Self::one())
                    }

                    pub fn next_power_of_two(self) -> $t {
                        // based on implementation in rust core
                        self.clone().le(Self::one()).select(
                            // special case if <= 1
                            Self::zero(),
                            // next_power_of_two_minus_1
                            Self::ones() >> (self - Self::one()).leading_zeros()
                        ) + Self::one()
                    }
                }
            }}

            pub fn rotate_left(self, other: $t) -> $t {
                Self(OpTree::rotl(0, self.0, other.0))
            }

            pub fn rotate_right(self, other: $t) -> $t {
                Self(OpTree::rotr(0, self.0, other.0))
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
        match_sig! { $s {
            s => {
                impl Neg for $t {
                    type Output = $t;
                    fn neg(self) -> $t {
                        Self(OpTree::neg(0, self.0))
                    }
                }
            }
            u => {}
        }}

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
            match_sig! { $s {
                s => {
                    fn shr(self, other: $t) -> $t {
                        Self(OpTree::shr_s(0, self.0, other.0))
                    }
                }
                u => {
                    fn shr(self, other: $t) -> $t {
                        Self(OpTree::shr_u(0, self.0, other.0))
                    }
                }
            }}
        }

        impl ShrAssign for $t {
            fn shr_assign(&mut self, other: $t) {
                *self = self.clone().shr(other)
            }
        }

        impl SecretEq for $t {
            fn eq(self, other: Self) -> SecretBool {
                SecretBool(OpTree::eq(0, self.0, other.0))
            }

            fn ne(self, other: Self) -> SecretBool {
                SecretBool(OpTree::ne(0, self.0, other.0))
            }
        }

        impl SecretOrd for $t {
            match_sig! { $s {
                s => {
                    fn lt(self, other: Self) -> SecretBool {
                        SecretBool(OpTree::lt_s(0, self.0, other.0))
                    }

                    fn le(self, other: Self) -> SecretBool {
                        SecretBool(OpTree::le_s(0, self.0, other.0))
                    }

                    fn gt(self, other: Self) -> SecretBool {
                        SecretBool(OpTree::gt_s(0, self.0, other.0))
                    }

                    fn ge(self, other: Self) -> SecretBool {
                        SecretBool(OpTree::ge_s(0, self.0, other.0))
                    }
                }
                u => {
                    fn lt(self, other: Self) -> SecretBool {
                        SecretBool(OpTree::lt_u(0, self.0, other.0))
                    }

                    fn le(self, other: Self) -> SecretBool {
                        SecretBool(OpTree::le_u(0, self.0, other.0))
                    }

                    fn gt(self, other: Self) -> SecretBool {
                        SecretBool(OpTree::gt_u(0, self.0, other.0))
                    }

                    fn ge(self, other: Self) -> SecretBool {
                        SecretBool(OpTree::ge_u(0, self.0, other.0))
                    }
                }
            }}
        }
    }
}

secret_impl! { SecretU8,    u8,       1,   u  }
secret_impl! { SecretU16,   u16,      2,   u  }
secret_impl! { SecretU32,   u32,      4,   u  }
secret_impl! { SecretU64,   u64,      8,   u  }
secret_impl! { SecretU128,  u128,     16,  u  }
secret_impl! { SecretU256,  [u8;32],  32,  ua }
secret_impl! { SecretU512,  [u8;64],  64,  ua }
secret_impl! { SecretI8,    i8,       1,   s  }
secret_impl! { SecretI16,   i16,      2,   s  }
secret_impl! { SecretI32,   i32,      4,   s  }
secret_impl! { SecretI64,   i64,      8,   s  }
secret_impl! { SecretI128,  i128,     16,  s  }
secret_impl! { SecretI256,  [u8;32],  32,  sa }
secret_impl! { SecretI512,  [u8;64],  64,  sa }


//// Conversions U* <-> U* ////

// these are really tedius, so we use a really heavy-weight macro here
macro_rules! secret_from_impl {
    // bool extending (bool -> u32)
    ($from:ty => FB($to:ty), $($rest:tt)*) => {
        impl From<$from> for $to {
            fn from(v: $from) -> $to {
                Self(v.truncated_tree())
            }
        }
        secret_from_impl! { $from => $($rest)* }
    };
    // cast sign (i32 -> u32)
    ($from:ty => CS($to:ty), $($rest:tt)*) => {
        impl Cast<$from> for $to {
            fn cast(v: $from) -> $to {
                Self(v.0)
            }
        }
        secret_from_impl! { $from => $($rest)* }
    };
    // cast truncating (u32 -> u8)
    ($from:ty => CT($to:ty), $($rest:tt)*) => {
        impl Cast<$from> for $to {
            fn cast(v: $from) -> $to {
                Self(OpTree::extract(0, v.0))
            }
        }
        secret_from_impl! { $from => $($rest)* }
    };
    // unsigned extending (u8 -> u32)
    ($from:ty => FU($to:ty), $($rest:tt)*) => {
        impl From<$from> for $to {
            fn from(v: $from) -> $to {
                Self(OpTree::extend_u(v.0))
            }
        }
        secret_from_impl! { $from => $($rest)* }
    };
    // signed extending (i8 -> i32)
    ($from:ty => FS($to:ty), $($rest:tt)*) => {
        impl From<$from> for $to {
            fn from(v: $from) -> $to {
                Self(OpTree::extend_s(v.0))
            }
        }
        secret_from_impl! { $from => $($rest)* }
    };
    // base cases
    ($from:ty => ) => {};
    ($_:ty => $from:ty => $($rest:tt)*) => {
        secret_from_impl! { $from => $($rest)* }
    };
}

secret_from_impl! {
    SecretBool  => FB(SecretU8), FB(SecretU16), FB(SecretU32), FB(SecretU64), FB(SecretU128), FB(SecretU256), FB(SecretU512),
    SecretBool  => FB(SecretI8), FB(SecretI16), FB(SecretI32), FB(SecretI64), FB(SecretI128), FB(SecretI256), FB(SecretI512),
}

secret_from_impl! {
    SecretU8    =>               FU(SecretU16), FU(SecretU32), FU(SecretU64), FU(SecretU128), FU(SecretU256), FU(SecretU512),
    SecretU16   => CT(SecretU8),                FU(SecretU32), FU(SecretU64), FU(SecretU128), FU(SecretU256), FU(SecretU512),
    SecretU32   => CT(SecretU8), CT(SecretU16),                FU(SecretU64), FU(SecretU128), FU(SecretU256), FU(SecretU512),
    SecretU64   => CT(SecretU8), CT(SecretU16), CT(SecretU32),                FU(SecretU128), FU(SecretU256), FU(SecretU512),
    SecretU128  => CT(SecretU8), CT(SecretU16), CT(SecretU32), CT(SecretU64),                 FU(SecretU256), FU(SecretU512),
    SecretU256  => CT(SecretU8), CT(SecretU16), CT(SecretU32), CT(SecretU64), CT(SecretU128),                 FU(SecretU512),
    SecretU512  => CT(SecretU8), CT(SecretU16), CT(SecretU32), CT(SecretU64), CT(SecretU128), CT(SecretU256),

    SecretU8    => CS(SecretI8), FU(SecretI16), FU(SecretI32), FU(SecretI64), FU(SecretI128), FU(SecretI256), FU(SecretI512),
    SecretU16   =>               CS(SecretI16), FU(SecretI32), FU(SecretI64), FU(SecretI128), FU(SecretI256), FU(SecretI512),
    SecretU32   =>                              CS(SecretI32), FU(SecretI64), FU(SecretI128), FU(SecretI256), FU(SecretI512),
    SecretU64   =>                                             CS(SecretI64), FU(SecretI128), FU(SecretI256), FU(SecretI512),
    SecretU128  =>                                                            CS(SecretI128), FU(SecretI256), FU(SecretI512),
    SecretU256  =>                                                                            CS(SecretI256), FU(SecretI512),
    SecretU512  =>                                                                                            CS(SecretI512),
}

secret_from_impl! {
    SecretI8    => CS(SecretU8),
    SecretI16   =>               CS(SecretU16),
    SecretI32   =>                              CS(SecretU32),
    SecretI64   =>                                             CS(SecretU64),
    SecretI128  =>                                                            CS(SecretU128),
    SecretI256  =>                                                                            CS(SecretU256),
    SecretI512  =>                                                                                            CS(SecretU512),

    SecretI8    =>               FS(SecretI16), FS(SecretI32), FS(SecretI64), FS(SecretI128), FS(SecretI256), FS(SecretI512),
    SecretI16   => CT(SecretI8),                FS(SecretI32), FS(SecretI64), FS(SecretI128), FS(SecretI256), FS(SecretI512),
    SecretI32   => CT(SecretI8), CT(SecretI16),                FS(SecretI64), FS(SecretI128), FS(SecretI256), FS(SecretI512),
    SecretI64   => CT(SecretI8), CT(SecretI16), CT(SecretI32),                FS(SecretI128), FS(SecretI256), FS(SecretI512),
    SecretI128  => CT(SecretI8), CT(SecretI16), CT(SecretI32), CT(SecretI64),                 FS(SecretI256), FS(SecretI512),
    SecretI256  => CT(SecretI8), CT(SecretI16), CT(SecretI32), CT(SecretI64), CT(SecretI128),                 FS(SecretI512),
    SecretI512  => CT(SecretI8), CT(SecretI16), CT(SecretI32), CT(SecretI64), CT(SecretI128), CT(SecretI256),
}


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


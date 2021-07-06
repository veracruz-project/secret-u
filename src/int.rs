//! Definitions of secret integers

use crate::opcode::OpTree;
use crate::opcode::OpKind;
use crate::opcode::OpType;
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
use std::ops::Div;
use std::ops::DivAssign;
use std::ops::Rem;
use std::ops::RemAssign;
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
    type TreeType;

    /// Build from tree
    fn from_tree(tree: Rc<OpTree<Self::TreeType>>) -> Self;

    /// Get underlying tree
    fn tree(self) -> Rc<OpTree<Self::TreeType>>;

    /// Evaluates to immediate form
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
        Ok(Self::from_tree(Rc::new(OpTree::new(OpKind::Imm(self.tree().eval()?)))))
    }
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
pub trait SecretTruncate<T> {
    fn truncate(t: T) -> Self;
}

impl<T, U> SecretTruncate<U> for T
where
    T: SecretType + From<U>,
    U: SecretType
{
    fn truncate(u: U) -> T {
        T::from(u)
    }
}


//// SecretBool ////

/// A secret bool who's value is ensured to not be leaked by Rust's type-system
pub struct SecretBool(Rc<OpTree<u8>>);

impl SecretBool {
    /// Wraps a non-secret value as a secret value
    pub fn new(n: bool) -> Self {
        Self(Rc::new(OpTree::new(OpKind::Imm(n as u8))))
    }

    /// Extracts the secret value into a non-secret value
    ///
    /// Note this effectively "leaks" the secret value, so
    /// is only allowed in unsafe code
    pub unsafe fn declassify(self) -> bool {
        self.try_declassify().unwrap()
    }

    /// Same as declassify but propagating internal VM errors
    ///
    /// Useful for catching things like divide-by-zero
    pub unsafe fn try_declassify(self) -> Result<bool, Error> {
        Ok(self.0.eval()? != 0)
    }

    /// Select operation for secrecy-preserving conditionals
    pub fn select<T>(self, a: T, b: T) -> T
    where
        T: SecretType + From<SecretBool>
    {
        T::from_tree(Rc::new(OpTree::new(OpKind::Select(
            T::from(self).tree(),
            a.tree(),
            b.tree()
        ))))
    }
}

impl SecretType for SecretBool {
    type TreeType = u8;

    fn from_tree(tree: Rc<OpTree<Self::TreeType>>) -> Self {
        Self(tree)
    }

    fn tree(self) -> Rc<OpTree<Self::TreeType>> {
        self.0
    }
}

impl From<bool> for SecretBool {
    fn from(v: bool) -> SecretBool {
        Self::new(v)
    }
}

impl Clone for SecretBool {
    /// Much like the underlying Rc type, clone is relatively cheap,
    /// but not a bytewise copy, which means we can't implement the
    /// Copy trait
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl Default for SecretBool {
    fn default() -> Self {
        // we use SecretU8 here for the shared constant
        Self(OpTree::zero())
    }
}

impl Not for SecretBool {
    type Output = SecretBool;
    fn not(self) -> SecretBool {
        Self(Rc::new(OpTree::new(OpKind::Eqz(self.0))))
    }
}

impl BitAnd for SecretBool {
    type Output = SecretBool;
    fn bitand(self, other: SecretBool) -> SecretBool {
        Self(Rc::new(OpTree::new(OpKind::And(self.0, other.0))))
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
        Self(Rc::new(OpTree::new(OpKind::Or(self.0, other.0))))
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
        Self(Rc::new(OpTree::new(OpKind::Xor(self.0, other.0))))
    }
}

impl BitXorAssign for SecretBool {
    fn bitxor_assign(&mut self, other: SecretBool) {
        *self = self.clone().bitxor(other)
    }
}

impl SecretEq for SecretBool {
    fn eq(self, other: Self) -> SecretBool {
        SecretBool(Rc::new(OpTree::new(OpKind::Eq(self.0, other.0))))
    }

    fn ne(self, other: Self) -> SecretBool {
        SecretBool(Rc::new(OpTree::new(OpKind::Ne(self.0, other.0))))
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
}

macro_rules! secret_eq_impl {
    // special case for u8, no truncate necessary
    // TODO should we try to avoid downcasting to u8 when not needed?
    ($t:ident, u8) => {
        impl SecretEq for u8 {
            fn eq(self, other: Self) -> SecretBool {
                SecretBool(Rc::new(OpTree::new(OpKind::Eq(self.0, other.0))))
            }

            fn ne(self, other: Self) -> SecretBool {
                SecretBool(Rc::new(OpTree::new(OpKind::Ne(self.0, other.0))))
            }
        }
    };
    ($t:ident, $u:ty) => {
        impl SecretEq for $t {
            fn eq(self, other: Self) -> SecretBool {
                SecretBool(Rc::new(OpTree::new(OpKind::Truncate(
                    Rc::new(OpTree::new(OpKind::Eq(self.0, other.0)))
                ))))
            }

            fn ne(self, other: Self) -> SecretBool {
                SecretBool(Rc::new(OpTree::new(OpKind::Truncate(
                    Rc::new(OpTree::new(OpKind::Eq(self.0, other.0)))
                ))))
            }
        }
    };
}

macro_rules! secret_ord_impl {
    // special case for u8, no truncate necessary
    // TODO should we try to avoid downcasting to u8 when not needed?
    ($t:ident, u8, $s:ident) => {
        impl SecretOrd for u8 {
            fn lt(self, other: Self) -> SecretBool {
                SecretBool(Rc::new(OpTree::new(OpKind::Lt(self.0, other.0))))
            }

            fn le(self, other: Self) -> SecretBool {
                SecretBool(Rc::new(OpTree::new(OpKind::Le(self.0, other.0))))
            }

            fn gt(self, other: Self) -> SecretBool {
                SecretBool(Rc::new(OpTree::new(OpKind::Gt(self.0, other.0))))
            }

            fn ge(self, other: Self) -> SecretBool {
                SecretBool(Rc::new(OpTree::new(OpKind::Ge(self.0, other.0))))
            }
        }
    };
    ($t:ident, $u:ty, $s:ident) => {
        impl SecretOrd for $t {
            match_sig! { $s {
                s => {
                    fn lt(self, other: Self) -> SecretBool {
                        SecretBool(Rc::new(OpTree::new(OpKind::Truncate(
                            Rc::new(OpTree::new(OpKind::Lts(self.0, other.0)))
                        ))))
                    }

                    fn le(self, other: Self) -> SecretBool {
                        SecretBool(Rc::new(OpTree::new(OpKind::Truncate(
                            Rc::new(OpTree::new(OpKind::Les(self.0, other.0)))
                        ))))
                    }

                    fn gt(self, other: Self) -> SecretBool {
                        SecretBool(Rc::new(OpTree::new(OpKind::Truncate(
                            Rc::new(OpTree::new(OpKind::Gts(self.0, other.0)))
                        ))))
                    }

                    fn ge(self, other: Self) -> SecretBool {
                        SecretBool(Rc::new(OpTree::new(OpKind::Truncate(
                            Rc::new(OpTree::new(OpKind::Ges(self.0, other.0)))
                        ))))
                    }
                }
                u => {
                    fn lt(self, other: Self) -> SecretBool {
                        SecretBool(Rc::new(OpTree::new(OpKind::Truncate(
                            Rc::new(OpTree::new(OpKind::Ltu(self.0, other.0)))
                        ))))
                    }

                    fn le(self, other: Self) -> SecretBool {
                        SecretBool(Rc::new(OpTree::new(OpKind::Truncate(
                            Rc::new(OpTree::new(OpKind::Leu(self.0, other.0)))
                        ))))
                    }

                    fn gt(self, other: Self) -> SecretBool {
                        SecretBool(Rc::new(OpTree::new(OpKind::Truncate(
                            Rc::new(OpTree::new(OpKind::Gtu(self.0, other.0)))
                        ))))
                    }

                    fn ge(self, other: Self) -> SecretBool {
                        SecretBool(Rc::new(OpTree::new(OpKind::Truncate(
                            Rc::new(OpTree::new(OpKind::Geu(self.0, other.0)))
                        ))))
                    }
                }
            }}
        }
    };
}

macro_rules! secret_impl {
    ($t:ident, $u:ty, $v:ty, $s:ident) => {
        /// A secret integer who's value is ensured to not be leaked by Rust's type-system
        pub struct $t(Rc<OpTree<$u>>);

        impl $t {
            /// Wraps a non-secret value as a secret value
            pub fn new(n: $v) -> Self {
                Self(Rc::new(OpTree::new(OpKind::Imm(n as $u))))
            }

            /// Extracts the secret value into a non-secret value
            ///
            /// Note this effectively "leaks" the secret value, so
            /// is only allowed in unsafe code
            pub unsafe fn declassify(self) -> $v {
                self.try_declassify().unwrap() as $v
            }

            /// Same as declassify but propagating internal VM errors
            ///
            /// Useful for catching things like divide-by-zero
            pub unsafe fn try_declassify(self) -> Result<$v, Error> {
                Ok(self.0.eval()? as $v)
            }

            // abs only available on signed types
            match_sig! { $s {
                s => {
                    pub fn abs(self) -> Self {
                        self.clone().lt(Self(OpTree::zero())).select(
                            self.clone().neg(),
                            self
                        )
                    }
                }
                u => {}
            }}

            // other non-trait operations
            pub fn trailing_zeros(self) -> $t {
                Self(Rc::new(OpTree::new(OpKind::Ctz(self.0))))
            }

            pub fn trailing_ones(self) -> $t {
                (!self).trailing_zeros()
            }

            pub fn leading_zeros(self) -> $t {
                Self(Rc::new(OpTree::new(OpKind::Clz(self.0))))
            }

            pub fn leading_ones(self) -> $t {
                (!self).leading_zeros()
            }

            pub fn count_zeros(self) -> $t {
                (!self).count_ones()
            }

            pub fn count_ones(self) -> $t {
                Self(Rc::new(OpTree::new(OpKind::Popcnt(self.0))))
            }

            // ipw2/npw2 only available on unsigned types
            match_sig! { $s {
                s => {}
                u => {
                    pub fn is_power_of_two(self) -> SecretBool {
                        self.count_ones().eq(Self(OpTree::one()))
                    }

                    pub fn next_power_of_two(self) -> $t {
                        // based on implementation in rust core
                        self.clone().le(Self(OpTree::one()).clone()).select(
                            // special case if <= 1
                            Self(OpTree::zero()),
                            // next_power_of_two_minus_1
                            Self(OpTree::ones())
                                >> (self - Self(OpTree::one()).clone()).leading_zeros()
                        ) + Self(OpTree::one())
                    }
                }
            }}

            pub fn rotate_left(self, other: $t) -> $t {
                Self(Rc::new(OpTree::new(OpKind::Rotl(self.0, other.0))))
            }

            pub fn rotate_right(self, other: $t) -> $t {
                Self(Rc::new(OpTree::new(OpKind::Rotr(self.0, other.0))))
            }
        }

        impl SecretType for $t {
            type TreeType = $u;

            fn from_tree(tree: Rc<OpTree<Self::TreeType>>) -> Self {
                Self(tree)
            }

            fn tree(self) -> Rc<OpTree<Self::TreeType>> {
                self.0
            }
        }

        impl From<$v> for $t {
            fn from(v: $v) -> $t {
                Self::new(v)
            }
        }

        impl Clone for $t {
            /// Much like the underlying Rc type, clone is relatively cheap,
            /// but not a bytewise copy, which means we can't implement the
            /// Copy trait
            fn clone(&self) -> Self {
                Self(self.0.clone())
            }
        }

        impl Default for $t {
            fn default() -> Self {
                Self(OpTree::zero())
            }
        }

        impl Not for $t {
            type Output = $t;
            fn not(self) -> $t {
                // note, this is how it's done in wasm
                self ^ Self(OpTree::ones())
            }
        }

        impl BitAnd for $t {
            type Output = $t;
            fn bitand(self, other: $t) -> $t {
                Self(Rc::new(OpTree::new(OpKind::And(self.0, other.0))))
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
                Self(Rc::new(OpTree::new(OpKind::Or(self.0, other.0))))
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
                Self(Rc::new(OpTree::new(OpKind::Xor(self.0, other.0))))
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
                        // note, this is how it's done in wasm
                        Self(OpTree::zero()) - self
                    }
                }
            }
            u => {}
        }}

        impl Add for $t {
            type Output = $t;
            fn add(self, other: $t) -> $t {
                Self(Rc::new(OpTree::new(OpKind::Add(self.0, other.0))))
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
                Self(Rc::new(OpTree::new(OpKind::Sub(self.0, other.0))))
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
                Self(Rc::new(OpTree::new(OpKind::Mul(self.0, other.0))))
            }
        }

        impl MulAssign for $t {
            fn mul_assign(&mut self, other: $t) {
                *self = self.clone().mul(other)
            }
        }

        impl Div for $t {
            type Output = $t;
            match_sig! { $s {
                s => {
                    fn div(self, other: $t) -> $t {
                        Self(Rc::new(OpTree::new(OpKind::Divs(self.0, other.0))))
                    }
                }
                u => {
                    fn div(self, other: $t) -> $t {
                        Self(Rc::new(OpTree::new(OpKind::Divu(self.0, other.0))))
                    }
                }
            }}
        }

        impl DivAssign for $t {
            fn div_assign(&mut self, other: $t) {
                *self = self.clone().div(other)
            }
        }

        impl Rem for $t {
            type Output = $t;
            match_sig! { $s {
                s => {
                    fn rem(self, other: $t) -> $t {
                        Self(Rc::new(OpTree::new(OpKind::Rems(self.0, other.0))))
                    }
                }
                u => {
                    fn rem(self, other: $t) -> $t {
                        Self(Rc::new(OpTree::new(OpKind::Remu(self.0, other.0))))
                    }
                }
            }}
        }

        impl RemAssign for $t {
            fn rem_assign(&mut self, other: $t) {
                *self = self.clone().rem(other)
            }
        }

        impl Shl for $t {
            type Output = $t;
            fn shl(self, other: $t) -> $t {
                Self(Rc::new(OpTree::new(OpKind::Shl(self.0, other.0))))
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
                        Self(Rc::new(OpTree::new(OpKind::Shrs(self.0, other.0))))
                    }
                }
                u => {
                    fn shr(self, other: $t) -> $t {
                        Self(Rc::new(OpTree::new(OpKind::Shru(self.0, other.0))))
                    }
                }
            }}
        }

        impl ShrAssign for $t {
            fn shr_assign(&mut self, other: $t) {
                *self = self.clone().shr(other)
            }
        }

        secret_eq_impl! { $t, $u }
        secret_ord_impl! { $t, $u, $s }
    }
}

secret_impl! { SecretU8,  u8,  u8,  u }
secret_impl! { SecretU16, u16, u16, u }
secret_impl! { SecretU32, u32, u32, u }
secret_impl! { SecretI8,  u8,  i8,  s }
secret_impl! { SecretI16, u16, i16, s }
secret_impl! { SecretI32, u32, i32, s }


//// Conversions U* <-> U* ////

impl From<SecretBool> for SecretU8 {
    fn from(v: SecretBool) -> SecretU8 {
        Self(v.0)
    }
}

impl From<SecretBool> for SecretU16 {
    fn from(v: SecretBool) -> SecretU16 {
        Self::from(SecretU8::from(v))
    }
}

impl From<SecretBool> for SecretU32 {
    fn from(v: SecretBool) -> SecretU32 {
        Self::from(SecretU8::from(v))
    }
}

impl From<SecretBool> for SecretI8 {
    fn from(v: SecretBool) -> SecretI8 {
        Self(v.0)
    }
}

impl From<SecretBool> for SecretI16 {
    fn from(v: SecretBool) -> SecretI16 {
        Self::from(SecretI8::from(v))
    }
}

impl From<SecretBool> for SecretI32 {
    fn from(v: SecretBool) -> SecretI32 {
        Self::from(SecretI8::from(v))
    }
}

impl From<SecretU8> for SecretU16 {
    fn from(v: SecretU8) -> SecretU16 {
        Self(Rc::new(OpTree::new(OpKind::Extendu(v.0))))
    }
}

impl From<SecretU8> for SecretU32 {
    fn from(v: SecretU8) -> SecretU32 {
        Self(Rc::new(OpTree::new(OpKind::Extendu(v.0))))
    }
}

impl SecretTruncate<SecretU8> for SecretI8 {
    fn truncate(v: SecretU8) -> SecretI8 {
        Self(v.0)
    }
}

impl From<SecretU8> for SecretI16 {
    fn from(v: SecretU8) -> SecretI16 {
        Self(Rc::new(OpTree::new(OpKind::Extendu(v.0))))
    }
}

impl From<SecretU8> for SecretI32 {
    fn from(v: SecretU8) -> SecretI32 {
        Self(Rc::new(OpTree::new(OpKind::Extendu(v.0))))
    }
}

impl SecretTruncate<SecretI8> for SecretU8 {
    fn truncate(v: SecretI8) -> SecretU8 {
        Self(v.0)
    }
}

impl From<SecretI8> for SecretI16 {
    fn from(v: SecretI8) -> SecretI16 {
        Self(Rc::new(OpTree::new(OpKind::Extends(v.0))))
    }
}

impl From<SecretI8> for SecretI32 {
    fn from(v: SecretI8) -> SecretI32 {
        Self(Rc::new(OpTree::new(OpKind::Extends(v.0))))
    }
}

impl SecretTruncate<SecretU16> for SecretI16 {
    fn truncate(v: SecretU16) -> SecretI16 {
        Self(v.0)
    }
}

impl SecretTruncate<SecretU16> for SecretU8 {
    fn truncate(v: SecretU16) -> SecretU8 {
        Self(Rc::new(OpTree::new(OpKind::Truncate(v.0))))
    }
}

impl From<SecretU16> for SecretU32 {
    fn from(v: SecretU16) -> SecretU32 {
        Self(Rc::new(OpTree::new(OpKind::Extendu(v.0))))
    }
}

impl From<SecretU16> for SecretI32 {
    fn from(v: SecretU16) -> SecretI32 {
        Self(Rc::new(OpTree::new(OpKind::Extendu(v.0))))
    }
}

impl SecretTruncate<SecretI16> for SecretU16 {
    fn truncate(v: SecretI16) -> SecretU16 {
        Self(v.0)
    }
}

impl SecretTruncate<SecretI16> for SecretI8 {
    fn truncate(v: SecretI16) -> SecretI8 {
        Self(Rc::new(OpTree::new(OpKind::Truncate(v.0))))
    }
}

impl From<SecretI16> for SecretI32 {
    fn from(v: SecretI16) -> SecretI32 {
        Self(Rc::new(OpTree::new(OpKind::Extends(v.0))))
    }
}

impl SecretTruncate<SecretU32> for SecretI32 {
    fn truncate(v: SecretU32) -> SecretI32 {
        Self(v.0)
    }
}

impl SecretTruncate<SecretU32> for SecretU8 {
    fn truncate(v: SecretU32) -> SecretU8 {
        Self(Rc::new(OpTree::new(OpKind::Truncate(v.0))))
    }
}

impl SecretTruncate<SecretU32> for SecretU16 {
    fn truncate(v: SecretU32) -> SecretU16 {
        Self(Rc::new(OpTree::new(OpKind::Truncate(v.0))))
    }
}

impl SecretTruncate<SecretI32> for SecretU32 {
    fn truncate(v: SecretI32) -> SecretU32 {
        Self(v.0)
    }
}

impl SecretTruncate<SecretI32> for SecretI8 {
    fn truncate(v: SecretI32) -> SecretI8 {
        Self(Rc::new(OpTree::new(OpKind::Truncate(v.0))))
    }
}

impl SecretTruncate<SecretI32> for SecretI16 {
    fn truncate(v: SecretI32) -> SecretI16 {
        Self(Rc::new(OpTree::new(OpKind::Truncate(v.0))))
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn int_bool1() {
        println!();
        let a = SecretBool::new(true);
        let b = SecretBool::new(true);
        let x = (a.clone() & b.clone()).eq(a | b);
        println!("{}", x.0);
        let v = unsafe { x.declassify() };
        println!("{}", v);
        assert_eq!(v, true);
    }

    #[test]
    fn int_bool2() {
        println!();
        let a = SecretBool::new(true);
        let b = SecretBool::new(false);
        let x = (a.clone() | b.clone()).select(a, b);
        println!("{}", x.0);
        let v = unsafe { x.declassify() };
        println!("{}", v);
        assert_eq!(v, true);
    }

    #[test]
    fn int_abs() {
        println!();
        let a = SecretI32::new(-100);
        let x = a.abs();
        println!("{}", x.0);
        let v = unsafe { x.declassify() };
        println!("{}", v);
        assert_eq!(v, 100);
    }

    #[test]
    fn int_u32() {
        println!();
        let a = SecretU32::new(3);
        let b = SecretU32::new(4);
        let c = SecretU32::new(5);
        let x = (a.clone()*a + b.clone()*b) / c;
        println!("{}", x.0);
        let v = unsafe { x.declassify() };
        println!("{}", v);
        assert_eq!(v, 5);
    }

    #[test]
    fn int_i32() {
        println!();
        let a = SecretI32::new(-3);
        let b = SecretI32::new(-4);
        let c = SecretI32::new(-5);
        let x = (a.clone()*a + b.clone()*b) / c;
        println!("{}", x.0);
        let v = unsafe { x.declassify() };
        println!("{}", v);
        assert_eq!(v, -5);
    }

    #[test]
    fn int_ord() {
        println!();

        fn test_ord(a: u32, b: u32, c: u32) {
            let sa = SecretU32::new(a);
            let sb = SecretU32::new(b);
            let sc = SecretU32::new(c);
            let x = sb.clone().lt(sc.clone());
            println!("{}", x.0);
            let v = unsafe { x.declassify() };
            println!("{}", v);
            assert_eq!(v, b < c);

            let x = sa.clamp(sb, sc);
            println!("{}", x.0);
            let v = unsafe { x.declassify() };
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
            println!("{}", x.0);
            let v = unsafe { x.declassify() };
            println!("{}", v);
            assert_eq!(v, n.leading_zeros());

            let x = a.clone().is_power_of_two();
            println!("{}", x.0);
            let v = unsafe { x.declassify() };
            println!("{}", v);
            assert_eq!(v, n.is_power_of_two());

            let x = a.next_power_of_two();
            println!("{}", x.0);
            let v = unsafe { x.declassify() };
            println!("{}", v);
            assert_eq!(v, n.next_power_of_two());
        }

        test_clz(0);
        test_clz(1);
        test_clz(2);
        test_clz(3);
    }
}


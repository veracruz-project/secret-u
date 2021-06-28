//! Definitions of secret integers

pub mod opcode;
pub mod error;

use std::str::FromStr;
use std::str::ParseBoolError;
use std::num::ParseIntError;
use std::ops::Not;
use std::ops::BitAnd;
use std::ops::BitAndAssign;
use std::ops::BitOr;
use std::ops::BitOrAssign;
use std::ops::BitXor;
use std::ops::BitXorAssign;


// TODO move these? the are copied from Rust's stdlib

// implements the unary operator "op &T"
// based on "op T" where T is expected to be `Copy`able
macro_rules! forward_ref_unop {
    (impl $imp:ident, $method:ident for $t:ty) => {
        impl $imp for &$t {
            type Output = <$t as $imp>::Output;
            fn $method(self) -> <$t as $imp>::Output {
                $imp::$method(*self)
            }
        }
    }
}

// implements binary operators "&T op U", "T op &U", "&T op &U"
// based on "T op U" where T and U are expected to be `Copy`able
macro_rules! forward_ref_binop {
    (impl $imp:ident, $method:ident for $t:ty, $u:ty) => {
        impl<'a> $imp<$u> for &'a $t {
            type Output = <$t as $imp<$u>>::Output;
            fn $method(self, other: $u) -> <$t as $imp<$u>>::Output {
                $imp::$method(*self, other)
            }
        }

        impl $imp<&$u> for $t {
            type Output = <$t as $imp<$u>>::Output;
            fn $method(self, other: &$u) -> <$t as $imp<$u>>::Output {
                $imp::$method(self, *other)
            }
        }

        impl $imp<&$u> for &$t {
            type Output = <$t as $imp<$u>>::Output;
            fn $method(self, other: &$u) -> <$t as $imp<$u>>::Output {
                $imp::$method(*self, *other)
            }
        }
    }
}

// implements "T op= &U", based on "T op= U"
// where U is expected to be `Copy`able
macro_rules! forward_ref_op_assign {
    (impl $imp:ident, $method:ident for $t:ty, $u:ty) => {
        impl $imp<&$u> for $t {
            fn $method(&mut self, other: &$u) {
                $imp::$method(self, *other);
            }
        }
    }
}

// implements "T op= U", based on "T = T op U"
// where U is expected to be `Copy`able
macro_rules! forward_op_assign {
    (impl $imp:ident, $method:ident<$op:ident> for $t:ty, $u:ty) => {
        impl $imp for $t {
            fn $method(&mut self, other: $u) {
                *self = (*self).$op(other);
            }
        }

        forward_ref_op_assign! { impl $imp, $method for $t, $u }
    }
}

//   // 
//   macro_rules! forward_binop {
//       (impl $imp:ident, $method:ident for $t:ty, $u:ty) => {
//           forward_ref_binop! { impl $imp, $method for $t, $u }
//           paste! {
//               forward_assign_binop! { impl [<$imp Assign>], [<$method _assign>] for $t, $u }
//           }
//       }
//   }



/// A secret bool who's value is ensured to not be leaked by Rust's type-system
#[derive(Copy, Clone, Default)]
pub struct SecretBool(bool);

impl SecretBool {
    /// Wraps a non-secret value as a secret value
    pub const fn new(n: bool) -> Self {
        Self(n)
    }

    /// Extracts the secret value into a non-secret value
    ///
    /// Note this effectively "leaks" the secret value, so
    /// is only allowed in unsafe code
    unsafe fn declassify(self) -> bool {
        self.0
    }
}

//// FromStr ////

impl FromStr for SecretBool {
    type Err = ParseBoolError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::new(bool::from_str(s)?))
    }
}

//// bitwise operations ////

impl Not for SecretBool {
    type Output = SecretBool;
    fn not(self) -> Self::Output {
        Self::new(unsafe { !self.declassify() })
    }
}
forward_ref_unop! { impl Not, not for SecretBool }

impl BitAnd for SecretBool {
    type Output = SecretBool;
    fn bitand(self, other: Self) -> Self::Output {
        Self::new(unsafe { self.declassify() & other.declassify() })
    }
}
forward_ref_binop! { impl BitAnd, bitand for SecretBool, SecretBool }
forward_op_assign! { impl BitAndAssign, bitand_assign<bitand> for SecretBool, SecretBool }

impl BitOr for SecretBool {
    type Output = SecretBool;
    fn bitor(self, other: Self) -> Self::Output {
        Self::new(unsafe { self.declassify() | other.declassify() })
    }
}
forward_ref_binop! { impl BitOr, bitor for SecretBool, SecretBool }
forward_op_assign! { impl BitOrAssign, bitor_assign<bitor> for SecretBool, SecretBool }


impl BitXor for SecretBool {
    type Output = SecretBool;
    fn bitxor(self, other: Self) -> Self::Output {
        Self::new(unsafe { self.declassify() ^ other.declassify() })
    }
}
forward_ref_binop! { impl BitXor, bitxor for SecretBool, SecretBool }
forward_op_assign! { impl BitXorAssign, bitxor_assign<bitxor> for SecretBool, SecretBool }

// TODO note shl/shr needed for u8-usize
// neg, add, sub, mul, div


//// SecretEq/SecretPartialEq ////

pub trait SecretPartialEq<Rhs: ?Sized = Self> {
    /// This method tests for `self` and `other` values to be equal.
    #[must_use]
    fn eq(&self, other: &Rhs) -> SecretBool;

    /// This method tests for `!=`.
    #[must_use]
    fn ne(&self, other: &Rhs) -> SecretBool {
        !self.eq(other)
    }
}

pub trait SecretEq: SecretPartialEq<Self> {}

impl SecretPartialEq for SecretBool {
    fn eq(&self, other: &Self) -> SecretBool {
        SecretBool::new(unsafe { self.declassify() == other.declassify() })
    }

    fn ne(&self, other: &Self) -> SecretBool {
        SecretBool::new(unsafe { self.declassify() != other.declassify() })
    }
}

impl SecretEq for SecretBool {}


//// SecretOrd/SecretPartialOrd ////

// TODO

//// Select ternary operator ////

pub trait Select<A, B> {
    /// The result of select.
    type Output;

    /// Selects either `a` or `b` based on the current value.
    #[must_use]
    fn select(&self, a: A, b: B) -> Self::Output;
}

macro_rules! select_impl {
    ($t:ty, $f:ty) => {
        impl Select<$f, $f> for $t {
            type Output = $f;
            fn select(&self, a: $f, b: $f) -> $f {
                <$f>::new(
                    unsafe {
                        if self.declassify() {
                            a.declassify()
                        } else {
                            b.declassify()
                        }
                    }
                )
            }
        }

        impl Select<&$f, $f> for $t {
            type Output = $f;
            fn select(&self, a: &$f, b: $f) -> $f {
                Select::select(self, *a, b)
            }
        }

        impl Select<$f, &$f> for $t {
            type Output = $f;
            fn select(&self, a: $f, b: &$f) -> $f {
                Select::select(self, a, *b)
            }
        }

        impl Select<&$f, &$f> for $t {
            type Output = $f;
            fn select(&self, a: &$f, b: &$f) -> $f {
                Select::select(self, *a, *b)
            }
        }
    }
}

select_impl! { SecretBool, SecretBool }





macro_rules! secret_integers {
    ( $( $U:ident($u:ty); )+ ) => {
        $(
            /// A secret integer who's value is ensured to not be leaked by Rust's type-system
            #[derive(Copy, Clone)]
            pub struct $U($u);

            impl $U {
                /// Creates a secret value
                pub const fn new(n: $u) -> Self {
                    Self(n)
                }

                /// Extracts the secret value into a non-secret value
                ///
                /// Note this effectively "leaks" the secret value, so
                /// is only allowed in unsafe code
                pub const unsafe fn declassify(self) -> $u {
                    self.0
                }
            }

            impl FromStr for $U {
                type Err = ParseIntError;
                fn from_str(s: &str) -> Result<Self, Self::Err> {
                    Ok(Self::new(<$u>::from_str(s)?))
                }
            }
        )+
    }
}

secret_integers! {
    SecretU8(u8);
    SecretU16(u16);
    SecretU32(u32);
    SecretU64(u64);
    SecretU128(u128);
    SecretUsize(usize);
}

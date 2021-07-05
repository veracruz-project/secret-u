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

/// A special trait for types that can eq as long as the result remains secret
pub trait SecretEq {
    fn eq(self, other: Self) -> SecretBool;
    fn ne(self, other: Self) -> SecretBool;
}


/// A secret bool who's value is ensured to not be leaked by Rust's type-system
///
/// Note that, much like the underlying Rc type, clone is relatively cheap, but
/// not a bytewise copy, which means we can't implement the Copy trait
#[derive(Clone, Default)]
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
    }
}


//pub mod opcode;
//pub mod error;
//pub mod vm;
//
//use std::str::FromStr;
//use std::str::ParseBoolError;
//use std::num::ParseIntError;
//use std::ops::Not;
//use std::ops::BitAnd;
//use std::ops::BitAndAssign;
//use std::ops::BitOr;
//use std::ops::BitOrAssign;
//use std::ops::BitXor;
//use std::ops::BitXorAssign;
//
//
///// A general secret wrapper for types who's value can
///// not be accessed without an explicit, unsafe declassify
///// call. Note by itself this is fairly useless except for
///// marking data that should be limited to this crate's
///// internals
//pub struct Secret<T>(T);
//
//impl<T> Secret<T> {
//    pub const fn new(t: T) -> Self {
//        Self(t)
//    }
//
//    pub unsafe fn declassify(self) -> T {
//        self.0
//    }
//
//    pub fn as_ref(&self) -> Secret<&T> {
//        Secret(&self.0)
//    }
//
//    pub fn as_mut(&mut self) -> Secret<&mut T> {
//        Secret(&mut self.0)
//    }
//}
//
//impl<T: Clone> Clone for Secret<T> {
//    fn clone(&self) -> Secret<T> {
//        Secret::new(self.0.clone())
//    }
//}
//
//
//// TODO move these? the are copied from Rust's stdlib
//
//// implements the unary operator "op &T"
//// based on "op T" where T is expected to be `Copy`able
//macro_rules! forward_ref_unop {
//    (impl $imp:ident, $method:ident for $t:ty) => {
//        impl $imp for &$t {
//            type Output = <$t as $imp>::Output;
//            fn $method(self) -> <$t as $imp>::Output {
//                $imp::$method(*self)
//            }
//        }
//    }
//}
//
//// implements binary operators "&T op U", "T op &U", "&T op &U"
//// based on "T op U" where T and U are expected to be `Copy`able
//macro_rules! forward_ref_binop {
//    (impl $imp:ident, $method:ident for $t:ty, $u:ty) => {
//        impl<'a> $imp<$u> for &'a $t {
//            type Output = <$t as $imp<$u>>::Output;
//            fn $method(self, other: $u) -> <$t as $imp<$u>>::Output {
//                $imp::$method(*self, other)
//            }
//        }
//
//        impl $imp<&$u> for $t {
//            type Output = <$t as $imp<$u>>::Output;
//            fn $method(self, other: &$u) -> <$t as $imp<$u>>::Output {
//                $imp::$method(self, *other)
//            }
//        }
//
//        impl $imp<&$u> for &$t {
//            type Output = <$t as $imp<$u>>::Output;
//            fn $method(self, other: &$u) -> <$t as $imp<$u>>::Output {
//                $imp::$method(*self, *other)
//            }
//        }
//    }
//}
//
//// implements "T op= &U", based on "T op= U"
//// where U is expected to be `Copy`able
//macro_rules! forward_ref_op_assign {
//    (impl $imp:ident, $method:ident for $t:ty, $u:ty) => {
//        impl $imp<&$u> for $t {
//            fn $method(&mut self, other: &$u) {
//                $imp::$method(self, *other);
//            }
//        }
//    }
//}
//
//// implements "T op= U", based on "T = T op U"
//// where U is expected to be `Copy`able
//macro_rules! forward_op_assign {
//    (impl $imp:ident, $method:ident<$op:ident> for $t:ty, $u:ty) => {
//        impl $imp for $t {
//            fn $method(&mut self, other: $u) {
//                *self = (*self).$op(other);
//            }
//        }
//
//        forward_ref_op_assign! { impl $imp, $method for $t, $u }
//    }
//}
//
////   // 
////   macro_rules! forward_binop {
////       (impl $imp:ident, $method:ident for $t:ty, $u:ty) => {
////           forward_ref_binop! { impl $imp, $method for $t, $u }
////           paste! {
////               forward_assign_binop! { impl [<$imp Assign>], [<$method _assign>] for $t, $u }
////           }
////       }
////   }
//
//
//
///// A secret bool who's value is ensured to not be leaked by Rust's type-system
//#[derive(Copy, Clone, Default)]
//pub struct SecretBool(bool);
//
//impl SecretBool {
//    /// Wraps a non-secret value as a secret value
//    pub const fn new(n: bool) -> Self {
//        Self(n)
//    }
//
//    /// Extracts the secret value into a non-secret value
//    ///
//    /// Note this effectively "leaks" the secret value, so
//    /// is only allowed in unsafe code
//    unsafe fn declassify(self) -> bool {
//        self.0
//    }
//}
//
////// FromStr ////
//
//impl FromStr for SecretBool {
//    type Err = ParseBoolError;
//    fn from_str(s: &str) -> Result<Self, Self::Err> {
//        Ok(Self::new(bool::from_str(s)?))
//    }
//}
//
////// bitwise operations ////
//
//impl Not for SecretBool {
//    type Output = SecretBool;
//    fn not(self) -> Self::Output {
//        Self::new(unsafe { !self.declassify() })
//    }
//}
//forward_ref_unop! { impl Not, not for SecretBool }
//
//impl BitAnd for SecretBool {
//    type Output = SecretBool;
//    fn bitand(self, other: Self) -> Self::Output {
//        Self::new(unsafe { self.declassify() & other.declassify() })
//    }
//}
//forward_ref_binop! { impl BitAnd, bitand for SecretBool, SecretBool }
//forward_op_assign! { impl BitAndAssign, bitand_assign<bitand> for SecretBool, SecretBool }
//
//impl BitOr for SecretBool {
//    type Output = SecretBool;
//    fn bitor(self, other: Self) -> Self::Output {
//        Self::new(unsafe { self.declassify() | other.declassify() })
//    }
//}
//forward_ref_binop! { impl BitOr, bitor for SecretBool, SecretBool }
//forward_op_assign! { impl BitOrAssign, bitor_assign<bitor> for SecretBool, SecretBool }
//
//
//impl BitXor for SecretBool {
//    type Output = SecretBool;
//    fn bitxor(self, other: Self) -> Self::Output {
//        Self::new(unsafe { self.declassify() ^ other.declassify() })
//    }
//}
//forward_ref_binop! { impl BitXor, bitxor for SecretBool, SecretBool }
//forward_op_assign! { impl BitXorAssign, bitxor_assign<bitxor> for SecretBool, SecretBool }
//
//// TODO note shl/shr needed for u8-usize
//// neg, add, sub, mul, div
//
//
////// SecretEq/SecretPartialEq ////
//
//pub trait SecretPartialEq<Rhs: ?Sized = Self> {
//    /// This method tests for `self` and `other` values to be equal.
//    #[must_use]
//    fn eq(&self, other: &Rhs) -> SecretBool;
//
//    /// This method tests for `!=`.
//    #[must_use]
//    fn ne(&self, other: &Rhs) -> SecretBool {
//        !self.eq(other)
//    }
//}
//
//pub trait SecretEq: SecretPartialEq<Self> {}
//
//impl SecretPartialEq for SecretBool {
//    fn eq(&self, other: &Self) -> SecretBool {
//        SecretBool::new(unsafe { self.declassify() == other.declassify() })
//    }
//
//    fn ne(&self, other: &Self) -> SecretBool {
//        SecretBool::new(unsafe { self.declassify() != other.declassify() })
//    }
//}
//
//impl SecretEq for SecretBool {}
//
//
////// SecretOrd/SecretPartialOrd ////
//
//// TODO
//
////// Select ternary operator ////
//
//pub trait Select<A, B> {
//    /// The result of select.
//    type Output;
//
//    /// Selects either `a` or `b` based on the current value.
//    #[must_use]
//    fn select(&self, a: A, b: B) -> Self::Output;
//}
//
//macro_rules! select_impl {
//    ($t:ty, $f:ty) => {
//        impl Select<$f, $f> for $t {
//            type Output = $f;
//            fn select(&self, a: $f, b: $f) -> $f {
//                <$f>::new(
//                    unsafe {
//                        if self.declassify() {
//                            a.declassify()
//                        } else {
//                            b.declassify()
//                        }
//                    }
//                )
//            }
//        }
//
//        impl Select<&$f, $f> for $t {
//            type Output = $f;
//            fn select(&self, a: &$f, b: $f) -> $f {
//                Select::select(self, *a, b)
//            }
//        }
//
//        impl Select<$f, &$f> for $t {
//            type Output = $f;
//            fn select(&self, a: $f, b: &$f) -> $f {
//                Select::select(self, a, *b)
//            }
//        }
//
//        impl Select<&$f, &$f> for $t {
//            type Output = $f;
//            fn select(&self, a: &$f, b: &$f) -> $f {
//                Select::select(self, *a, *b)
//            }
//        }
//    }
//}
//
//select_impl! { SecretBool, SecretBool }
//
//
//
//
//
//macro_rules! secret_integers {
//    ( $( $U:ident($u:ty); )+ ) => {
//        $(
//            /// A secret integer who's value is ensured to not be leaked by Rust's type-system
//            #[derive(Copy, Clone)]
//            pub struct $U($u);
//
//            impl $U {
//                /// Creates a secret value
//                pub const fn new(n: $u) -> Self {
//                    Self(n)
//                }
//
//                /// Extracts the secret value into a non-secret value
//                ///
//                /// Note this effectively "leaks" the secret value, so
//                /// is only allowed in unsafe code
//                pub unsafe fn declassify(self) -> $u {
//                    self.0
//                }
//            }
//
//            impl FromStr for $U {
//                type Err = ParseIntError;
//                fn from_str(s: &str) -> Result<Self, Self::Err> {
//                    Ok(Self::new(<$u>::from_str(s)?))
//                }
//            }
//        )+
//    }
//}
//
//secret_integers! {
//    SecretU8(u8);
//    SecretU16(u16);
//    SecretU32(u32);
//    SecretU64(u64);
//    SecretU128(u128);
//    SecretUsize(usize);
//}

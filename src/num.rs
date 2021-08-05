//! Definitions of secret integers

use crate::opcode::*;
use crate::traits::*;
use crate::error::Error;
use std::rc::Rc;
use std::mem::size_of;
use std::convert::TryFrom;
use std::borrow::Cow;

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
    pub const SIZE: usize = 1;

    /// Wraps a non-secret value as a secret value
    pub fn classify(v: bool) -> SecretBool {
        Self::from_tree(OpTree::<U8>::imm(if v { 0xffu8 } else { 0x00u8 }))
    }

    /// Extracts the secret value into a non-secret value, this
    /// effectively "leaks" the secret value, but is necessary
    /// to actually do anything
    pub fn declassify(&self) -> bool {
        self.try_declassify().unwrap()
    }

    /// Same as declassify but propagating internal VM errors
    pub fn try_declassify(&self) -> Result<bool, Error> {
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
    fn resolve<'a, U: OpU>(&'a self) -> Cow<'a, OpTree<U>> {
        OpTree::dyn_cast_s(self.deferred())
    }

    /// Select operation for constant-time conditionals
    pub fn select<T>(self, a: T, b: T) -> T
    where
        T: Select<SecretBool>
    {
        T::select(self, a, b)
    }
}

impl Eval for SecretBool {
    fn try_eval(&self) -> Result<Self, Error> {
        let tree = self.resolve::<U8>();
        Ok(Self::from_tree(tree.try_eval()?))
    }
}

impl Tree for SecretBool {
    type Tree = OpTree<U8>;

    fn from_tree(tree: OpTree<U8>) -> Self {
        Self(DeferredTree::Resolved(tree))
    }

    fn tree(&self) -> Cow<'_, OpTree<U8>> {
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

impl Eq for SecretBool {
    type Output = SecretBool;

    fn eq(self, other: Self) -> SecretBool {
        !(self ^ other)
    }

    fn ne(self, other: Self) -> SecretBool {
        self ^ other
    }
}

impl Ord for SecretBool {
    type Output = SecretBool;

    fn lt(self, other: Self) -> SecretBool {
        !self & other
    }

    fn le(self, other: Self) -> SecretBool {
        !self | other
    }

    fn gt(self, other: Self) -> SecretBool {
        self & !other
    }

    fn ge(self, other: Self) -> SecretBool {
        self | !other
    }

    fn min(self, other: Self) -> Self {
        self & other
    }

    fn max(self, other: Self) -> Self {
        self | other
    }
}

impl Select<SecretBool> for SecretBool {
    fn select(p: SecretBool, a: Self, b: Self) -> Self {
        Self::from_tree(OpTree::select(0,
            p.resolve::<U8>().into_owned(),
            a.resolve::<U8>().into_owned(),
            b.resolve::<U8>().into_owned()
        ))
    }
}


//// SecretU**/SecretI** ////

macro_rules! secret_u_impl {
    ($t:ident($U:ty; [u8; $n:literal]; $($p:ty)?{$($u:ty)?|$($s:ty)?})) => {
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
            pub const SIZE: usize = $n;

            /// Wraps a non-secret value as a secret value
            pub fn classify_le_bytes(v: [u8; $n]) -> Self {
                Self(OpTree::imm(v))
            }

            /// Extracts the secret value into a non-secret value, this
            /// effectively "leaks" the secret value, but is necessary
            /// to actually do anything
            pub fn declassify_le_bytes(&self) -> [u8; $n] {
                self.try_declassify_le_bytes().unwrap()
            }

            /// Same as declassify but propagating internal VM errors
            pub fn try_declassify_le_bytes(&self) -> Result<[u8; $n], Error> {
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
                pub fn declassify(&self) -> $p {
                    self.try_declassify().unwrap()
                }

                /// Same as declassify but propagating internal VM errors
                pub fn try_declassify(&self) -> Result<$p, Error> {
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
                    let _: $s;
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

        impl Eval for $t {
            fn try_eval(&self) -> Result<Self, Error> {
                Ok(Self::from_tree(self.tree().try_eval()?))
            }
        }

        impl Tree for $t {
            type Tree = OpTree<$U>;

            fn from_tree(tree: OpTree<$U>) -> Self {
                Self(tree)
            }

            fn tree<'a>(&'a self) -> Cow<'a, OpTree<$U>> {
                Cow::Borrowed(&self.0)
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
                    let _: $s;
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
                    let _: $s;
                    Self(OpTree::shr_s(0, self.0, other.0))
                )?
            }
        }

        impl ShrAssign for $t {
            fn shr_assign(&mut self, other: $t) {
                *self = self.clone().shr(other)
            }
        }

        impl Eq for $t {
            type Output = SecretBool;

            fn eq(self, other: Self) -> SecretBool {
                SecretBool::defer(Rc::new(OpTree::eq(0, self.0, other.0)))
            }

            fn ne(self, other: Self) -> SecretBool {
                SecretBool::defer(Rc::new(OpTree::ne(0, self.0, other.0)))
            }
        }

        impl Ord for $t {
            type Output = SecretBool;

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
                    let _: $s;
                    SecretBool::defer(Rc::new(OpTree::lt_s(0, self.0, other.0)))
                }

                fn le(self, other: Self) -> SecretBool {
                    let _: $s;
                    SecretBool::defer(Rc::new(OpTree::le_s(0, self.0, other.0)))
                }

                fn gt(self, other: Self) -> SecretBool {
                    let _: $s;
                    SecretBool::defer(Rc::new(OpTree::gt_s(0, self.0, other.0)))
                }

                fn ge(self, other: Self) -> SecretBool {
                    let _: $s;
                    SecretBool::defer(Rc::new(OpTree::ge_s(0, self.0, other.0)))
                }

                fn min(self, other: Self) -> Self {
                    let _: $s;
                    Self(OpTree::min_s(0, self.0, other.0))
                }

                fn max(self, other: Self) -> Self {
                    let _: $s;
                    Self(OpTree::max_s(0, self.0, other.0))
                }
            )?
        }

        impl Select<SecretBool> for $t {
            fn select(p: SecretBool, a: Self, b: Self) -> Self {
                Self(OpTree::select(0,
                    p.resolve().into_owned(),
                    a.0,
                    b.0
                ))
            }
        }
    }
}

// unsigned
secret_u_impl! { SecretU8  (U8;   [u8;  1]; u8  {u8  |}) }
secret_u_impl! { SecretU16 (U16;  [u8;  2]; u16 {u16 |}) }
secret_u_impl! { SecretU32 (U32;  [u8;  4]; u32 {u32 |}) }
secret_u_impl! { SecretU64 (U64;  [u8;  8]; u64 {u64 |}) }
secret_u_impl! { SecretU128(U128; [u8; 16]; u128{u128|}) }
secret_u_impl! { SecretU256(U256; [u8; 32];     {()  |}) }
secret_u_impl! { SecretU512(U512; [u8; 64];     {()  |}) }

// signed
secret_u_impl! { SecretI8  (U8;   [u8;  1]; i8  {|i8  }) }
secret_u_impl! { SecretI16 (U16;  [u8;  2]; i16 {|i16 }) }
secret_u_impl! { SecretI32 (U32;  [u8;  4]; i32 {|i32 }) }
secret_u_impl! { SecretI64 (U64;  [u8;  8]; i64 {|i64 }) }
secret_u_impl! { SecretI128(U128; [u8; 16]; i128{|i128}) }
secret_u_impl! { SecretI256(U256; [u8; 32];     {|()  }) }
secret_u_impl! { SecretI512(U512; [u8; 64];     {|()  }) }


//// SecretM**x** ////

macro_rules! secret_m_impl {
    (@p $a:ident: $p:ty) => { $p };
    (@from_lanes $x:ident $a:ident:$i:literal $($rest:tt)*) => {
        let $x = Self($a.resolve().into_owned());
        secret_m_impl!(@from_lanes2 $x $($rest)*);
    };
    (@from_lanes2 $x:ident $a:ident:$i:literal $($rest:tt)*) => {
        let $x = $x.replace($i, $a);
        secret_m_impl!(@from_lanes2 $x $($rest)*);
    };
    (@from_lanes2 $x:ident ) => {};
    ($t:ident(
        $U:ty;
        $V:ty;
        $npw2:literal;
        [u8; $n:literal];
        $u:ty;
        $o:ty;
        $p:ty{$($a:ident:$i:literal),+}
    )) => {
        /// A secret SIMD mask type who's value is ensured to not be leaked by
        /// Rust's type-system
        ///
        /// This mirror's packed_simd's m types, note that unlike bool, where
        /// true = 1 and false = 0, here true = all ones and false = all zeros.
        /// This really only matters when converting to integer types
        ///
        /// Note, like the underlying Rc type, clone is relatively cheap, but
        /// not a bytewise copy, which means we can't implement the Copy trait
        #[derive(Clone)]
        pub struct $t(OpTree<$U>);

        impl Default for $t {
            fn default() -> Self {
                Self::const_splat(false)
            }
        }

        impl $t {
            pub const SIZE: usize = $n;
            pub const LANES: usize = (1 << $npw2);

            /// Wraps a non-secret value as a secret value
            pub fn classify_lanes($($a: $p),+) -> Self {
                let mut bytes = [0; $n];
                $(
                    bytes[$i*size_of::<$p>() .. ($i+1)*size_of::<$p>()]
                        .copy_from_slice(
                            &if $a { <$V>::ones() } else { <$V>::zero() }.to_le_bytes()
                        );
                )+
                Self(OpTree::imm(bytes))
            }

            /// Extracts the secret value into a non-secret value, this
            /// effectively "leaks" the secret value, but is necessary
            /// to actually do anything
            pub fn declassify_lanes(&self) -> ($(secret_m_impl!(@p $a: $p),)+) {
                self.try_declassify_lanes().unwrap()
            }

            /// Same as declassify but propagating internal VM errors
            pub fn try_declassify_lanes(&self) -> Result<($(secret_m_impl!(@p $a: $p),)+), Error> {
                let bytes: [u8; $n] = self.try_eval()?.0.result();
                Ok(($(
                    !<$V>::from_le_bytes(
                        <_>::try_from(
                            &bytes[$i*size_of::<$p>() .. ($i+1)*size_of::<$p>()]
                        ).unwrap()
                    ).is_zero(),
                )+))
            }

            /// Wraps a non-secret value as a secret value
            pub fn new_lanes($($a: $p),+) -> Self {
                Self::classify_lanes($($a),+)
            }

            /// Wraps a non-secret value as a secret value
            pub fn const_lanes($($a: $p),+) -> Self {
                let mut bytes = [0; $n];
                $(
                    bytes[$i*size_of::<$p>() .. ($i+1)*size_of::<$p>()]
                        .copy_from_slice(
                            &if $a { <$V>::ones() } else { <$V>::zero() }.to_le_bytes()
                        );
                )+
                Self(OpTree::const_(bytes))
            }

            /// Wraps a non-secret value as a secret value
            pub fn classify_slice(slice: &[$p]) -> Self {
                Self::try_classify_slice(slice).unwrap()
            }

            /// Wraps a non-secret value as a secret value
            pub fn try_classify_slice(slice: &[$p]) -> Option<Self> {
                if slice.len() == 1 << $npw2 {
                    let mut bytes = [0; $n];
                    $(
                        bytes[$i*size_of::<$p>() .. ($i+1)*size_of::<$p>()]
                            .copy_from_slice(
                                &if slice[$i] { <$V>::ones() } else { <$V>::zero() }.to_le_bytes()
                            );
                    )+
                    Some(Self(OpTree::imm(bytes)))
                } else {
                    None
                }
            }

            /// Extracts the secret value into a non-secret value, this
            /// effectively "leaks" the secret value, but is necessary
            /// to actually do anything
            pub fn declassify_vec(&self) -> Vec<$p> {
                self.try_declassify_vec().unwrap()
            }

            /// Same as declassify but propagating internal VM errors
            pub fn try_declassify_vec(&self) -> Result<Vec<$p>, Error> {
                let bytes: [u8; $n] = self.try_eval()?.0.result();
                Ok(vec![$(
                    !<$V>::from_le_bytes(
                        <_>::try_from(
                            &bytes[$i*size_of::<$p>() .. ($i+1)*size_of::<$p>()]
                        ).unwrap()
                    ).is_zero(),
                )+])
            }

            /// Wraps a non-secret value as a secret value
            pub fn new_slice(slice: &[$p]) -> Self {
                Self::classify_slice(slice)
            }

            /// Wraps a non-secret value as a secret value
            pub fn try_new_slice(slice: &[$p]) -> Option<Self> {
                Self::try_classify_slice(slice)
            }

            /// Wraps a non-secret value as a secret value
            pub fn const_slice(slice: &[$p]) -> Self {
                Self::try_const_slice(slice).unwrap()
            }

            /// Wraps a non-secret value as a secret value
            pub fn try_const_slice(slice: &[$p]) -> Option<Self> {
                if slice.len() == 1 << $npw2 {
                    let mut bytes = [0; $n];
                    $(
                        bytes[$i*size_of::<$p>() .. ($i+1)*size_of::<$p>()]
                            .copy_from_slice(
                                &if slice[$i] { <$V>::ones() } else { <$V>::zero() }.to_le_bytes()
                            );
                    )+
                    Some(Self(OpTree::const_(bytes)))
                } else {
                    None
                }
            }

            /// Wraps a non-secret value as a secret value
            pub fn new_splat(v: $p) -> Self {
                Self(OpTree::imm(<$U>::splat(if v { <$U>::ones() } else { <$U>::zero() })))
            }

            /// Create a non-secret constant value, these are available
            /// for more optimizations than secret values
            pub fn const_splat(v: $p) -> Self {
                Self(OpTree::const_(<$U>::splat(if v { <$U>::ones() } else { <$U>::zero() })))
            }

            /// Build from lanes
            pub fn from_lanes($($a: SecretBool),+) -> Self {
                #[allow(unused)]
                let x: Self;
                secret_m_impl!(@from_lanes x $($a:$i)+);
                x
            }

            /// Extract all lanes
            pub fn to_lanes(self) -> ($(secret_m_impl!(@p $a: SecretBool),)+) {
                ($(
                    self.clone().extract($i),
                )+)
            }

            /// Build from lanes, panicking if the slice length does not match
            pub fn from_slice(slice: &[SecretBool]) -> Self {
                Self::try_from_slice(slice).unwrap()
            }

            /// Build from lanes, returning None if the slice length does not match
            pub fn try_from_slice(slice: &[SecretBool]) -> Option<Self> {
                if slice.len() == 1 << $npw2 {
                    let x = <$t>::default();
                    $(
                        let x = x.replace($i, slice[$i].clone());
                    )+
                    Some(x)
                } else {
                    None
                }
            }

            /// Extract all lanes
            pub fn to_vec(self) -> Vec<SecretBool> {
                vec![$(
                    self.clone().extract($i),
                )+]
            }

            /// Splat a given value to all lanes
            pub fn splat(value: SecretBool) -> Self {
                Self(OpTree::splat(value.resolve::<$V>().into_owned()))
            }

            /// Extract a specific lane
            pub fn extract(self, lane: usize) -> SecretBool {
                assert!(lane < (1 << $npw2));
                SecretBool::defer(Rc::new(OpTree::<$V>::extract(lane as u8, self.0)))
            }

            /// Replace a specific lane
            pub fn replace(self, lane: usize, value: SecretBool) -> Self {
                assert!(lane < (1 << $npw2));
                Self(OpTree::replace::<$V>(lane as u8, self.0, value.resolve().into_owned()))
            }

            /// Find if no lanes are true
            pub fn none(self) -> SecretBool {
                SecretBool::defer(Rc::new(OpTree::none(self.0)))
            }

            /// Find if any lanes are true
            pub fn any(self) -> SecretBool {
                SecretBool::defer(Rc::new(OpTree::all(0, self.0)))
            }

            /// Find if all lanes are true
            pub fn all(self) -> SecretBool {
                SecretBool::defer(Rc::new(OpTree::all($npw2, self.0)))
            }

            /// Select operation for constant-time conditionals
            pub fn select<T>(self, a: T, b: T) -> T
            where
                T: Select<$t>
            {
                T::select(self, a, b)
            }
        }

        impl Eval for $t {
            fn try_eval(&self) -> Result<Self, Error> {
                Ok(Self::from_tree(self.tree().try_eval()?))
            }
        }

        impl Tree for $t {
            type Tree = OpTree<$U>;

            fn from_tree(tree: OpTree<$U>) -> Self {
                Self(tree)
            }

            fn tree<'a>(&'a self) -> Cow<'a, OpTree<$U>> {
                Cow::Borrowed(&self.0)
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

        impl Eq for $t {
            type Output = $t;

            fn eq(self, other: Self) -> $t {
                !(self ^ other)
            }

            fn ne(self, other: Self) -> $t {
                self ^ other
            }
        }

        impl Ord for $t {
            type Output = $t;

            fn lt(self, other: Self) -> $t {
                !self & other
            }

            fn le(self, other: Self) -> $t {
                !self | other
            }

            fn gt(self, other: Self) -> $t {
                self & !other
            }

            fn ge(self, other: Self) -> $t {
                self | !other
            }

            fn min(self, other: Self) -> Self {
                self & other
            }

            fn max(self, other: Self) -> Self {
                self | other
            }
        }

        impl Select<$t> for $t {
            fn select(p: $t, a: Self, b: Self) -> Self {
                Self(OpTree::select($npw2, p.0, a.0, b.0))
            }
        }

        impl Shuffle<$u> for $t {
            fn shuffle(p: $u, a: Self, b: Self) -> Self {
                Self(OpTree::shuffle($npw2,
                    p.0,
                    a.0,
                    b.0,
                ))
            }
        }

        impl Shuffle<$o> for $t {
            fn shuffle(p: $o, a: Self, b: Self) -> Self {
                Self(OpTree::shuffle($npw2,
                    p.0,
                    a.0,
                    b.0,
                ))
            }
        }
    }
}

secret_m_impl! { SecretM8x1   (U8;   U8;   0; [u8;  1]; SecretU8x1;   SecretI8x1;   bool{a:0}) }
secret_m_impl! { SecretM8x2   (U16;  U8;   1; [u8;  2]; SecretU8x2;   SecretI8x2;   bool{a:0,b:1}) }
secret_m_impl! { SecretM8x4   (U32;  U8;   2; [u8;  4]; SecretU8x4;   SecretI8x4;   bool{a:0,b:1,c:2,d:3}) }
secret_m_impl! { SecretM8x8   (U64;  U8;   3; [u8;  8]; SecretU8x8;   SecretI8x8;   bool{
    a:0,b:1,c:2,d:3,e:4,f:5,g:6,h:7}) }
secret_m_impl! { SecretM8x16  (U128; U8;   4; [u8; 16]; SecretU8x16;  SecretI8x16;  bool{
    a:0,b:1,c:2,d:3,e:4,f:5,g:6,h:7,i:8,j:9,k:10,l:11,m:12,n:13,o:14,p:15}) }
secret_m_impl! { SecretM8x32  (U256; U8;   5; [u8; 32]; SecretU8x32;  SecretI8x32;  bool{
    a: 0,b: 1,c: 2,d: 3,e: 4,f: 5,g: 6,h: 7,i: 8,j: 9,k: 10,l: 11,m: 12,n: 13,o: 14,p: 15,
    q:16,r:17,s:18,t:19,u:20,v:21,w:22,x:23,y:24,z:25,a2:26,b2:27,c2:28,d2:29,e2:30,f2:31}) }
secret_m_impl! { SecretM8x64  (U512; U8;   6; [u8; 64]; SecretU8x64;  SecretI8x64;  bool{
    a:  0,b:  1,c:  2,d:  3,e:  4,f:  5,g:  6, h: 7,i:  8,j:  9,k: 10,l: 11,m: 12,n: 13,o: 14,p: 15,
    q: 16,r: 17,s: 18,t: 19,u: 20,v: 21,w: 22, x:23,y: 24,z: 25,a2:26,b2:27,c2:28,d2:29,e2:30,f2:31,
    g2:32,h2:33,i2:34,j2:35,k2:36,l2:37,m2:38,n2:39,o2:40,p2:41,q2:42,r2:43,s2:44,t2:45,u2:46,v2:47,
    w2:48,x2:49,y2:50,z2:51,a3:52,b3:53,c3:54,d3:55,e3:56,f3:57,g3:58,h3:59,i3:60,j3:61,k3:62,l3:63}) }
secret_m_impl! { SecretM16x1  (U16;  U16;  0; [u8;  2]; SecretU16x1;  SecretI16x1;  bool{a:0}) }
secret_m_impl! { SecretM16x2  (U32;  U16;  1; [u8;  4]; SecretU16x2;  SecretI16x2;  bool{a:0,b:1}) }
secret_m_impl! { SecretM16x4  (U64;  U16;  2; [u8;  8]; SecretU16x4;  SecretI16x4;  bool{a:0,b:1,c:2,d:3}) }
secret_m_impl! { SecretM16x8  (U128; U16;  3; [u8; 16]; SecretU16x8;  SecretI16x8;  bool{
    a:0,b:1,c:2,d:3,e:4,f:5,g:6,h:7}) }
secret_m_impl! { SecretM16x16 (U256; U16;  4; [u8; 32]; SecretU16x16; SecretI16x16; bool{
    a:0,b:1,c:2,d:3,e:4,f:5,g:6,h:7,i:8,j:9,k:10,l:11,m:12,n:13,o:14,p:15}) }
secret_m_impl! { SecretM16x32 (U512; U16;  5; [u8; 64]; SecretU16x32; SecretI16x32; bool{
    a: 0,b: 1,c: 2,d: 3,e: 4,f: 5,g: 6,h: 7,i: 8,j: 9,k: 10,l: 11,m: 12,n: 13,o: 14,p: 15,
    q:16,r:17,s:18,t:19,u:20,v:21,w:22,x:23,y:24,z:25,a2:26,b2:27,c2:28,d2:29,e2:30,f2:31}) }
secret_m_impl! { SecretM32x1  (U32;  U32;  0; [u8;  4]; SecretU32x1;  SecretI32x1;  bool{a:0}) }
secret_m_impl! { SecretM32x2  (U64;  U32;  1; [u8;  8]; SecretU32x2;  SecretI32x2;  bool{a:0,b:1}) }
secret_m_impl! { SecretM32x4  (U128; U32;  2; [u8; 16]; SecretU32x4;  SecretI32x4;  bool{a:0,b:1,c:2,d:3}) }
secret_m_impl! { SecretM32x8  (U256; U32;  3; [u8; 32]; SecretU32x8;  SecretI32x8;  bool{
    a:0,b:1,c:2,d:3,e:4,f:5,g:6,h:7}) }
secret_m_impl! { SecretM32x16 (U512; U32;  4; [u8; 64]; SecretU32x16; SecretI32x16; bool{
    a:0,b:1,c:2,d:3,e:4,f:5,g:6,h:7,i:8,j:9,k:10,l:11,m:12,n:13,o:14,p:15}) }
secret_m_impl! { SecretM64x1  (U64;  U64;  0; [u8;  8]; SecretU64x1;  SecretI64x1;  bool{a:0}) }
secret_m_impl! { SecretM64x2  (U128; U64;  1; [u8; 16]; SecretU64x2;  SecretI64x2;  bool{a:0,b:1}) }
secret_m_impl! { SecretM64x4  (U256; U64;  2; [u8; 32]; SecretU64x4;  SecretI64x4;  bool{a:0,b:1,c:2,d:3}) }
secret_m_impl! { SecretM64x8  (U512; U64;  3; [u8; 64]; SecretU64x8;  SecretI64x8;  bool{
    a:0,b:1,c:2,d:3,e:4,f:5,g:6,h:7}) }
secret_m_impl! { SecretM128x1 (U128; U128; 0; [u8; 16]; SecretU128x1; SecretI128x1; bool{a:0}) }
secret_m_impl! { SecretM128x2 (U256; U128; 1; [u8; 32]; SecretU128x2; SecretI128x2; bool{a:0,b:1}) }
secret_m_impl! { SecretM128x4 (U512; U128; 2; [u8; 64]; SecretU128x4; SecretI128x4; bool{a:0,b:1,c:2,d:3}) }
secret_m_impl! { SecretM256x1 (U256; U256; 0; [u8; 32]; SecretU256x1; SecretI256x1; bool{a:0}) }
secret_m_impl! { SecretM256x2 (U512; U256; 1; [u8; 64]; SecretU256x2; SecretI256x2; bool{a:0,b:1}) }
secret_m_impl! { SecretM512x1 (U512; U512; 0; [u8; 64]; SecretU512x1; SecretI512x1; bool{a:0}) }


//// SecretU**x**/SecretI**x** ////

macro_rules! secret_x_impl {
    (@p $a:ident: $p:ty) => { $p };
    (@from_lanes $x:ident $a:ident:$i:literal $($rest:tt)*) => {
        let $x = Self(OpTree::extend_u($a.0));
        secret_x_impl!(@from_lanes2 $x $($rest)*);
    };
    (@from_lanes2 $x:ident $a:ident:$i:literal $($rest:tt)*) => {
        let $x = $x.replace($i, $a);
        secret_x_impl!(@from_lanes2 $x $($rest)*);
    };
    (@from_lanes2 $x:ident ) => {};
    // these extra rules are needed due to nested repetition weirdness
    ($t:ident(
        $U:ty;
        $V:ty;
        $npw2:literal;
        [u8; $n:literal];
        $m:ident;
        $o:ident;
        $v:ident;
        $p:ty{$($pu:ty)?|$($ps:ty)?}{$($pa:ident:$pi:literal),+}
    )) => {
        secret_x_impl! { $t($U; $V; $npw2; [u8;$n]; $m; $o; $v;
            $p{$($pu)?|$($ps)?}{$($pa:$pi),+};
            {$($pu)?|$($ps)?}{$($pa:$pi),+}) }
    };
    ($t:ident(
        $U:ty;
        $V:ty;
        $npw2:literal;
        [u8; $n:literal];
        $m:ident;
        $o:ident;
        $v:ident;
        {$($u:ty)?|$($s:ty)?}{$($a:ident:$i:literal),+}
    )) => {
        secret_x_impl! { $t($U; $V; $npw2; [u8;$n]; $m; $o; $v;
            ;
            {$($u)?|$($s)?}{$($a:$i),+}) }
    };
    ($t:ident(
        $U:ty;
        $V:ty;
        $npw2:literal;
        [u8; $n:literal];
        $m:ident;
        $o:ident;
        $v:ident;
        $($p:ty{$($pu:ty)?|$($ps:ty)?}{$($pa:ident:$pi:literal),+})?;
        {$($u:ty)?|$($s:ty)?}{$($a:ident:$i:literal),+}
    )) => {
        /// A secret SIMD mask type who's value is ensured to not be leaked by
        /// Rust's type-system
        ///
        /// This mirror's packed_simd's m types, note that unlike bool, where
        /// true = 1 and false = 0, here true = all ones and false = all zeros.
        /// This really only matters when converting to integer types
        ///
        /// Note, like the underlying Rc type, clone is relatively cheap, but
        /// not a bytewise copy, which means we can't implement the Copy trait
        #[derive(Clone)]
        pub struct $t(OpTree<$U>);

        impl Default for $t {
            fn default() -> Self {
                Self::zero()
            }
        }

        impl $t {
            pub const SIZE: usize = $n;
            pub const LANES: usize = (1 << $npw2);

            /// Wraps a non-secret value as a secret value
            pub fn classify_le_bytes(v: [u8; $n]) -> Self {
                Self(OpTree::imm(v))
            }

            /// Extracts the secret value into a non-secret value, this
            /// effectively "leaks" the secret value, but is necessary
            /// to actually do anything
            pub fn declassify_le_bytes(&self) -> [u8; $n] {
                self.try_declassify_le_bytes().unwrap()
            }

            /// Same as declassify but propagating internal VM errors
            pub fn try_declassify_le_bytes(&self) -> Result<[u8; $n], Error> {
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
                pub fn classify_lanes($($pa: $p),+) -> Self {
                    let mut bytes = [0; $n];
                    $(
                        bytes[$pi*size_of::<$p>() .. ($pi+1)*size_of::<$p>()]
                            .copy_from_slice(&<$V>::from($pa).to_le_bytes());
                    )+
                    Self(OpTree::imm(bytes))
                }

                /// Extracts the secret value into a non-secret value, this
                /// effectively "leaks" the secret value, but is necessary
                /// to actually do anything
                pub fn declassify_lanes(&self) -> ($(secret_m_impl!(@p $pa: $p),)+) {
                    self.try_declassify_lanes().unwrap()
                }

                /// Same as declassify but propagating internal VM errors
                pub fn try_declassify_lanes(&self) -> Result<($(secret_m_impl!(@p $pa: $p),)+), Error> {
                    let bytes: [u8; $n] = self.try_eval()?.0.result();
                    Ok(($(
                        <$p>::from_le_bytes(
                            <_>::try_from(
                                &bytes[$pi*size_of::<$p>() .. ($pi+1)*size_of::<$p>()]
                            ).unwrap()
                        ),
                    )+))
                }

                /// Wraps a non-secret value as a secret value
                pub fn new_lanes($($pa: $p),+) -> Self {
                    Self::classify_lanes($($pa),+)
                }

                /// Wraps a non-secret value as a secret value
                pub fn const_lanes($($pa: $p),+) -> Self {
                    let mut bytes = [0; $n];
                    $(
                        bytes[$pi*size_of::<$p>() .. ($pi+1)*size_of::<$p>()]
                            .copy_from_slice(&<$V>::from($pa).to_le_bytes());
                    )+
                    Self(OpTree::const_(bytes))
                }

                /// Wraps a non-secret value as a secret value
                pub fn classify_slice(slice: &[$p]) -> Self {
                    Self::try_classify_slice(slice).unwrap()
                }

                /// Wraps a non-secret value as a secret value
                pub fn try_classify_slice(slice: &[$p]) -> Option<Self> {
                    if slice.len() == 1 << $npw2 {
                        let mut bytes = [0; $n];
                        $(
                            bytes[$pi*size_of::<$p>() .. ($pi+1)*size_of::<$p>()]
                                .copy_from_slice(&<$V>::from(slice[$pi]).to_le_bytes());
                        )+
                        Some(Self(OpTree::imm(bytes)))
                    } else {
                        None
                    }
                }

                /// Extracts the secret value into a non-secret value, this
                /// effectively "leaks" the secret value, but is necessary
                /// to actually do anything
                pub fn declassify_vec(&self) -> Vec<$p> {
                    self.try_declassify_vec().unwrap()
                }

                /// Same as declassify but propagating internal VM errors
                pub fn try_declassify_vec(&self) -> Result<Vec<$p>, Error> {
                    let bytes: [u8; $n] = self.try_eval()?.0.result();
                    Ok(vec![$(
                        <$p>::from_le_bytes(
                            <_>::try_from(
                                &bytes[$pi*size_of::<$p>() .. ($pi+1)*size_of::<$p>()]
                            ).unwrap()
                        ),
                    )+])
                }

                /// Wraps a non-secret value as a secret value
                pub fn new_slice(slice: &[$p]) -> Self {
                    Self::classify_slice(slice)
                }

                /// Wraps a non-secret value as a secret value
                pub fn try_new_slice(slice: &[$p]) -> Option<Self> {
                    Self::try_classify_slice(slice)
                }

                /// Wraps a non-secret value as a secret value
                pub fn const_slice(slice: &[$p]) -> Self {
                    Self::try_const_slice(slice).unwrap()
                }

                /// Wraps a non-secret value as a secret value
                pub fn try_const_slice(slice: &[$p]) -> Option<Self> {
                    if slice.len() == 1 << $npw2 {
                        let mut bytes = [0; $n];
                        $(
                            bytes[$pi*size_of::<$p>() .. ($pi+1)*size_of::<$p>()]
                                .copy_from_slice(&<$V>::from(slice[$pi]).to_le_bytes());
                        )+
                        Some(Self(OpTree::const_(bytes)))
                    } else {
                        None
                    }
                }

                /// Wraps a non-secret value as a secret value
                pub fn new_splat(v: $p) -> Self {
                    Self(OpTree::imm(<$U>::splat(<$V>::from(v))))
                }

                /// Create a non-secret constant value, these are available
                /// for more optimizations than secret values
                pub fn const_splat(v: $p) -> Self {
                    Self(OpTree::const_(<$U>::splat(<$V>::from(v))))
                }
            )?

            /// Build from lanes
            pub fn from_lanes($($a: $v),+) -> Self {
                #[allow(unused)]
                let x: Self;
                secret_x_impl!(@from_lanes x $($a:$i)+);
                x
            }

            /// Extract all lanes
            pub fn to_lanes(self) -> ($(secret_m_impl!(@p $a: $v),)+) {
                ($(
                    self.clone().extract($i),
                )+)
            }

            /// Build from lanes, panicking if the slice length does not match
            pub fn from_slice(slice: &[$v]) -> Self {
                Self::try_from_slice(slice).unwrap()
            }

            /// Build from lanes, returning None if the slice length does not match
            pub fn try_from_slice(slice: &[$v]) -> Option<Self> {
                if slice.len() == 1 << $npw2 {
                    let x = <$t>::default();
                    $(
                        let x = x.replace($i, slice[$i].clone());
                    )+
                    Some(x)
                } else {
                    None
                }
            }

            /// Extract all lanes
            pub fn to_vec(self) -> Vec<$v> {
                vec![$(
                    self.clone().extract($i),
                )+]
            }

            /// Splat a given value to all lanes
            pub fn splat(value: $v) -> Self {
                Self(OpTree::splat(value.0))
            }

            /// Extract a specific lane
            pub fn extract(self, lane: usize) -> $v {
                assert!(lane < (1 << $npw2));
                <$v>::from_tree(OpTree::<$V>::extract(lane as u8, self.0))
            }

            /// Replace a specific lane
            pub fn replace(self, lane: usize, value: $v) -> Self {
                assert!(lane < (1 << $npw2));
                Self(OpTree::replace::<$V>(lane as u8, self.0, value.0))
            }

            /// A constant, non-secret 0, in all lanes
            pub fn zero() -> Self {
                Self(OpTree::zero())
            }

            /// A constant, non-secret 1, in all lanes
            pub fn one() -> Self {
                Self(OpTree::const_(<$U>::splat(<$V>::one())))
            }

            /// A constant with all bits set to 1, non-secret, in all lanes
            pub fn ones() -> Self {
                Self(OpTree::ones())
            }

            // abs only available on signed types
            $(
                pub fn abs(self) -> Self {
                    let _: $s;
                    Self(OpTree::abs($npw2, self.0))
                }
            )?

            // other non-trait operations
            pub fn trailing_zeros(self) -> $t {
                Self(OpTree::ctz($npw2, self.0))
            }

            pub fn trailing_ones(self) -> $t {
                (!self).trailing_zeros()
            }

            pub fn leading_zeros(self) -> $t {
                Self(OpTree::clz($npw2, self.0))
            }

            pub fn leading_ones(self) -> $t {
                (!self).leading_zeros()
            }

            pub fn count_zeros(self) -> $t {
                (!self).count_ones()
            }

            pub fn count_ones(self) -> $t {
                Self(OpTree::popcnt($npw2, self.0))
            }

            // ipw2/npw2 only available on unsigned types
            $(
                pub fn is_power_of_two(self) -> $m {
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
                Self(OpTree::rotl($npw2, self.0, other.0))
            }

            pub fn rotate_right(self, other: $t) -> $t {
                Self(OpTree::rotr($npw2, self.0, other.0))
            }

            /// Apply an operation horizontally, reducing the input to a single lane
            ///
            /// Note that this runs in log2(number of lanes)
            pub fn reduce<F>(mut self, f: F) -> $v
            where
                F: Fn(Self, Self) -> Self
            {
                // note this doesn't need to go through OpTree, but it means
                // one less type parameter
                for i in 0..$npw2 {
                    let shift: u32 = 8 << (i + <$V>::NPW2);
                    let b = Self(OpTree::shr_u(0,
                        self.0.clone(),
                        // a bit of an annoying workaround for type limitations
                        {
                            let mut bytes = [0; $n];
                            #[allow(unconditional_panic)]
                            if shift > 128 {
                                bytes[0..2].copy_from_slice(
                                    &u16::try_from(shift).unwrap()
                                        .to_le_bytes()
                                );
                            } else {
                                bytes[0] = u8::try_from(shift).unwrap();
                            }
                            OpTree::const_(bytes)
                        }
                    ));
                    self = f(self, b);
                }
                self.extract(0)
            }

            pub fn horizontal_sum(self) -> $v {
                self.reduce(|a, b| a + b)
            }

            pub fn horizontal_product(self) -> $v {
                self.reduce(|a, b| a * b)
            }

            pub fn horizontal_and(self) -> $v {
                self.reduce(|a, b| a & b)
            }

            pub fn horizontal_or(self) -> $v {
                self.reduce(|a, b| a | b)
            }

            pub fn horizontal_xor(self) -> $v {
                self.reduce(|a, b| a ^ b)
            }

            pub fn horizontal_min(self) -> $v {
                self.reduce(|a, b| a.min(b))
            }

            pub fn horizontal_max(self) -> $v {
                self.reduce(|a, b| a.max(b))
            }

            /// Shuffle operation using this value as indices
            ///
            /// For each lane:
            /// 0..lanes       <= lane from a
            /// lanes..2*lanes <= lane-lanes from b
            /// otherwise      <= 0
            pub fn shuffle<T>(self, a: T, b: T) -> T
            where
                T: Shuffle<$t>
            {
                T::shuffle(self, a, b)
            }
        }

        impl Eval for $t {
            fn try_eval(&self) -> Result<Self, Error> {
                Ok(Self::from_tree(self.tree().try_eval()?))
            }
        }

        impl Tree for $t {
            type Tree = OpTree<$U>;

            fn from_tree(tree: OpTree<$U>) -> Self {
                Self(tree)
            }

            fn tree<'a>(&'a self) -> Cow<'a, OpTree<$U>> {
                Cow::Borrowed(&self.0)
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
                    let _: $s;
                    Self(OpTree::neg($npw2, self.0))
                }
            }
        )?

        impl Add for $t {
            type Output = $t;
            fn add(self, other: $t) -> $t {
                Self(OpTree::add($npw2, self.0, other.0))
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
                Self(OpTree::sub($npw2, self.0, other.0))
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
                Self(OpTree::mul($npw2, self.0, other.0))
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
                Self(OpTree::shl($npw2, self.0, other.0))
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
                    Self(OpTree::shr_u($npw2, self.0, other.0))
                )?
                $(
                    let _: $s;
                    Self(OpTree::shr_s($npw2, self.0, other.0))
                )?
            }
        }

        impl ShrAssign for $t {
            fn shr_assign(&mut self, other: $t) {
                *self = self.clone().shr(other)
            }
        }

        impl Eq for $t {
            type Output = $m;

            fn eq(self, other: Self) -> $m {
                $m(OpTree::eq($npw2, self.0, other.0))
            }

            fn ne(self, other: Self) -> $m {
                $m(OpTree::ne($npw2, self.0, other.0))
            }
        }

        impl Ord for $t {
            type Output = $m;

            $(
                fn lt(self, other: Self) -> $m {
                    let _: $u;
                    $m(OpTree::lt_u($npw2, self.0, other.0))
                }

                fn le(self, other: Self) -> $m {
                    let _: $u;
                    $m(OpTree::le_u($npw2, self.0, other.0))
                }

                fn gt(self, other: Self) -> $m {
                    let _: $u;
                    $m(OpTree::gt_u($npw2, self.0, other.0))
                }

                fn ge(self, other: Self) -> $m {
                    let _: $u;
                    $m(OpTree::ge_u($npw2, self.0, other.0))
                }

                fn min(self, other: Self) -> Self {
                    let _: $u;
                    Self(OpTree::min_u($npw2, self.0, other.0))
                }

                fn max(self, other: Self) -> Self {
                    let _: $u;
                    Self(OpTree::max_u($npw2, self.0, other.0))
                }
            )?
            $(
                fn lt(self, other: Self) -> $m {
                    let _: $s;
                    $m(OpTree::lt_s($npw2, self.0, other.0))
                }

                fn le(self, other: Self) -> $m {
                    let _: $s;
                    $m(OpTree::le_s($npw2, self.0, other.0))
                }

                fn gt(self, other: Self) -> $m {
                    let _: $s;
                    $m(OpTree::gt_s($npw2, self.0, other.0))
                }

                fn ge(self, other: Self) -> $m {
                    let _: $s;
                    $m(OpTree::ge_s($npw2, self.0, other.0))
                }

                fn min(self, other: Self) -> Self {
                    let _: $s;
                    Self(OpTree::min_s($npw2, self.0, other.0))
                }

                fn max(self, other: Self) -> Self {
                    let _: $s;
                    Self(OpTree::max_s($npw2, self.0, other.0))
                }
            )?
        }

        impl Select<$m> for $t {
            fn select(p: $m, a: Self, b: Self) -> Self {
                Self(OpTree::select($npw2,
                    p.0,
                    a.0,
                    b.0
                ))
            }
        }

        impl Shuffle<$t> for $t {
            fn shuffle(p: $t, a: Self, b: Self) -> Self {
                Self(OpTree::shuffle($npw2,
                    p.0,
                    a.0,
                    b.0,
                ))
            }
        }

        impl Shuffle<$o> for $t {
            fn shuffle(p: $o, a: Self, b: Self) -> Self {
                Self(OpTree::shuffle($npw2,
                    p.0,
                    a.0,
                    b.0,
                ))
            }
        }
    }
}

// unsigned
secret_x_impl! { SecretU8x1   (U8;   U8;   0; [u8;  1]; SecretM8x1;   SecretI8x1;   SecretU8;   u8  {u8  |}{a:0}) }
secret_x_impl! { SecretU8x2   (U16;  U8;   1; [u8;  2]; SecretM8x2;   SecretI8x2;   SecretU8;   u8  {u8  |}{a:0,b:1}) }
secret_x_impl! { SecretU8x4   (U32;  U8;   2; [u8;  4]; SecretM8x4;   SecretI8x4;   SecretU8;   u8  {u8  |}{a:0,b:1,c:2,d:3}) }
secret_x_impl! { SecretU8x8   (U64;  U8;   3; [u8;  8]; SecretM8x8;   SecretI8x8;   SecretU8;   u8  {u8  |}{
    a:0,b:1,c:2,d:3,e:4,f:5,g:6,h:7}) }
secret_x_impl! { SecretU8x16  (U128; U8;   4; [u8; 16]; SecretM8x16;  SecretI8x16;  SecretU8;   u8  {u8  |}{
    a:0,b:1,c:2,d:3,e:4,f:5,g:6,h:7,i:8,j:9,k:10,l:11,m:12,n:13,o:14,p:15}) }
secret_x_impl! { SecretU8x32  (U256; U8;   5; [u8; 32]; SecretM8x32;  SecretI8x32;  SecretU8;   u8  {u8  |}{
    a: 0,b: 1,c: 2,d: 3,e: 4,f: 5,g: 6,h: 7,i: 8,j: 9,k: 10,l: 11,m: 12,n: 13,o: 14,p: 15,
    q:16,r:17,s:18,t:19,u:20,v:21,w:22,x:23,y:24,z:25,a2:26,b2:27,c2:28,d2:29,e2:30,f2:31}) }
secret_x_impl! { SecretU8x64  (U512; U8;   6; [u8; 64]; SecretM8x64;  SecretI8x64;  SecretU8;   u8  {u8  |}{
    a:  0,b:  1,c:  2,d:  3,e:  4,f:  5,g:  6, h: 7,i:  8,j:  9,k: 10,l: 11,m: 12,n: 13,o: 14,p: 15,
    q: 16,r: 17,s: 18,t: 19,u: 20,v: 21,w: 22, x:23,y: 24,z: 25,a2:26,b2:27,c2:28,d2:29,e2:30,f2:31,
    g2:32,h2:33,i2:34,j2:35,k2:36,l2:37,m2:38,n2:39,o2:40,p2:41,q2:42,r2:43,s2:44,t2:45,u2:46,v2:47,
    w2:48,x2:49,y2:50,z2:51,a3:52,b3:53,c3:54,d3:55,e3:56,f3:57,g3:58,h3:59,i3:60,j3:61,k3:62,l3:63}) }
secret_x_impl! { SecretU16x1  (U16;  U16;  0; [u8;  2]; SecretM16x1;  SecretI16x1;  SecretU16;  u16 {u16 |}{a:0}) }
secret_x_impl! { SecretU16x2  (U32;  U16;  1; [u8;  4]; SecretM16x2;  SecretI16x2;  SecretU16;  u16 {u16 |}{a:0,b:1}) }
secret_x_impl! { SecretU16x4  (U64;  U16;  2; [u8;  8]; SecretM16x4;  SecretI16x4;  SecretU16;  u16 {u16 |}{a:0,b:1,c:2,d:3}) }
secret_x_impl! { SecretU16x8  (U128; U16;  3; [u8; 16]; SecretM16x8;  SecretI16x8;  SecretU16;  u16 {u16 |}{
    a:0,b:1,c:2,d:3,e:4,f:5,g:6,h:7}) }
secret_x_impl! { SecretU16x16 (U256; U16;  4; [u8; 32]; SecretM16x16; SecretI16x16; SecretU16;  u16 {u16 |}{
    a:0,b:1,c:2,d:3,e:4,f:5,g:6,h:7,i:8,j:9,k:10,l:11,m:12,n:13,o:14,p:15}) }
secret_x_impl! { SecretU16x32 (U512; U16;  5; [u8; 64]; SecretM16x32; SecretI16x32; SecretU16;  u16 {u16 |}{
    a: 0,b: 1,c: 2,d: 3,e: 4,f: 5,g: 6,h: 7,i: 8,j: 9,k: 10,l: 11,m: 12,n: 13,o: 14,p: 15,
    q:16,r:17,s:18,t:19,u:20,v:21,w:22,x:23,y:24,z:25,a2:26,b2:27,c2:28,d2:29,e2:30,f2:31}) }
secret_x_impl! { SecretU32x1  (U32;  U32;  0; [u8;  4]; SecretM32x1;  SecretI32x1;  SecretU32;  u32 {u32 |}{a:0}) }
secret_x_impl! { SecretU32x2  (U64;  U32;  1; [u8;  8]; SecretM32x2;  SecretI32x2;  SecretU32;  u32 {u32 |}{a:0,b:1}) }
secret_x_impl! { SecretU32x4  (U128; U32;  2; [u8; 16]; SecretM32x4;  SecretI32x4;  SecretU32;  u32 {u32 |}{a:0,b:1,c:2,d:3}) }
secret_x_impl! { SecretU32x8  (U256; U32;  3; [u8; 32]; SecretM32x8;  SecretI32x8;  SecretU32;  u32 {u32 |}{
    a:0,b:1,c:2,d:3,e:4,f:5,g:6,h:7}) }
secret_x_impl! { SecretU32x16 (U512; U32;  4; [u8; 64]; SecretM32x16; SecretI32x16; SecretU32;  u32 {u32 |}{
    a:0,b:1,c:2,d:3,e:4,f:5,g:6,h:7,i:8,j:9,k:10,l:11,m:12,n:13,o:14,p:15}) }
secret_x_impl! { SecretU64x1  (U64;  U64;  0; [u8;  8]; SecretM64x1;  SecretI64x1;  SecretU64;  u64 {u64 |}{a:0}) }
secret_x_impl! { SecretU64x2  (U128; U64;  1; [u8; 16]; SecretM64x2;  SecretI64x2;  SecretU64;  u64 {u64 |}{a:0,b:1}) }
secret_x_impl! { SecretU64x4  (U256; U64;  2; [u8; 32]; SecretM64x4;  SecretI64x4;  SecretU64;  u64 {u64 |}{a:0,b:1,c:2,d:3}) }
secret_x_impl! { SecretU64x8  (U512; U64;  3; [u8; 64]; SecretM64x8;  SecretI64x8;  SecretU64;  u64 {u64 |}{
    a:0,b:1,c:2,d:3,e:4,f:5,g:6,h:7}) }
secret_x_impl! { SecretU128x1 (U128; U128; 0; [u8; 16]; SecretM128x1; SecretI128x1; SecretU128; u128{u128|}{a:0}) }
secret_x_impl! { SecretU128x2 (U256; U128; 1; [u8; 32]; SecretM128x2; SecretI128x2; SecretU128; u128{u128|}{a:0,b:1}) }
secret_x_impl! { SecretU128x4 (U512; U128; 2; [u8; 64]; SecretM128x4; SecretI128x4; SecretU128; u128{u128|}{a:0,b:1,c:2,d:3}) }
secret_x_impl! { SecretU256x1 (U256; U256; 0; [u8; 32]; SecretM256x1; SecretI256x1; SecretU256;     {()  |}{a:0}) }
secret_x_impl! { SecretU256x2 (U512; U256; 1; [u8; 64]; SecretM256x2; SecretI256x2; SecretU256;     {()  |}{a:0,b:1}) }
secret_x_impl! { SecretU512x1 (U512; U512; 0; [u8; 64]; SecretM512x1; SecretI512x1; SecretU512;     {()  |}{a:0}) }

// signed
secret_x_impl! { SecretI8x1   (U8;   U8;   0; [u8;  1]; SecretM8x1;   SecretU8x1;   SecretI8;   i8  {|i8  }{a:0}) }
secret_x_impl! { SecretI8x2   (U16;  U8;   1; [u8;  2]; SecretM8x2;   SecretU8x2;   SecretI8;   i8  {|i8  }{a:0,b:1}) }
secret_x_impl! { SecretI8x4   (U32;  U8;   2; [u8;  4]; SecretM8x4;   SecretU8x4;   SecretI8;   i8  {|i8  }{a:0,b:1,c:2,d:3}) }
secret_x_impl! { SecretI8x8   (U64;  U8;   3; [u8;  8]; SecretM8x8;   SecretU8x8;   SecretI8;   i8  {|i8  }{
    a:0,b:1,c:2,d:3,e:4,f:5,g:6,h:7}) }
secret_x_impl! { SecretI8x16  (U128; U8;   4; [u8; 16]; SecretM8x16;  SecretU8x16;  SecretI8;   i8  {|i8  }{
    a:0,b:1,c:2,d:3,e:4,f:5,g:6,h:7,i:8,j:9,k:10,l:11,m:12,n:13,o:14,p:15}) }
secret_x_impl! { SecretI8x32  (U256; U8;   5; [u8; 32]; SecretM8x32;  SecretU8x32;  SecretI8;   i8  {|i8  }{
    a: 0,b: 1,c: 2,d: 3,e: 4,f: 5,g: 6,h: 7,i: 8,j: 9,k: 10,l: 11,m: 12,n: 13,o: 14,p: 15,
    q:16,r:17,s:18,t:19,u:20,v:21,w:22,x:23,y:24,z:25,a2:26,b2:27,c2:28,d2:29,e2:30,f2:31}) }
secret_x_impl! { SecretI8x64  (U512; U8;   6; [u8; 64]; SecretM8x64;  SecretU8x64;  SecretI8;   i8  {|i8  }{
    a:  0,b:  1,c:  2,d:  3,e:  4,f:  5,g:  6, h: 7,i:  8,j:  9,k: 10,l: 11,m: 12,n: 13,o: 14,p: 15,
    q: 16,r: 17,s: 18,t: 19,u: 20,v: 21,w: 22, x:23,y: 24,z: 25,a2:26,b2:27,c2:28,d2:29,e2:30,f2:31,
    g2:32,h2:33,i2:34,j2:35,k2:36,l2:37,m2:38,n2:39,o2:40,p2:41,q2:42,r2:43,s2:44,t2:45,u2:46,v2:47,
    w2:48,x2:49,y2:50,z2:51,a3:52,b3:53,c3:54,d3:55,e3:56,f3:57,g3:58,h3:59,i3:60,j3:61,k3:62,l3:63}) }
secret_x_impl! { SecretI16x1  (U16;  U16;  0; [u8;  2]; SecretM16x1;  SecretU16x1;  SecretI16;  i16 {|i16 }{a:0}) }
secret_x_impl! { SecretI16x2  (U32;  U16;  1; [u8;  4]; SecretM16x2;  SecretU16x2;  SecretI16;  i16 {|i16 }{a:0,b:1}) }
secret_x_impl! { SecretI16x4  (U64;  U16;  2; [u8;  8]; SecretM16x4;  SecretU16x4;  SecretI16;  i16 {|i16 }{a:0,b:1,c:2,d:3}) }
secret_x_impl! { SecretI16x8  (U128; U16;  3; [u8; 16]; SecretM16x8;  SecretU16x8;  SecretI16;  i16 {|i16 }{
    a:0,b:1,c:2,d:3,e:4,f:5,g:6,h:7}) }
secret_x_impl! { SecretI16x16 (U256; U16;  4; [u8; 32]; SecretM16x16; SecretU16x16; SecretI16;  i16 {|i16 }{
    a:0,b:1,c:2,d:3,e:4,f:5,g:6,h:7,i:8,j:9,k:10,l:11,m:12,n:13,o:14,p:15}) }
secret_x_impl! { SecretI16x32 (U512; U16;  5; [u8; 64]; SecretM16x32; SecretU16x32; SecretI16;  i16 {|i16 }{
    a: 0,b: 1,c: 2,d: 3,e: 4,f: 5,g: 6,h: 7,i: 8,j: 9,k: 10,l: 11,m: 12,n: 13,o: 14,p: 15,
    q:16,r:17,s:18,t:19,u:20,v:21,w:22,x:23,y:24,z:25,a2:26,b2:27,c2:28,d2:29,e2:30,f2:31}) }
secret_x_impl! { SecretI32x1  (U32;  U32;  0; [u8;  4]; SecretM32x1;  SecretU32x1;  SecretI32;  i32 {|i32 }{a:0}) }
secret_x_impl! { SecretI32x2  (U64;  U32;  1; [u8;  8]; SecretM32x2;  SecretU32x2;  SecretI32;  i32 {|i32 }{a:0,b:1}) }
secret_x_impl! { SecretI32x4  (U128; U32;  2; [u8; 16]; SecretM32x4;  SecretU32x4;  SecretI32;  i32 {|i32 }{a:0,b:1,c:2,d:3}) }
secret_x_impl! { SecretI32x8  (U256; U32;  3; [u8; 32]; SecretM32x8;  SecretU32x8;  SecretI32;  i32 {|i32 }{
    a:0,b:1,c:2,d:3,e:4,f:5,g:6,h:7}) }
secret_x_impl! { SecretI32x16 (U512; U32;  4; [u8; 64]; SecretM32x16; SecretU32x16; SecretI32;  i32 {|i32 }{
    a:0,b:1,c:2,d:3,e:4,f:5,g:6,h:7,i:8,j:9,k:10,l:11,m:12,n:13,o:14,p:15}) }
secret_x_impl! { SecretI64x1  (U64;  U64;  0; [u8;  8]; SecretM64x1;  SecretU64x1;  SecretI64;  i64 {|i64 }{a:0}) }
secret_x_impl! { SecretI64x2  (U128; U64;  1; [u8; 16]; SecretM64x2;  SecretU64x2;  SecretI64;  i64 {|i64 }{a:0,b:1}) }
secret_x_impl! { SecretI64x4  (U256; U64;  2; [u8; 32]; SecretM64x4;  SecretU64x4;  SecretI64;  i64 {|i64 }{a:0,b:1,c:2,d:3}) }
secret_x_impl! { SecretI64x8  (U512; U64;  3; [u8; 64]; SecretM64x8;  SecretU64x8;  SecretI64;  i64 {|i64 }{
    a:0,b:1,c:2,d:3,e:4,f:5,g:6,h:7}) }
secret_x_impl! { SecretI128x1 (U128; U128; 0; [u8; 16]; SecretM128x1; SecretU128x1; SecretI128; i128{|i128}{a:0}) }
secret_x_impl! { SecretI128x2 (U256; U128; 1; [u8; 32]; SecretM128x2; SecretU128x2; SecretI128; i128{|i128}{a:0,b:1}) }
secret_x_impl! { SecretI128x4 (U512; U128; 2; [u8; 64]; SecretM128x4; SecretU128x4; SecretI128; i128{|i128}{a:0,b:1,c:2,d:3}) }
secret_x_impl! { SecretI256x1 (U256; U256; 0; [u8; 32]; SecretM256x1; SecretU256x1; SecretI256;     {|()  }{a:0}) }
secret_x_impl! { SecretI256x2 (U512; U256; 1; [u8; 64]; SecretM256x2; SecretU256x2; SecretI256;     {|()  }{a:0,b:1}) }
secret_x_impl! { SecretI512x1 (U512; U512; 0; [u8; 64]; SecretM512x1; SecretU512x1; SecretI512;     {|()  }{a:0}) }


//// Conversions U* <-> U* ////

// these are really tedius, so we use a really heavy-weight macro here
macro_rules! from_impl {
    // bool extending (bool -> u32)
    (@from FB $from:ident for $to:ident) => {
        impl From<$from> for $to {
            fn from(v: $from) -> $to {
                Self(OpTree::and(v.resolve().into_owned(), <$to>::one().0))
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
    // cast same width (u8x4 -> u32)
    (@from CW $from:ident for $to:ident) => {
        impl Cast<$from> for $to {
            fn cast(v: $from) -> $to {
                Self(v.0)
            }
        }
    };
    // unsigned extending lanes (u8x4 -> u32x4)
    (@from FV $from:ident for $to:ident) => {
        impl From<$from> for $to {
            fn from(v: $from) -> $to {
                let mut lanes = [0xff; <$to>::SIZE];
                for i in 0..<$from>::LANES {
                    // this works because i can be at most 64, < u8
                    let off = i*(<$to>::SIZE/<$to>::LANES);
                    lanes[off] = u8::try_from(i).unwrap();
                    lanes[off + 1 .. off + (<$from>::SIZE/<$from>::LANES)]
                        .fill(0x00);
                }

                // drop down to OpTree to avoid extra type parameter
                let extended = OpTree::extend_u(v.0);
                Self(
                    OpTree::shuffle(
                        u8::try_from(
                            (<$to>::LANES * (<$to>::SIZE/<$from>::SIZE))
                                .trailing_zeros()
                        ).unwrap(),
                        OpTree::const_(lanes),
                        extended.clone(),
                        extended
                    )
                )
            }
        }
    };
    // signed extending lanes (i8x4 -> i32x4)
    (@from FZ $from:ident for $to:ident) => {
        impl From<$from> for $to {
            fn from(v: $from) -> $to {
                let mut lanes = [0xff; <$to>::SIZE];
                for i in 0..<$from>::LANES {
                    // this works because i can be at most 64, < u8
                    let off = i*(<$to>::SIZE/<$to>::LANES)
                        + ((<$to>::SIZE/<$to>::LANES)-(<$from>::SIZE/<$from>::LANES));
                    lanes[off] = u8::try_from(i).unwrap();
                    lanes[off + 1 .. off + (<$from>::SIZE/<$from>::LANES)]
                        .fill(0x00);
                }

                // drop down to OpTree to avoid extra type parameter
                let extended = OpTree::extend_u(v.0);
                let shift = 8*((<$to>::SIZE/<$to>::LANES)-(<$from>::SIZE/<$from>::LANES));
                Self(
                    OpTree::shr_s(
                        u8::try_from(<$to>::LANES.trailing_zeros()).unwrap(),
                        OpTree::shuffle(
                            u8::try_from(
                                (<$to>::LANES * (<$to>::SIZE/<$from>::SIZE))
                                    .trailing_zeros()
                            ).unwrap(),
                            OpTree::const_(lanes),
                            extended.clone(),
                            extended
                        ),
                        // a bit of an annoying workaround for type limitations
                        {
                            let mut bytes = [0; <$to>::SIZE];
                            for i in 0..<$to>::LANES {
                                #[allow(unconditional_panic)]
                                if shift > 128 {
                                    bytes[i*(<$to>::SIZE/<$to>::LANES) .. i*(<$to>::SIZE/<$to>::LANES)+2]
                                        .copy_from_slice(
                                            &u16::try_from(shift).unwrap()
                                                .to_le_bytes()
                                        );
                                } else {
                                    bytes[i*(<$to>::SIZE/<$to>::LANES)] = u8::try_from(shift).unwrap();
                                }
                            }
                            OpTree::const_(bytes)
                        }
                    )
                )
            }
        }
    };
    // truncating lanes (u32x4 -> u8x4)
    (@from CX $from:ident for $to:ident) => {
        impl Cast<$from> for $to {
            fn cast(v: $from) -> $to {
                let mut lanes = [0; <$from>::SIZE];
                for i in 0..<$from>::LANES {
                    // this works because i can be at most 64, < u8
                    lanes[i*(<$to>::SIZE/<$to>::LANES)]
                        = u8::try_from(i*(<$from>::SIZE/<$to>::SIZE)).unwrap();
                }

                // drop down to OpTree to avoid extra type parameter
                Self(
                    OpTree::extract(0,
                        OpTree::shuffle(
                            u8::try_from(
                                (<$to>::LANES * (<$from>::SIZE/<$to>::SIZE))
                                    .trailing_zeros()
                            ).unwrap(),
                            OpTree::const_(lanes),
                            v.0.clone(),
                            v.0
                        )
                    )
                )
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
from_impl! { SecretU8  (CW SecretI8,                                                                                      ) }
from_impl! { SecretU16 (             CW SecretI16,                                                                        ) }
from_impl! { SecretU32 (                           CW SecretI32,                                                          ) }
from_impl! { SecretU64 (                                         CW SecretI64,                                            ) }
from_impl! { SecretU128(                                                       CW SecretI128,                             ) }
from_impl! { SecretU256(                                                                      CW SecretI256,              ) }
from_impl! { SecretU512(                                                                                     CW SecretI512) }

// signed from signed
from_impl! { SecretI8  (             CT SecretI16, CT SecretI32, CT SecretI64, CT SecretI128, CT SecretI256, CT SecretI512) }
from_impl! { SecretI16 (FS SecretI8,               CT SecretI32, CT SecretI64, CT SecretI128, CT SecretI256, CT SecretI512) }
from_impl! { SecretI32 (FS SecretI8, FS SecretI16,               CT SecretI64, CT SecretI128, CT SecretI256, CT SecretI512) }
from_impl! { SecretI64 (FS SecretI8, FS SecretI16, FS SecretI32,               CT SecretI128, CT SecretI256, CT SecretI512) }
from_impl! { SecretI128(FS SecretI8, FS SecretI16, FS SecretI32, FS SecretI64,                CT SecretI256, CT SecretI512) }
from_impl! { SecretI256(FS SecretI8, FS SecretI16, FS SecretI32, FS SecretI64, FS SecretI128,                CT SecretI512) }
from_impl! { SecretI512(FS SecretI8, FS SecretI16, FS SecretI32, FS SecretI64, FS SecretI128, FS SecretI256,              ) }

// signed from unsigned
from_impl! { SecretI8  (CW SecretU8,                                                                                      ) }
from_impl! { SecretI16 (FU SecretU8, CW SecretU16,                                                                        ) }
from_impl! { SecretI32 (FU SecretU8, FU SecretU16, CW SecretU32,                                                          ) }
from_impl! { SecretI64 (FU SecretU8, FU SecretU16, FU SecretU32, CW SecretU64,                                            ) }
from_impl! { SecretI128(FU SecretU8, FU SecretU16, FU SecretU32, FU SecretU64, CW SecretU128,                             ) }
from_impl! { SecretI256(FU SecretU8, FU SecretU16, FU SecretU32, FU SecretU64, FU SecretU128, CW SecretU256,              ) }
from_impl! { SecretI512(FU SecretU8, FU SecretU16, FU SecretU32, FU SecretU64, FU SecretU128, FU SecretU256, CW SecretU512) }

// unsigned from same width
from_impl! { SecretU8    (               CW SecretU8x1                                                                                                      ) }
from_impl! { SecretU16   (               CW SecretU8x2,  CW SecretU16x1                                                                                     ) }
from_impl! { SecretU32   (               CW SecretU8x4,  CW SecretU16x2,  CW SecretU32x1                                                                    ) }
from_impl! { SecretU64   (               CW SecretU8x8,  CW SecretU16x4,  CW SecretU32x2,  CW SecretU64x1                                                   ) }
from_impl! { SecretU128  (               CW SecretU8x16, CW SecretU16x8,  CW SecretU32x4,  CW SecretU64x2, CW SecretU128x1                                  ) }
from_impl! { SecretU256  (               CW SecretU8x32, CW SecretU16x16, CW SecretU32x8,  CW SecretU64x4, CW SecretU128x2, CW SecretU256x1                 ) }
from_impl! { SecretU512  (               CW SecretU8x64, CW SecretU16x32, CW SecretU32x16, CW SecretU64x8, CW SecretU128x4, CW SecretU256x2, CW SecretU512x1) }

from_impl! { SecretU8    (               CW SecretI8x1                                                                                                      ) }
from_impl! { SecretU16   (               CW SecretI8x2,  CW SecretI16x1                                                                                     ) }
from_impl! { SecretU32   (               CW SecretI8x4,  CW SecretI16x2,  CW SecretI32x1                                                                    ) }
from_impl! { SecretU64   (               CW SecretI8x8,  CW SecretI16x4,  CW SecretI32x2,  CW SecretI64x1                                                   ) }
from_impl! { SecretU128  (               CW SecretI8x16, CW SecretI16x8,  CW SecretI32x4,  CW SecretI64x2, CW SecretI128x1                                  ) }
from_impl! { SecretU256  (               CW SecretI8x32, CW SecretI16x16, CW SecretI32x8,  CW SecretI64x4, CW SecretI128x2, CW SecretI256x1                 ) }
from_impl! { SecretU512  (               CW SecretI8x64, CW SecretI16x32, CW SecretI32x16, CW SecretI64x8, CW SecretI128x4, CW SecretI256x2, CW SecretI512x1) }

from_impl! { SecretU8    (               CW SecretM8x1                                                                                                      ) }
from_impl! { SecretU16   (               CW SecretM8x2,  CW SecretM16x1                                                                                     ) }
from_impl! { SecretU32   (               CW SecretM8x4,  CW SecretM16x2,  CW SecretM32x1                                                                    ) }
from_impl! { SecretU64   (               CW SecretM8x8,  CW SecretM16x4,  CW SecretM32x2,  CW SecretM64x1                                                   ) }
from_impl! { SecretU128  (               CW SecretM8x16, CW SecretM16x8,  CW SecretM32x4,  CW SecretM64x2, CW SecretM128x1                                  ) }
from_impl! { SecretU256  (               CW SecretM8x32, CW SecretM16x16, CW SecretM32x8,  CW SecretM64x4, CW SecretM128x2, CW SecretM256x1                 ) }
from_impl! { SecretU512  (               CW SecretM8x64, CW SecretM16x32, CW SecretM32x16, CW SecretM64x8, CW SecretM128x4, CW SecretM256x2, CW SecretM512x1) }

// signed from same width
from_impl! { SecretI8    (               CW SecretU8x1                                                                                                      ) }
from_impl! { SecretI16   (               CW SecretU8x2,  CW SecretU16x1                                                                                     ) }
from_impl! { SecretI32   (               CW SecretU8x4,  CW SecretU16x2,  CW SecretU32x1                                                                    ) }
from_impl! { SecretI64   (               CW SecretU8x8,  CW SecretU16x4,  CW SecretU32x2,  CW SecretU64x1                                                   ) }
from_impl! { SecretI128  (               CW SecretU8x16, CW SecretU16x8,  CW SecretU32x4,  CW SecretU64x2, CW SecretU128x1                                  ) }
from_impl! { SecretI256  (               CW SecretU8x32, CW SecretU16x16, CW SecretU32x8,  CW SecretU64x4, CW SecretU128x2, CW SecretU256x1                 ) }
from_impl! { SecretI512  (               CW SecretU8x64, CW SecretU16x32, CW SecretU32x16, CW SecretU64x8, CW SecretU128x4, CW SecretU256x2, CW SecretU512x1) }

from_impl! { SecretI8    (               CW SecretI8x1                                                                                                      ) }
from_impl! { SecretI16   (               CW SecretI8x2,  CW SecretI16x1                                                                                     ) }
from_impl! { SecretI32   (               CW SecretI8x4,  CW SecretI16x2,  CW SecretI32x1                                                                    ) }
from_impl! { SecretI64   (               CW SecretI8x8,  CW SecretI16x4,  CW SecretI32x2,  CW SecretI64x1                                                   ) }
from_impl! { SecretI128  (               CW SecretI8x16, CW SecretI16x8,  CW SecretI32x4,  CW SecretI64x2, CW SecretI128x1                                  ) }
from_impl! { SecretI256  (               CW SecretI8x32, CW SecretI16x16, CW SecretI32x8,  CW SecretI64x4, CW SecretI128x2, CW SecretI256x1                 ) }
from_impl! { SecretI512  (               CW SecretI8x64, CW SecretI16x32, CW SecretI32x16, CW SecretI64x8, CW SecretI128x4, CW SecretI256x2, CW SecretI512x1) }

from_impl! { SecretI8    (               CW SecretM8x1                                                                                                      ) }
from_impl! { SecretI16   (               CW SecretM8x2,  CW SecretM16x1                                                                                     ) }
from_impl! { SecretI32   (               CW SecretM8x4,  CW SecretM16x2,  CW SecretM32x1                                                                    ) }
from_impl! { SecretI64   (               CW SecretM8x8,  CW SecretM16x4,  CW SecretM32x2,  CW SecretM64x1                                                   ) }
from_impl! { SecretI128  (               CW SecretM8x16, CW SecretM16x8,  CW SecretM32x4,  CW SecretM64x2, CW SecretM128x1                                  ) }
from_impl! { SecretI256  (               CW SecretM8x32, CW SecretM16x16, CW SecretM32x8,  CW SecretM64x4, CW SecretM128x2, CW SecretM256x1                 ) }
from_impl! { SecretI512  (               CW SecretM8x64, CW SecretM16x32, CW SecretM32x16, CW SecretM64x8, CW SecretM128x4, CW SecretM256x2, CW SecretM512x1) }

// unsigned lanes from same width
from_impl! { SecretU8x1  (CW SecretU8,                                                                                                                      ) }
from_impl! { SecretU16x1 (CW SecretU16,  CW SecretU8x2                                                                                                      ) }
from_impl! { SecretU32x1 (CW SecretU32,  CW SecretU8x4,  CW SecretU16x2                                                                                     ) }
from_impl! { SecretU64x1 (CW SecretU64,  CW SecretU8x8,  CW SecretU16x4,  CW SecretU32x2                                                                    ) }
from_impl! { SecretU128x1(CW SecretU128, CW SecretU8x16, CW SecretU16x8,  CW SecretU32x4,  CW SecretU64x2                                                   ) }
from_impl! { SecretU256x1(CW SecretU256, CW SecretU8x32, CW SecretU16x16, CW SecretU32x8,  CW SecretU64x4, CW SecretU128x2                                  ) }
from_impl! { SecretU512x1(CW SecretU512, CW SecretU8x64, CW SecretU16x32, CW SecretU32x16, CW SecretU64x8, CW SecretU128x4, CW SecretU256x2                 ) }
                                                         
from_impl! { SecretU8x1  (CW SecretI8,   CW SecretI8x1                                                                                                      ) }
from_impl! { SecretU16x1 (CW SecretI16,  CW SecretI8x2,  CW SecretI16x1                                                                                     ) }
from_impl! { SecretU32x1 (CW SecretI32,  CW SecretI8x4,  CW SecretI16x2,  CW SecretI32x1                                                                    ) }
from_impl! { SecretU64x1 (CW SecretI64,  CW SecretI8x8,  CW SecretI16x4,  CW SecretI32x2,  CW SecretI64x1                                                   ) }
from_impl! { SecretU128x1(CW SecretI128, CW SecretI8x16, CW SecretI16x8,  CW SecretI32x4,  CW SecretI64x2, CW SecretI128x1                                  ) }
from_impl! { SecretU256x1(CW SecretI256, CW SecretI8x32, CW SecretI16x16, CW SecretI32x8,  CW SecretI64x4, CW SecretI128x2, CW SecretI256x1                 ) }
from_impl! { SecretU512x1(CW SecretI512, CW SecretI8x64, CW SecretI16x32, CW SecretI32x16, CW SecretI64x8, CW SecretI128x4, CW SecretI256x2, CW SecretI512x1) }
                                                         
from_impl! { SecretU8x1  (               CW SecretM8x1                                                                                                      ) }
from_impl! { SecretU16x1 (               CW SecretM8x2,  CW SecretM16x1                                                                                     ) }
from_impl! { SecretU32x1 (               CW SecretM8x4,  CW SecretM16x2,  CW SecretM32x1                                                                    ) }
from_impl! { SecretU64x1 (               CW SecretM8x8,  CW SecretM16x4,  CW SecretM32x2,  CW SecretM64x1                                                   ) }
from_impl! { SecretU128x1(               CW SecretM8x16, CW SecretM16x8,  CW SecretM32x4,  CW SecretM64x2, CW SecretM128x1                                  ) }
from_impl! { SecretU256x1(               CW SecretM8x32, CW SecretM16x16, CW SecretM32x8,  CW SecretM64x4, CW SecretM128x2, CW SecretM256x1                 ) }
from_impl! { SecretU512x1(               CW SecretM8x64, CW SecretM16x32, CW SecretM32x16, CW SecretM64x8, CW SecretM128x4, CW SecretM256x2, CW SecretM512x1) }

from_impl! { SecretU8x2  (CW SecretU16,                  CW SecretU16x1                                                                                     ) }
from_impl! { SecretU16x2 (CW SecretU32,  CW SecretU8x4,                   CW SecretU32x1                                                                    ) }
from_impl! { SecretU32x2 (CW SecretU64,  CW SecretU8x8,  CW SecretU16x4,                   CW SecretU64x1                                                   ) }
from_impl! { SecretU64x2 (CW SecretU128, CW SecretU8x16, CW SecretU16x8,  CW SecretU32x4,                  CW SecretU128x1                                  ) }
from_impl! { SecretU128x2(CW SecretU256, CW SecretU8x32, CW SecretU16x16, CW SecretU32x8,  CW SecretU64x4,                  CW SecretU256x1                 ) }
from_impl! { SecretU256x2(CW SecretU512, CW SecretU8x64, CW SecretU16x32, CW SecretU32x16, CW SecretU64x8, CW SecretU128x4,                  CW SecretU512x1) }

from_impl! { SecretU8x2  (CW SecretI16,  CW SecretI8x2,  CW SecretI16x1                                                                                     ) }
from_impl! { SecretU16x2 (CW SecretI32,  CW SecretI8x4,  CW SecretI16x2,  CW SecretI32x1                                                                    ) }
from_impl! { SecretU32x2 (CW SecretI64,  CW SecretI8x8,  CW SecretI16x4,  CW SecretI32x2,  CW SecretI64x1                                                   ) }
from_impl! { SecretU64x2 (CW SecretI128, CW SecretI8x16, CW SecretI16x8,  CW SecretI32x4,  CW SecretI64x2, CW SecretI128x1                                  ) }
from_impl! { SecretU128x2(CW SecretI256, CW SecretI8x32, CW SecretI16x16, CW SecretI32x8,  CW SecretI64x4, CW SecretI128x2, CW SecretI256x1                 ) }
from_impl! { SecretU256x2(CW SecretI512, CW SecretI8x64, CW SecretI16x32, CW SecretI32x16, CW SecretI64x8, CW SecretI128x4, CW SecretI256x2, CW SecretI512x1) }

from_impl! { SecretU8x2  (               CW SecretM8x2,  CW SecretM16x1                                                                                     ) }
from_impl! { SecretU16x2 (               CW SecretM8x4,  CW SecretM16x2,  CW SecretM32x1                                                                    ) }
from_impl! { SecretU32x2 (               CW SecretM8x8,  CW SecretM16x4,  CW SecretM32x2,  CW SecretM64x1                                                   ) }
from_impl! { SecretU64x2 (               CW SecretM8x16, CW SecretM16x8,  CW SecretM32x4,  CW SecretM64x2, CW SecretM128x1                                  ) }
from_impl! { SecretU128x2(               CW SecretM8x32, CW SecretM16x16, CW SecretM32x8,  CW SecretM64x4, CW SecretM128x2, CW SecretM256x1                 ) }
from_impl! { SecretU256x2(               CW SecretM8x64, CW SecretM16x32, CW SecretM32x16, CW SecretM64x8, CW SecretM128x4, CW SecretM256x2, CW SecretM512x1) }

from_impl! { SecretU8x4  (CW SecretU32,                  CW SecretU16x2,  CW SecretU32x1                                                                    ) }
from_impl! { SecretU16x4 (CW SecretU64,  CW SecretU8x8,                   CW SecretU32x2,  CW SecretU64x1                                                   ) }
from_impl! { SecretU32x4 (CW SecretU128, CW SecretU8x16, CW SecretU16x8,                   CW SecretU64x2, CW SecretU128x1                                  ) }
from_impl! { SecretU64x4 (CW SecretU256, CW SecretU8x32, CW SecretU16x16, CW SecretU32x8,                  CW SecretU128x2, CW SecretU256x1                 ) }
from_impl! { SecretU128x4(CW SecretU512, CW SecretU8x64, CW SecretU16x32, CW SecretU32x16, CW SecretU64x8,                  CW SecretU256x2, CW SecretU512x1) }

from_impl! { SecretU8x4  (CW SecretI32,  CW SecretI8x4,  CW SecretI16x2,  CW SecretI32x1                                                                    ) }
from_impl! { SecretU16x4 (CW SecretI64,  CW SecretI8x8,  CW SecretI16x4,  CW SecretI32x2,  CW SecretI64x1                                                   ) }
from_impl! { SecretU32x4 (CW SecretI128, CW SecretI8x16, CW SecretI16x8,  CW SecretI32x4,  CW SecretI64x2, CW SecretI128x1                                  ) }
from_impl! { SecretU64x4 (CW SecretI256, CW SecretI8x32, CW SecretI16x16, CW SecretI32x8,  CW SecretI64x4, CW SecretI128x2, CW SecretI256x1                 ) }
from_impl! { SecretU128x4(CW SecretI512, CW SecretI8x64, CW SecretI16x32, CW SecretI32x16, CW SecretI64x8, CW SecretI128x4, CW SecretI256x2, CW SecretI512x1) }

from_impl! { SecretU8x4  (               CW SecretM8x4,  CW SecretM16x2,  CW SecretM32x1                                                                    ) }
from_impl! { SecretU16x4 (               CW SecretM8x8,  CW SecretM16x4,  CW SecretM32x2,  CW SecretM64x1                                                   ) }
from_impl! { SecretU32x4 (               CW SecretM8x16, CW SecretM16x8,  CW SecretM32x4,  CW SecretM64x2, CW SecretM128x1                                  ) }
from_impl! { SecretU64x4 (               CW SecretM8x32, CW SecretM16x16, CW SecretM32x8,  CW SecretM64x4, CW SecretM128x2, CW SecretM256x1                 ) }
from_impl! { SecretU128x4(               CW SecretM8x64, CW SecretM16x32, CW SecretM32x16, CW SecretM64x8, CW SecretM128x4, CW SecretM256x2, CW SecretM512x1) }

from_impl! { SecretU8x8  (CW SecretU64,                  CW SecretU16x4,  CW SecretU32x2,  CW SecretU64x1                                                   ) }
from_impl! { SecretU16x8 (CW SecretU128, CW SecretU8x16,                  CW SecretU32x4,  CW SecretU64x2, CW SecretU128x1                                  ) }
from_impl! { SecretU32x8 (CW SecretU256, CW SecretU8x32, CW SecretU16x16,                  CW SecretU64x4, CW SecretU128x2, CW SecretU256x1                 ) }
from_impl! { SecretU64x8 (CW SecretU512, CW SecretU8x64, CW SecretU16x32, CW SecretU32x16,                 CW SecretU128x4, CW SecretU256x2, CW SecretU512x1) }

from_impl! { SecretU8x8  (CW SecretI64,  CW SecretI8x8,  CW SecretI16x4,  CW SecretI32x2,  CW SecretI64x1                                                   ) }
from_impl! { SecretU16x8 (CW SecretI128, CW SecretI8x16, CW SecretI16x8,  CW SecretI32x4,  CW SecretI64x2, CW SecretI128x1                                  ) }
from_impl! { SecretU32x8 (CW SecretI256, CW SecretI8x32, CW SecretI16x16, CW SecretI32x8,  CW SecretI64x4, CW SecretI128x2, CW SecretI256x1                 ) }
from_impl! { SecretU64x8 (CW SecretI512, CW SecretI8x64, CW SecretI16x32, CW SecretI32x16, CW SecretI64x8, CW SecretI128x4, CW SecretI256x2, CW SecretI512x1) }

from_impl! { SecretU8x8  (               CW SecretM8x8,  CW SecretM16x4,  CW SecretM32x2,  CW SecretM64x1                                                   ) }
from_impl! { SecretU16x8 (               CW SecretM8x16, CW SecretM16x8,  CW SecretM32x4,  CW SecretM64x2, CW SecretM128x1                                  ) }
from_impl! { SecretU32x8 (               CW SecretM8x32, CW SecretM16x16, CW SecretM32x8,  CW SecretM64x4, CW SecretM128x2, CW SecretM256x1                 ) }
from_impl! { SecretU64x8 (               CW SecretM8x64, CW SecretM16x32, CW SecretM32x16, CW SecretM64x8, CW SecretM128x4, CW SecretM256x2, CW SecretM512x1) }

from_impl! { SecretU8x16 (CW SecretU128,                 CW SecretU16x8,  CW SecretU32x4,  CW SecretU64x2, CW SecretU128x1                                  ) }
from_impl! { SecretU16x16(CW SecretU256, CW SecretU8x32,                  CW SecretU32x8,  CW SecretU64x4, CW SecretU128x2, CW SecretU256x1                 ) }
from_impl! { SecretU32x16(CW SecretU512, CW SecretU8x64, CW SecretU16x32,                  CW SecretU64x8, CW SecretU128x4, CW SecretU256x2, CW SecretU512x1) }

from_impl! { SecretU8x16 (CW SecretI128, CW SecretI8x16, CW SecretI16x8,  CW SecretI32x4,  CW SecretI64x2, CW SecretI128x1                                  ) }
from_impl! { SecretU16x16(CW SecretI256, CW SecretI8x32, CW SecretI16x16, CW SecretI32x8,  CW SecretI64x4, CW SecretI128x2, CW SecretI256x1                 ) }
from_impl! { SecretU32x16(CW SecretI512, CW SecretI8x64, CW SecretI16x32, CW SecretI32x16, CW SecretI64x8, CW SecretI128x4, CW SecretI256x2, CW SecretI512x1) }

from_impl! { SecretU8x16 (               CW SecretM8x16, CW SecretM16x8,  CW SecretM32x4,  CW SecretM64x2, CW SecretM128x1                                  ) }
from_impl! { SecretU16x16(               CW SecretM8x32, CW SecretM16x16, CW SecretM32x8,  CW SecretM64x4, CW SecretM128x2, CW SecretM256x1                 ) }
from_impl! { SecretU32x16(               CW SecretM8x64, CW SecretM16x32, CW SecretM32x16, CW SecretM64x8, CW SecretM128x4, CW SecretM256x2, CW SecretM512x1) }

from_impl! { SecretU8x32 (CW SecretU256,                 CW SecretU16x16, CW SecretU32x8,  CW SecretU64x4, CW SecretU128x2, CW SecretU256x1                 ) }
from_impl! { SecretU16x32(CW SecretU512, CW SecretU8x64,                  CW SecretU32x16, CW SecretU64x8, CW SecretU128x4, CW SecretU256x2, CW SecretU512x1) }

from_impl! { SecretU8x32 (CW SecretI256, CW SecretI8x32, CW SecretI16x16, CW SecretI32x8,  CW SecretI64x4, CW SecretI128x2, CW SecretI256x1                 ) }
from_impl! { SecretU16x32(CW SecretI512, CW SecretI8x64, CW SecretI16x32, CW SecretI32x16, CW SecretI64x8, CW SecretI128x4, CW SecretI256x2, CW SecretI512x1) }

from_impl! { SecretU8x32 (               CW SecretM8x32, CW SecretM16x16, CW SecretM32x8,  CW SecretM64x4, CW SecretM128x2, CW SecretM256x1                 ) }
from_impl! { SecretU16x32(               CW SecretM8x64, CW SecretM16x32, CW SecretM32x16, CW SecretM64x8, CW SecretM128x4, CW SecretM256x2, CW SecretM512x1) }

from_impl! { SecretU8x64 (CW SecretU512,                 CW SecretU16x32, CW SecretU32x16, CW SecretU64x8, CW SecretU128x4, CW SecretU256x2, CW SecretU512x1) }

from_impl! { SecretU8x64 (CW SecretI512, CW SecretI8x64, CW SecretI16x32, CW SecretI32x16, CW SecretI64x8, CW SecretI128x4, CW SecretI256x2, CW SecretI512x1) }

from_impl! { SecretU8x64 (               CW SecretM8x64, CW SecretM16x32, CW SecretM32x16, CW SecretM64x8, CW SecretM128x4, CW SecretM256x2, CW SecretM512x1) }

// signed lanes from same width
from_impl! { SecretI8x1  (CW SecretU8,   CW SecretU8x1                                                                                                      ) }
from_impl! { SecretI16x1 (CW SecretU16,  CW SecretU8x2,  CW SecretU16x1                                                                                     ) }
from_impl! { SecretI32x1 (CW SecretU32,  CW SecretU8x4,  CW SecretU16x2,  CW SecretU32x1                                                                    ) }
from_impl! { SecretI64x1 (CW SecretU64,  CW SecretU8x8,  CW SecretU16x4,  CW SecretU32x2,  CW SecretU64x1                                                   ) }
from_impl! { SecretI128x1(CW SecretU128, CW SecretU8x16, CW SecretU16x8,  CW SecretU32x4,  CW SecretU64x2, CW SecretU128x1                                  ) }
from_impl! { SecretI256x1(CW SecretU256, CW SecretU8x32, CW SecretU16x16, CW SecretU32x8,  CW SecretU64x4, CW SecretU128x2, CW SecretU256x1                 ) }
from_impl! { SecretI512x1(CW SecretU512, CW SecretU8x64, CW SecretU16x32, CW SecretU32x16, CW SecretU64x8, CW SecretU128x4, CW SecretU256x2, CW SecretU512x1) }

from_impl! { SecretI8x1  (CW SecretI8,                                                                                                                      ) }
from_impl! { SecretI16x1 (CW SecretI16,  CW SecretI8x2                                                                                                      ) }
from_impl! { SecretI32x1 (CW SecretI32,  CW SecretI8x4,  CW SecretI16x2                                                                                     ) }
from_impl! { SecretI64x1 (CW SecretI64,  CW SecretI8x8,  CW SecretI16x4,  CW SecretI32x2                                                                    ) }
from_impl! { SecretI128x1(CW SecretI128, CW SecretI8x16, CW SecretI16x8,  CW SecretI32x4,  CW SecretI64x2                                                   ) }
from_impl! { SecretI256x1(CW SecretI256, CW SecretI8x32, CW SecretI16x16, CW SecretI32x8,  CW SecretI64x4, CW SecretI128x2                                  ) }
from_impl! { SecretI512x1(CW SecretI512, CW SecretI8x64, CW SecretI16x32, CW SecretI32x16, CW SecretI64x8, CW SecretI128x4, CW SecretI256x2                 ) }

from_impl! { SecretI8x1  (               CW SecretM8x1                                                                                                      ) }
from_impl! { SecretI16x1 (               CW SecretM8x2,  CW SecretM16x1                                                                                     ) }
from_impl! { SecretI32x1 (               CW SecretM8x4,  CW SecretM16x2,  CW SecretM32x1                                                                    ) }
from_impl! { SecretI64x1 (               CW SecretM8x8,  CW SecretM16x4,  CW SecretM32x2,  CW SecretM64x1                                                   ) }
from_impl! { SecretI128x1(               CW SecretM8x16, CW SecretM16x8,  CW SecretM32x4,  CW SecretM64x2, CW SecretM128x1                                  ) }
from_impl! { SecretI256x1(               CW SecretM8x32, CW SecretM16x16, CW SecretM32x8,  CW SecretM64x4, CW SecretM128x2, CW SecretM256x1                 ) }
from_impl! { SecretI512x1(               CW SecretM8x64, CW SecretM16x32, CW SecretM32x16, CW SecretM64x8, CW SecretM128x4, CW SecretM256x2, CW SecretM512x1) }

from_impl! { SecretI8x2  (CW SecretU16,  CW SecretU8x2,  CW SecretU16x1                                                                                     ) }
from_impl! { SecretI16x2 (CW SecretU32,  CW SecretU8x4,  CW SecretU16x2,  CW SecretU32x1                                                                    ) }
from_impl! { SecretI32x2 (CW SecretU64,  CW SecretU8x8,  CW SecretU16x4,  CW SecretU32x2,  CW SecretU64x1                                                   ) }
from_impl! { SecretI64x2 (CW SecretU128, CW SecretU8x16, CW SecretU16x8,  CW SecretU32x4,  CW SecretU64x2, CW SecretU128x1                                  ) }
from_impl! { SecretI128x2(CW SecretU256, CW SecretU8x32, CW SecretU16x16, CW SecretU32x8,  CW SecretU64x4, CW SecretU128x2, CW SecretU256x1                 ) }
from_impl! { SecretI256x2(CW SecretU512, CW SecretU8x64, CW SecretU16x32, CW SecretU32x16, CW SecretU64x8, CW SecretU128x4, CW SecretU256x2, CW SecretU512x1) }

from_impl! { SecretI8x2  (CW SecretI16,                  CW SecretI16x1                                                                                     ) }
from_impl! { SecretI16x2 (CW SecretI32,  CW SecretI8x4,                   CW SecretI32x1                                                                    ) }
from_impl! { SecretI32x2 (CW SecretI64,  CW SecretI8x8,  CW SecretI16x4,                   CW SecretI64x1                                                   ) }
from_impl! { SecretI64x2 (CW SecretI128, CW SecretI8x16, CW SecretI16x8,  CW SecretI32x4,                  CW SecretI128x1                                  ) }
from_impl! { SecretI128x2(CW SecretI256, CW SecretI8x32, CW SecretI16x16, CW SecretI32x8,  CW SecretI64x4,                  CW SecretI256x1                 ) }
from_impl! { SecretI256x2(CW SecretI512, CW SecretI8x64, CW SecretI16x32, CW SecretI32x16, CW SecretI64x8, CW SecretI128x4,                  CW SecretI512x1) }

from_impl! { SecretI8x2  (               CW SecretM8x2,  CW SecretM16x1                                                                                     ) }
from_impl! { SecretI16x2 (               CW SecretM8x4,  CW SecretM16x2,  CW SecretM32x1                                                                    ) }
from_impl! { SecretI32x2 (               CW SecretM8x8,  CW SecretM16x4,  CW SecretM32x2,  CW SecretM64x1                                                   ) }
from_impl! { SecretI64x2 (               CW SecretM8x16, CW SecretM16x8,  CW SecretM32x4,  CW SecretM64x2, CW SecretM128x1                                  ) }
from_impl! { SecretI128x2(               CW SecretM8x32, CW SecretM16x16, CW SecretM32x8,  CW SecretM64x4, CW SecretM128x2, CW SecretM256x1                 ) }
from_impl! { SecretI256x2(               CW SecretM8x64, CW SecretM16x32, CW SecretM32x16, CW SecretM64x8, CW SecretM128x4, CW SecretM256x2, CW SecretM512x1) }

from_impl! { SecretI8x4  (CW SecretU32,  CW SecretU8x4,  CW SecretU16x2,  CW SecretU32x1                                                                    ) }
from_impl! { SecretI16x4 (CW SecretU64,  CW SecretU8x8,  CW SecretU16x4,  CW SecretU32x2,  CW SecretU64x1                                                   ) }
from_impl! { SecretI32x4 (CW SecretU128, CW SecretU8x16, CW SecretU16x8,  CW SecretU32x4,  CW SecretU64x2, CW SecretU128x1                                  ) }
from_impl! { SecretI64x4 (CW SecretU256, CW SecretU8x32, CW SecretU16x16, CW SecretU32x8,  CW SecretU64x4, CW SecretU128x2, CW SecretU256x1                 ) }
from_impl! { SecretI128x4(CW SecretU512, CW SecretU8x64, CW SecretU16x32, CW SecretU32x16, CW SecretU64x8, CW SecretU128x4, CW SecretU256x2, CW SecretU512x1) }

from_impl! { SecretI8x4  (CW SecretI32,                  CW SecretI16x2,  CW SecretI32x1                                                                    ) }
from_impl! { SecretI16x4 (CW SecretI64,  CW SecretI8x8,                   CW SecretI32x2,  CW SecretI64x1                                                   ) }
from_impl! { SecretI32x4 (CW SecretI128, CW SecretI8x16, CW SecretI16x8,                   CW SecretI64x2, CW SecretI128x1                                  ) }
from_impl! { SecretI64x4 (CW SecretI256, CW SecretI8x32, CW SecretI16x16, CW SecretI32x8,                  CW SecretI128x2, CW SecretI256x1                 ) }
from_impl! { SecretI128x4(CW SecretI512, CW SecretI8x64, CW SecretI16x32, CW SecretI32x16, CW SecretI64x8,                  CW SecretI256x2, CW SecretI512x1) }

from_impl! { SecretI8x4  (               CW SecretM8x4,  CW SecretM16x2,  CW SecretM32x1                                                                    ) }
from_impl! { SecretI16x4 (               CW SecretM8x8,  CW SecretM16x4,  CW SecretM32x2,  CW SecretM64x1                                                   ) }
from_impl! { SecretI32x4 (               CW SecretM8x16, CW SecretM16x8,  CW SecretM32x4,  CW SecretM64x2, CW SecretM128x1                                  ) }
from_impl! { SecretI64x4 (               CW SecretM8x32, CW SecretM16x16, CW SecretM32x8,  CW SecretM64x4, CW SecretM128x2, CW SecretM256x1                 ) }
from_impl! { SecretI128x4(               CW SecretM8x64, CW SecretM16x32, CW SecretM32x16, CW SecretM64x8, CW SecretM128x4, CW SecretM256x2, CW SecretM512x1) }

from_impl! { SecretI8x8  (CW SecretU64,  CW SecretU8x8,  CW SecretU16x4,  CW SecretU32x2,  CW SecretU64x1                                                   ) }
from_impl! { SecretI16x8 (CW SecretU128, CW SecretU8x16, CW SecretU16x8,  CW SecretU32x4,  CW SecretU64x2, CW SecretU128x1                                  ) }
from_impl! { SecretI32x8 (CW SecretU256, CW SecretU8x32, CW SecretU16x16, CW SecretU32x8,  CW SecretU64x4, CW SecretU128x2, CW SecretU256x1                 ) }
from_impl! { SecretI64x8 (CW SecretU512, CW SecretU8x64, CW SecretU16x32, CW SecretU32x16, CW SecretU64x8, CW SecretU128x4, CW SecretU256x2, CW SecretU512x1) }

from_impl! { SecretI8x8  (CW SecretI64,                  CW SecretI16x4,  CW SecretI32x2,  CW SecretI64x1                                                   ) }
from_impl! { SecretI16x8 (CW SecretI128, CW SecretI8x16,                  CW SecretI32x4,  CW SecretI64x2, CW SecretI128x1                                  ) }
from_impl! { SecretI32x8 (CW SecretI256, CW SecretI8x32, CW SecretI16x16,                  CW SecretI64x4, CW SecretI128x2, CW SecretI256x1                 ) }
from_impl! { SecretI64x8 (CW SecretI512, CW SecretI8x64, CW SecretI16x32, CW SecretI32x16,                 CW SecretI128x4, CW SecretI256x2, CW SecretI512x1) }

from_impl! { SecretI8x8  (               CW SecretM8x8,  CW SecretM16x4,  CW SecretM32x2,  CW SecretM64x1                                                   ) }
from_impl! { SecretI16x8 (               CW SecretM8x16, CW SecretM16x8,  CW SecretM32x4,  CW SecretM64x2, CW SecretM128x1                                  ) }
from_impl! { SecretI32x8 (               CW SecretM8x32, CW SecretM16x16, CW SecretM32x8,  CW SecretM64x4, CW SecretM128x2, CW SecretM256x1                 ) }
from_impl! { SecretI64x8 (               CW SecretM8x64, CW SecretM16x32, CW SecretM32x16, CW SecretM64x8, CW SecretM128x4, CW SecretM256x2, CW SecretM512x1) }

from_impl! { SecretI8x16 (CW SecretU128, CW SecretU8x16, CW SecretU16x8,  CW SecretU32x4,  CW SecretU64x2, CW SecretU128x1                                  ) }
from_impl! { SecretI16x16(CW SecretU256, CW SecretU8x32, CW SecretU16x16, CW SecretU32x8,  CW SecretU64x4, CW SecretU128x2, CW SecretU256x1                 ) }
from_impl! { SecretI32x16(CW SecretU512, CW SecretU8x64, CW SecretU16x32, CW SecretU32x16, CW SecretU64x8, CW SecretU128x4, CW SecretU256x2, CW SecretU512x1) }

from_impl! { SecretI8x16 (CW SecretI128,                 CW SecretI16x8,  CW SecretI32x4,  CW SecretI64x2, CW SecretI128x1                                  ) }
from_impl! { SecretI16x16(CW SecretI256, CW SecretI8x32,                  CW SecretI32x8,  CW SecretI64x4, CW SecretI128x2, CW SecretI256x1                 ) }
from_impl! { SecretI32x16(CW SecretI512, CW SecretI8x64, CW SecretI16x32,                  CW SecretI64x8, CW SecretI128x4, CW SecretI256x2, CW SecretI512x1) }

from_impl! { SecretI8x16 (               CW SecretM8x16, CW SecretM16x8,  CW SecretM32x4,  CW SecretM64x2, CW SecretM128x1                                  ) }
from_impl! { SecretI16x16(               CW SecretM8x32, CW SecretM16x16, CW SecretM32x8,  CW SecretM64x4, CW SecretM128x2, CW SecretM256x1                 ) }
from_impl! { SecretI32x16(               CW SecretM8x64, CW SecretM16x32, CW SecretM32x16, CW SecretM64x8, CW SecretM128x4, CW SecretM256x2, CW SecretM512x1) }

from_impl! { SecretI8x32 (CW SecretU256, CW SecretU8x32, CW SecretU16x16, CW SecretU32x8,  CW SecretU64x4, CW SecretU128x2, CW SecretU256x1                 ) }
from_impl! { SecretI16x32(CW SecretU512, CW SecretU8x64, CW SecretU16x32, CW SecretU32x16, CW SecretU64x8, CW SecretU128x4, CW SecretU256x2, CW SecretU512x1) }

from_impl! { SecretI8x32 (CW SecretI256,                 CW SecretI16x16, CW SecretI32x8,  CW SecretI64x4, CW SecretI128x2, CW SecretI256x1                 ) }
from_impl! { SecretI16x32(CW SecretI512, CW SecretI8x64,                  CW SecretI32x16, CW SecretI64x8, CW SecretI128x4, CW SecretI256x2, CW SecretI512x1) }

from_impl! { SecretI8x32 (               CW SecretM8x32, CW SecretM16x16, CW SecretM32x8,  CW SecretM64x4, CW SecretM128x2, CW SecretM256x1                 ) }
from_impl! { SecretI16x32(               CW SecretM8x64, CW SecretM16x32, CW SecretM32x16, CW SecretM64x8, CW SecretM128x4, CW SecretM256x2, CW SecretM512x1) }

from_impl! { SecretI8x64 (CW SecretU512, CW SecretU8x64, CW SecretU16x32, CW SecretU32x16, CW SecretU64x8, CW SecretU128x4, CW SecretU256x2, CW SecretU512x1) }

from_impl! { SecretI8x64 (CW SecretI512,                 CW SecretI16x32, CW SecretI32x16, CW SecretI64x8, CW SecretI128x4, CW SecretI256x2, CW SecretI512x1) }

from_impl! { SecretI8x64 (               CW SecretM8x64, CW SecretM16x32, CW SecretM32x16, CW SecretM64x8, CW SecretM128x4, CW SecretM256x2, CW SecretM512x1) }

// masks from same width
from_impl! { SecretM8x1  (CW SecretU8,   CW SecretU8x1                                                                                                      ) }
from_impl! { SecretM16x1 (CW SecretU16,  CW SecretU8x2,  CW SecretU16x1                                                                                     ) }
from_impl! { SecretM32x1 (CW SecretU32,  CW SecretU8x4,  CW SecretU16x2,  CW SecretU32x1                                                                    ) }
from_impl! { SecretM64x1 (CW SecretU64,  CW SecretU8x8,  CW SecretU16x4,  CW SecretU32x2,  CW SecretU64x1                                                   ) }
from_impl! { SecretM128x1(CW SecretU128, CW SecretU8x16, CW SecretU16x8,  CW SecretU32x4,  CW SecretU64x2, CW SecretU128x1                                  ) }
from_impl! { SecretM256x1(CW SecretU256, CW SecretU8x32, CW SecretU16x16, CW SecretU32x8,  CW SecretU64x4, CW SecretU128x2, CW SecretU256x1                 ) }
from_impl! { SecretM512x1(CW SecretU512, CW SecretU8x64, CW SecretU16x32, CW SecretU32x16, CW SecretU64x8, CW SecretU128x4, CW SecretU256x2, CW SecretU512x1) }

from_impl! { SecretM8x1  (CW SecretI8,   CW SecretI8x1                                                                                                      ) }
from_impl! { SecretM16x1 (CW SecretI16,  CW SecretI8x2,  CW SecretI16x1                                                                                     ) }
from_impl! { SecretM32x1 (CW SecretI32,  CW SecretI8x4,  CW SecretI16x2,  CW SecretI32x1                                                                    ) }
from_impl! { SecretM64x1 (CW SecretI64,  CW SecretI8x8,  CW SecretI16x4,  CW SecretI32x2,  CW SecretI64x1                                                   ) }
from_impl! { SecretM128x1(CW SecretI128, CW SecretI8x16, CW SecretI16x8,  CW SecretI32x4,  CW SecretI64x2, CW SecretI128x1                                  ) }
from_impl! { SecretM256x1(CW SecretI256, CW SecretI8x32, CW SecretI16x16, CW SecretI32x8,  CW SecretI64x4, CW SecretI128x2, CW SecretI256x1                 ) }
from_impl! { SecretM512x1(CW SecretI512, CW SecretI8x64, CW SecretI16x32, CW SecretI32x16, CW SecretI64x8, CW SecretI128x4, CW SecretI256x2, CW SecretI512x1) }

from_impl! { SecretM8x1  (                                                                                                                                  ) }
from_impl! { SecretM16x1 (               CW SecretM8x2                                                                                                      ) }
from_impl! { SecretM32x1 (               CW SecretM8x4,  CW SecretM16x2                                                                                     ) }
from_impl! { SecretM64x1 (               CW SecretM8x8,  CW SecretM16x4,  CW SecretM32x2                                                                    ) }
from_impl! { SecretM128x1(               CW SecretM8x16, CW SecretM16x8,  CW SecretM32x4,  CW SecretM64x2                                                   ) }
from_impl! { SecretM256x1(               CW SecretM8x32, CW SecretM16x16, CW SecretM32x8,  CW SecretM64x4, CW SecretM128x2                                  ) }
from_impl! { SecretM512x1(               CW SecretM8x64, CW SecretM16x32, CW SecretM32x16, CW SecretM64x8, CW SecretM128x4, CW SecretM256x2                 ) }

from_impl! { SecretM8x2  (CW SecretU16,  CW SecretU8x2,  CW SecretU16x1                                                                                     ) }
from_impl! { SecretM16x2 (CW SecretU32,  CW SecretU8x4,  CW SecretU16x2,  CW SecretU32x1                                                                    ) }
from_impl! { SecretM32x2 (CW SecretU64,  CW SecretU8x8,  CW SecretU16x4,  CW SecretU32x2,  CW SecretU64x1                                                   ) }
from_impl! { SecretM64x2 (CW SecretU128, CW SecretU8x16, CW SecretU16x8,  CW SecretU32x4,  CW SecretU64x2, CW SecretU128x1                                  ) }
from_impl! { SecretM128x2(CW SecretU256, CW SecretU8x32, CW SecretU16x16, CW SecretU32x8,  CW SecretU64x4, CW SecretU128x2, CW SecretU256x1                 ) }
from_impl! { SecretM256x2(CW SecretU512, CW SecretU8x64, CW SecretU16x32, CW SecretU32x16, CW SecretU64x8, CW SecretU128x4, CW SecretU256x2, CW SecretU512x1) }

from_impl! { SecretM8x2  (CW SecretI16,  CW SecretI8x2,  CW SecretI16x1                                                                                     ) }
from_impl! { SecretM16x2 (CW SecretI32,  CW SecretI8x4,  CW SecretI16x2,  CW SecretI32x1                                                                    ) }
from_impl! { SecretM32x2 (CW SecretI64,  CW SecretI8x8,  CW SecretI16x4,  CW SecretI32x2,  CW SecretI64x1                                                   ) }
from_impl! { SecretM64x2 (CW SecretI128, CW SecretI8x16, CW SecretI16x8,  CW SecretI32x4,  CW SecretI64x2, CW SecretI128x1                                  ) }
from_impl! { SecretM128x2(CW SecretI256, CW SecretI8x32, CW SecretI16x16, CW SecretI32x8,  CW SecretI64x4, CW SecretI128x2, CW SecretI256x1                 ) }
from_impl! { SecretM256x2(CW SecretI512, CW SecretI8x64, CW SecretI16x32, CW SecretI32x16, CW SecretI64x8, CW SecretI128x4, CW SecretI256x2, CW SecretI512x1) }

from_impl! { SecretM8x2  (                               CW SecretM16x1                                                                                     ) }
from_impl! { SecretM16x2 (               CW SecretM8x4,                   CW SecretM32x1                                                                    ) }
from_impl! { SecretM32x2 (               CW SecretM8x8,  CW SecretM16x4,                   CW SecretM64x1                                                   ) }
from_impl! { SecretM64x2 (               CW SecretM8x16, CW SecretM16x8,  CW SecretM32x4,                  CW SecretM128x1                                  ) }
from_impl! { SecretM128x2(               CW SecretM8x32, CW SecretM16x16, CW SecretM32x8,  CW SecretM64x4,                  CW SecretM256x1                 ) }
from_impl! { SecretM256x2(               CW SecretM8x64, CW SecretM16x32, CW SecretM32x16, CW SecretM64x8, CW SecretM128x4,                  CW SecretM512x1) }

from_impl! { SecretM8x4  (CW SecretU32,  CW SecretU8x4,  CW SecretU16x2,  CW SecretU32x1                                                                    ) }
from_impl! { SecretM16x4 (CW SecretU64,  CW SecretU8x8,  CW SecretU16x4,  CW SecretU32x2,  CW SecretU64x1                                                   ) }
from_impl! { SecretM32x4 (CW SecretU128, CW SecretU8x16, CW SecretU16x8,  CW SecretU32x4,  CW SecretU64x2, CW SecretU128x1                                  ) }
from_impl! { SecretM64x4 (CW SecretU256, CW SecretU8x32, CW SecretU16x16, CW SecretU32x8,  CW SecretU64x4, CW SecretU128x2, CW SecretU256x1                 ) }
from_impl! { SecretM128x4(CW SecretU512, CW SecretU8x64, CW SecretU16x32, CW SecretU32x16, CW SecretU64x8, CW SecretU128x4, CW SecretU256x2, CW SecretU512x1) }

from_impl! { SecretM8x4  (CW SecretI32,  CW SecretI8x4,  CW SecretI16x2,  CW SecretI32x1                                                                    ) }
from_impl! { SecretM16x4 (CW SecretI64,  CW SecretI8x8,  CW SecretI16x4,  CW SecretI32x2,  CW SecretI64x1                                                   ) }
from_impl! { SecretM32x4 (CW SecretI128, CW SecretI8x16, CW SecretI16x8,  CW SecretI32x4,  CW SecretI64x2, CW SecretI128x1                                  ) }
from_impl! { SecretM64x4 (CW SecretI256, CW SecretI8x32, CW SecretI16x16, CW SecretI32x8,  CW SecretI64x4, CW SecretI128x2, CW SecretI256x1                 ) }
from_impl! { SecretM128x4(CW SecretI512, CW SecretI8x64, CW SecretI16x32, CW SecretI32x16, CW SecretI64x8, CW SecretI128x4, CW SecretI256x2, CW SecretI512x1) }

from_impl! { SecretM8x4  (                               CW SecretM16x2,  CW SecretM32x1                                                                    ) }
from_impl! { SecretM16x4 (               CW SecretM8x8,                   CW SecretM32x2,  CW SecretM64x1                                                   ) }
from_impl! { SecretM32x4 (               CW SecretM8x16, CW SecretM16x8,                   CW SecretM64x2, CW SecretM128x1                                  ) }
from_impl! { SecretM64x4 (               CW SecretM8x32, CW SecretM16x16, CW SecretM32x8,                  CW SecretM128x2, CW SecretM256x1                 ) }
from_impl! { SecretM128x4(               CW SecretM8x64, CW SecretM16x32, CW SecretM32x16, CW SecretM64x8,                  CW SecretM256x2, CW SecretM512x1) }

from_impl! { SecretM8x8  (CW SecretU64,  CW SecretU8x8,  CW SecretU16x4,  CW SecretU32x2,  CW SecretU64x1                                                   ) }
from_impl! { SecretM16x8 (CW SecretU128, CW SecretU8x16, CW SecretU16x8,  CW SecretU32x4,  CW SecretU64x2, CW SecretU128x1                                  ) }
from_impl! { SecretM32x8 (CW SecretU256, CW SecretU8x32, CW SecretU16x16, CW SecretU32x8,  CW SecretU64x4, CW SecretU128x2, CW SecretU256x1                 ) }
from_impl! { SecretM64x8 (CW SecretU512, CW SecretU8x64, CW SecretU16x32, CW SecretU32x16, CW SecretU64x8, CW SecretU128x4, CW SecretU256x2, CW SecretU512x1) }

from_impl! { SecretM8x8  (CW SecretI64,  CW SecretI8x8,  CW SecretI16x4,  CW SecretI32x2,  CW SecretI64x1                                                   ) }
from_impl! { SecretM16x8 (CW SecretI128, CW SecretI8x16, CW SecretI16x8,  CW SecretI32x4,  CW SecretI64x2, CW SecretI128x1                                  ) }
from_impl! { SecretM32x8 (CW SecretI256, CW SecretI8x32, CW SecretI16x16, CW SecretI32x8,  CW SecretI64x4, CW SecretI128x2, CW SecretI256x1                 ) }
from_impl! { SecretM64x8 (CW SecretI512, CW SecretI8x64, CW SecretI16x32, CW SecretI32x16, CW SecretI64x8, CW SecretI128x4, CW SecretI256x2, CW SecretI512x1) }

from_impl! { SecretM8x8  (                               CW SecretM16x4,  CW SecretM32x2,  CW SecretM64x1                                                   ) }
from_impl! { SecretM16x8 (               CW SecretM8x16,                  CW SecretM32x4,  CW SecretM64x2, CW SecretM128x1                                  ) }
from_impl! { SecretM32x8 (               CW SecretM8x32, CW SecretM16x16,                  CW SecretM64x4, CW SecretM128x2, CW SecretM256x1                 ) }
from_impl! { SecretM64x8 (               CW SecretM8x64, CW SecretM16x32, CW SecretM32x16,                 CW SecretM128x4, CW SecretM256x2, CW SecretM512x1) }

from_impl! { SecretM8x16 (CW SecretU128, CW SecretU8x16, CW SecretU16x8,  CW SecretU32x4,  CW SecretU64x2, CW SecretU128x1                                  ) }
from_impl! { SecretM16x16(CW SecretU256, CW SecretU8x32, CW SecretU16x16, CW SecretU32x8,  CW SecretU64x4, CW SecretU128x2, CW SecretU256x1                 ) }
from_impl! { SecretM32x16(CW SecretU512, CW SecretU8x64, CW SecretU16x32, CW SecretU32x16, CW SecretU64x8, CW SecretU128x4, CW SecretU256x2, CW SecretU512x1) }

from_impl! { SecretM8x16 (CW SecretI128, CW SecretI8x16, CW SecretI16x8,  CW SecretI32x4,  CW SecretI64x2, CW SecretI128x1                                  ) }
from_impl! { SecretM16x16(CW SecretI256, CW SecretI8x32, CW SecretI16x16, CW SecretI32x8,  CW SecretI64x4, CW SecretI128x2, CW SecretI256x1                 ) }
from_impl! { SecretM32x16(CW SecretI512, CW SecretI8x64, CW SecretI16x32, CW SecretI32x16, CW SecretI64x8, CW SecretI128x4, CW SecretI256x2, CW SecretI512x1) }

from_impl! { SecretM8x16 (                               CW SecretM16x8,  CW SecretM32x4,  CW SecretM64x2, CW SecretM128x1                                  ) }
from_impl! { SecretM16x16(               CW SecretM8x32,                  CW SecretM32x8,  CW SecretM64x4, CW SecretM128x2, CW SecretM256x1                 ) }
from_impl! { SecretM32x16(               CW SecretM8x64, CW SecretM16x32,                  CW SecretM64x8, CW SecretM128x4, CW SecretM256x2, CW SecretM512x1) }

from_impl! { SecretM8x32 (CW SecretU256, CW SecretU8x32, CW SecretU16x16, CW SecretU32x8,  CW SecretU64x4, CW SecretU128x2, CW SecretU256x1                 ) }
from_impl! { SecretM16x32(CW SecretU512, CW SecretU8x64, CW SecretU16x32, CW SecretU32x16, CW SecretU64x8, CW SecretU128x4, CW SecretU256x2, CW SecretU512x1) }

from_impl! { SecretM8x32 (CW SecretI256, CW SecretI8x32, CW SecretI16x16, CW SecretI32x8,  CW SecretI64x4, CW SecretI128x2, CW SecretI256x1                 ) }
from_impl! { SecretM16x32(CW SecretI512, CW SecretI8x64, CW SecretI16x32, CW SecretI32x16, CW SecretI64x8, CW SecretI128x4, CW SecretI256x2, CW SecretI512x1) }

from_impl! { SecretM8x32 (                               CW SecretM16x16, CW SecretM32x8,  CW SecretM64x4, CW SecretM128x2, CW SecretM256x1                 ) }
from_impl! { SecretM16x32(               CW SecretM8x64,                  CW SecretM32x16, CW SecretM64x8, CW SecretM128x4, CW SecretM256x2, CW SecretM512x1) }

from_impl! { SecretM8x64 (CW SecretU512, CW SecretU8x64, CW SecretU16x32, CW SecretU32x16, CW SecretU64x8, CW SecretU128x4, CW SecretU256x2, CW SecretU512x1) }

from_impl! { SecretM8x64 (CW SecretI512, CW SecretI8x64, CW SecretI16x32, CW SecretI32x16, CW SecretI64x8, CW SecretI128x4, CW SecretI256x2, CW SecretI512x1) }

from_impl! { SecretM8x64 (                               CW SecretM16x32, CW SecretM32x16, CW SecretM64x8, CW SecretM128x4, CW SecretM256x2, CW SecretM512x1) }

// unsigned from unsigned
from_impl! { SecretU8x1  (                CX SecretU16x1,  CX SecretU32x1,  CX SecretU64x1,  CX SecretU128x1,  CX SecretU256x1,  CX SecretU512x1 ) }
from_impl! { SecretU16x1 (FV SecretU8x1,                   CX SecretU32x1,  CX SecretU64x1,  CX SecretU128x1,  CX SecretU256x1,  CX SecretU512x1 ) }
from_impl! { SecretU32x1 (FV SecretU8x1,  FV SecretU16x1,                   CX SecretU64x1,  CX SecretU128x1,  CX SecretU256x1,  CX SecretU512x1 ) }
from_impl! { SecretU64x1 (FV SecretU8x1,  FV SecretU16x1,  FV SecretU32x1,                   CX SecretU128x1,  CX SecretU256x1,  CX SecretU512x1 ) }
from_impl! { SecretU128x1(FV SecretU8x1,  FV SecretU16x1,  FV SecretU32x1,  FV SecretU64x1,                    CX SecretU256x1,  CX SecretU512x1 ) }
from_impl! { SecretU256x1(FV SecretU8x1,  FV SecretU16x1,  FV SecretU32x1,  FV SecretU64x1,  FV SecretU128x1,                    CX SecretU512x1 ) }
from_impl! { SecretU512x1(FV SecretU8x1,  FV SecretU16x1,  FV SecretU32x1,  FV SecretU64x1,  FV SecretU128x1,  FV SecretU256x1,                  ) }

from_impl! { SecretU8x2  (                CX SecretU16x2,  CX SecretU32x2,  CX SecretU64x2,  CX SecretU128x2,  CX SecretU256x2,                  ) }
from_impl! { SecretU16x2 (FV SecretU8x2,                   CX SecretU32x2,  CX SecretU64x2,  CX SecretU128x2,  CX SecretU256x2,                  ) }
from_impl! { SecretU32x2 (FV SecretU8x2,  FV SecretU16x2,                   CX SecretU64x2,  CX SecretU128x2,  CX SecretU256x2,                  ) }
from_impl! { SecretU64x2 (FV SecretU8x2,  FV SecretU16x2,  FV SecretU32x2,                   CX SecretU128x2,  CX SecretU256x2,                  ) }
from_impl! { SecretU128x2(FV SecretU8x2,  FV SecretU16x2,  FV SecretU32x2,  FV SecretU64x2,                    CX SecretU256x2,                  ) }
from_impl! { SecretU256x2(FV SecretU8x2,  FV SecretU16x2,  FV SecretU32x2,  FV SecretU64x2,  FV SecretU128x2,                                    ) }

from_impl! { SecretU8x4  (                CX SecretU16x4,  CX SecretU32x4,  CX SecretU64x4,  CX SecretU128x4,                                    ) }
from_impl! { SecretU16x4 (FV SecretU8x4,                   CX SecretU32x4,  CX SecretU64x4,  CX SecretU128x4,                                    ) }
from_impl! { SecretU32x4 (FV SecretU8x4,  FV SecretU16x4,                   CX SecretU64x4,  CX SecretU128x4,                                    ) }
from_impl! { SecretU64x4 (FV SecretU8x4,  FV SecretU16x4,  FV SecretU32x4,                   CX SecretU128x4,                                    ) }
from_impl! { SecretU128x4(FV SecretU8x4,  FV SecretU16x4,  FV SecretU32x4,  FV SecretU64x4,                                                      ) }

from_impl! { SecretU8x8  (                CX SecretU16x8,  CX SecretU32x8,  CX SecretU64x8,                                                      ) }
from_impl! { SecretU16x8 (FV SecretU8x8,                   CX SecretU32x8,  CX SecretU64x8,                                                      ) }
from_impl! { SecretU32x8 (FV SecretU8x8,  FV SecretU16x8,                   CX SecretU64x8,                                                      ) }
from_impl! { SecretU64x8 (FV SecretU8x8,  FV SecretU16x8,  FV SecretU32x8,                                                                       ) }

from_impl! { SecretU8x16 (                CX SecretU16x16, CX SecretU32x16,                                                                      ) }
from_impl! { SecretU16x16(FV SecretU8x16,                  CX SecretU32x16,                                                                      ) }
from_impl! { SecretU32x16(FV SecretU8x16, FV SecretU16x16,                                                                                       ) }

from_impl! { SecretU8x32 (                CX SecretU16x32,                                                                                       ) }
from_impl! { SecretU16x32(FV SecretU8x32,                                                                                                        ) }

from_impl! { SecretU8x64 (                                                                                                                       ) }

// signed from signed
from_impl! { SecretI8x1  (                CX SecretI16x1,  CX SecretI32x1,  CX SecretI64x1,  CX SecretI128x1,  CX SecretI256x1,  CX SecretI512x1 ) }
from_impl! { SecretI16x1 (FZ SecretI8x1,                   CX SecretI32x1,  CX SecretI64x1,  CX SecretI128x1,  CX SecretI256x1,  CX SecretI512x1 ) }
from_impl! { SecretI32x1 (FZ SecretI8x1,  FZ SecretI16x1,                   CX SecretI64x1,  CX SecretI128x1,  CX SecretI256x1,  CX SecretI512x1 ) }
from_impl! { SecretI64x1 (FZ SecretI8x1,  FZ SecretI16x1,  FZ SecretI32x1,                   CX SecretI128x1,  CX SecretI256x1,  CX SecretI512x1 ) }
from_impl! { SecretI128x1(FZ SecretI8x1,  FZ SecretI16x1,  FZ SecretI32x1,  FZ SecretI64x1,                    CX SecretI256x1,  CX SecretI512x1 ) }
from_impl! { SecretI256x1(FZ SecretI8x1,  FZ SecretI16x1,  FZ SecretI32x1,  FZ SecretI64x1,  FZ SecretI128x1,                    CX SecretI512x1 ) }
from_impl! { SecretI512x1(FZ SecretI8x1,  FZ SecretI16x1,  FZ SecretI32x1,  FZ SecretI64x1,  FZ SecretI128x1,  FZ SecretI256x1,                  ) }

from_impl! { SecretI8x2  (                CX SecretI16x2,  CX SecretI32x2,  CX SecretI64x2,  CX SecretI128x2,  CX SecretI256x2,                  ) }
from_impl! { SecretI16x2 (FZ SecretI8x2,                   CX SecretI32x2,  CX SecretI64x2,  CX SecretI128x2,  CX SecretI256x2,                  ) }
from_impl! { SecretI32x2 (FZ SecretI8x2,  FZ SecretI16x2,                   CX SecretI64x2,  CX SecretI128x2,  CX SecretI256x2,                  ) }
from_impl! { SecretI64x2 (FZ SecretI8x2,  FZ SecretI16x2,  FZ SecretI32x2,                   CX SecretI128x2,  CX SecretI256x2,                  ) }
from_impl! { SecretI128x2(FZ SecretI8x2,  FZ SecretI16x2,  FZ SecretI32x2,  FZ SecretI64x2,                    CX SecretI256x2,                  ) }
from_impl! { SecretI256x2(FZ SecretI8x2,  FZ SecretI16x2,  FZ SecretI32x2,  FZ SecretI64x2,  FZ SecretI128x2,                                    ) }

from_impl! { SecretI8x4  (                CX SecretI16x4,  CX SecretI32x4,  CX SecretI64x4,  CX SecretI128x4,                                    ) }
from_impl! { SecretI16x4 (FZ SecretI8x4,                   CX SecretI32x4,  CX SecretI64x4,  CX SecretI128x4,                                    ) }
from_impl! { SecretI32x4 (FZ SecretI8x4,  FZ SecretI16x4,                   CX SecretI64x4,  CX SecretI128x4,                                    ) }
from_impl! { SecretI64x4 (FZ SecretI8x4,  FZ SecretI16x4,  FZ SecretI32x4,                   CX SecretI128x4,                                    ) }
from_impl! { SecretI128x4(FZ SecretI8x4,  FZ SecretI16x4,  FZ SecretI32x4,  FZ SecretI64x4,                                                      ) }

from_impl! { SecretI8x8  (                CX SecretI16x8,  CX SecretI32x8,  CX SecretI64x8,                                                      ) }
from_impl! { SecretI16x8 (FZ SecretI8x8,                   CX SecretI32x8,  CX SecretI64x8,                                                      ) }
from_impl! { SecretI32x8 (FZ SecretI8x8,  FZ SecretI16x8,                   CX SecretI64x8,                                                      ) }
from_impl! { SecretI64x8 (FZ SecretI8x8,  FZ SecretI16x8,  FZ SecretI32x8,                                                                       ) }

from_impl! { SecretI8x16 (                CX SecretI16x16, CX SecretI32x16,                                                                      ) }
from_impl! { SecretI16x16(FZ SecretI8x16,                  CX SecretI32x16,                                                                      ) }
from_impl! { SecretI32x16(FZ SecretI8x16, FZ SecretI16x16,                                                                                       ) }

from_impl! { SecretI8x32 (                CX SecretI16x32,                                                                                       ) }
from_impl! { SecretI16x32(FZ SecretI8x32,                                                                                                        ) }

from_impl! { SecretI8x64 (                                                                                                                       ) }

// masks from masks
from_impl! { SecretM8x1  (                CX SecretM16x1,  CX SecretM32x1,  CX SecretM64x1,  CX SecretM128x1,  CX SecretM256x1,  CX SecretM512x1 ) }
from_impl! { SecretM16x1 (FZ SecretM8x1,                   CX SecretM32x1,  CX SecretM64x1,  CX SecretM128x1,  CX SecretM256x1,  CX SecretM512x1 ) }
from_impl! { SecretM32x1 (FZ SecretM8x1,  FZ SecretM16x1,                   CX SecretM64x1,  CX SecretM128x1,  CX SecretM256x1,  CX SecretM512x1 ) }
from_impl! { SecretM64x1 (FZ SecretM8x1,  FZ SecretM16x1,  FZ SecretM32x1,                   CX SecretM128x1,  CX SecretM256x1,  CX SecretM512x1 ) }
from_impl! { SecretM128x1(FZ SecretM8x1,  FZ SecretM16x1,  FZ SecretM32x1,  FZ SecretM64x1,                    CX SecretM256x1,  CX SecretM512x1 ) }
from_impl! { SecretM256x1(FZ SecretM8x1,  FZ SecretM16x1,  FZ SecretM32x1,  FZ SecretM64x1,  FZ SecretM128x1,                    CX SecretM512x1 ) }
from_impl! { SecretM512x1(FZ SecretM8x1,  FZ SecretM16x1,  FZ SecretM32x1,  FZ SecretM64x1,  FZ SecretM128x1,  FZ SecretM256x1,                  ) }

from_impl! { SecretM8x2  (                CX SecretM16x2,  CX SecretM32x2,  CX SecretM64x2,  CX SecretM128x2,  CX SecretM256x2,                  ) }
from_impl! { SecretM16x2 (FZ SecretM8x2,                   CX SecretM32x2,  CX SecretM64x2,  CX SecretM128x2,  CX SecretM256x2,                  ) }
from_impl! { SecretM32x2 (FZ SecretM8x2,  FZ SecretM16x2,                   CX SecretM64x2,  CX SecretM128x2,  CX SecretM256x2,                  ) }
from_impl! { SecretM64x2 (FZ SecretM8x2,  FZ SecretM16x2,  FZ SecretM32x2,                   CX SecretM128x2,  CX SecretM256x2,                  ) }
from_impl! { SecretM128x2(FZ SecretM8x2,  FZ SecretM16x2,  FZ SecretM32x2,  FZ SecretM64x2,                    CX SecretM256x2,                  ) }
from_impl! { SecretM256x2(FZ SecretM8x2,  FZ SecretM16x2,  FZ SecretM32x2,  FZ SecretM64x2,  FZ SecretM128x2,                                    ) }

from_impl! { SecretM8x4  (                CX SecretM16x4,  CX SecretM32x4,  CX SecretM64x4,  CX SecretM128x4,                                    ) }
from_impl! { SecretM16x4 (FZ SecretM8x4,                   CX SecretM32x4,  CX SecretM64x4,  CX SecretM128x4,                                    ) }
from_impl! { SecretM32x4 (FZ SecretM8x4,  FZ SecretM16x4,                   CX SecretM64x4,  CX SecretM128x4,                                    ) }
from_impl! { SecretM64x4 (FZ SecretM8x4,  FZ SecretM16x4,  FZ SecretM32x4,                   CX SecretM128x4,                                    ) }
from_impl! { SecretM128x4(FZ SecretM8x4,  FZ SecretM16x4,  FZ SecretM32x4,  FZ SecretM64x4,                                                      ) }

from_impl! { SecretM8x8  (                CX SecretM16x8,  CX SecretM32x8,  CX SecretM64x8,                                                      ) }
from_impl! { SecretM16x8 (FZ SecretM8x8,                   CX SecretM32x8,  CX SecretM64x8,                                                      ) }
from_impl! { SecretM32x8 (FZ SecretM8x8,  FZ SecretM16x8,                   CX SecretM64x8,                                                      ) }
from_impl! { SecretM64x8 (FZ SecretM8x8,  FZ SecretM16x8,  FZ SecretM32x8,                                                                       ) }

from_impl! { SecretM8x16 (                CX SecretM16x16, CX SecretM32x16,                                                                      ) }
from_impl! { SecretM16x16(FZ SecretM8x16,                  CX SecretM32x16,                                                                      ) }
from_impl! { SecretM32x16(FZ SecretM8x16, FZ SecretM16x16,                                                                                       ) }

from_impl! { SecretM8x32 (                CX SecretM16x32,                                                                                       ) }
from_impl! { SecretM16x32(FZ SecretM8x32,                                                                                                        ) }

from_impl! { SecretM8x64 (                                                                                                                       ) }

// signed from unsigned
from_impl! { SecretI8x1  (                                                                                                                       ) }
from_impl! { SecretI16x1 (FV SecretU8x1,                                                                                                         ) }
from_impl! { SecretI32x1 (FV SecretU8x1,  FV SecretU16x1,                                                                                        ) }
from_impl! { SecretI64x1 (FV SecretU8x1,  FV SecretU16x1,  FV SecretU32x1,                                                                       ) }
from_impl! { SecretI128x1(FV SecretU8x1,  FV SecretU16x1,  FV SecretU32x1,  FV SecretU64x1,                                                      ) }
from_impl! { SecretI256x1(FV SecretU8x1,  FV SecretU16x1,  FV SecretU32x1,  FV SecretU64x1,  FV SecretU128x1,                                    ) }
from_impl! { SecretI512x1(FV SecretU8x1,  FV SecretU16x1,  FV SecretU32x1,  FV SecretU64x1,  FV SecretU128x1,  FV SecretU256x1,                  ) }

from_impl! { SecretI8x2  (                                                                                                                       ) }
from_impl! { SecretI16x2 (FV SecretU8x2,                                                                                                         ) }
from_impl! { SecretI32x2 (FV SecretU8x2,  FV SecretU16x2,                                                                                        ) }
from_impl! { SecretI64x2 (FV SecretU8x2,  FV SecretU16x2,  FV SecretU32x2,                                                                       ) }
from_impl! { SecretI128x2(FV SecretU8x2,  FV SecretU16x2,  FV SecretU32x2,  FV SecretU64x2,                                                      ) }
from_impl! { SecretI256x2(FV SecretU8x2,  FV SecretU16x2,  FV SecretU32x2,  FV SecretU64x2,  FV SecretU128x2,                                    ) }

from_impl! { SecretI8x4  (                                                                                                                       ) }
from_impl! { SecretI16x4 (FV SecretU8x4,                                                                                                         ) }
from_impl! { SecretI32x4 (FV SecretU8x4,  FV SecretU16x4,                                                                                        ) }
from_impl! { SecretI64x4 (FV SecretU8x4,  FV SecretU16x4,  FV SecretU32x4,                                                                       ) }
from_impl! { SecretI128x4(FV SecretU8x4,  FV SecretU16x4,  FV SecretU32x4,  FV SecretU64x4,                                                      ) }

from_impl! { SecretI8x8  (                                                                                                                       ) }
from_impl! { SecretI16x8 (FV SecretU8x8,                                                                                                         ) }
from_impl! { SecretI32x8 (FV SecretU8x8,  FV SecretU16x8,                                                                                        ) }
from_impl! { SecretI64x8 (FV SecretU8x8,  FV SecretU16x8,  FV SecretU32x8,                                                                       ) }

from_impl! { SecretI8x16 (                                                                                                                       ) }
from_impl! { SecretI16x16(FV SecretU8x16,                                                                                                        ) }
from_impl! { SecretI32x16(FV SecretU8x16, FV SecretU16x16,                                                                                       ) }

from_impl! { SecretI8x32 (                                                                                                                       ) }
from_impl! { SecretI16x32(FV SecretU8x32,                                                                                                        ) }

from_impl! { SecretI8x64 (                                                                                                                       ) }



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
        x.tree().disas(io::stdout()).unwrap();
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
        x.tree().disas(io::stdout()).unwrap();
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

        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, false);

        let x = (!a.clone().gt(b.clone())).select(a, b);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, 10);
    }

    #[test]
    fn int_abs() {
        println!();
        let a = SecretI32::new(-100);
        let x = a.abs();
        x.tree().disas(io::stdout()).unwrap();
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
        x.tree().disas(io::stdout()).unwrap();
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
        x.tree().disas(io::stdout()).unwrap();
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
            x.tree().disas(io::stdout()).unwrap();
            let v = x.declassify();
            println!("{}", v);
            assert_eq!(v, b < c);

            let x = sa.clamp(sb, sc);
            x.tree().disas(io::stdout()).unwrap();
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
            x.tree().disas(io::stdout()).unwrap();
            let v = x.declassify();
            println!("{}", v);
            assert_eq!(v, n.leading_zeros());

            let x = a.clone().is_power_of_two();
            x.tree().disas(io::stdout()).unwrap();
            let v = x.declassify();
            println!("{}", v);
            assert_eq!(v, n.is_power_of_two());

            let x = a.next_power_of_two();
            x.tree().disas(io::stdout()).unwrap();
            let v = x.declassify();
            println!("{}", v);
            assert_eq!(v, n.next_power_of_two());
        }

        test_clz(0);
        test_clz(1);
        test_clz(2);
        test_clz(3);
    }

    #[test]
    fn int_reduce() {
        println!();

        let a = SecretU8x64::new_lanes(
            0,   1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15,
            16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
            32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
            48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63);
        let x = a.horizontal_max();
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, 63);

        let a = SecretU32x16::new_lanes(
            0,   1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15);
        let x = a.horizontal_sum();
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, 120);
    }

    #[test]
    fn int_lane_casts() {
        println!();

        let a = SecretU32x16::new_lanes(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
        let x = SecretU8x16::cast(a);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_vec();
        println!("{:?}", v);
        assert_eq!(v, vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]);

        let a = SecretU256x2::from_lanes(
            SecretU256::from(SecretU16::new(1000)),
            SecretU256::from(SecretU16::new(2000))
        );
        let x = SecretU16x2::cast(a);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_lanes();
        println!("{:?}", v);
        assert_eq!(v, (1000, 2000));

        let a = SecretU8x16::new_lanes(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
        let x = SecretU32x16::from(a);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_vec();
        println!("{:?}", v);
        assert_eq!(v, vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]);

        let a = SecretU16x2::new_lanes(1000, 2000);
        let b = SecretU256x2::from(a);
        let x = SecretU32x2::cast(b);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_lanes();
        println!("{:?}", v);
        assert_eq!(v, (1000, 2000));

        let a = SecretI32x16::new_lanes(-1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16);
        let x = SecretI8x16::cast(a);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_vec();
        println!("{:?}", v);
        assert_eq!(v, vec![-1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16]);

        let a = SecretI256x2::from_lanes(
            SecretI256::from(SecretI16::new(-1000)),
            SecretI256::from(SecretI16::new(-2000))
        );
        let x = SecretI16x2::cast(a);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_lanes();
        println!("{:?}", v);
        assert_eq!(v, (-1000, -2000));

        let a = SecretI8x16::new_lanes(-1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16);
        let x = SecretI32x16::from(a);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_vec();
        println!("{:?}", v);
        assert_eq!(v, vec![-1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16]);

        let a = SecretI16x2::new_lanes(-1000, -2000);
        let b = SecretI256x2::from(a);
        let x = SecretI32x2::cast(b);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_lanes();
        println!("{:?}", v);
        assert_eq!(v, (-1000, -2000));
    }
}


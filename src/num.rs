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

use secret_u_macros::for_secret_t;
use secret_u_macros::for_secret_t_2;


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

    /// A constant, non-secret false
    pub fn false_() -> Self {
        Self::from_tree(OpTree::zero())
    }

    /// A constant, non-secret true
    pub fn true_() -> Self {
        Self::from_tree(OpTree::ones())
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

for_secret_t! {
    __if(__t == "u" || __t == "i") {
        /// A secret integer who's value is ensured to not be leaked by Rust's type-system
        ///
        /// Note, like the underlying Rc type, clone is relatively cheap, but
        /// not a bytewise copy, which means we can't implement the Copy trait
        #[derive(Clone)]
        pub struct __secret_t(OpTree<__U>);

        __if(__has_prim) {
            impl From<__prim_t> for __secret_t {
                fn from(v: __prim_t) -> __secret_t {
                    Self::classify(v)
                }
            }
        }

        impl Default for __secret_t {
            fn default() -> Self {
                Self::zero()
            }
        }

        impl __secret_t {
            pub const SIZE: usize = __size;

            /// Wraps a non-secret value as a secret value
            pub fn classify_le_bytes(v: [u8; __size]) -> Self {
                Self(OpTree::imm(v))
            }

            /// Extracts the secret value into a non-secret value, this
            /// effectively "leaks" the secret value, but is necessary
            /// to actually do anything
            pub fn declassify_le_bytes(&self) -> [u8; __size] {
                self.try_declassify_le_bytes().unwrap()
            }

            /// Same as declassify but propagating internal VM errors
            pub fn try_declassify_le_bytes(&self) -> Result<[u8; __size], Error> {
                Ok(self.try_eval()?.0.result())
            }

            /// Wraps a non-secret value as a secret value
            pub fn from_le_bytes(v: [u8; __size]) -> Self {
                Self::classify_le_bytes(v)
            }

            /// Create a non-secret constant value, these are available
            /// for more optimizations than secret values
            pub fn const_le_bytes(v: [u8; __size]) -> Self {
                Self(OpTree::const_(v))
            }

            __if(__has_prim) {
                /// Wraps a non-secret value as a secret value
                pub fn classify(v: __prim_t) -> Self {
                    Self(OpTree::imm(v.to_le_bytes()))
                }

                /// Extracts the secret value into a non-secret value, this
                /// effectively "leaks" the secret value, but is necessary
                /// to actually do anything
                pub fn declassify(&self) -> __prim_t {
                    self.try_declassify().unwrap()
                }

                /// Same as declassify but propagating internal VM errors
                pub fn try_declassify(&self) -> Result<__prim_t, Error> {
                    Ok(self.try_eval()?.0.result())
                }

                /// Wraps a non-secret value as a secret value
                pub fn new(v: __prim_t) -> Self {
                    Self::classify(v)
                }

                /// Create a non-secret constant value, these are available
                /// for more optimizations than secret values
                pub fn const_(v: __prim_t) -> Self {
                    Self::const_le_bytes(v.to_le_bytes())
                }
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

            // abs only available on signed types
            __if(__t == "i") {
                pub fn abs(self) -> Self {
                    Self(OpTree::abs(0, self.0))
                }
            }

            // other non-trait operations
            pub fn trailing_zeros(self) -> __secret_t {
                Self(OpTree::ctz(0, self.0))
            }

            pub fn trailing_ones(self) -> __secret_t {
                (!self).trailing_zeros()
            }

            pub fn leading_zeros(self) -> __secret_t {
                Self(OpTree::clz(0, self.0))
            }

            pub fn leading_ones(self) -> __secret_t {
                (!self).leading_zeros()
            }

            pub fn count_zeros(self) -> __secret_t {
                (!self).count_ones()
            }

            pub fn count_ones(self) -> __secret_t {
                Self(OpTree::popcnt(0, self.0))
            }

            // ipw2/npw2 only available on unsigned types
            __if(__t == "u") {
                pub fn is_power_of_two(self) -> SecretBool {
                    self.count_ones().eq(Self::one())
                }

                pub fn next_power_of_two(self) -> __secret_t {
                    // based on implementation in rust core
                    self.clone().le(Self::one()).select(
                        // special case if <= 1
                        Self::zero(),
                        // next_power_of_two_minus_1
                        Self::ones() >> (self - Self::one()).leading_zeros()
                    ) + Self::one()
                }
            }

            pub fn rotate_left(self, other: __secret_t) -> __secret_t {
                Self(OpTree::rotl(0, self.0, other.0))
            }

            pub fn rotate_right(self, other: __secret_t) -> __secret_t {
                Self(OpTree::rotr(0, self.0, other.0))
            }

            pub fn reverse_bits(mut self) -> __secret_t {
                // reverse bytes
                if __size > 1 {
                    self = self.reverse_bytes();
                }

                // reverse bits in bytes
                let mut mask = 0xffu8;
                for sh in [4,2,1] {
                    mask ^= mask << sh;
                    let sh_s = Self::from_cast(SecretU8::const_(sh));
                    let mask_s = Self::const_le_bytes([mask; __size]);
                    // fall back to OpTree to avoid signed-bitshifts
                    self = Self(OpTree::or(
                        OpTree::and(
                            OpTree::shr_u(0, self.0.clone(), sh_s.0.clone()),
                            mask_s.0.clone(),
                        ),
                        OpTree::andnot(
                            OpTree::shl(0, self.0, sh_s.0),
                            mask_s.0
                        )
                    ));
                }

                self
            }

            pub fn reverse_bytes(self) -> __secret_t {
                let mut bytes = [0xff; __size];
                for i in 0..__size {
                    // this works because i can be at most 64, < u8
                    bytes[i] = u8::try_from(__size-1 - i).unwrap();
                }

                Self(OpTree::shuffle(
                    __npw2,
                    OpTree::const_(bytes),
                    self.0.clone(),
                    self.0
                ))
            }
        }

        impl Eval for __secret_t {
            fn try_eval(&self) -> Result<Self, Error> {
                Ok(Self::from_tree(self.tree().try_eval()?))
            }
        }

        impl Tree for __secret_t {
            type Tree = OpTree<__U>;

            fn from_tree(tree: OpTree<__U>) -> Self {
                Self(tree)
            }

            fn tree<'a>(&'a self) -> Cow<'a, OpTree<__U>> {
                Cow::Borrowed(&self.0)
            }
        }

        impl Not for __secret_t {
            type Output = __secret_t;
            fn not(self) -> __secret_t {
                Self(OpTree::not(self.0))
            }
        }

        impl BitAnd for __secret_t {
            type Output = __secret_t;
            fn bitand(self, other: __secret_t) -> __secret_t {
                Self(OpTree::and(self.0, other.0))
            }
        }

        impl BitAndAssign for __secret_t {
            fn bitand_assign(&mut self, other: __secret_t) {
                *self = self.clone().bitand(other)
            }
        }

        impl BitOr for __secret_t {
            type Output = __secret_t;
            fn bitor(self, other: __secret_t) -> __secret_t {
                Self(OpTree::or(self.0, other.0))
            }
        }

        impl BitOrAssign for __secret_t {
            fn bitor_assign(&mut self, other: __secret_t) {
                *self = self.clone().bitor(other)
            }
        }

        impl BitXor for __secret_t {
            type Output = __secret_t;
            fn bitxor(self, other: __secret_t) -> __secret_t {
                Self(OpTree::xor(self.0, other.0))
            }
        }

        impl BitXorAssign for __secret_t {
            fn bitxor_assign(&mut self, other: __secret_t) {
                *self = self.clone().bitxor(other)
            }
        }

        // negate only available for signed types
        __if(__t == "i") {
            impl Neg for __secret_t {
                type Output = __secret_t;
                fn neg(self) -> __secret_t {
                    Self(OpTree::neg(0, self.0))
                }
            }
        }

        impl Add for __secret_t {
            type Output = __secret_t;
            fn add(self, other: __secret_t) -> __secret_t {
                Self(OpTree::add(0, self.0, other.0))
            }
        }

        impl AddAssign for __secret_t {
            fn add_assign(&mut self, other: __secret_t) {
                *self = self.clone().add(other)
            }
        }

        impl Sub for __secret_t {
            type Output = __secret_t;
            fn sub(self, other: __secret_t) -> __secret_t {
                Self(OpTree::sub(0, self.0, other.0))
            }
        }

        impl SubAssign for __secret_t {
            fn sub_assign(&mut self, other: __secret_t) {
                *self = self.clone().sub(other)
            }
        }

        impl Mul for __secret_t {
            type Output = __secret_t;
            fn mul(self, other: __secret_t) -> __secret_t {
                Self(OpTree::mul(0, self.0, other.0))
            }
        }

        impl MulAssign for __secret_t {
            fn mul_assign(&mut self, other: __secret_t) {
                *self = self.clone().mul(other)
            }
        }

        impl Shl for __secret_t {
            type Output = __secret_t;
            fn shl(self, other: __secret_t) -> __secret_t {
                Self(OpTree::shl(0, self.0, other.0))
            }
        }

        impl ShlAssign for __secret_t {
            fn shl_assign(&mut self, other: __secret_t) {
                *self = self.clone().shl(other)
            }
        }

        impl Shr for __secret_t {
            type Output = __secret_t;
            fn shr(self, other: __secret_t) -> __secret_t {
                __if(__t == "u") {
                    Self(OpTree::shr_u(0, self.0, other.0))
                }
                __if(__t == "i") {
                    Self(OpTree::shr_s(0, self.0, other.0))
                }
            }
        }

        impl ShrAssign for __secret_t {
            fn shr_assign(&mut self, other: __secret_t) {
                *self = self.clone().shr(other)
            }
        }

        impl Eq for __secret_t {
            type Output = SecretBool;

            fn eq(self, other: Self) -> SecretBool {
                SecretBool::defer(Rc::new(OpTree::eq(0, self.0, other.0)))
            }

            fn ne(self, other: Self) -> SecretBool {
                SecretBool::defer(Rc::new(OpTree::ne(0, self.0, other.0)))
            }
        }

        impl Ord for __secret_t {
            type Output = SecretBool;

            __if(__t == "u") {
                fn lt(self, other: Self) -> SecretBool {
                    SecretBool::defer(Rc::new(OpTree::lt_u(0, self.0, other.0)))
                }

                fn le(self, other: Self) -> SecretBool {
                    SecretBool::defer(Rc::new(OpTree::le_u(0, self.0, other.0)))
                }

                fn gt(self, other: Self) -> SecretBool {
                    SecretBool::defer(Rc::new(OpTree::gt_u(0, self.0, other.0)))
                }

                fn ge(self, other: Self) -> SecretBool {
                    SecretBool::defer(Rc::new(OpTree::ge_u(0, self.0, other.0)))
                }

                fn min(self, other: Self) -> Self {
                    Self(OpTree::min_u(0, self.0, other.0))
                }

                fn max(self, other: Self) -> Self {
                    Self(OpTree::max_u(0, self.0, other.0))
                }
            }
            __if(__t == "i") {
                fn lt(self, other: Self) -> SecretBool {
                    SecretBool::defer(Rc::new(OpTree::lt_s(0, self.0, other.0)))
                }

                fn le(self, other: Self) -> SecretBool {
                    SecretBool::defer(Rc::new(OpTree::le_s(0, self.0, other.0)))
                }

                fn gt(self, other: Self) -> SecretBool {
                    SecretBool::defer(Rc::new(OpTree::gt_s(0, self.0, other.0)))
                }

                fn ge(self, other: Self) -> SecretBool {
                    SecretBool::defer(Rc::new(OpTree::ge_s(0, self.0, other.0)))
                }

                fn min(self, other: Self) -> Self {
                    Self(OpTree::min_s(0, self.0, other.0))
                }

                fn max(self, other: Self) -> Self {
                    Self(OpTree::max_s(0, self.0, other.0))
                }
            }
        }

        impl Select<SecretBool> for __secret_t {
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


//// SecretM**x** ////

for_secret_t! {
    __if(__t == "mx") {
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
        pub struct __secret_t(OpTree<__U>);

        impl Default for __secret_t {
            fn default() -> Self {
                Self::const_splat(false)
            }
        }

        impl __secret_t {
            pub const SIZE: usize = __size;
            pub const LANES: usize = __lanes;

            /// Wraps a non-secret value as a secret value
            pub fn classify_lanes(__for_lanes { __a: bool, }) -> Self {
                let mut bytes = [0; __size];
                __for_lanes {
                    bytes[__i*size_of::<bool>() .. (__i+1)*size_of::<bool>()]
                        .copy_from_slice(
                            &if __a { <__lane_U>::ones() } else { <__lane_U>::zero() }.to_le_bytes()
                        );
                }
                Self(OpTree::imm(bytes))
            }

            /// Extracts the secret value into a non-secret value, this
            /// effectively "leaks" the secret value, but is necessary
            /// to actually do anything
            pub fn declassify_lanes(&self) -> (__for_lanes { bool, }) {
                self.try_declassify_lanes().unwrap()
            }

            /// Same as declassify but propagating internal VM errors
            pub fn try_declassify_lanes(&self) -> Result<(__for_lanes { bool, }), Error> {
                let bytes: [u8; __size] = self.try_eval()?.0.result();
                Ok((__for_lanes {
                    !<__lane_U>::from_le_bytes(
                        <_>::try_from(
                            &bytes[__i*size_of::<bool>() .. (__i+1)*size_of::<bool>()]
                        ).unwrap()
                    ).is_zero(),
                }))
            }

            /// Wraps a non-secret value as a secret value
            pub fn new_lanes(__for_lanes { __a: bool, }) -> Self {
                Self::classify_lanes(__for_lanes { __a, })
            }

            /// Wraps a non-secret value as a secret value
            pub fn const_lanes(__for_lanes { __a: bool, }) -> Self {
                let mut bytes = [0; __size];
                __for_lanes {
                    bytes[__i*size_of::<bool>() .. (__i+1)*size_of::<bool>()]
                        .copy_from_slice(
                            &if __a { <__lane_U>::ones() } else { <__lane_U>::zero() }.to_le_bytes()
                        );
                }
                Self(OpTree::const_(bytes))
            }

            /// Wraps a non-secret value as a secret value
            pub fn classify_slice(slice: &[bool]) -> Self {
                Self::try_classify_slice(slice).unwrap()
            }

            /// Wraps a non-secret value as a secret value
            pub fn try_classify_slice(slice: &[bool]) -> Option<Self> {
                if slice.len() == __lanes {
                    let mut bytes = [0; __size];
                    __for_lanes{
                        bytes[__i*size_of::<bool>() .. (__i+1)*size_of::<bool>()]
                            .copy_from_slice(
                                &if slice[__i] { <__lane_U>::ones() } else { <__lane_U>::zero() }.to_le_bytes()
                            );
                    }
                    Some(Self(OpTree::imm(bytes)))
                } else {
                    None
                }
            }

            /// Extracts the secret value into a non-secret value, this
            /// effectively "leaks" the secret value, but is necessary
            /// to actually do anything
            pub fn declassify_vec(&self) -> Vec<bool> {
                self.try_declassify_vec().unwrap()
            }

            /// Same as declassify but propagating internal VM errors
            pub fn try_declassify_vec(&self) -> Result<Vec<bool>, Error> {
                let bytes: [u8; __size] = self.try_eval()?.0.result();
                Ok(vec![__for_lanes {
                    !<__lane_U>::from_le_bytes(
                        <_>::try_from(
                            &bytes[__i*size_of::<bool>() .. (__i+1)*size_of::<bool>()]
                        ).unwrap()
                    ).is_zero(),
                }])
            }

            /// Wraps a non-secret value as a secret value
            pub fn new_slice(slice: &[bool]) -> Self {
                Self::classify_slice(slice)
            }

            /// Wraps a non-secret value as a secret value
            pub fn try_new_slice(slice: &[bool]) -> Option<Self> {
                Self::try_classify_slice(slice)
            }

            /// Wraps a non-secret value as a secret value
            pub fn const_slice(slice: &[bool]) -> Self {
                Self::try_const_slice(slice).unwrap()
            }

            /// Wraps a non-secret value as a secret value
            pub fn try_const_slice(slice: &[bool]) -> Option<Self> {
                if slice.len() == __lanes {
                    let mut bytes = [0; __size];
                    __for_lanes {
                        bytes[__i*size_of::<bool>() .. (__i+1)*size_of::<bool>()]
                            .copy_from_slice(
                                &if slice[__i] { <__lane_U>::ones() } else { <__lane_U>::zero() }.to_le_bytes()
                            );
                    }
                    Some(Self(OpTree::const_(bytes)))
                } else {
                    None
                }
            }

            /// Wraps a non-secret value as a secret value
            pub fn new_splat(v: bool) -> Self {
                Self(OpTree::imm(<__U>::splat(if v { <__U>::ones() } else { <__U>::zero() })))
            }

            /// Create a non-secret constant value, these are available
            /// for more optimizations than secret values
            pub fn const_splat(v: bool) -> Self {
                Self(OpTree::const_(<__U>::splat(if v { <__U>::ones() } else { <__U>::zero() })))
            }

            /// Build from lanes
            pub fn from_lanes(__for_lanes { __a: SecretBool, }) -> Self {
                __for_lanes {
                    __if(__i == 0) {
                        let x = Self(__a.resolve().into_owned());
                    }
                    __if(__i > 0) {
                        let x = x.replace(__i, __a);
                    } 
                }

                x
            }

            /// Extract all lanes
            pub fn to_lanes(self) -> (__for_lanes { SecretBool, }) {
                (__for_lanes { self.clone().extract(__i), })
            }

            /// Build from lanes, panicking if the slice length does not match
            pub fn from_slice(slice: &[SecretBool]) -> Self {
                Self::try_from_slice(slice).unwrap()
            }

            /// Build from lanes, returning None if the slice length does not match
            pub fn try_from_slice(slice: &[SecretBool]) -> Option<Self> {
                if slice.len() == __lanes {
                    __for_lanes {
                        __if(__i == 0) {
                            let x = Self(slice[__i].clone().resolve().into_owned());
                        }
                        __if(__i > 0) {
                            let x = x.replace(__i, slice[__i].clone());
                        } 
                    }
                    Some(x)
                } else {
                    None
                }
            }

            /// Extract all lanes
            pub fn to_vec(self) -> Vec<SecretBool> {
                vec![__for_lanes {
                    self.clone().extract(__i),
                }]
            }

            /// Splat a given value to all lanes
            pub fn splat(value: SecretBool) -> Self {
                Self(OpTree::splat(value.resolve::<__lane_U>().into_owned()))
            }

            /// Extract a specific lane
            pub fn extract(self, lane: usize) -> SecretBool {
                assert!(lane < __lanes);
                SecretBool::defer(Rc::new(OpTree::<__lane_U>::extract(
                    u16::try_from(lane).unwrap(), self.0
                )))
            }

            /// Replace a specific lane
            pub fn replace(self, lane: usize, value: SecretBool) -> Self {
                assert!(lane < __lanes);
                Self(OpTree::replace::<__lane_U>(
                    u16::try_from(lane).unwrap(), self.0, value.resolve().into_owned()
                ))
            }

            /// Reverse lanes
            pub fn reverse_lanes(self) -> Self {
                let mut lanes = [0xff; __size];
                for i in 0..__lanes {
                    // this works because i can be at most 64, < u8
                    let off = i*__lane_size;
                    lanes[off] = u8::try_from(__lanes-1 - i).unwrap();
                    lanes[off + 1 .. off + __lane_size]
                        .fill(0x00);
                }

                <__secret_ux>::const_le_bytes(lanes).shuffle(self.clone(), self)
            }

            /// A constant, non-secret false in each lane
            pub fn false_() -> Self {
                Self(OpTree::zero())
            }

            /// A constant, non-secret true in each lane
            pub fn true_() -> Self {
                Self(OpTree::ones())
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
                SecretBool::defer(Rc::new(OpTree::all(__lnpw2, self.0)))
            }

            /// Select operation for constant-time conditionals
            pub fn select<T>(self, a: T, b: T) -> T
            where
                T: Select<__secret_t>
            {
                T::select(self, a, b)
            }
        }

        impl Eval for __secret_t {
            fn try_eval(&self) -> Result<Self, Error> {
                Ok(Self::from_tree(self.tree().try_eval()?))
            }
        }

        impl Tree for __secret_t {
            type Tree = OpTree<__U>;

            fn from_tree(tree: OpTree<__U>) -> Self {
                Self(tree)
            }

            fn tree<'a>(&'a self) -> Cow<'a, OpTree<__U>> {
                Cow::Borrowed(&self.0)
            }
        }

        impl Not for __secret_t {
            type Output = __secret_t;
            fn not(self) -> __secret_t {
                Self(OpTree::not(self.0))
            }
        }

        impl BitAnd for __secret_t {
            type Output = __secret_t;
            fn bitand(self, other: __secret_t) -> __secret_t {
                Self(OpTree::and(self.0, other.0))
            }
        }

        impl BitAndAssign for __secret_t {
            fn bitand_assign(&mut self, other: __secret_t) {
                *self = self.clone().bitand(other)
            }
        }

        impl BitOr for __secret_t {
            type Output = __secret_t;
            fn bitor(self, other: __secret_t) -> __secret_t {
                Self(OpTree::or(self.0, other.0))
            }
        }

        impl BitOrAssign for __secret_t {
            fn bitor_assign(&mut self, other: __secret_t) {
                *self = self.clone().bitor(other)
            }
        }

        impl BitXor for __secret_t {
            type Output = __secret_t;
            fn bitxor(self, other: __secret_t) -> __secret_t {
                Self(OpTree::xor(self.0, other.0))
            }
        }

        impl BitXorAssign for __secret_t {
            fn bitxor_assign(&mut self, other: __secret_t) {
                *self = self.clone().bitxor(other)
            }
        }

        impl Eq for __secret_t {
            type Output = __secret_t;

            fn eq(self, other: Self) -> __secret_t {
                !(self ^ other)
            }

            fn ne(self, other: Self) -> __secret_t {
                self ^ other
            }
        }

        impl Ord for __secret_t {
            type Output = __secret_t;

            fn lt(self, other: Self) -> __secret_t {
                !self & other
            }

            fn le(self, other: Self) -> __secret_t {
                !self | other
            }

            fn gt(self, other: Self) -> __secret_t {
                self & !other
            }

            fn ge(self, other: Self) -> __secret_t {
                self | !other
            }

            fn min(self, other: Self) -> Self {
                self & other
            }

            fn max(self, other: Self) -> Self {
                self | other
            }
        }

        impl Select<__secret_t> for __secret_t {
            fn select(p: __secret_t, a: Self, b: Self) -> Self {
                Self(OpTree::select(__lnpw2, p.0, a.0, b.0))
            }
        }

        impl Shuffle<__secret_ux> for __secret_t {
            fn shuffle(p: __secret_ux, a: Self, b: Self) -> Self {
                Self(OpTree::shuffle(__lnpw2,
                    p.0,
                    a.0,
                    b.0,
                ))
            }
        }

        impl Shuffle<__secret_ix> for __secret_t {
            fn shuffle(p: __secret_ix, a: Self, b: Self) -> Self {
                Self(OpTree::shuffle(__lnpw2,
                    p.0,
                    a.0,
                    b.0,
                ))
            }
        }
    }
}


//// SecretU**x**/SecretI**x** ////

for_secret_t! {
    __if(__t == "ux" || __t == "ix") {
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
        pub struct __secret_t(OpTree<__U>);

        impl Default for __secret_t {
            fn default() -> Self {
                Self::zero()
            }
        }

        impl __secret_t {
            pub const SIZE: usize = __size;
            pub const LANES: usize = __lanes;

            /// Wraps a non-secret value as a secret value
            pub fn classify_le_bytes(v: [u8; __size]) -> Self {
                Self(OpTree::imm(v))
            }

            /// Extracts the secret value into a non-secret value, this
            /// effectively "leaks" the secret value, but is necessary
            /// to actually do anything
            pub fn declassify_le_bytes(&self) -> [u8; __size] {
                self.try_declassify_le_bytes().unwrap()
            }

            /// Same as declassify but propagating internal VM errors
            pub fn try_declassify_le_bytes(&self) -> Result<[u8; __size], Error> {
                Ok(self.try_eval()?.0.result())
            }

            /// Wraps a non-secret value as a secret value
            pub fn from_le_bytes(v: [u8; __size]) -> Self {
                Self::classify_le_bytes(v)
            }

            /// Create a non-secret constant value, these are available
            /// for more optimizations than secret values
            pub fn const_le_bytes(v: [u8; __size]) -> Self {
                Self(OpTree::const_(v))
            }

            __if(__has_prim) {
                /// Wraps a non-secret value as a secret value
                pub fn classify_lanes(__for_lanes {__a: __prim_t,}) -> Self {
                    let mut bytes = [0; __size];
                    __for_lanes {
                        bytes[__i*size_of::<__prim_t>() .. (__i+1)*size_of::<__prim_t>()]
                            .copy_from_slice(&<__lane_U>::from(__a).to_le_bytes());
                    }
                    Self(OpTree::imm(bytes))
                }

                /// Extracts the secret value into a non-secret value, this
                /// effectively "leaks" the secret value, but is necessary
                /// to actually do anything
                pub fn declassify_lanes(&self) -> (__for_lanes {__prim_t,}) {
                    self.try_declassify_lanes().unwrap()
                }

                /// Same as declassify but propagating internal VM errors
                pub fn try_declassify_lanes(&self) -> Result<(__for_lanes {__prim_t,}), Error> {
                    let bytes: [u8; __size] = self.try_eval()?.0.result();
                    Ok((__for_lanes {
                        <__prim_t>::from_le_bytes(
                            <_>::try_from(
                                &bytes[__i*size_of::<__prim_t>() .. (__i+1)*size_of::<__prim_t>()]
                            ).unwrap()
                        ),
                    }))
                }

                /// Wraps a non-secret value as a secret value
                pub fn new_lanes(__for_lanes {__a: __prim_t,}) -> Self {
                    Self::classify_lanes(__for_lanes {__a,})
                }

                /// Wraps a non-secret value as a secret value
                pub fn const_lanes(__for_lanes {__a: __prim_t,}) -> Self {
                    let mut bytes = [0; __size];
                    __for_lanes {
                        bytes[__i*size_of::<__prim_t>() .. (__i+1)*size_of::<__prim_t>()]
                            .copy_from_slice(&<__lane_U>::from(__a).to_le_bytes());
                    }
                    Self(OpTree::const_(bytes))
                }

                /// Wraps a non-secret value as a secret value
                pub fn classify_slice(slice: &[__prim_t]) -> Self {
                    Self::try_classify_slice(slice).unwrap()
                }

                /// Wraps a non-secret value as a secret value
                pub fn try_classify_slice(slice: &[__prim_t]) -> Option<Self> {
                    if slice.len() == __lanes {
                        let mut bytes = [0; __size];
                        __for_lanes {
                            bytes[__i*size_of::<__prim_t>() .. (__i+1)*size_of::<__prim_t>()]
                                .copy_from_slice(&<__lane_U>::from(slice[__i]).to_le_bytes());
                        }
                        Some(Self(OpTree::imm(bytes)))
                    } else {
                        None
                    }
                }

                /// Extracts the secret value into a non-secret value, this
                /// effectively "leaks" the secret value, but is necessary
                /// to actually do anything
                pub fn declassify_vec(&self) -> Vec<__prim_t> {
                    self.try_declassify_vec().unwrap()
                }

                /// Same as declassify but propagating internal VM errors
                pub fn try_declassify_vec(&self) -> Result<Vec<__prim_t>, Error> {
                    let bytes: [u8; __size] = self.try_eval()?.0.result();
                    Ok(vec![__for_lanes {
                        <__prim_t>::from_le_bytes(
                            <_>::try_from(
                                &bytes[__i*size_of::<__prim_t>() .. (__i+1)*size_of::<__prim_t>()]
                            ).unwrap()
                        ),
                    }])
                }

                /// Wraps a non-secret value as a secret value
                pub fn new_slice(slice: &[__prim_t]) -> Self {
                    Self::classify_slice(slice)
                }

                /// Wraps a non-secret value as a secret value
                pub fn try_new_slice(slice: &[__prim_t]) -> Option<Self> {
                    Self::try_classify_slice(slice)
                }

                /// Wraps a non-secret value as a secret value
                pub fn const_slice(slice: &[__prim_t]) -> Self {
                    Self::try_const_slice(slice).unwrap()
                }

                /// Wraps a non-secret value as a secret value
                pub fn try_const_slice(slice: &[__prim_t]) -> Option<Self> {
                    if slice.len() == __lanes {
                        let mut bytes = [0; __size];
                        __for_lanes {
                            bytes[__i*size_of::<__prim_t>() .. (__i+1)*size_of::<__prim_t>()]
                                .copy_from_slice(&<__lane_U>::from(slice[__i]).to_le_bytes());
                        }
                        Some(Self(OpTree::const_(bytes)))
                    } else {
                        None
                    }
                }

                /// Wraps a non-secret value as a secret value
                pub fn new_splat(v: __prim_t) -> Self {
                    Self(OpTree::imm(<__U>::splat(<__lane_U>::from(v))))
                }

                /// Create a non-secret constant value, these are available
                /// for more optimizations than secret values
                pub fn const_splat(v: __prim_t) -> Self {
                    Self(OpTree::const_(<__U>::splat(<__lane_U>::from(v))))
                }
            }

            /// Build from lanes
            pub fn from_lanes(__for_lanes {__a: __lane_t,}) -> Self {
                #[allow(unused)]
                let x: Self;
                __for_lanes {
                    __if(__i == 0) {
                        let x = Self(OpTree::extend_u(__a.0));
                    }
                    __if(__i > 0) {
                        let x = x.replace(__i, __a);
                    } 
                }
                x
            }

            /// Extract all lanes
            pub fn to_lanes(self) -> (__for_lanes {__lane_t,}) {
                (__for_lanes {
                    self.clone().extract(__i),
                })
            }

            /// Build from lanes, panicking if the slice length does not match
            pub fn from_slice(slice: &[__lane_t]) -> Self {
                Self::try_from_slice(slice).unwrap()
            }

            /// Build from lanes, returning None if the slice length does not match
            pub fn try_from_slice(slice: &[__lane_t]) -> Option<Self> {
                if slice.len() == __lanes {
                    __for_lanes {
                        __if(__i == 0) {
                            let x = Self(OpTree::extend_u(slice[__i].clone().0));
                        }
                        __if(__i > 0) {
                            let x = x.replace(__i, slice[__i].clone());
                        } 
                    }
                    Some(x)
                } else {
                    None
                }
            }

            /// Extract all lanes
            pub fn to_vec(self) -> Vec<__lane_t> {
                vec![__for_lanes {
                    self.clone().extract(__i),
                }]
            }

            /// Splat a given value to all lanes
            pub fn splat(value: __lane_t) -> Self {
                Self(OpTree::splat(value.0))
            }

            /// Extract a specific lane
            pub fn extract(self, lane: usize) -> __lane_t {
                assert!(lane < __lanes);
                <__lane_t>::from_tree(OpTree::<__lane_U>::extract(
                    u16::try_from(lane).unwrap(), self.0
                ))
            }

            /// Replace a specific lane
            pub fn replace(self, lane: usize, value: __lane_t) -> Self {
                assert!(lane < __lanes);
                Self(OpTree::replace::<__lane_U>(
                    u16::try_from(lane).unwrap(), self.0, value.0
                ))
            }

            /// Reverse lanes
            pub fn reverse_lanes(self) -> Self {
                let mut lanes = [0xff; __size];
                for i in 0..__lanes {
                    // this works because i can be at most 64, < u8
                    let off = i*__lane_size;
                    lanes[off] = u8::try_from(__lanes-1 - i).unwrap();
                    lanes[off + 1 .. off + __lane_size]
                        .fill(0x00);
                }

                Self::const_le_bytes(lanes).shuffle(self.clone(), self)
            }

            /// A constant, non-secret 0, in all lanes
            pub fn zero() -> Self {
                Self(OpTree::zero())
            }

            /// A constant, non-secret 1, in all lanes
            pub fn one() -> Self {
                Self(OpTree::const_(<__U>::splat(<__lane_U>::one())))
            }

            /// A constant with all bits set to 1, non-secret, in all lanes
            pub fn ones() -> Self {
                Self(OpTree::ones())
            }

            // abs only available on signed types
            __if(__t == "ix") {
                pub fn abs(self) -> Self {
                    Self(OpTree::abs(__lnpw2, self.0))
                }
            }

            // other non-trait operations
            pub fn trailing_zeros(self) -> __secret_t {
                Self(OpTree::ctz(__lnpw2, self.0))
            }

            pub fn trailing_ones(self) -> __secret_t {
                (!self).trailing_zeros()
            }

            pub fn leading_zeros(self) -> __secret_t {
                Self(OpTree::clz(__lnpw2, self.0))
            }

            pub fn leading_ones(self) -> __secret_t {
                (!self).leading_zeros()
            }

            pub fn count_zeros(self) -> __secret_t {
                (!self).count_ones()
            }

            pub fn count_ones(self) -> __secret_t {
                Self(OpTree::popcnt(__lnpw2, self.0))
            }

            // ipw2/npw2 only available on unsigned types
            __if(__t == "ux") {
                pub fn is_power_of_two(self) -> __secret_mx {
                    self.count_ones().eq(Self::one())
                }

                pub fn next_power_of_two(self) -> __secret_t {
                    // based on implementation in rust core
                    self.clone().le(Self::one()).select(
                        // special case if <= 1
                        Self::zero(),
                        // next_power_of_two_minus_1
                        Self::ones() >> (self - Self::one()).leading_zeros()
                    ) + Self::one()
                }
            }

            pub fn rotate_left(self, other: __secret_t) -> __secret_t {
                Self(OpTree::rotl(__lnpw2, self.0, other.0))
            }

            pub fn rotate_right(self, other: __secret_t) -> __secret_t {
                Self(OpTree::rotr(__lnpw2, self.0, other.0))
            }

            pub fn reverse_bits(mut self) -> __secret_t {
                // reverse bytes
                if __lane_size > 1 {
                    self = self.reverse_bytes();
                }

                // reverse bits in bytes
                let mut mask = 0xffu8;
                for sh in [4,2,1] {
                    mask ^= mask << sh;
                    let sh_s = Self::splat(<__lane_t>::from_cast(SecretU8::const_(sh)));
                    let mask_s = Self::splat(<__lane_t>::const_le_bytes([mask; __lane_size]));
                    // fall back to OpTree to avoid signed-bitshifts
                    self = Self(OpTree::or(
                        OpTree::and(
                            OpTree::shr_u(__lnpw2, self.0.clone(), sh_s.0.clone()),
                            mask_s.0.clone(),
                        ),
                        OpTree::andnot(
                            OpTree::shl(__lnpw2, self.0, sh_s.0),
                            mask_s.0
                        )
                    ));
                }

                self
            }

            pub fn reverse_bytes(self) -> __secret_t {
                let mut bytes = [0xff; __size];
                for j in (0..__size).step_by(__lane_size) {
                    for i in 0..__lane_size {
                        // this works because i can be at most 64, < u8
                        bytes[j+i] = u8::try_from(j + __lane_size-1 - i).unwrap();
                    }
                }

                Self(OpTree::shuffle(
                    __npw2,
                    OpTree::const_(bytes),
                    self.0.clone(),
                    self.0
                ))
            }

            /// Apply an operation horizontally, reducing the input to a single lane
            ///
            /// Note that this runs in log2(number of lanes)
            pub fn reduce<F>(mut self, f: F) -> __lane_t
            where
                F: Fn(Self, Self) -> Self
            {
                // note this doesn't need to go through OpTree, but it means
                // one less type parameter
                for i in 0..__lnpw2 {
                    let shift: u32 = 8 << (i + __lane_npw2);
                    let b = Self(OpTree::shr_u(0,
                        self.0.clone(),
                        // a bit of an annoying workaround for type limitations
                        {
                            let mut bytes = [0; __size];
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

            pub fn horizontal_sum(self) -> __lane_t {
                self.reduce(|a, b| a + b)
            }

            pub fn horizontal_product(self) -> __lane_t {
                self.reduce(|a, b| a * b)
            }

            pub fn horizontal_and(self) -> __lane_t {
                self.reduce(|a, b| a & b)
            }

            pub fn horizontal_or(self) -> __lane_t {
                self.reduce(|a, b| a | b)
            }

            pub fn horizontal_xor(self) -> __lane_t {
                self.reduce(|a, b| a ^ b)
            }

            pub fn horizontal_min(self) -> __lane_t {
                self.reduce(|a, b| a.min(b))
            }

            pub fn horizontal_max(self) -> __lane_t {
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
                T: Shuffle<__secret_t>
            {
                T::shuffle(self, a, b)
            }
        }

        impl Eval for __secret_t {
            fn try_eval(&self) -> Result<Self, Error> {
                Ok(Self::from_tree(self.tree().try_eval()?))
            }
        }

        impl Tree for __secret_t {
            type Tree = OpTree<__U>;

            fn from_tree(tree: OpTree<__U>) -> Self {
                Self(tree)
            }

            fn tree<'a>(&'a self) -> Cow<'a, OpTree<__U>> {
                Cow::Borrowed(&self.0)
            }
        }

        impl Not for __secret_t {
            type Output = __secret_t;
            fn not(self) -> __secret_t {
                Self(OpTree::not(self.0))
            }
        }

        impl BitAnd for __secret_t {
            type Output = __secret_t;
            fn bitand(self, other: __secret_t) -> __secret_t {
                Self(OpTree::and(self.0, other.0))
            }
        }

        impl BitAndAssign for __secret_t {
            fn bitand_assign(&mut self, other: __secret_t) {
                *self = self.clone().bitand(other)
            }
        }

        impl BitOr for __secret_t {
            type Output = __secret_t;
            fn bitor(self, other: __secret_t) -> __secret_t {
                Self(OpTree::or(self.0, other.0))
            }
        }

        impl BitOrAssign for __secret_t {
            fn bitor_assign(&mut self, other: __secret_t) {
                *self = self.clone().bitor(other)
            }
        }

        impl BitXor for __secret_t {
            type Output = __secret_t;
            fn bitxor(self, other: __secret_t) -> __secret_t {
                Self(OpTree::xor(self.0, other.0))
            }
        }

        impl BitXorAssign for __secret_t {
            fn bitxor_assign(&mut self, other: __secret_t) {
                *self = self.clone().bitxor(other)
            }
        }

        // negate only available for signed types
        __if(__t == "ix") {
            impl Neg for __secret_t {
                type Output = __secret_t;
                fn neg(self) -> __secret_t {
                    Self(OpTree::neg(__lnpw2, self.0))
                }
            }
        }

        impl Add for __secret_t {
            type Output = __secret_t;
            fn add(self, other: __secret_t) -> __secret_t {
                Self(OpTree::add(__lnpw2, self.0, other.0))
            }
        }

        impl AddAssign for __secret_t {
            fn add_assign(&mut self, other: __secret_t) {
                *self = self.clone().add(other)
            }
        }

        impl Sub for __secret_t {
            type Output = __secret_t;
            fn sub(self, other: __secret_t) -> __secret_t {
                Self(OpTree::sub(__lnpw2, self.0, other.0))
            }
        }

        impl SubAssign for __secret_t {
            fn sub_assign(&mut self, other: __secret_t) {
                *self = self.clone().sub(other)
            }
        }

        impl Mul for __secret_t {
            type Output = __secret_t;
            fn mul(self, other: __secret_t) -> __secret_t {
                Self(OpTree::mul(__lnpw2, self.0, other.0))
            }
        }

        impl MulAssign for __secret_t {
            fn mul_assign(&mut self, other: __secret_t) {
                *self = self.clone().mul(other)
            }
        }

        impl Shl for __secret_t {
            type Output = __secret_t;
            fn shl(self, other: __secret_t) -> __secret_t {
                Self(OpTree::shl(__lnpw2, self.0, other.0))
            }
        }

        impl ShlAssign for __secret_t {
            fn shl_assign(&mut self, other: __secret_t) {
                *self = self.clone().shl(other)
            }
        }

        impl Shr for __secret_t {
            type Output = __secret_t;
            fn shr(self, other: __secret_t) -> __secret_t {
                __if(__t == "ux") {
                    Self(OpTree::shr_u(__lnpw2, self.0, other.0))
                }
                __if(__t == "ix") {
                    Self(OpTree::shr_s(__lnpw2, self.0, other.0))
                }
            }
        }

        impl ShrAssign for __secret_t {
            fn shr_assign(&mut self, other: __secret_t) {
                *self = self.clone().shr(other)
            }
        }

        impl Eq for __secret_t {
            type Output = __secret_mx;

            fn eq(self, other: Self) -> __secret_mx {
                __secret_mx(OpTree::eq(__lnpw2, self.0, other.0))
            }

            fn ne(self, other: Self) -> __secret_mx {
                __secret_mx(OpTree::ne(__lnpw2, self.0, other.0))
            }
        }

        impl Ord for __secret_t {
            type Output = __secret_mx;

            __if(__t == "ux") {
                fn lt(self, other: Self) -> __secret_mx {
                    __secret_mx(OpTree::lt_u(__lnpw2, self.0, other.0))
                }

                fn le(self, other: Self) -> __secret_mx {
                    __secret_mx(OpTree::le_u(__lnpw2, self.0, other.0))
                }

                fn gt(self, other: Self) -> __secret_mx {
                    __secret_mx(OpTree::gt_u(__lnpw2, self.0, other.0))
                }

                fn ge(self, other: Self) -> __secret_mx {
                    __secret_mx(OpTree::ge_u(__lnpw2, self.0, other.0))
                }

                fn min(self, other: Self) -> Self {
                    Self(OpTree::min_u(__lnpw2, self.0, other.0))
                }

                fn max(self, other: Self) -> Self {
                    Self(OpTree::max_u(__lnpw2, self.0, other.0))
                }
            }
            __if(__t == "ix") {
                fn lt(self, other: Self) -> __secret_mx {
                    __secret_mx(OpTree::lt_s(__lnpw2, self.0, other.0))
                }

                fn le(self, other: Self) -> __secret_mx {
                    __secret_mx(OpTree::le_s(__lnpw2, self.0, other.0))
                }

                fn gt(self, other: Self) -> __secret_mx {
                    __secret_mx(OpTree::gt_s(__lnpw2, self.0, other.0))
                }

                fn ge(self, other: Self) -> __secret_mx {
                    __secret_mx(OpTree::ge_s(__lnpw2, self.0, other.0))
                }

                fn min(self, other: Self) -> Self {
                    Self(OpTree::min_s(__lnpw2, self.0, other.0))
                }

                fn max(self, other: Self) -> Self {
                    Self(OpTree::max_s(__lnpw2, self.0, other.0))
                }
            }
        }

        impl Select<__secret_mx> for __secret_t {
            fn select(p: __secret_mx, a: Self, b: Self) -> Self {
                Self(OpTree::select(__lnpw2,
                    p.0,
                    a.0,
                    b.0
                ))
            }
        }

        impl Shuffle<__secret_ux> for __secret_t {
            fn shuffle(p: __secret_ux, a: Self, b: Self) -> Self {
                Self(OpTree::shuffle(__lnpw2,
                    p.0,
                    a.0,
                    b.0,
                ))
            }
        }

        impl Shuffle<__secret_ix> for __secret_t {
            fn shuffle(p: __secret_ix, a: Self, b: Self) -> Self {
                Self(OpTree::shuffle(__lnpw2,
                    p.0,
                    a.0,
                    b.0,
                ))
            }
        }
    }
}


//// Conversions U* <-> U* ////

// these are really tedious, so we use a really heavy-weight macro here

for_secret_t! {
    __if(__t == "u" || __t == "i") {
        // bool extending (bool -> u32)
        impl From<SecretBool> for __secret_t {
            fn from(v: SecretBool) -> __secret_t {
                Self(OpTree::and(v.resolve().into_owned(), <__secret_t>::one().0))
            }
        }
    }
}

for_secret_t_2! {
    // unsigned extending (u8 -> u32)
    __if(__t_2 == "u" && __npw2 > __npw2_2) {
        impl From<__secret_t_2> for __secret_t {
            fn from(v: __secret_t_2) -> __secret_t {
                Self(OpTree::extend_u(v.0))
            }
        }
    }

    // signed extending (i8 -> i32)
    __if(__t == "i" && __t_2 == "i" && __npw2 > __npw2_2) {
        impl From<__secret_t_2> for __secret_t {
            fn from(v: __secret_t_2) -> __secret_t {
                Self(OpTree::extend_s(v.0))
            }
        }
    }

    // truncating (i32 -> i8)
    __if((__t == "u" || __t == "i") && __t == __t_2 && __npw2 < __npw2_2) {
        impl FromCast<__secret_t_2> for __secret_t {
            fn from_cast(v: __secret_t_2) -> __secret_t {
                Self(OpTree::extract(0, v.0))
            }
        }
    }

    // cast same width (u8x4 -> u32)
    __if((__t != __t_2 || __lnpw2 != __lnpw2_2) && __npw2 == __npw2_2) {
        impl FromCast<__secret_t_2> for __secret_t {
            fn from_cast(v: __secret_t_2) -> __secret_t {
                Self(v.0)
            }
        }
    }

    // lane extending (u8x1 -> u8x4)
    __if((__t == "ux" || __t == "ix" || __t == "mx")
            && __t == __t_2 && __lane_npw2 == __lane_npw2_2 && __lnpw2 > __lnpw2_2) {
        impl From<__secret_t_2> for __secret_t {
            fn from(v: __secret_t_2) -> __secret_t {
                Self(OpTree::extend_u(v.0))
            }
        }
    }

    // lane truncating (i8x4 -> i8x1)
    __if((__t == "ux" || __t == "ix" || __t == "mx")
            && __t == __t_2 && __lane_npw2 == __lane_npw2_2 && __lnpw2 < __lnpw2_2) {
        impl FromCast<__secret_t_2> for __secret_t {
            fn from_cast(v: __secret_t_2) -> __secret_t {
                Self(OpTree::extract(0, v.0))
            }
        }
    }

    // unsigned extending lanes (u8x4 -> u32x4)
    __if((((__t == "ux" || __t == "ix") && __t_2 == "ux") || (__t == "mx" && __t_2 == "mx"))
            && __lane_npw2 > __lane_npw2_2 && __lnpw2 == __lnpw2_2) {
        impl From<__secret_t_2> for __secret_t {
            fn from(v: __secret_t_2) -> __secret_t {
                let mut lanes = [0xff; __size];
                for i in 0..__lanes_2 {
                    // this works because i can be at most 64, < u8
                    let off = i*__lane_size;
                    lanes[off] = u8::try_from(i).unwrap();
                    lanes[off + 1 .. off + __lane_size_2]
                        .fill(0x00);
                }

                // drop down to OpTree to avoid extra type parameter
                let extended = OpTree::extend_u(v.0);
                Self(
                    OpTree::shuffle(
                        u8::try_from(
                            ((__lanes * (__size/__size_2)) as usize)
                                .trailing_zeros()
                        ).unwrap(),
                        OpTree::const_(lanes),
                        extended.clone(),
                        extended
                    )
                )
            }
        }
    }

    // signed extending lanes (i8x4 -> i32x4)
    __if(__t == "ix" && __t_2 == "ix"
            && __lane_npw2 > __lane_npw2_2 && __lnpw2 == __lnpw2_2) {
        impl From<__secret_t_2> for __secret_t {
            fn from(v: __secret_t_2) -> __secret_t {
                let mut lanes = [0xff; __size];
                for i in 0..__lanes_2 {
                    // this works because i can be at most 64, < u8
                    let off = i*__lane_size
                        + (__lane_size-__lane_size_2);
                    lanes[off] = u8::try_from(i).unwrap();
                    lanes[off + 1 .. off + __lane_size_2]
                        .fill(0x00);
                }

                // drop down to OpTree to avoid extra type parameter
                let extended = OpTree::extend_u(v.0);
                let shift = 8*(__lane_size-__lane_size_2);
                Self(
                    OpTree::shr_s(
                        __lnpw2,
                        OpTree::shuffle(
                            u8::try_from(
                                ((__lanes * (__size/__size_2)) as usize)
                                    .trailing_zeros()
                            ).unwrap(),
                            OpTree::const_(lanes),
                            extended.clone(),
                            extended
                        ),
                        // a bit of an annoying workaround for type limitations
                        {
                            let mut bytes = [0; __size];
                            for i in 0..__lanes {
                                #[allow(unconditional_panic)]
                                if shift > 128 {
                                    bytes[i*__lane_size .. i*__lane_size+2]
                                        .copy_from_slice(
                                            &u16::try_from(shift).unwrap()
                                                .to_le_bytes()
                                        );
                                } else {
                                    bytes[i*__lane_size] = u8::try_from(shift).unwrap();
                                }
                            }
                            OpTree::const_(bytes)
                        }
                    )
                )
            }
        }
    }

    // truncating lanes (u32x4 -> u8x4)
    __if((__t == "ux" || __t == "ix" || __t == "mx") && __t == __t_2
            && __lane_npw2 < __lane_npw2_2 && __lnpw2 == __lnpw2_2) {
        impl FromCast<__secret_t_2> for __secret_t {
            fn from_cast(v: __secret_t_2) -> __secret_t {
                let mut lanes = [0; __size_2];
                for i in 0..__lanes_2 {
                    // this works because i can be at most 64, < u8
                    lanes[i*__lane_size]
                        = u8::try_from(i*(__size_2/__size)).unwrap();
                }

                // drop down to OpTree to avoid extra type parameter
                Self(
                    OpTree::extract(0,
                        OpTree::shuffle(
                            u8::try_from(
                                ((__lanes * (__size_2/__size)) as usize)
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
    }
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
    fn int_reverse() {
        println!();

        let a = SecretU32::new(0x12345678);
        let x = a.clone().reverse_bytes();
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, 0x78563412);

        let a = SecretU32::new(0x12345678);
        let x = a.clone().reverse_bits();
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, 0x1e6a2c48);

        let a = SecretU16x2::from_cast(SecretU32::new(0x12345678));
        let x = SecretU32::from_cast(a.clone().reverse_lanes());
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, 0x56781234);

        let a = SecretU16x2::from_cast(SecretU32::new(0x12345678));
        let x = SecretU32::from_cast(a.clone().reverse_bytes());
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, 0x34127856);

        let a = SecretU16x2::from_cast(SecretU32::new(0x12345678));
        let x = SecretU32::from_cast(a.clone().reverse_bits());
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify();
        println!("{}", v);
        assert_eq!(v, 0x2c481e6a);
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
        let x = SecretU8x16::from_cast(a);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_vec();
        println!("{:?}", v);
        assert_eq!(v, vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]);

        let a = SecretU256x2::from_lanes(
            SecretU256::from(SecretU16::new(1000)),
            SecretU256::from(SecretU16::new(2000))
        );
        let x = SecretU16x2::from_cast(a);
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
        let x = SecretU32x2::from_cast(b);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_lanes();
        println!("{:?}", v);
        assert_eq!(v, (1000, 2000));

        let a = SecretI32x16::new_lanes(-1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16);
        let x = SecretI8x16::from_cast(a);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_vec();
        println!("{:?}", v);
        assert_eq!(v, vec![-1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16]);

        let a = SecretI256x2::from_lanes(
            SecretI256::from(SecretI16::new(-1000)),
            SecretI256::from(SecretI16::new(-2000))
        );
        let x = SecretI16x2::from_cast(a);
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
        let x = SecretI32x2::from_cast(b);
        x.tree().disas(io::stdout()).unwrap();
        let v = x.declassify_lanes();
        println!("{:?}", v);
        assert_eq!(v, (-1000, -2000));
    }
}


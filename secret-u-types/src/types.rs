//! Definitions of secret integers

use std::rc::Rc;
use std::convert::TryFrom;
use std::mem::take;
use std::mem::transmute;
use std::mem::MaybeUninit;
use std::ops::Range;
use std::iter::FusedIterator;

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

use secret_u_opcode::Error;
use secret_u_optree::*;
use crate::traits::*;

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

impl Default for SecretBool {
    #[inline]
    fn default() -> Self {
        Self::const_(false)
    }
}

impl Classify<bool> for SecretBool {
    #[inline]
    fn classify(v: bool) -> SecretBool {
        Self::from_tree(OpTree::<U8>::imm(if v { 0xffu8 } else { 0x00u8 }))
    }

    #[inline]
    fn const_(v: bool) -> SecretBool {
        Self::from_tree(if v { OpTree::<U8>::ones() } else { OpTree::<U8>::zero() })
    }
}

impl FromDeclassify<SecretBool> for bool {
    type Error = Error;

    #[inline]
    fn try_from_declassify(v: SecretBool) -> Result<bool, Error> {
        Ok(v.resolve::<U8>().try_eval()?.result::<u8>() != 0)
    }
}

impl From<bool> for SecretBool {
    #[inline]
    fn from(v: bool) -> SecretBool {
        Self::classify(v)
    }
}

impl SecretBool {
    pub const SIZE: usize = 1;

    /// Alias for classify
    #[inline]
    pub fn new(v: bool) -> Self {
        Self::classify(v)
    }

    /// A constant, non-secret false
    #[inline]
    pub fn false_() -> Self {
        Self::from_tree(OpTree::zero())
    }

    /// A constant, non-secret true
    #[inline]
    pub fn true_() -> Self {
        Self::from_tree(OpTree::ones())
    }

    /// Extracts the secret value into a non-secret value, this
    /// effectively "leaks" the secret value, but is necessary
    /// to actually do anything with it.
    #[inline]
    pub fn declassify(self) -> bool {
        bool::from_declassify(self)
    }

    /// Same as declassify but propagating internal VM errors
    #[inline] 
    pub fn try_declassify(self) -> Result<bool, Error> {
        bool::try_from_declassify(self)
    }

    /// Create a deferred SecretBool, the actual type will resolved until
    /// needed to avoid unecessary truncates/extends
    #[inline]
    fn defer(tree: Rc<dyn DynOpTree>) -> Self {
        Self(DeferredTree::Deferred(tree))
    }

    /// Force into deferred SecretBool
    #[inline]
    fn deferred<'a>(&'a self) -> &'a dyn DynOpTree {
        match &self.0 {
            DeferredTree::Resolved(tree) => tree,
            DeferredTree::Deferred(tree) => tree.as_ref(),
        }
    }

    /// Reduce a deferred SecretBool down into a U8 if necessary
    #[inline]
    fn resolve<U: OpU>(self) -> OpTree<U> {
        OpTree::dyn_cast_s(self.deferred()).into_owned()
    }
}

impl Eval for SecretBool {
    #[inline]
    fn try_eval(self) -> Result<Self, Error> {
        Ok(Self::from_tree(self.resolve::<U8>().try_eval()?))
    }
}

impl Tree for SecretBool {
    type Tree = OpTree<U8>;

    #[inline]
    fn from_tree(tree: OpTree<U8>) -> Self {
        Self(DeferredTree::Resolved(tree))
    }

    #[inline]
    fn into_tree(self) -> OpTree<U8> {
        self.resolve::<U8>()
    }
}

impl Not for SecretBool {
    type Output = SecretBool;
    #[inline]
    fn not(self) -> SecretBool {
        match self.0 {
            DeferredTree::Resolved(tree) => Self::from_tree(OpTree::not(tree)),
            DeferredTree::Deferred(tree) => Self::defer(tree.dyn_not()),
        }
    }
}

impl BitAnd for SecretBool {
    type Output = SecretBool;
    #[inline]
    fn bitand(self, other: SecretBool) -> SecretBool {
        Self::defer(self.deferred().dyn_and(other.deferred()))
    }
}

impl BitAndAssign for SecretBool {
    #[inline]
    fn bitand_assign(&mut self, other: SecretBool) {
        *self = take(self).bitand(other)
    }
}

impl BitOr for SecretBool {
    type Output = SecretBool;
    #[inline]
    fn bitor(self, other: SecretBool) -> SecretBool {
        Self::defer(self.deferred().dyn_or(other.deferred()))
    }
}

impl BitOrAssign for SecretBool {
    #[inline]
    fn bitor_assign(&mut self, other: SecretBool) {
        *self = take(self).bitor(other)
    }
}

impl BitXor for SecretBool {
    type Output = SecretBool;
    #[inline]
    fn bitxor(self, other: SecretBool) -> SecretBool {
        Self::defer(self.deferred().dyn_xor(other.deferred()))
    }
}

impl BitXorAssign for SecretBool {
    #[inline]
    fn bitxor_assign(&mut self, other: SecretBool) {
        *self = take(self).bitxor(other)
    }
}

impl Eq for SecretBool {
    type Output = SecretBool;

    #[inline]
    fn eq(self, other: Self) -> SecretBool {
        !(self ^ other)
    }

    #[inline]
    fn ne(self, other: Self) -> SecretBool {
        self ^ other
    }
}

impl Ord for SecretBool {
    type Output = SecretBool;

    #[inline]
    fn lt(self, other: Self) -> SecretBool {
        !self & other
    }

    #[inline]
    fn le(self, other: Self) -> SecretBool {
        !self | other
    }

    #[inline]
    fn gt(self, other: Self) -> SecretBool {
        self & !other
    }

    #[inline]
    fn ge(self, other: Self) -> SecretBool {
        self | !other
    }

    #[inline]
    fn min(self, other: Self) -> Self {
        self & other
    }

    #[inline]
    fn max(self, other: Self) -> Self {
        self | other
    }
}

impl Select<SecretBool> for SecretBool {
    #[inline]
    fn select(self, a: SecretBool, b: SecretBool) -> SecretBool {
        SecretBool::from_tree(OpTree::select(0,
            self.resolve::<U8>(),
            a.resolve::<U8>(),
            b.resolve::<U8>()
        ))
    }
}


//// SecretU**/SecretI** ////

for_secret_t! {
    __if(__t == "u" || __t == "i" || __t == "p") {
        /// A secret integer who's value is ensured to not be leaked by Rust's type-system
        ///
        /// Note, like the underlying Rc type, clone is relatively cheap, but
        /// not a bytewise copy, which means we can't implement the Copy trait
        #[derive(Clone)]
        pub struct __secret_t(OpTree<__U>);

        impl Default for __secret_t {
            #[inline]
            fn default() -> Self {
                Self::zero()
            }
        }

        __if(__has_prim) {
            impl Classify<__prim_t> for __secret_t {
                #[inline]
                fn classify(v: __prim_t) -> __secret_t {
                    Self(OpTree::imm(v))
                }

                #[inline]
                fn const_(v: __prim_t) -> __secret_t {
                    Self(OpTree::const_(v))
                }
            }

            impl FromDeclassify<__secret_t> for __prim_t {
                type Error = Error;

                #[inline]
                fn try_from_declassify(v: __secret_t) -> Result<__prim_t, Error> {
                    Ok(v.try_eval()?.0.result())
                }
            }
        }

        impl ClassifyLeBytes<[u8; __size]> for __secret_t {
            #[inline]
            fn classify_le_bytes(v: [u8; __size]) -> __secret_t {
                Self(OpTree::imm(v))
            }

            #[inline]
            fn const_le_bytes(v: [u8; __size]) -> __secret_t {
                Self(OpTree::const_(v))
            }
        }

        impl FromDeclassifyLeBytes<__secret_t> for [u8; __size] {
            type Error = Error;

            #[inline]
            fn try_from_declassify_le_bytes(v: __secret_t) -> Result<[u8; __size], Error> {
                Ok(v.try_eval()?.0.result())
            }
        }

        impl ClassifyLeBytes<Box<[u8; __size]>> for __secret_t {
            #[inline]
            fn classify_le_bytes(v: Box<[u8; __size]>) -> __secret_t {
                Self(OpTree::imm(v))
            }

            #[inline]
            fn const_le_bytes(v: Box<[u8; __size]>) -> __secret_t {
                Self(OpTree::const_(v))
            }
        }

        impl FromDeclassifyLeBytes<__secret_t> for Box<[u8; __size]> {
            type Error = Error;

            #[inline]
            fn try_from_declassify_le_bytes(v: __secret_t) -> Result<Box<[u8; __size]>, Error> {
                Ok(v.try_eval()?.0.result())
            }
        }

        impl TryClassifyLeBytes<Box<[u8]>> for __secret_t {
            type Error = Box<[u8]>;

            #[inline]
            fn try_classify_le_bytes(v: Box<[u8]>) -> Result<__secret_t, Self::Error> {
                Ok(Self::classify_le_bytes(Box::<[u8; __size]>::try_from(v)?))
            }

            #[inline]
            fn try_const_le_bytes(v: Box<[u8]>) -> Result<__secret_t, Self::Error> {
                Ok(Self::const_le_bytes(Box::<[u8; __size]>::try_from(v)?))
            }
        }

        impl FromDeclassifyLeBytes<__secret_t> for Box<[u8]> {
            type Error = Error;

            #[inline]
            fn try_from_declassify_le_bytes(v: __secret_t) -> Result<Box<[u8]>, Error> {
                Ok(Box::<[u8; __size]>::try_from_declassify_le_bytes(v)? as Box<[u8]>)
            }
        }

        impl TryClassifyLeBytes<Vec<u8>> for __secret_t {
            type Error = Vec<u8>;

            #[inline]
            fn try_classify_le_bytes(v: Vec<u8>) -> Result<__secret_t, Self::Error> {
                Self::try_classify_le_bytes(Box::<[u8]>::from(v)).map_err(Vec::<u8>::from)
            }

            #[inline]
            fn try_const_le_bytes(v: Vec<u8>) -> Result<__secret_t, Self::Error> {
                Self::try_const_le_bytes(Box::<[u8]>::from(v)).map_err(Vec::<u8>::from)
            }
        }

        impl FromDeclassifyLeBytes<__secret_t> for Vec<u8> {
            type Error = Error;

            #[inline]
            fn try_from_declassify_le_bytes(v: __secret_t) -> Result<Vec<u8>, Error> {
                Ok(Vec::<u8>::from(Box::<[u8]>::try_from_declassify_le_bytes(v)?))
            }
        }

        impl ClassifyLeBytes<&[u8; __size]> for __secret_t {
            #[inline]
            fn classify_le_bytes(v: &[u8; __size]) -> __secret_t {
                Self(OpTree::imm(v))
            }

            #[inline]
            fn const_le_bytes(v: &[u8; __size]) -> __secret_t {
                Self(OpTree::const_(v))
            }
        }

        impl<'a> TryClassifyLeBytes<&'a [u8]> for __secret_t {
            type Error = &'a [u8];

            #[inline]
            fn try_classify_le_bytes(v: &'a [u8]) -> Result<__secret_t, Self::Error> {
                Ok(Self::classify_le_bytes(<&[u8; __size]>::try_from(v).map_err(|_| v)?))
            }

            #[inline]
            fn try_const_le_bytes(v: &'a [u8]) -> Result<__secret_t, Self::Error> {
                Ok(Self::const_le_bytes(<&[u8; __size]>::try_from(v).map_err(|_| v)?))
            }
        }

        impl ClassifyBeBytes<[u8; __size]> for __secret_t {
            #[inline]
            fn classify_be_bytes(v: [u8; __size]) -> __secret_t {
                let mut v = __U::from(v);
                v.reverse();
                Self(OpTree::imm(v))
            }

            #[inline]
            fn const_be_bytes(v: [u8; __size]) -> __secret_t {
                let mut v = __U::from(v);
                v.reverse();
                Self(OpTree::const_(v))
            }
        }

        impl FromDeclassifyBeBytes<__secret_t> for [u8; __size] {
            type Error = Error;

            #[inline]
            fn try_from_declassify_be_bytes(v: __secret_t) -> Result<[u8; __size], Error> {
                let mut v = v.try_eval()?.0.result::<__U>();
                v.reverse();
                Ok(v.into())
            }
        }

        impl ClassifyBeBytes<Box<[u8; __size]>> for __secret_t {
            #[inline]
            fn classify_be_bytes(v: Box<[u8; __size]>) -> __secret_t {
                let mut v = __U::from(v);
                v.reverse();
                Self(OpTree::imm(v))
            }

            #[inline]
            fn const_be_bytes(v: Box<[u8; __size]>) -> __secret_t {
                let mut v = __U::from(v);
                v.reverse();
                Self(OpTree::const_(v))
            }
        }

        impl FromDeclassifyBeBytes<__secret_t> for Box<[u8; __size]> {
            type Error = Error;

            #[inline]
            fn try_from_declassify_be_bytes(v: __secret_t) -> Result<Box<[u8; __size]>, Error> {
                let mut v = v.try_eval()?.0.result::<__U>();
                v.reverse();
                Ok(v.into())
            }
        }

        impl TryClassifyBeBytes<Box<[u8]>> for __secret_t {
            type Error = Box<[u8]>;

            #[inline]
            fn try_classify_be_bytes(v: Box<[u8]>) -> Result<__secret_t, Self::Error> {
                Ok(Self::classify_be_bytes(Box::<[u8; __size]>::try_from(v)?))
            }

            #[inline]
            fn try_const_be_bytes(v: Box<[u8]>) -> Result<__secret_t, Self::Error> {
                Ok(Self::const_be_bytes(Box::<[u8; __size]>::try_from(v)?))
            }
        }

        impl FromDeclassifyBeBytes<__secret_t> for Box<[u8]> {
            type Error = Error;

            #[inline]
            fn try_from_declassify_be_bytes(v: __secret_t) -> Result<Box<[u8]>, Error> {
                Ok(Box::<[u8; __size]>::try_from_declassify_be_bytes(v)? as Box<[u8]>)
            }
        }

        impl TryClassifyBeBytes<Vec<u8>> for __secret_t {
            type Error = Vec<u8>;

            #[inline]
            fn try_classify_be_bytes(v: Vec<u8>) -> Result<__secret_t, Self::Error> {
                Self::try_classify_be_bytes(Box::<[u8]>::from(v)).map_err(Vec::<u8>::from)
            }

            #[inline]
            fn try_const_be_bytes(v: Vec<u8>) -> Result<__secret_t, Self::Error> {
                Self::try_const_be_bytes(Box::<[u8]>::from(v)).map_err(Vec::<u8>::from)
            }
        }

        impl FromDeclassifyBeBytes<__secret_t> for Vec<u8> {
            type Error = Error;

            #[inline]
            fn try_from_declassify_be_bytes(v: __secret_t) -> Result<Vec<u8>, Error> {
                Ok(Vec::<u8>::from(Box::<[u8]>::try_from_declassify_be_bytes(v)?))
            }
        }

        impl ClassifyBeBytes<&[u8; __size]> for __secret_t {
            #[inline]
            fn classify_be_bytes(v: &[u8; __size]) -> __secret_t {
                let mut v = __U::from(v);
                v.reverse();
                Self(OpTree::imm(v))
            }

            #[inline]
            fn const_be_bytes(v: &[u8; __size]) -> __secret_t {
                let mut v = __U::from(v);
                v.reverse();
                Self(OpTree::const_(v))
            }
        }

        impl<'a> TryClassifyBeBytes<&'a [u8]> for __secret_t {
            type Error = &'a [u8];

            #[inline]
            fn try_classify_be_bytes(v: &'a [u8]) -> Result<__secret_t, Self::Error> {
                Ok(Self::classify_be_bytes(<&[u8; __size]>::try_from(v).map_err(|_| v)?))
            }

            #[inline]
            fn try_const_be_bytes(v: &'a [u8]) -> Result<__secret_t, Self::Error> {
                Ok(Self::const_be_bytes(<&[u8; __size]>::try_from(v).map_err(|_| v)?))
            }
        }

        __if(__has_prim) {
            impl From<__prim_t> for __secret_t {
                #[inline]
                fn from(v: __prim_t) -> __secret_t {
                    Self::classify(v)
                }
            }
        }

        impl __secret_t {
            pub const SIZE: usize = __size;

            __if(__has_prim) {
                /// Alias for classify
                #[inline]
                pub fn new(v: __prim_t) -> Self {
                    Self::classify(v)
                }
            }

            /// Alias for classify_le_bytes
            #[inline]
            pub fn from_le_bytes<T>(v: T) -> Self
            where
                Self: ClassifyLeBytes<T>
            {
                Self::classify_le_bytes(v)
            }

            /// Alias for try_classify_le_bytes
            #[inline]
            pub fn try_from_le_bytes<T>(v: T) -> Result<Self, <Self as TryClassifyLeBytes<T>>::Error>
            where
                Self: TryClassifyLeBytes<T>
            {
                Self::try_classify_le_bytes(v)
            }

            /// Alias for classify_be_bytes
            #[inline]
            pub fn from_be_bytes<T>(v: T) -> Self
            where
                Self: ClassifyBeBytes<T>
            {
                Self::classify_be_bytes(v)
            }

            /// Alias for try_classify_be_bytes
            #[inline]
            pub fn try_from_be_bytes<T>(v: T) -> Result<Self, <Self as TryClassifyBeBytes<T>>::Error>
            where
                Self: TryClassifyBeBytes<T>
            {
                Self::try_classify_be_bytes(v)
            }

            /// Alias for classify_ne_bytes
            #[inline]
            pub fn from_ne_bytes<T>(v: T) -> Self
            where
                Self: ClassifyNeBytes<T>
            {
                Self::classify_ne_bytes(v)
            }

            /// Alias for try_classify_ne_bytes
            #[inline]
            pub fn try_from_ne_bytes<T>(v: T) -> Result<Self, <Self as TryClassifyNeBytes<T>>::Error>
            where
                Self: TryClassifyNeBytes<T>
            {
                Self::try_classify_ne_bytes(v)
            }

            /// A constant, non-secret 0
            #[inline]
            pub fn zero() -> Self {
                Self(OpTree::zero())
            }

            /// A constant, non-secret 1
            #[inline]
            pub fn one() -> Self {
                Self(OpTree::one())
            }

            /// A constant with all bits set to 1, non-secret
            #[inline]
            pub fn ones() -> Self {
                Self(OpTree::ones())
            }

            __if(__has_prim) {
                /// Extracts the secret value into a non-secret value, this
                /// effectively "leaks" the secret value, but is necessary
                /// to actually do anything with it.
                #[inline]
                pub fn declassify(self) -> __prim_t {
                    __prim_t::from_declassify(self)
                }

                /// Same as declassify but propagating internal VM errors
                #[inline] 
                pub fn try_declassify(self) -> Result<__prim_t, Error> {
                    __prim_t::try_from_declassify(self)
                }
            }

            /// Extracts the secret value into a non-secret value, this
            /// effectively "leaks" the secret value, but is necessary
            /// to actually do anything with it.
            #[inline]
            pub fn declassify_le_bytes<T>(self) -> T
            where
                T: FromDeclassifyLeBytes<Self>
            {
                T::from_declassify_le_bytes(self)
            }

            /// Same as declassify but propagating internal VM errors
            #[inline] 
            pub fn try_declassify_le_bytes<T>(self) -> Result<T, T::Error>
            where
                T: FromDeclassifyLeBytes<Self>
            {
                T::try_from_declassify_le_bytes(self)
            }

            /// Extracts the secret value into a non-secret value, this
            /// effectively "leaks" the secret value, but is necessary
            /// to actually do anything with it.
            #[inline]
            pub fn declassify_be_bytes<T>(self) -> T
            where
                T: FromDeclassifyBeBytes<Self>
            {
                T::from_declassify_be_bytes(self)
            }

            /// Same as declassify but propagating internal VM errors
            #[inline] 
            pub fn try_declassify_be_bytes<T>(self) -> Result<T, T::Error>
            where
                T: FromDeclassifyBeBytes<Self>
            {
                T::try_from_declassify_be_bytes(self)
            }

            /// Extracts the secret value into a non-secret value, this
            /// effectively "leaks" the secret value, but is necessary
            /// to actually do anything with it.
            #[inline]
            pub fn declassify_ne_bytes<T>(self) -> T
            where
                T: FromDeclassifyNeBytes<Self>
            {
                T::from_declassify_ne_bytes(self)
            }

            /// Same as declassify but propagating internal VM errors
            #[inline] 
            pub fn try_declassify_ne_bytes<T>(self) -> Result<T, T::Error>
            where
                T: FromDeclassifyNeBytes<Self>
            {
                T::try_from_declassify_ne_bytes(self)
            }

            // abs only available on signed types
            __if(__t == "i") {
                #[inline]
                pub fn abs(self) -> Self {
                    Self(OpTree::abs(0, self.0))
                }
            }

            // other non-trait operations
            #[inline]
            pub fn trailing_zeros(self) -> __secret_t {
                Self(OpTree::ctz(0, self.0))
            }

            #[inline]
            pub fn trailing_ones(self) -> __secret_t {
                (!self).trailing_zeros()
            }

            #[inline]
            pub fn leading_zeros(self) -> __secret_t {
                Self(OpTree::clz(0, self.0))
            }

            #[inline]
            pub fn leading_ones(self) -> __secret_t {
                (!self).leading_zeros()
            }

            #[inline]
            pub fn count_zeros(self) -> __secret_t {
                (!self).count_ones()
            }

            #[inline]
            pub fn count_ones(self) -> __secret_t {
                Self(OpTree::popcnt(0, self.0))
            }

            // ipw2/npw2 only available on unsigned types
            __if(__t == "u") {
                #[inline]
                pub fn is_power_of_two(self) -> SecretBool {
                    self.count_ones().eq(Self::one())
                }

                #[inline]
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

            #[inline]
            pub fn rotate_left(self, other: __secret_t) -> __secret_t {
                Self(OpTree::rotl(0, self.0, other.0))
            }

            #[inline]
            pub fn rotate_right(self, other: __secret_t) -> __secret_t {
                Self(OpTree::rotr(0, self.0, other.0))
            }

            #[inline]
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

            #[inline]
            pub fn reverse_bytes(self) -> __secret_t {
                __if(__lane_size == 1) {
                    // nop
                    self
                }
                __if(__lane_size > 1 && __size <= 256) {
                    // types with <256 bytes can always use a single shuffle
                    let mut bytes = [0; __size];
                    for i in 0..__size {
                        bytes[i] = u8::try_from(__size-1 - i).unwrap();
                    }

                    Self(OpTree::shuffle(
                        __npw2,
                        OpTree::const_(bytes),
                        self.0.clone(),
                        self.0
                    ))
                }
                __if(__lane_size > 1 && __size > 256) {
                    // types with >256 bytes need to use multiple u16 shuffles in
                    // order to address all bytes 
                    let mut bytes = [0; __size];
                    for i in 0..__size/2 {
                        bytes[i*2..i*2+2].copy_from_slice(
                            &u16::try_from(__size/2-1 - i).unwrap().to_le_bytes()
                        );
                    }

                    // note we reverse lo/hi when we piece the type back together
                    let bytes = OpTree::<__U>::const_(bytes);
                    let lo = OpTree::and(
                        self.0.clone(),
                        OpTree::splat(OpTree::<U16>::const_(0x00ffu16)),
                    );
                    let hi = OpTree::shr_u(
                        __npw2-1,
                        self.0,
                        OpTree::splat(OpTree::<U16>::const_(8u16)),
                    );
                    let lo = OpTree::shuffle(
                        __npw2-1,
                        bytes.clone(),
                        lo.clone(),
                        lo
                    );
                    let hi = OpTree::shuffle(
                        __npw2-1,
                        bytes,
                        hi.clone(),
                        hi
                    );
                    Self(OpTree::or(
                        hi,
                        OpTree::shl(
                            __npw2-1,
                            lo,
                            OpTree::splat(OpTree::<U16>::const_(8u16))
                        )
                    ))
                }
            }
        }

        impl Eval for __secret_t {
            #[inline]
            fn try_eval(self) -> Result<Self, Error> {
                Ok(Self::from_tree(self.0.try_eval()?))
            }
        }

        impl Tree for __secret_t {
            type Tree = OpTree<__U>;

            #[inline]
            fn from_tree(tree: OpTree<__U>) -> Self {
                Self(tree)
            }

            #[inline]
            fn into_tree(self) -> OpTree<__U> {
                self.0
            }
        }

        impl Not for __secret_t {
            type Output = __secret_t;
            #[inline]
            fn not(self) -> __secret_t {
                Self(OpTree::not(self.0))
            }
        }

        impl BitAnd for __secret_t {
            type Output = __secret_t;
            #[inline]
            fn bitand(self, other: __secret_t) -> __secret_t {
                Self(OpTree::and(self.0, other.0))
            }
        }

        impl BitAndAssign for __secret_t {
            #[inline]
            fn bitand_assign(&mut self, other: __secret_t) {
                *self = take(self).bitand(other)
            }
        }

        impl BitOr for __secret_t {
            type Output = __secret_t;
            #[inline]
            fn bitor(self, other: __secret_t) -> __secret_t {
                Self(OpTree::or(self.0, other.0))
            }
        }

        impl BitOrAssign for __secret_t {
            #[inline]
            fn bitor_assign(&mut self, other: __secret_t) {
                *self = take(self).bitor(other)
            }
        }

        impl BitXor for __secret_t {
            type Output = __secret_t;
            #[inline]
            fn bitxor(self, other: __secret_t) -> __secret_t {
                Self(OpTree::xor(self.0, other.0))
            }
        }

        impl BitXorAssign for __secret_t {
            #[inline]
            fn bitxor_assign(&mut self, other: __secret_t) {
                *self = take(self).bitxor(other)
            }
        }

        // negate only available for signed types
        __if(__t == "i") {
            impl Neg for __secret_t {
                type Output = __secret_t;
                #[inline]
                fn neg(self) -> __secret_t {
                    Self(OpTree::neg(0, self.0))
                }
            }
        }

        __if(__t == "u" || __t == "i") {
            impl Add for __secret_t {
                type Output = __secret_t;
                #[inline]
                fn add(self, other: __secret_t) -> __secret_t {
                    Self(OpTree::add(0, self.0, other.0))
                }
            }

            impl AddAssign for __secret_t {
                #[inline]
                fn add_assign(&mut self, other: __secret_t) {
                    *self = take(self).add(other)
                }
            }

            impl Sub for __secret_t {
                type Output = __secret_t;
                #[inline]
                fn sub(self, other: __secret_t) -> __secret_t {
                    Self(OpTree::sub(0, self.0, other.0))
                }
            }

            impl SubAssign for __secret_t {
                #[inline]
                fn sub_assign(&mut self, other: __secret_t) {
                    *self = take(self).sub(other)
                }
            }

            impl Mul for __secret_t {
                type Output = __secret_t;
                #[inline]
                fn mul(self, other: __secret_t) -> __secret_t {
                    Self(OpTree::mul(0, self.0, other.0))
                }
            }

            impl MulAssign for __secret_t {
                #[inline]
                fn mul_assign(&mut self, other: __secret_t) {
                    *self = take(self).mul(other)
                }
            }
        }

        __if(__t == "p") {
            impl Add for __secret_t {
                type Output = __secret_t;
                #[inline]
                fn add(self, other: __secret_t) -> __secret_t {
                    Self(OpTree::xor(self.0, other.0))
                }
            }

            impl AddAssign for __secret_t {
                #[inline]
                fn add_assign(&mut self, other: __secret_t) {
                    *self = take(self).add(other)
                }
            }

            impl Sub for __secret_t {
                type Output = __secret_t;
                #[inline]
                fn sub(self, other: __secret_t) -> __secret_t {
                    Self(OpTree::xor(self.0, other.0))
                }
            }

            impl SubAssign for __secret_t {
                #[inline]
                fn sub_assign(&mut self, other: __secret_t) {
                    *self = take(self).sub(other)
                }
            }

            impl Mul for __secret_t {
                type Output = __secret_t;
                #[inline]
                fn mul(self, other: __secret_t) -> __secret_t {
                    Self(OpTree::xmul(0, self.0, other.0))
                }
            }

            impl MulAssign for __secret_t {
                #[inline]
                fn mul_assign(&mut self, other: __secret_t) {
                    *self = take(self).mul(other)
                }
            }
        }

        impl Shl for __secret_t {
            type Output = __secret_t;
            #[inline]
            fn shl(self, other: __secret_t) -> __secret_t {
                Self(OpTree::shl(0, self.0, other.0))
            }
        }

        impl ShlAssign for __secret_t {
            #[inline]
            fn shl_assign(&mut self, other: __secret_t) {
                *self = take(self).shl(other)
            }
        }

        impl Shr for __secret_t {
            type Output = __secret_t;
            #[inline]
            fn shr(self, other: __secret_t) -> __secret_t {
                __if(__t == "u" || __t == "p") {
                    Self(OpTree::shr_u(0, self.0, other.0))
                }
                __if(__t == "i") {
                    Self(OpTree::shr_s(0, self.0, other.0))
                }
            }
        }

        impl ShrAssign for __secret_t {
            #[inline]
            fn shr_assign(&mut self, other: __secret_t) {
                *self = take(self).shr(other)
            }
        }

        impl Eq for __secret_t {
            type Output = SecretBool;

            #[inline]
            fn eq(self, other: Self) -> SecretBool {
                SecretBool::defer(Rc::new(OpTree::eq(0, self.0, other.0)))
            }

            #[inline]
            fn ne(self, other: Self) -> SecretBool {
                SecretBool::defer(Rc::new(OpTree::ne(0, self.0, other.0)))
            }
        }

        __if(__t == "u") {
            impl Ord for __secret_t {
                type Output = SecretBool;

                #[inline]
                fn lt(self, other: Self) -> SecretBool {
                    SecretBool::defer(Rc::new(OpTree::lt_u(0, self.0, other.0)))
                }

                #[inline]
                fn le(self, other: Self) -> SecretBool {
                    SecretBool::defer(Rc::new(OpTree::le_u(0, self.0, other.0)))
                }

                #[inline]
                fn gt(self, other: Self) -> SecretBool {
                    SecretBool::defer(Rc::new(OpTree::gt_u(0, self.0, other.0)))
                }

                #[inline]
                fn ge(self, other: Self) -> SecretBool {
                    SecretBool::defer(Rc::new(OpTree::ge_u(0, self.0, other.0)))
                }

                #[inline]
                fn min(self, other: Self) -> Self {
                    Self(OpTree::min_u(0, self.0, other.0))
                }

                #[inline]
                fn max(self, other: Self) -> Self {
                    Self(OpTree::max_u(0, self.0, other.0))
                }
            }
        }

        __if(__t == "i") {
            impl Ord for __secret_t {
                type Output = SecretBool;

                #[inline]
                fn lt(self, other: Self) -> SecretBool {
                    SecretBool::defer(Rc::new(OpTree::lt_s(0, self.0, other.0)))
                }

                #[inline]
                fn le(self, other: Self) -> SecretBool {
                    SecretBool::defer(Rc::new(OpTree::le_s(0, self.0, other.0)))
                }

                #[inline]
                fn gt(self, other: Self) -> SecretBool {
                    SecretBool::defer(Rc::new(OpTree::gt_s(0, self.0, other.0)))
                }

                #[inline]
                fn ge(self, other: Self) -> SecretBool {
                    SecretBool::defer(Rc::new(OpTree::ge_s(0, self.0, other.0)))
                }

                #[inline]
                fn min(self, other: Self) -> Self {
                    Self(OpTree::min_s(0, self.0, other.0))
                }

                #[inline]
                fn max(self, other: Self) -> Self {
                    Self(OpTree::max_s(0, self.0, other.0))
                }
            }
        }

        impl Select<__secret_t> for SecretBool {
            #[inline]
            fn select(self, a: __secret_t, b: __secret_t) -> __secret_t {
                __secret_t(OpTree::select(0,
                    self.resolve(),
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
            #[inline]
            fn default() -> Self {
                Self::const_splat(false)
            }
        }

        impl Classify<[bool; __lanes]> for __secret_t {
            #[inline]
            fn classify(v: [bool; __lanes]) -> __secret_t {
                Self::classify(&v)
            }

            #[inline]
            fn const_(v: [bool; __lanes]) -> __secret_t {
                Self::const_(&v)
            }
        }

        impl FromDeclassify<__secret_t> for [bool; __lanes] {
            type Error = Error;

            #[inline]
            fn try_from_declassify(v: __secret_t) -> Result<[bool; __lanes], Error> {
                let bytes = v.try_eval()?.0.result::<__U>();
                let mut lanes = [false; __lanes];
                for i in 0..__lanes {
                    lanes[i] = !<__lane_U>::try_from(
                        &bytes[i*__lane_size .. (i+1)*__lane_size]
                    ).unwrap().is_zero();
                }
                Ok(lanes)
            }
        }

        impl Classify<Box<[bool; __lanes]>> for __secret_t {
            #[inline]
            fn classify(v: Box<[bool; __lanes]>) -> __secret_t {
                Self::classify(v.as_ref())
            }

            #[inline]
            fn const_(v: Box<[bool; __lanes]>) -> __secret_t {
                Self::const_(v.as_ref())
            }
        }

        impl FromDeclassify<__secret_t> for Box<[bool; __lanes]> {
            type Error = Error;

            #[inline]
            fn try_from_declassify(v: __secret_t) -> Result<Box<[bool; __lanes]>, Error> {
                let bytes = v.try_eval()?.0.result::<__U>();
                let mut lanes = Vec::with_capacity(__lanes);
                for i in 0..__lanes {
                    lanes.push(!<__lane_U>::try_from(
                        &bytes[i*__lane_size .. (i+1)*__lane_size]
                    ).unwrap().is_zero());
                }
                Ok(Box::<[bool; __lanes]>::try_from(
                    Box::<[bool]>::from(lanes)
                ).unwrap())
            }
        }

        impl TryClassify<Box<[bool]>> for __secret_t {
            type Error = Box<[bool]>;

            #[inline]
            fn try_classify(v: Box<[bool]>) -> Result<__secret_t, Self::Error> {
                Ok(Self::classify(Box::<[bool; __lanes]>::try_from(v)?))
            }

            #[inline]
            fn try_const(v: Box<[bool]>) -> Result<__secret_t, Self::Error> {
                Ok(Self::const_(Box::<[bool; __lanes]>::try_from(v)?))
            }
        }

        impl FromDeclassify<__secret_t> for Box<[bool]> {
            type Error = Error;

            #[inline]
            fn try_from_declassify(v: __secret_t) -> Result<Box<[bool]>, Error> {
                Ok(Box::<[bool; __lanes]>::try_from_declassify(v)? as Box<[bool]>)
            }
        }

        impl TryClassify<Vec<bool>> for __secret_t {
            type Error = Vec<bool>;

            #[inline]
            fn try_classify(v: Vec<bool>) -> Result<__secret_t, Self::Error> {
                Self::try_classify(Box::<[bool]>::from(v)).map_err(Vec::<bool>::from)
            }

            #[inline]
            fn try_const(v: Vec<bool>) -> Result<__secret_t, Self::Error> {
                Self::try_const(Box::<[bool]>::from(v)).map_err(Vec::<bool>::from)
            }
        }

        impl FromDeclassify<__secret_t> for Vec<bool> {
            type Error = Error;

            #[inline]
            fn try_from_declassify(v: __secret_t) -> Result<Vec<bool>, Error> {
                Ok(Vec::from(Box::<[bool]>::try_from_declassify(v)?))
            }
        }

        impl Classify<&[bool; __lanes]> for __secret_t {
            #[inline]
            fn classify(lanes: &[bool; __lanes]) -> __secret_t {
                let mut bytes = <__U>::zero();
                for (i, lane) in lanes.iter().enumerate() {
                    bytes[i*__lane_size .. (i+1)*__lane_size]
                        .copy_from_slice(
                            &if *lane {
                                <__lane_U>::ones()
                            } else {
                                <__lane_U>::zero()
                            }
                        )
                }
                Self(OpTree::imm(bytes))
            }

            #[inline]
            fn const_(lanes: &[bool; __lanes]) -> __secret_t {
                let mut bytes = <__U>::zero();
                for (i, lane) in lanes.iter().enumerate() {
                    bytes[i*__lane_size .. (i+1)*__lane_size]
                        .copy_from_slice(
                            &if *lane {
                                <__lane_U>::ones()
                            } else {
                                <__lane_U>::zero()
                            }
                        )
                }
                Self(OpTree::const_(bytes))
            }
        }

        impl<'a> TryClassify<&'a [bool]> for __secret_t {
            type Error = &'a [bool];

            #[inline]
            fn try_classify(v: &'a [bool]) -> Result<__secret_t, Self::Error> {
                Ok(Self::classify(<&[bool; __lanes]>::try_from(v).map_err(|_| v)?))
            }

            #[inline]
            fn try_const(v: &'a [bool]) -> Result<__secret_t, Self::Error> {
                Ok(Self::const_(<&[bool; __lanes]>::try_from(v).map_err(|_| v)?))
            }
        }

        impl From<[bool; __lanes]> for __secret_t {
            #[inline]
            fn from(v: [bool; __lanes]) -> __secret_t {
                Self::classify(v)
            }
        }

        impl From<Box<[bool; __lanes]>> for __secret_t {
            #[inline]
            fn from(v: Box<[bool; __lanes]>) -> __secret_t {
                Self::classify(v)
            }
        }

        impl TryFrom<Box<[bool]>> for __secret_t {
            type Error = Box<[bool]>;

            #[inline]
            fn try_from(v: Box<[bool]>) -> Result<__secret_t, Self::Error> {
                Self::try_classify(v)
            }
        }

        impl TryFrom<Vec<bool>> for __secret_t {
            type Error = Vec<bool>;

            #[inline]
            fn try_from(v: Vec<bool>) -> Result<__secret_t, Self::Error> {
                Self::try_classify(v)
            }
        }

        impl From<&[bool; __lanes]> for __secret_t {
            #[inline]
            fn from(v: &[bool; __lanes]) -> __secret_t {
                Self::classify(v)
            }
        }

        impl<'a> TryFrom<&'a [bool]> for __secret_t {
            type Error = &'a [bool];

            #[inline]
            fn try_from(v: &'a [bool]) -> Result<__secret_t, Self::Error> {
                Self::try_classify(v)
            }
        }

        impl From<[SecretBool; __lanes]> for __secret_t {
            /// Build from lanes
            #[inline]
            fn from(lanes: [SecretBool; __lanes]) -> Self {
                // into iter here to avoid cloning
                let mut lanes = IntoIterator::into_iter(lanes);
                let mut x = Self(lanes.next().unwrap().resolve());
                for i in 1..__lanes {
                    x = x.replace(i, lanes.next().unwrap())
                }
                x
            }
        }

        impl From<Box<[SecretBool; __lanes]>> for __secret_t {
            /// Build from lanes
            #[inline]
            fn from(lanes: Box<[SecretBool; __lanes]>) -> Self {
                // into iter here to avoid cloning
                let mut lanes = Vec::from(lanes as Box<[SecretBool]>).into_iter();
                let mut x = Self(lanes.next().unwrap().resolve());
                for i in 1..__lanes {
                    x = x.replace(i, lanes.next().unwrap())
                }
                x
            }
        }

        impl TryFrom<Box<[SecretBool]>> for __secret_t {
            type Error = Box<[SecretBool]>;

            /// Build from lanes
            #[inline]
            fn try_from(lanes: Box<[SecretBool]>) -> Result<Self, Self::Error> {
                Ok(Self::from(Box::<[SecretBool; __lanes]>::try_from(lanes)?))
            }
        }

        impl TryFrom<Vec<SecretBool>> for __secret_t {
            type Error = Vec<SecretBool>;

            /// Build from lanes
            #[inline]
            fn try_from(lanes: Vec<SecretBool>) -> Result<Self, Self::Error> {
                Ok(Self::try_from(Box::<[SecretBool]>::from(lanes)).map_err(Vec::<SecretBool>::from)?)
            }
        }

        impl From<&[SecretBool; __lanes]> for __secret_t {
            /// Build from lanes
            #[inline]
            fn from(lanes: &[SecretBool; __lanes]) -> Self {
                let mut lanes = lanes.iter();
                let mut x = Self(lanes.next().unwrap().clone().resolve());
                for i in 1..__lanes {
                    x = x.replace(i, lanes.next().unwrap().clone())
                }
                x
            }
        }

        impl<'a> TryFrom<&'a [SecretBool]> for __secret_t {
            type Error = &'a [SecretBool];

            /// Build from lanes
            #[inline]
            fn try_from(lanes: &'a [SecretBool]) -> Result<Self, Self::Error> {
                Ok(Self::from(<&[SecretBool; __lanes]>::try_from(lanes).map_err(|_| lanes)?))
            }
        }

        impl From<__secret_t> for [SecretBool; __lanes] {
            /// Extract all lanes
            #[inline]
            fn from(self_: __secret_t) -> Self {
                let mut lanes: [MaybeUninit<SecretBool>; __lanes]
                    = unsafe { MaybeUninit::uninit().assume_init() };
                for i in 0..__lanes {
                    lanes[i] = MaybeUninit::new(self_.clone().extract(i))
                }
                unsafe { transmute(lanes) }
            }
        }

        impl From<__secret_t> for Box<[SecretBool; __lanes]> {
            /// Extract all lanes
            #[inline]
            fn from(self_: __secret_t) -> Self {
                let mut lanes = Vec::<SecretBool>::with_capacity(__lanes);
                for i in 0..__lanes {
                    lanes.push(self_.clone().extract(i));
                }
                Box::<[SecretBool; __lanes]>::try_from(Box::<[SecretBool]>::from(lanes)).ok().unwrap()
            }
        }

        impl From<__secret_t> for Box<[SecretBool]> {
            /// Extract all lanes
            #[inline]
            fn from(self_: __secret_t) -> Self {
                Box::<[SecretBool; __lanes]>::from(self_) as Box<[SecretBool]>
            }
        }

        impl From<__secret_t> for Vec<SecretBool> {
            /// Extract all lanes
            #[inline]
            fn from(self_: __secret_t) -> Self {
                Vec::<SecretBool>::from(Box::<[SecretBool]>::from(self_))
            }
        }

        /// Lane iteration
        #[derive(Clone)]
        pub struct __iter_t {
            lanes: __secret_t,
            range: Range<u16>,
        }

        impl IntoIterator for __secret_t {
            type Item = SecretBool;
            type IntoIter = __iter_t;

            fn into_iter(self) -> __iter_t {
                __iter_t {
                    lanes: self,
                    range: 0..__lanes,
                }
            }
        }

        impl Iterator for __iter_t {
            type Item = SecretBool;

            fn next(&mut self) -> Option<Self::Item> {
                self.range.next().map(|i| self.lanes.clone().extract(usize::from(i)))
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                (__lanes, Some(__lanes))
            }
        }

        impl DoubleEndedIterator for __iter_t {
            fn next_back(&mut self) -> Option<Self::Item> {
                self.range.next_back().map(|i| self.lanes.clone().extract(usize::from(i)))
            }
        }

        impl ExactSizeIterator for __iter_t {}
        impl FusedIterator for __iter_t {}

        impl __secret_t {
            pub const SIZE: usize = __size;
            pub const LANES: usize = __lanes;

            /// Wraps a non-secret value as a secret value
            #[inline]
            pub fn new_splat(v: bool) -> Self {
                Self(OpTree::imm(<__U>::splat(if v { <__U>::ones() } else { <__U>::zero() })))
            }

            /// Create a non-secret constant value, these are available
            /// for more optimizations than secret values
            #[inline]
            pub fn const_splat(v: bool) -> Self {
                Self(OpTree::const_(<__U>::splat(if v { <__U>::ones() } else { <__U>::zero() })))
            }

            /// A constant, non-secret false in each lane
            #[inline]
            pub fn false_() -> Self {
                Self(OpTree::zero())
            }

            /// A constant, non-secret true in each lane
            #[inline]
            pub fn true_() -> Self {
                Self(OpTree::ones())
            }

            /// Extracts the secret value into a non-secret value, this
            /// effectively "leaks" the secret value, but is necessary
            /// to actually do anything with it.
            #[inline]
            pub fn declassify<T>(self) -> T
            where
                T: FromDeclassify<Self>
            {
                T::from_declassify(self)
            }

            /// Same as declassify but propagating internal VM errors
            #[inline] 
            pub fn try_declassify<T>(self) -> Result<T, T::Error>
            where
                T: FromDeclassify<Self>
            {
                T::try_from_declassify(self)
            }

            /// Splat a given value to all lanes
            #[inline]
            pub fn splat(value: SecretBool) -> Self {
                Self(OpTree::splat(value.resolve::<__lane_U>()))
            }

            /// Extract a specific lane
            #[inline]
            pub fn extract(self, lane: usize) -> SecretBool {
                assert!(lane < __lanes);
                SecretBool::defer(Rc::new(OpTree::<__lane_U>::extract(
                    u16::try_from(lane).unwrap(), self.0
                )))
            }

            /// Replace a specific lane
            #[inline]
            pub fn replace(self, lane: usize, value: SecretBool) -> Self {
                assert!(lane < __lanes);
                Self(OpTree::replace::<__lane_U>(
                    u16::try_from(lane).unwrap(), self.0, value.resolve()
                ))
            }

            /// Reverse lanes
            #[inline]
            pub fn reverse_lanes(self) -> Self {
                __if(__lanes <= 256) {
                    // types with <256 lanes can always use a single shuffle
                    let mut lanes = [0; __size];
                    for i in 0..__lanes {
                        let off = i*__lane_size;
                        lanes[off] = u8::try_from(__lanes-1 - i).unwrap();
                    }

                    Self(OpTree::shuffle(
                        __lnpw2,
                        OpTree::const_(lanes),
                        self.0.clone(),
                        self.0
                    ))
                }
                __if(__lanes > 256 && __lane_size > 1) {
                    // types >u8 can always use a single shuffle
                    let mut lanes = [0; __size];
                    for i in 0..__lanes {
                        let off = i*__lane_size;
                        lanes[off..off+2].copy_from_slice(
                            &u16::try_from(__lanes-1 - i).unwrap().to_le_bytes()
                        );
                    }

                    Self(OpTree::shuffle(
                        __lnpw2,
                        OpTree::const_(lanes),
                        self.0.clone(),
                        self.0
                    ))
                }
                __if(__lanes > 256 && __lane_size == 1) {
                    // types with >256 u8s need to use multiple u16 shuffles in
                    // order to address all lanes
                    let mut lanes = [0; __size];
                    for i in 0..__lanes/2 {
                        let off = i*2*__lane_size;
                        lanes[off..off+2].copy_from_slice(
                            &u16::try_from(__lanes/2-1 - i).unwrap().to_le_bytes()
                        );
                    }

                    // note we reverse lo/hi when we piece the type back together
                    let lanes = OpTree::<__U>::const_(lanes);
                    let lo = OpTree::and(
                        self.0.clone(),
                        OpTree::splat(OpTree::<U16>::const_(0x00ffu16)),
                    );
                    let hi = OpTree::shr_u(
                        __lnpw2-1,
                        self.0,
                        OpTree::splat(OpTree::<U16>::const_(8u16)),
                    );
                    let lo = OpTree::shuffle(
                        __lnpw2-1,
                        lanes.clone(),
                        lo.clone(),
                        lo
                    );
                    let hi = OpTree::shuffle(
                        __lnpw2-1,
                        lanes,
                        hi.clone(),
                        hi
                    );
                    Self(OpTree::or(
                        hi,
                        OpTree::shl(
                            __lnpw2-1,
                            lo,
                            OpTree::splat(OpTree::<U16>::const_(8u16))
                        )
                    ))
                }
            }

            /// Apply an operation horizontally, reducing the input to a single lane
            ///
            /// Note that this runs in log2(number of lanes)
            #[inline]
            pub fn reduce<F>(mut self, f: F) -> SecretBool
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
                                bytes[0..4].copy_from_slice(
                                    &u32::try_from(shift).unwrap()
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


            /// Find if no lanes are true
            #[inline]
            pub fn none(self) -> SecretBool {
                SecretBool::defer(Rc::new(OpTree::eq(0, self.0, OpTree::zero())))
            }

            /// Find if any lanes are true
            #[inline]
            pub fn any(self) -> SecretBool {
                SecretBool::defer(Rc::new(OpTree::ne(0, self.0, OpTree::zero())))
            }

            /// Find if all lanes are true
            #[inline]
            pub fn all(self) -> SecretBool {
                self.reduce(|a, b| a & b)
            }
        }

        impl Eval for __secret_t {
            #[inline]
            fn try_eval(self) -> Result<Self, Error> {
                Ok(Self::from_tree(self.0.try_eval()?))
            }
        }

        impl Tree for __secret_t {
            type Tree = OpTree<__U>;

            #[inline]
            fn from_tree(tree: OpTree<__U>) -> Self {
                Self(tree)
            }

            #[inline]
            fn into_tree(self) -> OpTree<__U> {
                self.0
            }
        }

        impl Not for __secret_t {
            type Output = __secret_t;
            #[inline]
            fn not(self) -> __secret_t {
                Self(OpTree::not(self.0))
            }
        }

        impl BitAnd for __secret_t {
            type Output = __secret_t;
            #[inline]
            fn bitand(self, other: __secret_t) -> __secret_t {
                Self(OpTree::and(self.0, other.0))
            }
        }

        impl BitAndAssign for __secret_t {
            #[inline]
            fn bitand_assign(&mut self, other: __secret_t) {
                *self = take(self).bitand(other)
            }
        }

        impl BitOr for __secret_t {
            type Output = __secret_t;
            #[inline]
            fn bitor(self, other: __secret_t) -> __secret_t {
                Self(OpTree::or(self.0, other.0))
            }
        }

        impl BitOrAssign for __secret_t {
            #[inline]
            fn bitor_assign(&mut self, other: __secret_t) {
                *self = take(self).bitor(other)
            }
        }

        impl BitXor for __secret_t {
            type Output = __secret_t;
            #[inline]
            fn bitxor(self, other: __secret_t) -> __secret_t {
                Self(OpTree::xor(self.0, other.0))
            }
        }

        impl BitXorAssign for __secret_t {
            #[inline]
            fn bitxor_assign(&mut self, other: __secret_t) {
                *self = take(self).bitxor(other)
            }
        }

        impl Eq for __secret_t {
            type Output = __secret_t;

            #[inline]
            fn eq(self, other: Self) -> __secret_t {
                !(self ^ other)
            }

            #[inline]
            fn ne(self, other: Self) -> __secret_t {
                self ^ other
            }
        }

        impl Ord for __secret_t {
            type Output = __secret_t;

            #[inline]
            fn lt(self, other: Self) -> __secret_t {
                !self & other
            }

            #[inline]
            fn le(self, other: Self) -> __secret_t {
                !self | other
            }

            #[inline]
            fn gt(self, other: Self) -> __secret_t {
                self & !other
            }

            #[inline]
            fn ge(self, other: Self) -> __secret_t {
                self | !other
            }

            #[inline]
            fn min(self, other: Self) -> Self {
                self & other
            }

            #[inline]
            fn max(self, other: Self) -> Self {
                self | other
            }
        }

        impl Select<__secret_t> for __secretmx_t {
            #[inline]
            fn select(self, a: __secret_t, b: __secret_t) -> __secret_t {
                __secret_t(OpTree::select(__lnpw2, self.0, a.0, b.0))
            }
        }

        impl Shuffle<__secret_t> for __secretux_t {
            #[inline]
            fn shuffle(self, a: __secret_t) -> __secret_t {
                __secret_t(OpTree::shuffle(__lnpw2,
                    self.0,
                    a.0,
                    OpTree::zero(),
                ))
            }
        }

        impl Shuffle<__secret_t> for __secretix_t {
            #[inline]
            fn shuffle(self, a: __secret_t) -> __secret_t {
                __secret_t(OpTree::shuffle(__lnpw2,
                    self.0,
                    a.0,
                    OpTree::zero(),
                ))
            }
        }

        impl Shuffle2<__secret_t> for __secretux_t {
            #[inline]
            fn shuffle2(self, a: __secret_t, b: __secret_t) -> __secret_t {
                __secret_t(OpTree::shuffle(__lnpw2,
                    self.0,
                    a.0,
                    b.0,
                ))
            }
        }

        impl Shuffle2<__secret_t> for __secretix_t {
            #[inline]
            fn shuffle2(self, a: __secret_t, b: __secret_t) -> __secret_t {
                __secret_t(OpTree::shuffle(__lnpw2,
                    self.0,
                    a.0,
                    b.0,
                ))
            }
        }
    }
}


//// SecretU**x**/SecretI**x** ////

for_secret_t! {
    __if(__t == "ux" || __t == "ix" || __t == "px") {
        /// A secret SIMD mask type who's value is ensured to not be leaked by
        /// Rust's type-system
        ///
        /// Note, like the underlying Rc type, clone is relatively cheap, but
        /// not a bytewise copy, which means we can't implement the Copy trait
        #[derive(Clone)]
        pub struct __secret_t(OpTree<__U>);

        impl Default for __secret_t {
            #[inline]
            fn default() -> Self {
                Self::zero()
            }
        }

        __if(__has_prim) {
            impl Classify<[__prim_t; __lanes]> for __secret_t {
                #[inline]
                fn classify(v: [__prim_t; __lanes]) -> __secret_t {
                    let mut v = v;
                    for i in 0..__lanes {
                        v[i] = v[i].to_le();
                    }
                    let bytes = unsafe { transmute::<_, [u8; __size]>(v) };
                    Self(OpTree::imm(bytes))
                }

                #[inline]
                fn const_(v: [__prim_t; __lanes]) -> __secret_t {
                    let mut v = v;
                    for i in 0..__lanes {
                        v[i] = v[i].to_le();
                    }
                    let bytes = unsafe { transmute::<_, [u8; __size]>(v) };
                    Self(OpTree::const_(bytes))
                }
            }

            impl FromDeclassify<__secret_t> for [__prim_t; __lanes] {
                type Error = Error;

                #[inline]
                fn try_from_declassify(v: __secret_t) -> Result<[__prim_t; __lanes], Error> {
                    let bytes = v.try_eval()?.0.result::<[u8; __size]>();
                    let mut v = unsafe { transmute::<_, [__prim_t; __lanes]>(bytes) };
                    for i in 0..__lanes {
                        v[i] = __prim_t::from_le(v[i]);
                    }
                    Ok(v)
                }
            }

            impl Classify<Box<[__prim_t; __lanes]>> for __secret_t {
                #[inline]
                fn classify(v: Box<[__prim_t; __lanes]>) -> __secret_t {
                    let mut v = v;
                    for i in 0..__lanes {
                        v[i] = v[i].to_le();
                    }
                    let bytes = unsafe { Box::from_raw(Box::into_raw(v) as *mut [u8; __size]) };
                    Self(OpTree::imm(bytes))
                }

                #[inline]
                fn const_(v: Box<[__prim_t; __lanes]>) -> __secret_t {
                    let mut v = v;
                    for i in 0..__lanes {
                        v[i] = v[i].to_le();
                    }
                    let bytes = unsafe { Box::from_raw(Box::into_raw(v) as *mut [u8; __size]) };
                    Self(OpTree::const_(bytes))
                }
            }

            impl FromDeclassify<__secret_t> for Box<[__prim_t; __lanes]> {
                type Error = Error;

                #[inline]
                fn try_from_declassify(v: __secret_t) -> Result<Box<[__prim_t; __lanes]>, Error> {
                    let bytes = v.try_eval()?.0.result::<Box<[u8; __size]>>();
                    let mut v = unsafe { Box::from_raw(Box::into_raw(bytes) as *mut [__prim_t; __lanes]) };
                    for i in 0..__lanes {
                        v[i] = __prim_t::from_le(v[i]);
                    }
                    Ok(v)
                }
            }

            impl TryClassify<Box<[__prim_t]>> for __secret_t {
                type Error = Box<[__prim_t]>;

                #[inline]
                fn try_classify(v: Box<[__prim_t]>) -> Result<__secret_t, Self::Error> {
                    Ok(Self::classify(Box::<[__prim_t; __lanes]>::try_from(v)?))
                }

                #[inline]
                fn try_const(v: Box<[__prim_t]>) -> Result<__secret_t, Self::Error> {
                    Ok(Self::const_(Box::<[__prim_t; __lanes]>::try_from(v)?))
                }
            }

            impl FromDeclassify<__secret_t> for Box<[__prim_t]> {
                type Error = Error;

                #[inline]
                fn try_from_declassify(v: __secret_t) -> Result<Box<[__prim_t]>, Error> {
                    Ok(Box::<[__prim_t; __lanes]>::try_from_declassify(v)? as Box<[__prim_t]>)
                }
            }

            impl TryClassify<Vec<__prim_t>> for __secret_t {
                type Error = Vec<__prim_t>;

                #[inline]
                fn try_classify(v: Vec<__prim_t>) -> Result<__secret_t, Self::Error> {
                    Self::try_classify(Box::<[__prim_t]>::from(v)).map_err(Vec::<__prim_t>::from)
                }

                #[inline]
                fn try_const(v: Vec<__prim_t>) -> Result<__secret_t, Self::Error> {
                    Self::try_const(Box::<[__prim_t]>::from(v)).map_err(Vec::<__prim_t>::from)
                }
            }

            impl FromDeclassify<__secret_t> for Vec<__prim_t> {
                type Error = Error;

                #[inline]
                fn try_from_declassify(v: __secret_t) -> Result<Vec<__prim_t>, Error> {
                    Ok(Vec::from(Box::<[__prim_t]>::try_from_declassify(v)?))
                }
            }

            impl Classify<&[__prim_t; __lanes]> for __secret_t {
                #[inline]
                fn classify(lanes: &[__prim_t; __lanes]) -> __secret_t {
                    let mut bytes = <__U>::zero();
                    for (i, lane) in lanes.iter().enumerate() {
                        bytes[i*__lane_size .. (i+1)*__lane_size]
                            .copy_from_slice(&<__lane_U>::from(*lane))
                    }
                    Self(OpTree::imm(bytes))
                }

                #[inline]
                fn const_(lanes: &[__prim_t; __lanes]) -> __secret_t {
                    let mut bytes = <__U>::zero();
                    for (i, lane) in lanes.iter().enumerate() {
                        bytes[i*__lane_size .. (i+1)*__lane_size]
                            .copy_from_slice(&<__lane_U>::from(*lane))
                    }
                    Self(OpTree::const_(bytes))
                }
            }

            impl<'a> TryClassify<&'a [__prim_t]> for __secret_t {
                type Error = &'a [__prim_t];

                #[inline]
                fn try_classify(v: &'a [__prim_t]) -> Result<__secret_t, Self::Error> {
                    Ok(Self::classify(<&[__prim_t; __lanes]>::try_from(v).map_err(|_| v)?))
                }

                #[inline]
                fn try_const(v: &'a [__prim_t]) -> Result<__secret_t, Self::Error> {
                    Ok(Self::const_(<&[__prim_t; __lanes]>::try_from(v).map_err(|_| v)?))
                }
            }
        }

        impl ClassifyLeBytes<[u8; __size]> for __secret_t {
            #[inline]
            fn classify_le_bytes(v: [u8; __size]) -> __secret_t {
                Self(OpTree::imm(v))
            }

            #[inline]
            fn const_le_bytes(v: [u8; __size]) -> __secret_t {
                Self(OpTree::const_(v))
            }
        }

        impl FromDeclassifyLeBytes<__secret_t> for [u8; __size] {
            type Error = Error;

            #[inline]
            fn try_from_declassify_le_bytes(v: __secret_t) -> Result<[u8; __size], Error> {
                Ok(v.try_eval()?.0.result())
            }
        }

        impl ClassifyLeBytes<Box<[u8; __size]>> for __secret_t {
            #[inline]
            fn classify_le_bytes(v: Box<[u8; __size]>) -> __secret_t {
                Self(OpTree::imm(v))
            }

            #[inline]
            fn const_le_bytes(v: Box<[u8; __size]>) -> __secret_t {
                Self(OpTree::const_(v))
            }
        }

        impl FromDeclassifyLeBytes<__secret_t> for Box<[u8; __size]> {
            type Error = Error;

            #[inline]
            fn try_from_declassify_le_bytes(v: __secret_t) -> Result<Box<[u8; __size]>, Error> {
                Ok(v.try_eval()?.0.result())
            }
        }

        impl TryClassifyLeBytes<Box<[u8]>> for __secret_t {
            type Error = Box<[u8]>;

            #[inline]
            fn try_classify_le_bytes(v: Box<[u8]>) -> Result<__secret_t, Self::Error> {
                Ok(Self::classify_le_bytes(Box::<[u8; __size]>::try_from(v)?))
            }

            #[inline]
            fn try_const_le_bytes(v: Box<[u8]>) -> Result<__secret_t, Self::Error> {
                Ok(Self::const_le_bytes(Box::<[u8; __size]>::try_from(v)?))
            }
        }

        impl FromDeclassifyLeBytes<__secret_t> for Box<[u8]> {
            type Error = Error;

            #[inline]
            fn try_from_declassify_le_bytes(v: __secret_t) -> Result<Box<[u8]>, Error> {
                Ok(Box::<[u8; __size]>::try_from_declassify_le_bytes(v)? as Box<[u8]>)
            }
        }

        impl TryClassifyLeBytes<Vec<u8>> for __secret_t {
            type Error = Vec<u8>;

            #[inline]
            fn try_classify_le_bytes(v: Vec<u8>) -> Result<__secret_t, Self::Error> {
                Self::try_classify_le_bytes(Box::<[u8]>::from(v)).map_err(Vec::<u8>::from)
            }

            #[inline]
            fn try_const_le_bytes(v: Vec<u8>) -> Result<__secret_t, Self::Error> {
                Self::try_const_le_bytes(Box::<[u8]>::from(v)).map_err(Vec::<u8>::from)
            }
        }

        impl FromDeclassifyLeBytes<__secret_t> for Vec<u8> {
            type Error = Error;

            #[inline]
            fn try_from_declassify_le_bytes(v: __secret_t) -> Result<Vec<u8>, Error> {
                Ok(Vec::<u8>::from(Box::<[u8]>::try_from_declassify_le_bytes(v)?))
            }
        }

        impl ClassifyLeBytes<&[u8; __size]> for __secret_t {
            #[inline]
            fn classify_le_bytes(v: &[u8; __size]) -> __secret_t {
                Self(OpTree::imm(v))
            }

            #[inline]
            fn const_le_bytes(v: &[u8; __size]) -> __secret_t {
                Self(OpTree::const_(v))
            }
        }

        impl<'a> TryClassifyLeBytes<&'a [u8]> for __secret_t {
            type Error = &'a [u8];

            #[inline]
            fn try_classify_le_bytes(v: &'a [u8]) -> Result<__secret_t, Self::Error> {
                Ok(Self::classify_le_bytes(<&[u8; __size]>::try_from(v).map_err(|_| v)?))
            }

            #[inline]
            fn try_const_le_bytes(v: &'a [u8]) -> Result<__secret_t, Self::Error> {
                Ok(Self::const_le_bytes(<&[u8; __size]>::try_from(v).map_err(|_| v)?))
            }
        }

        impl ClassifyBeBytes<[u8; __size]> for __secret_t {
            #[inline]
            fn classify_be_bytes(v: [u8; __size]) -> __secret_t {
                let mut v = __U::from(v);
                v.reverse();
                Self(OpTree::imm(v))
            }

            #[inline]
            fn const_be_bytes(v: [u8; __size]) -> __secret_t {
                let mut v = __U::from(v);
                v.reverse();
                Self(OpTree::const_(v))
            }
        }

        impl FromDeclassifyBeBytes<__secret_t> for [u8; __size] {
            type Error = Error;

            #[inline]
            fn try_from_declassify_be_bytes(v: __secret_t) -> Result<[u8; __size], Error> {
                let mut v = v.try_eval()?.0.result::<__U>();
                v.reverse();
                Ok(v.into())
            }
        }

        impl ClassifyBeBytes<Box<[u8; __size]>> for __secret_t {
            #[inline]
            fn classify_be_bytes(v: Box<[u8; __size]>) -> __secret_t {
                let mut v = __U::from(v);
                v.reverse();
                Self(OpTree::imm(v))
            }

            #[inline]
            fn const_be_bytes(v: Box<[u8; __size]>) -> __secret_t {
                let mut v = __U::from(v);
                v.reverse();
                Self(OpTree::const_(v))
            }
        }

        impl FromDeclassifyBeBytes<__secret_t> for Box<[u8; __size]> {
            type Error = Error;

            #[inline]
            fn try_from_declassify_be_bytes(v: __secret_t) -> Result<Box<[u8; __size]>, Error> {
                let mut v = v.try_eval()?.0.result::<__U>();
                v.reverse();
                Ok(v.into())
            }
        }

        impl TryClassifyBeBytes<Box<[u8]>> for __secret_t {
            type Error = Box<[u8]>;

            #[inline]
            fn try_classify_be_bytes(v: Box<[u8]>) -> Result<__secret_t, Self::Error> {
                Ok(Self::classify_be_bytes(Box::<[u8; __size]>::try_from(v)?))
            }

            #[inline]
            fn try_const_be_bytes(v: Box<[u8]>) -> Result<__secret_t, Self::Error> {
                Ok(Self::const_be_bytes(Box::<[u8; __size]>::try_from(v)?))
            }
        }

        impl FromDeclassifyBeBytes<__secret_t> for Box<[u8]> {
            type Error = Error;

            #[inline]
            fn try_from_declassify_be_bytes(v: __secret_t) -> Result<Box<[u8]>, Error> {
                Ok(Box::<[u8; __size]>::try_from_declassify_be_bytes(v)? as Box<[u8]>)
            }
        }

        impl TryClassifyBeBytes<Vec<u8>> for __secret_t {
            type Error = Vec<u8>;

            #[inline]
            fn try_classify_be_bytes(v: Vec<u8>) -> Result<__secret_t, Self::Error> {
                Self::try_classify_be_bytes(Box::<[u8]>::from(v)).map_err(Vec::<u8>::from)
            }

            #[inline]
            fn try_const_be_bytes(v: Vec<u8>) -> Result<__secret_t, Self::Error> {
                Self::try_const_be_bytes(Box::<[u8]>::from(v)).map_err(Vec::<u8>::from)
            }
        }

        impl FromDeclassifyBeBytes<__secret_t> for Vec<u8> {
            type Error = Error;

            #[inline]
            fn try_from_declassify_be_bytes(v: __secret_t) -> Result<Vec<u8>, Error> {
                Ok(Vec::<u8>::from(Box::<[u8]>::try_from_declassify_be_bytes(v)?))
            }
        }

        impl ClassifyBeBytes<&[u8; __size]> for __secret_t {
            #[inline]
            fn classify_be_bytes(v: &[u8; __size]) -> __secret_t {
                let mut v = __U::from(v);
                v.reverse();
                Self(OpTree::imm(v))
            }

            #[inline]
            fn const_be_bytes(v: &[u8; __size]) -> __secret_t {
                let mut v = __U::from(v);
                v.reverse();
                Self(OpTree::const_(v))
            }
        }

        impl<'a> TryClassifyBeBytes<&'a [u8]> for __secret_t {
            type Error = &'a [u8];

            #[inline]
            fn try_classify_be_bytes(v: &'a [u8]) -> Result<__secret_t, Self::Error> {
                Ok(Self::classify_be_bytes(<&[u8; __size]>::try_from(v).map_err(|_| v)?))
            }

            #[inline]
            fn try_const_be_bytes(v: &'a [u8]) -> Result<__secret_t, Self::Error> {
                Ok(Self::const_be_bytes(<&[u8; __size]>::try_from(v).map_err(|_| v)?))
            }
        }

        __if(__has_prim) {
            impl From<[__prim_t; __lanes]> for __secret_t {
                #[inline]
                fn from(v: [__prim_t; __lanes]) -> __secret_t {
                    Self::classify(v)
                }
            }

            impl From<Box<[__prim_t; __lanes]>> for __secret_t {
                #[inline]
                fn from(v: Box<[__prim_t; __lanes]>) -> __secret_t {
                    Self::classify(v)
                }
            }

            impl TryFrom<Box<[__prim_t]>> for __secret_t {
                type Error = Box<[__prim_t]>;

                #[inline]
                fn try_from(v: Box<[__prim_t]>) -> Result<__secret_t, Self::Error> {
                    Self::try_classify(v)
                }
            }

            impl TryFrom<Vec<__prim_t>> for __secret_t {
                type Error = Vec<__prim_t>;

                #[inline]
                fn try_from(v: Vec<__prim_t>) -> Result<__secret_t, Self::Error> {
                    Self::try_classify(v)
                }
            }

            impl From<&[__prim_t; __lanes]> for __secret_t {
                #[inline]
                fn from(v: &[__prim_t; __lanes]) -> __secret_t {
                    Self::classify(v)
                }
            }

            impl<'a> TryFrom<&'a [__prim_t]> for __secret_t {
                type Error = &'a [__prim_t];

                #[inline]
                fn try_from(v: &'a [__prim_t]) -> Result<__secret_t, Self::Error> {
                    Self::try_classify(v)
                }
            }
        }

        impl From<[__lane_t; __lanes]> for __secret_t {
            /// Build from lanes
            #[inline]
            fn from(lanes: [__lane_t; __lanes]) -> Self {
                // into iter here to avoid cloning
                let mut lanes = IntoIterator::into_iter(lanes);
                let mut x = Self(OpTree::extend_u(0, lanes.next().unwrap().0));
                for i in 1..__lanes {
                    x = x.replace(i, lanes.next().unwrap())
                }
                x
            }
        }

        impl From<Box<[__lane_t; __lanes]>> for __secret_t {
            /// Build from lanes
            #[inline]
            fn from(lanes: Box<[__lane_t; __lanes]>) -> Self {
                // into iter here to avoid cloning
                let mut lanes = Vec::from(lanes as Box<[__lane_t]>).into_iter();
                let mut x = Self(OpTree::extend_u(0, lanes.next().unwrap().0));
                for i in 1..__lanes {
                    x = x.replace(i, lanes.next().unwrap())
                }
                x
            }
        }

        impl TryFrom<Box<[__lane_t]>> for __secret_t {
            type Error = Box<[__lane_t]>;

            /// Build from lanes
            #[inline]
            fn try_from(lanes: Box<[__lane_t]>) -> Result<Self, Self::Error> {
                Ok(Self::from(Box::<[__lane_t; __lanes]>::try_from(lanes)?))
            }
        }

        impl TryFrom<Vec<__lane_t>> for __secret_t {
            type Error = Vec<__lane_t>;

            /// Build from lanes
            #[inline]
            fn try_from(lanes: Vec<__lane_t>) -> Result<Self, Self::Error> {
                Ok(Self::try_from(Box::<[__lane_t]>::from(lanes)).map_err(Vec::<__lane_t>::from)?)
            }
        }

        impl From<&[__lane_t; __lanes]> for __secret_t {
            /// Build from lanes
            #[inline]
            fn from(lanes: &[__lane_t; __lanes]) -> Self {
                let mut lanes = lanes.iter();
                let mut x = Self(OpTree::extend_u(0, lanes.next().unwrap().clone().0));
                for i in 1..__lanes {
                    x = x.replace(i, lanes.next().unwrap().clone())
                }
                x
            }
        }

        impl<'a> TryFrom<&'a [__lane_t]> for __secret_t {
            type Error = &'a [__lane_t];

            /// Build from lanes
            #[inline]
            fn try_from(lanes: &'a [__lane_t]) -> Result<Self, Self::Error> {
                Ok(Self::from(<&[__lane_t; __lanes]>::try_from(lanes).map_err(|_| lanes)?))
            }
        }

        impl From<__secret_t> for [__lane_t; __lanes] {
            /// Extract all lanes
            #[inline]
            fn from(self_: __secret_t) -> Self {
                let mut lanes: [MaybeUninit<__lane_t>; __lanes]
                    = unsafe { MaybeUninit::uninit().assume_init() };
                for i in 0..__lanes {
                    lanes[i] = MaybeUninit::new(self_.clone().extract(i))
                }
                unsafe { transmute(lanes) }
            }
        }

        impl From<__secret_t> for Box<[__lane_t; __lanes]> {
            /// Extract all lanes
            #[inline]
            fn from(self_: __secret_t) -> Self {
                let mut lanes = Vec::<__lane_t>::with_capacity(__lanes);
                for i in 0..__lanes {
                    lanes.push(self_.clone().extract(i));
                }
                Box::<[__lane_t; __lanes]>::try_from(Box::<[__lane_t]>::from(lanes)).ok().unwrap()
            }
        }

        impl From<__secret_t> for Box<[__lane_t]> {
            /// Extract all lanes
            #[inline]
            fn from(self_: __secret_t) -> Self {
                Box::<[__lane_t; __lanes]>::from(self_) as Box<[__lane_t]>
            }
        }

        impl From<__secret_t> for Vec<__lane_t> {
            /// Extract all lanes
            #[inline]
            fn from(self_: __secret_t) -> Self {
                Vec::<__lane_t>::from(Box::<[__lane_t]>::from(self_))
            }
        }

        /// Lane iteration
        #[derive(Clone)]
        pub struct __iter_t {
            lanes: __secret_t,
            range: Range<u16>,
        }

        impl IntoIterator for __secret_t {
            type Item = __lane_t;
            type IntoIter = __iter_t;

            fn into_iter(self) -> __iter_t {
                __iter_t {
                    lanes: self,
                    range: 0..__lanes,
                }
            }
        }

        impl Iterator for __iter_t {
            type Item = __lane_t;

            fn next(&mut self) -> Option<Self::Item> {
                self.range.next().map(|i| self.lanes.clone().extract(usize::from(i)))
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                (__lanes, Some(__lanes))
            }
        }

        impl DoubleEndedIterator for __iter_t {
            fn next_back(&mut self) -> Option<Self::Item> {
                self.range.next_back().map(|i| self.lanes.clone().extract(usize::from(i)))
            }
        }

        impl ExactSizeIterator for __iter_t {}
        impl FusedIterator for __iter_t {}

        impl __secret_t {
            pub const SIZE: usize = __size;
            pub const LANES: usize = __lanes;

            /// Alias for classify_le_bytes
            #[inline]
            pub fn from_le_bytes<T>(v: T) -> Self
            where
                Self: ClassifyLeBytes<T>
            {
                Self::classify_le_bytes(v)
            }

            /// Alias for try_classify_le_bytes
            #[inline]
            pub fn try_from_le_bytes<T>(v: T) -> Result<Self, <Self as TryClassifyLeBytes<T>>::Error>
            where
                Self: TryClassifyLeBytes<T>
            {
                Self::try_classify_le_bytes(v)
            }

            /// Alias for classify_be_bytes
            #[inline]
            pub fn from_be_bytes<T>(v: T) -> Self
            where
                Self: ClassifyBeBytes<T>
            {
                Self::classify_be_bytes(v)
            }

            /// Alias for try_classify_be_bytes
            #[inline]
            pub fn try_from_be_bytes<T>(v: T) -> Result<Self, <Self as TryClassifyBeBytes<T>>::Error>
            where
                Self: TryClassifyBeBytes<T>
            {
                Self::try_classify_be_bytes(v)
            }

            /// Alias for classify_ne_bytes
            #[inline]
            pub fn from_ne_bytes<T>(v: T) -> Self
            where
                Self: ClassifyNeBytes<T>
            {
                Self::classify_ne_bytes(v)
            }

            /// Alias for try_classify_ne_bytes
            #[inline]
            pub fn try_from_ne_bytes<T>(v: T) -> Result<Self, <Self as TryClassifyNeBytes<T>>::Error>
            where
                Self: TryClassifyNeBytes<T>
            {
                Self::try_classify_ne_bytes(v)
            }

            __if(__has_prim) {
                /// Wraps a non-secret value as a secret value
                #[inline]
                pub fn new_splat(v: __prim_t) -> Self {
                    Self(OpTree::imm(<__U>::splat(<__lane_U>::from(v))))
                }

                /// Create a non-secret constant value, these are available
                /// for more optimizations than secret values
                #[inline]
                pub fn const_splat(v: __prim_t) -> Self {
                    Self(OpTree::const_(<__U>::splat(<__lane_U>::from(v))))
                }
            }

            /// A constant, non-secret 0, in all lanes
            #[inline]
            pub fn zero() -> Self {
                Self(OpTree::zero())
            }

            /// A constant, non-secret 1, in all lanes
            #[inline]
            pub fn one() -> Self {
                Self(OpTree::const_(<__U>::splat(<__lane_U>::one())))
            }

            /// A constant with all bits set to 1, non-secret, in all lanes
            #[inline]
            pub fn ones() -> Self {
                Self(OpTree::ones())
            }

            /// Extracts the secret value into a non-secret value, this
            /// effectively "leaks" the secret value, but is necessary
            /// to actually do anything with it.
            #[inline]
            pub fn declassify<T>(self) -> T
            where
                T: FromDeclassify<Self>
            {
                T::from_declassify(self)
            }

            /// Same as declassify but propagating internal VM errors
            #[inline] 
            pub fn try_declassify<T>(self) -> Result<T, T::Error>
            where
                T: FromDeclassify<Self>
            {
                T::try_from_declassify(self)
            }

            /// Extracts the secret value into a non-secret value, this
            /// effectively "leaks" the secret value, but is necessary
            /// to actually do anything with it.
            #[inline]
            pub fn declassify_le_bytes<T>(self) -> T
            where
                T: FromDeclassifyLeBytes<Self>
            {
                T::from_declassify_le_bytes(self)
            }

            /// Same as declassify but propagating internal VM errors
            #[inline] 
            pub fn try_declassify_le_bytes<T>(self) -> Result<T, T::Error>
            where
                T: FromDeclassifyLeBytes<Self>
            {
                T::try_from_declassify_le_bytes(self)
            }

            /// Extracts the secret value into a non-secret value, this
            /// effectively "leaks" the secret value, but is necessary
            /// to actually do anything with it.
            #[inline]
            pub fn declassify_be_bytes<T>(self) -> T
            where
                T: FromDeclassifyBeBytes<Self>
            {
                T::from_declassify_be_bytes(self)
            }

            /// Same as declassify but propagating internal VM errors
            #[inline] 
            pub fn try_declassify_be_bytes<T>(self) -> Result<T, T::Error>
            where
                T: FromDeclassifyBeBytes<Self>
            {
                T::try_from_declassify_be_bytes(self)
            }

            /// Extracts the secret value into a non-secret value, this
            /// effectively "leaks" the secret value, but is necessary
            /// to actually do anything with it.
            #[inline]
            pub fn declassify_ne_bytes<T>(self) -> T
            where
                T: FromDeclassifyNeBytes<Self>
            {
                T::from_declassify_ne_bytes(self)
            }

            /// Same as declassify but propagating internal VM errors
            #[inline] 
            pub fn try_declassify_ne_bytes<T>(self) -> Result<T, T::Error>
            where
                T: FromDeclassifyNeBytes<Self>
            {
                T::try_from_declassify_ne_bytes(self)
            }

            /// Splat a given value to all lanes
            #[inline]
            pub fn splat(value: __lane_t) -> Self {
                Self(OpTree::splat(value.0))
            }

            /// Extract a specific lane
            #[inline]
            pub fn extract(self, lane: usize) -> __lane_t {
                assert!(lane < __lanes);
                <__lane_t>::from_tree(OpTree::<__lane_U>::extract(
                    u16::try_from(lane).unwrap(), self.0
                ))
            }

            /// Replace a specific lane
            #[inline]
            pub fn replace(self, lane: usize, value: __lane_t) -> Self {
                assert!(lane < __lanes);
                Self(OpTree::replace::<__lane_U>(
                    u16::try_from(lane).unwrap(), self.0, value.0
                ))
            }

            /// Reverse lanes
            #[inline]
            pub fn reverse_lanes(self) -> Self {
                __if(__lanes <= 256) {
                    // types with <256 lanes can always use a single shuffle
                    let mut lanes = [0; __size];
                    for i in 0..__lanes {
                        let off = i*__lane_size;
                        lanes[off] = u8::try_from(__lanes-1 - i).unwrap();
                    }

                    Self(OpTree::shuffle(
                        __lnpw2,
                        OpTree::const_(lanes),
                        self.0.clone(),
                        self.0
                    ))
                }
                __if(__lanes > 256 && __lane_size > 1) {
                    // types >u8 can always use a single shuffle
                    let mut lanes = [0; __size];
                    for i in 0..__lanes {
                        let off = i*__lane_size;
                        lanes[off..off+2].copy_from_slice(
                            &u16::try_from(__lanes-1 - i).unwrap().to_le_bytes()
                        );
                    }

                    Self(OpTree::shuffle(
                        __lnpw2,
                        OpTree::const_(lanes),
                        self.0.clone(),
                        self.0
                    ))
                }
                __if(__lanes > 256 && __lane_size == 1) {
                    // types with >256 u8s need to use multiple u16 shuffles in
                    // order to address all lanes
                    let mut lanes = [0; __size];
                    for i in 0..__lanes/2 {
                        let off = i*2*__lane_size;
                        lanes[off..off+2].copy_from_slice(
                            &u16::try_from(__lanes/2-1 - i).unwrap().to_le_bytes()
                        );
                    }

                    // note we reverse lo/hi when we piece the type back together
                    let lanes = OpTree::<__U>::const_(lanes);
                    let lo = OpTree::and(
                        self.0.clone(),
                        OpTree::splat(OpTree::<U16>::const_(0x00ffu16)),
                    );
                    let hi = OpTree::shr_u(
                        __lnpw2-1,
                        self.0,
                        OpTree::splat(OpTree::<U16>::const_(8u16)),
                    );
                    let lo = OpTree::shuffle(
                        __lnpw2-1,
                        lanes.clone(),
                        lo.clone(),
                        lo
                    );
                    let hi = OpTree::shuffle(
                        __lnpw2-1,
                        lanes,
                        hi.clone(),
                        hi
                    );
                    Self(OpTree::or(
                        hi,
                        OpTree::shl(
                            __lnpw2-1,
                            lo,
                            OpTree::splat(OpTree::<U16>::const_(8u16))
                        )
                    ))
                }
            }

            // abs only available on signed types
            __if(__t == "ix") {
                #[inline]
                pub fn abs(self) -> Self {
                    Self(OpTree::abs(__lnpw2, self.0))
                }
            }

            // other non-trait operations
            #[inline]
            pub fn trailing_zeros(self) -> __secret_t {
                Self(OpTree::ctz(__lnpw2, self.0))
            }

            #[inline]
            pub fn trailing_ones(self) -> __secret_t {
                (!self).trailing_zeros()
            }

            #[inline]
            pub fn leading_zeros(self) -> __secret_t {
                Self(OpTree::clz(__lnpw2, self.0))
            }

            #[inline]
            pub fn leading_ones(self) -> __secret_t {
                (!self).leading_zeros()
            }

            #[inline]
            pub fn count_zeros(self) -> __secret_t {
                (!self).count_ones()
            }

            #[inline]
            pub fn count_ones(self) -> __secret_t {
                Self(OpTree::popcnt(__lnpw2, self.0))
            }

            // ipw2/npw2 only available on unsigned types
            __if(__t == "ux") {
                #[inline]
                pub fn is_power_of_two(self) -> __secretmx_t {
                    self.count_ones().eq(Self::one())
                }

                #[inline]
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

            #[inline]
            pub fn rotate_left(self, other: __secret_t) -> __secret_t {
                Self(OpTree::rotl(__lnpw2, self.0, other.0))
            }

            #[inline]
            pub fn rotate_right(self, other: __secret_t) -> __secret_t {
                Self(OpTree::rotr(__lnpw2, self.0, other.0))
            }

            #[inline]
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

            #[inline]
            pub fn reverse_bytes(self) -> __secret_t {
                __if(__lane_size == 1) {
                    // nop
                    self
                }
                __if(__lane_size > 1 && __size <= 256) {
                    // types with <256 bytes can always use a single shuffle
                    let mut bytes = [0; __size];
                    for j in (0..__size).step_by(__lane_size) {
                        for i in 0..__lane_size {
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
                __if(__lane_size > 1 && __size > 256) {
                    // types with >256 bytes need to use multiple u16 shuffles in
                    // order to address all bytes 
                    let mut bytes = [0; __size];
                    for j in (0..__size/2).step_by(__lane_size/2) {
                        for i in 0..__lane_size/2 {
                            bytes[j*2+i*2..j*2+i*2+2].copy_from_slice(
                                &u16::try_from(j + __lane_size/2-1 - i).unwrap().to_le_bytes()
                            );
                        }
                    }

                    // note we reverse lo/hi when we piece the type back together
                    let bytes = OpTree::<__U>::const_(bytes);
                    let lo = OpTree::and(
                        self.0.clone(),
                        OpTree::splat(OpTree::<U16>::const_(0x00ffu16)),
                    );
                    let hi = OpTree::shr_u(
                        __npw2-1,
                        self.0,
                        OpTree::splat(OpTree::<U16>::const_(8u16)),
                    );
                    let lo = OpTree::shuffle(
                        __npw2-1,
                        bytes.clone(),
                        lo.clone(),
                        lo
                    );
                    let hi = OpTree::shuffle(
                        __npw2-1,
                        bytes,
                        hi.clone(),
                        hi
                    );
                    Self(OpTree::or(
                        hi,
                        OpTree::shl(
                            __npw2-1,
                            lo,
                            OpTree::splat(OpTree::<U16>::const_(8u16))
                        )
                    ))
                }
            }

            /// Apply an operation horizontally, reducing the input to a single lane
            ///
            /// Note that this runs in log2(number of lanes)
            #[inline]
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
                                bytes[0..4].copy_from_slice(
                                    &u32::try_from(shift).unwrap()
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

            #[inline]
            pub fn horizontal_sum(self) -> __lane_t {
                self.reduce(|a, b| a + b)
            }

            #[inline]
            pub fn horizontal_product(self) -> __lane_t {
                self.reduce(|a, b| a * b)
            }

            #[inline]
            pub fn horizontal_and(self) -> __lane_t {
                self.reduce(|a, b| a & b)
            }

            #[inline]
            pub fn horizontal_or(self) -> __lane_t {
                self.reduce(|a, b| a | b)
            }

            #[inline]
            pub fn horizontal_xor(self) -> __lane_t {
                self.reduce(|a, b| a ^ b)
            }

            __if(__t == "ux" || __t == "ix") {
                #[inline]
                pub fn horizontal_min(self) -> __lane_t {
                    self.reduce(|a, b| a.min(b))
                }

                #[inline]
                pub fn horizontal_max(self) -> __lane_t {
                    self.reduce(|a, b| a.max(b))
                }
            }
        }

        impl Eval for __secret_t {
            #[inline]
            fn try_eval(self) -> Result<Self, Error> {
                Ok(Self::from_tree(self.0.try_eval()?))
            }
        }

        impl Tree for __secret_t {
            type Tree = OpTree<__U>;

            #[inline]
            fn from_tree(tree: OpTree<__U>) -> Self {
                Self(tree)
            }

            #[inline]
            fn into_tree(self) -> OpTree<__U> {
                self.0
            }
        }

        impl Not for __secret_t {
            type Output = __secret_t;
            #[inline]
            fn not(self) -> __secret_t {
                Self(OpTree::not(self.0))
            }
        }

        impl BitAnd for __secret_t {
            type Output = __secret_t;
            #[inline]
            fn bitand(self, other: __secret_t) -> __secret_t {
                Self(OpTree::and(self.0, other.0))
            }
        }

        impl BitAndAssign for __secret_t {
            #[inline]
            fn bitand_assign(&mut self, other: __secret_t) {
                *self = take(self).bitand(other)
            }
        }

        impl BitOr for __secret_t {
            type Output = __secret_t;
            #[inline]
            fn bitor(self, other: __secret_t) -> __secret_t {
                Self(OpTree::or(self.0, other.0))
            }
        }

        impl BitOrAssign for __secret_t {
            #[inline]
            fn bitor_assign(&mut self, other: __secret_t) {
                *self = take(self).bitor(other)
            }
        }

        impl BitXor for __secret_t {
            type Output = __secret_t;
            #[inline]
            fn bitxor(self, other: __secret_t) -> __secret_t {
                Self(OpTree::xor(self.0, other.0))
            }
        }

        impl BitXorAssign for __secret_t {
            #[inline]
            fn bitxor_assign(&mut self, other: __secret_t) {
                *self = take(self).bitxor(other)
            }
        }

        // negate only available for signed types
        __if(__t == "ix") {
            impl Neg for __secret_t {
                type Output = __secret_t;
                #[inline]
                fn neg(self) -> __secret_t {
                    Self(OpTree::neg(__lnpw2, self.0))
                }
            }
        }

        __if(__t == "ux" || __t == "ix") {
            impl Add for __secret_t {
                type Output = __secret_t;
                #[inline]
                fn add(self, other: __secret_t) -> __secret_t {
                    Self(OpTree::add(__lnpw2, self.0, other.0))
                }
            }

            impl AddAssign for __secret_t {
                #[inline]
                fn add_assign(&mut self, other: __secret_t) {
                    *self = take(self).add(other)
                }
            }

            impl Sub for __secret_t {
                type Output = __secret_t;
                #[inline]
                fn sub(self, other: __secret_t) -> __secret_t {
                    Self(OpTree::sub(__lnpw2, self.0, other.0))
                }
            }

            impl SubAssign for __secret_t {
                #[inline]
                fn sub_assign(&mut self, other: __secret_t) {
                    *self = take(self).sub(other)
                }
            }

            impl Mul for __secret_t {
                type Output = __secret_t;
                #[inline]
                fn mul(self, other: __secret_t) -> __secret_t {
                    Self(OpTree::mul(__lnpw2, self.0, other.0))
                }
            }

            impl MulAssign for __secret_t {
                #[inline]
                fn mul_assign(&mut self, other: __secret_t) {
                    *self = take(self).mul(other)
                }
            }
        }

        __if(__t == "px") {
            impl Add for __secret_t {
                type Output = __secret_t;
                #[inline]
                fn add(self, other: __secret_t) -> __secret_t {
                    Self(OpTree::xor(self.0, other.0))
                }
            }

            impl AddAssign for __secret_t {
                #[inline]
                fn add_assign(&mut self, other: __secret_t) {
                    *self = take(self).add(other)
                }
            }

            impl Sub for __secret_t {
                type Output = __secret_t;
                #[inline]
                fn sub(self, other: __secret_t) -> __secret_t {
                    Self(OpTree::xor(self.0, other.0))
                }
            }

            impl SubAssign for __secret_t {
                #[inline]
                fn sub_assign(&mut self, other: __secret_t) {
                    *self = take(self).sub(other)
                }
            }

            impl Mul for __secret_t {
                type Output = __secret_t;
                #[inline]
                fn mul(self, other: __secret_t) -> __secret_t {
                    Self(OpTree::xmul(__lnpw2, self.0, other.0))
                }
            }

            impl MulAssign for __secret_t {
                #[inline]
                fn mul_assign(&mut self, other: __secret_t) {
                    *self = take(self).mul(other)
                }
            }
        }

        impl Shl for __secret_t {
            type Output = __secret_t;
            #[inline]
            fn shl(self, other: __secret_t) -> __secret_t {
                Self(OpTree::shl(__lnpw2, self.0, other.0))
            }
        }

        impl ShlAssign for __secret_t {
            #[inline]
            fn shl_assign(&mut self, other: __secret_t) {
                *self = take(self).shl(other)
            }
        }

        impl Shr for __secret_t {
            type Output = __secret_t;
            #[inline]
            fn shr(self, other: __secret_t) -> __secret_t {
                __if(__t == "ux" || __t == "px") {
                    Self(OpTree::shr_u(__lnpw2, self.0, other.0))
                }
                __if(__t == "ix") {
                    Self(OpTree::shr_s(__lnpw2, self.0, other.0))
                }
            }
        }

        impl ShrAssign for __secret_t {
            #[inline]
            fn shr_assign(&mut self, other: __secret_t) {
                *self = take(self).shr(other)
            }
        }

        impl Eq for __secret_t {
            type Output = __secretmx_t;

            #[inline]
            fn eq(self, other: Self) -> __secretmx_t {
                __secretmx_t(OpTree::eq(__lnpw2, self.0, other.0))
            }

            #[inline]
            fn ne(self, other: Self) -> __secretmx_t {
                __secretmx_t(OpTree::ne(__lnpw2, self.0, other.0))
            }
        }

        __if(__t == "ux") {
            impl Ord for __secret_t {
                type Output = __secretmx_t;

                #[inline]
                fn lt(self, other: Self) -> __secretmx_t {
                    __secretmx_t(OpTree::lt_u(__lnpw2, self.0, other.0))
                }

                #[inline]
                fn le(self, other: Self) -> __secretmx_t {
                    __secretmx_t(OpTree::le_u(__lnpw2, self.0, other.0))
                }

                #[inline]
                fn gt(self, other: Self) -> __secretmx_t {
                    __secretmx_t(OpTree::gt_u(__lnpw2, self.0, other.0))
                }

                #[inline]
                fn ge(self, other: Self) -> __secretmx_t {
                    __secretmx_t(OpTree::ge_u(__lnpw2, self.0, other.0))
                }

                #[inline]
                fn min(self, other: Self) -> Self {
                    Self(OpTree::min_u(__lnpw2, self.0, other.0))
                }

                #[inline]
                fn max(self, other: Self) -> Self {
                    Self(OpTree::max_u(__lnpw2, self.0, other.0))
                }
            }
        }

        __if(__t == "ix") {
            impl Ord for __secret_t {
                type Output = __secretmx_t;
                #[inline]
                fn lt(self, other: Self) -> __secretmx_t {
                    __secretmx_t(OpTree::lt_s(__lnpw2, self.0, other.0))
                }

                #[inline]
                fn le(self, other: Self) -> __secretmx_t {
                    __secretmx_t(OpTree::le_s(__lnpw2, self.0, other.0))
                }

                #[inline]
                fn gt(self, other: Self) -> __secretmx_t {
                    __secretmx_t(OpTree::gt_s(__lnpw2, self.0, other.0))
                }

                #[inline]
                fn ge(self, other: Self) -> __secretmx_t {
                    __secretmx_t(OpTree::ge_s(__lnpw2, self.0, other.0))
                }

                #[inline]
                fn min(self, other: Self) -> Self {
                    Self(OpTree::min_s(__lnpw2, self.0, other.0))
                }

                #[inline]
                fn max(self, other: Self) -> Self {
                    Self(OpTree::max_s(__lnpw2, self.0, other.0))
                }
            }
        }

        impl Select<__secret_t> for __secretmx_t {
            #[inline]
            fn select(self, a: __secret_t, b: __secret_t) -> __secret_t {
                __secret_t(OpTree::select(__lnpw2,
                    self.0,
                    a.0,
                    b.0
                ))
            }
        }

        impl Shuffle<__secret_t> for __secretux_t {
            #[inline]
            fn shuffle(self, a: __secret_t) -> __secret_t {
                __secret_t(OpTree::shuffle(__lnpw2,
                    self.0,
                    a.0,
                    OpTree::zero(),
                ))
            }
        }

        impl Shuffle<__secret_t> for __secretix_t {
            #[inline]
            fn shuffle(self, a: __secret_t) -> __secret_t {
                __secret_t(OpTree::shuffle(__lnpw2,
                    self.0,
                    a.0,
                    OpTree::zero(),
                ))
            }
        }

        impl Shuffle2<__secret_t> for __secretux_t {
            #[inline]
            fn shuffle2(self, a: __secret_t, b: __secret_t) -> __secret_t {
                __secret_t(OpTree::shuffle(__lnpw2,
                    self.0,
                    a.0,
                    b.0,
                ))
            }
        }

        impl Shuffle2<__secret_t> for __secretix_t {
            #[inline]
            fn shuffle2(self, a: __secret_t, b: __secret_t) -> __secret_t {
                __secret_t(OpTree::shuffle(__lnpw2,
                    self.0,
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
            #[inline]
            fn from(v: SecretBool) -> __secret_t {
                Self(OpTree::and(v.resolve(), <__secret_t>::one().0))
            }
        }
    }
}

for_secret_t_2! {
    // unsigned extending (u8 -> u32)
    __if(__t_2 == "u" && __npw2 > __npw2_2) {
        impl From<__secret_t_2> for __secret_t {
            #[inline]
            fn from(v: __secret_t_2) -> __secret_t {
                Self(OpTree::extend_u(0, v.0))
            }
        }
    }

    // signed extending (i8 -> i32)
    __if(__t == "i" && __t_2 == "i" && __npw2 > __npw2_2) {
        impl From<__secret_t_2> for __secret_t {
            #[inline]
            fn from(v: __secret_t_2) -> __secret_t {
                Self(OpTree::extend_s(0, v.0))
            }
        }
    }

    // truncating (i32 -> i8)
    __if((__t == "u" || __t == "i") && __t == __t_2 && __npw2 < __npw2_2) {
        impl FromCast<__secret_t_2> for __secret_t {
            #[inline]
            fn from_cast(v: __secret_t_2) -> __secret_t {
                Self(OpTree::truncate(0, v.0))
            }
        }
    }

    // cast same width (u8x4 -> u32)
    __if((__t != __t_2 || __lnpw2 != __lnpw2_2) && __npw2 == __npw2_2) {
        impl FromCast<__secret_t_2> for __secret_t {
            #[inline]
            fn from_cast(v: __secret_t_2) -> __secret_t {
                Self(v.0)
            }
        }
    }

    // lane extending (u8x1 -> u8x4)
    __if((__t == "ux" || __t == "ix" || __t == "mx")
            && __t == __t_2 && __lane_npw2 == __lane_npw2_2 && __lnpw2 > __lnpw2_2) {
        impl From<__secret_t_2> for __secret_t {
            #[inline]
            fn from(v: __secret_t_2) -> __secret_t {
                Self(OpTree::extend_u(0, v.0))
            }
        }
    }

    // lane truncating (i8x4 -> i8x1)
    __if((__t == "ux" || __t == "ix" || __t == "mx")
            && __t == __t_2 && __lane_npw2 == __lane_npw2_2 && __lnpw2 < __lnpw2_2) {
        impl FromCast<__secret_t_2> for __secret_t {
            #[inline]
            fn from_cast(v: __secret_t_2) -> __secret_t {
                Self(OpTree::truncate(0, v.0))
            }
        }
    }

    // unsigned extending lanes (u8x4 -> u32x4)
    __if((((__t == "ux" || __t == "ix") && __t_2 == "ux") || (__t == "mx" && __t_2 == "mx"))
            && __lane_npw2 > __lane_npw2_2 && __lnpw2 == __lnpw2_2) {
        impl From<__secret_t_2> for __secret_t {
            #[inline]
            fn from(v: __secret_t_2) -> __secret_t {
                Self(OpTree::extend_u(__lnpw2, v.0))
            }
        }
    }

    // signed extending lanes (i8x4 -> i32x4)
    __if(__t == "ix" && __t_2 == "ix"
            && __lane_npw2 > __lane_npw2_2 && __lnpw2 == __lnpw2_2) {
        impl From<__secret_t_2> for __secret_t {
            #[inline]
            fn from(v: __secret_t_2) -> __secret_t {
                Self(OpTree::extend_s(__lnpw2, v.0))
            }
        }
    }

    // truncating lanes (u32x4 -> u8x4)
    __if((__t == "ux" || __t == "ix" || __t == "mx") && __t == __t_2
            && __lane_npw2 < __lane_npw2_2 && __lnpw2 == __lnpw2_2) {
        impl FromCast<__secret_t_2> for __secret_t {
            #[inline]
            fn from_cast(v: __secret_t_2) -> __secret_t {
                Self(OpTree::truncate(__lnpw2, v.0))
            }
        }
    }
}


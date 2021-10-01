//! Traits implemented by secret types

use secret_u_opcode::Error;
use std::fmt::Debug;


/// A trait for types that can eq as long as the result remains secret
pub trait Eq {
    type Output;
    fn eq(self, other: Self) -> Self::Output;
    fn ne(self, other: Self) -> Self::Output;
}

/// A trait for types that can be compared as long as the result remains secret
pub trait Ord {
    type Output;
    fn lt(self, other: Self) -> Self::Output;
    fn le(self, other: Self) -> Self::Output;
    fn gt(self, other: Self) -> Self::Output;
    fn ge(self, other: Self) -> Self::Output;

    // convenience functions
    fn max(self, other: Self) -> Self;
    fn min(self, other: Self) -> Self;

    #[inline]
    fn clamp(self, min: Self, max: Self) -> Self
    where
        Self: Sized
    {
        self.max(min).min(max)
    }
}

/// A trait for objects that can select 
pub trait Select<T> {
    /// Select operation for constant-time conditionals
    fn select(self, a: T, b: T) -> T;
}

/// A trait for objects that can shuffle
pub trait Shuffle<T> {
    /// Shuffle operation using this value as indices
    ///
    /// For each lane:
    /// 0..lanes       <= lane from a
    /// otherwise      <= 0
    fn shuffle(self, a: T) -> T;
}

/// A trait for objects that can shuffle 
pub trait Shuffle2<T> {
    /// Shuffle operation using this value as indices
    ///
    /// For each lane:
    /// 0..lanes       <= lane from a
    /// lanes..2*lanes <= lane-lanes from b
    /// otherwise      <= 0
    fn shuffle2(self, a: T, b: T) -> T;
}

/// A trait for objects that can be flattened to reduce tree size
pub trait Eval: Sized {
    /// Evaluate to immediate form
    ///
    /// Normally eval is internally called by declassify,
    /// but this can be useful for flattening the internal
    /// tree manually to avoid growing too larger during a
    /// computation
    #[inline]
    fn eval(self) -> Self {
        self.try_eval().unwrap()
    }

    /// Same as eval but propagating internal VM errors
    fn try_eval(self) -> Result<Self, Error>;
}

/// A trait for objects backed by an internal OpTree, this is used
/// for compiling down to bytecode
pub trait Tree: Sized
where
    <Self as Tree>::Tree: Clone
{
    /// Internal tree representation
    type Tree;

    /// Build from internal tree
    fn from_tree(tree: Self::Tree) -> Self;

    /// Get internal tree
    fn into_tree(self) -> Self::Tree;
}


/// A trait for secret types that can wrap a non-secret value
/// as a secret value
pub trait Classify<T>
where
    Self: Sized
{
    fn classify(t: T) -> Self;

    /// An optional way to hint to the secret type that the underlying
    /// value is not actually secret. This should only be used on
    /// non-secret values.
    #[inline]
    fn const_(t: T) -> Self {
        Self::classify(t)
    }
}

/// A trait for secret types that can try to wrap a non-secret value
/// as a secret value
pub trait TryClassify<T>
where
    Self: Sized
{
    type Error;

    fn try_classify(t: T) -> Result<Self, Self::Error>;

    /// An optional way to hint to the secret type that the underlying
    /// value is not actually secret. This should only be used on
    /// non-secret values.
    #[inline]
    fn try_const(t: T) -> Result<Self, Self::Error> {
        Self::try_classify(t)
    }
}

/// A trait for secret types that can extract a non-secret value
/// from a secret value. Note this effectively "leaks" the secret
/// value, but is necessary to actually do anything with it.
///
/// Note that Declassify types should NOT provide a From/Into implementation,
/// declassify should always be called explicitly
pub trait FromDeclassify<T>
where
    Self: Sized,
    <Self as FromDeclassify<T>>::Error: Debug
{
    type Error;

    #[inline]
    fn from_declassify(t: T) -> Self {
        Self::try_from_declassify(t).unwrap()
    }

    fn try_from_declassify(t: T) -> Result<Self, Self::Error>;
}

/// A trait for secret types that can wrap a non-secret value
/// as a secret value, as little-endian bytes
pub trait ClassifyLeBytes<T>
where
    Self: Sized
{
    fn classify_le_bytes(t: T) -> Self;

    /// An optional way to hint to the secret type that the underlying
    /// value is not actually secret. This should only be used on
    /// non-secret values.
    #[inline]
    fn const_le_bytes(t: T) -> Self {
        Self::classify_le_bytes(t)
    }
}

/// A trait for secret types that can try to wrap a non-secret value
/// as a secret value, as little-endian bytes
pub trait TryClassifyLeBytes<T>
where
    Self: Sized
{
    type Error;

    fn try_classify_le_bytes(t: T) -> Result<Self, Self::Error>;

    /// An optional way to hint to the secret type that the underlying
    /// value is not actually secret. This should only be used on
    /// non-secret values.
    #[inline]
    fn try_const_le_bytes(t: T) -> Result<Self, Self::Error> {
        Self::try_classify_le_bytes(t)
    }
}

/// A trait for secret types that can extract a non-secret value
/// from a secret value. Note this effectively "leaks" the secret
/// value, but is necessary to actually do anything with it.
///
/// Note that Declassify types should NOT provide a From/Into implementation,
/// declassify should always be called explicitly
pub trait FromDeclassifyLeBytes<T>
where
    Self: Sized,
    <Self as FromDeclassifyLeBytes<T>>::Error: Debug
{
    type Error;

    #[inline]
    fn from_declassify_le_bytes(t: T) -> Self {
        Self::try_from_declassify_le_bytes(t).unwrap()
    }

    fn try_from_declassify_le_bytes(t: T) -> Result<Self, Self::Error>;
}

/// A trait for secret types that can wrap a non-secret value
/// as a secret value, as big-endian bytes
pub trait ClassifyBeBytes<T>
where
    Self: Sized
{
    fn classify_be_bytes(t: T) -> Self;

    /// An optional way to hint to the secret type that the underlying
    /// value is not actually secret. This should only be used on
    /// non-secret values.
    #[inline]
    fn const_be_bytes(t: T) -> Self {
        Self::classify_be_bytes(t)
    }
}

/// A trait for secret types that can try to wrap a non-secret value
/// as a secret value, as big-endian bytes
pub trait TryClassifyBeBytes<T>
where
    Self: Sized
{
    type Error;

    fn try_classify_be_bytes(t: T) -> Result<Self, Self::Error>;

    /// An optional way to hint to the secret type that the underlying
    /// value is not actually secret. This should only be used on
    /// non-secret values.
    #[inline]
    fn try_const_be_bytes(t: T) -> Result<Self, Self::Error> {
        Self::try_classify_be_bytes(t)
    }
}

/// A trait for secret types that can extract a non-secret value
/// from a secret value. Note this effectively "leaks" the secret
/// value, but is necessary to actually do anything with it.
///
/// Note that Declassify types should NOT provide a From/Into implementation,
/// declassify should always be called explicitly
pub trait FromDeclassifyBeBytes<T>
where
    Self: Sized,
    <Self as FromDeclassifyBeBytes<T>>::Error: Debug
{
    type Error;

    #[inline]
    fn from_declassify_be_bytes(t: T) -> Self {
        Self::try_from_declassify_be_bytes(t).unwrap()
    }

    fn try_from_declassify_be_bytes(t: T) -> Result<Self, Self::Error>;
}

/// A trait for secret types that can wrap a non-secret value
/// as a secret value, as native-endian bytes
pub trait ClassifyNeBytes<T>
where
    Self: Sized
{
    fn classify_ne_bytes(t: T) -> Self;

    /// An optional way to hint to the secret type that the underlying
    /// value is not actually secret. This should only be used on
    /// non-secret values.
    #[inline]
    fn const_ne_bytes(t: T) -> Self {
        Self::classify_ne_bytes(t)
    }
}

/// A trait for secret types that can try to wrap a non-secret value
/// as a secret value, as big-endian bytes
pub trait TryClassifyNeBytes<T>
where
    Self: Sized
{
    type Error;

    fn try_classify_ne_bytes(t: T) -> Result<Self, Self::Error>;

    /// An optional way to hint to the secret type that the underlying
    /// value is not actually secret. This should only be used on
    /// non-secret values.
    #[inline]
    fn try_const_ne_bytes(t: T) -> Result<Self, Self::Error> {
        Self::try_classify_ne_bytes(t)
    }
}

/// A trait for secret types that can extract a non-secret value
/// from a secret value. Note this effectively "leaks" the secret
/// value, but is necessary to actually do anything with it.
///
/// Note that Declassify types should NOT provide a From/Into implementation,
/// declassify should always be called explicitly
pub trait FromDeclassifyNeBytes<T>
where
    Self: Sized,
    <Self as FromDeclassifyNeBytes<T>>::Error: Debug
{
    type Error;

    #[inline]
    fn from_declassify_ne_bytes(t: T) -> Self {
        Self::try_from_declassify_ne_bytes(t).unwrap()
    }

    fn try_from_declassify_ne_bytes(t: T) -> Result<Self, Self::Error>;
}

/// Blanket implementation for native-endian classify
impl<T, U> ClassifyNeBytes<T> for U
where
    U: Sized + ClassifyLeBytes<T> + ClassifyBeBytes<T>
{
    #[cfg(target_endian="little")]
    #[inline]
    fn classify_ne_bytes(t: T) -> Self {
        Self::classify_le_bytes(t)
    }
    #[cfg(target_endian="big")]
    #[inline]
    fn classify_ne_bytes(t: T) -> Self {
        Self::classify_be_bytes(t)
    }

    #[cfg(target_endian="little")]
    #[inline]
    fn const_ne_bytes(t: T) -> Self {
        Self::const_le_bytes(t)
    }
    #[cfg(target_endian="big")]
    #[inline]
    fn const_ne_bytes(t: T) -> Self {
        Self::const_be_bytes(t)
    }
}

/// Blanket implementation for native-endian try_classify
impl<T, U> TryClassifyNeBytes<T> for U
where
    U: Sized + TryClassifyLeBytes<T> + TryClassifyBeBytes<T>
{
    #[cfg(target_endian="little")]
    type Error = <Self as TryClassifyLeBytes<T>>::Error;
    #[cfg(target_endian="big")]
    type Error = <Self as TryClassifyBeBytes<T>>::Error;

    #[cfg(target_endian="little")]
    #[inline]
    fn try_classify_ne_bytes(t: T) -> Result<Self, Self::Error> {
        Self::try_classify_le_bytes(t)
    }
    #[cfg(target_endian="big")]
    #[inline]
    fn try_classify_ne_bytes(t: T) -> Result<Self, Self::Error> {
        Self::try_classify_be_bytes(t)
    }

    #[cfg(target_endian="little")]
    #[inline]
    fn try_const_ne_bytes(t: T) -> Result<Self, Self::Error> {
        Self::try_const_le_bytes(t)
    }
    #[cfg(target_endian="big")]
    #[inline]
    fn try_const_ne_bytes(t: T) -> Result<Self, Self::Error> {
        Self::try_const_be_bytes(t)
    }
}

/// Blanket implementation for native-endian declassify
impl<T, U> FromDeclassifyNeBytes<T> for U
where
    U: Sized + FromDeclassifyLeBytes<T> + FromDeclassifyBeBytes<T>
{
    #[cfg(target_endian="little")]
    type Error = <Self as FromDeclassifyLeBytes<T>>::Error;
    #[cfg(target_endian="big")]
    type Error = <Self as FromDeclassifyBeBytes<T>>::Error;

    #[cfg(target_endian="little")]
    #[inline]
    fn try_from_declassify_ne_bytes(t: T) -> Result<Self, Self::Error> {
        Self::try_from_declassify_le_bytes(t)
    }
    #[cfg(target_endian="big")]
    #[inline]
    fn try_from_declassify_ne_bytes(t: T) -> Result<Self, Self::Error> {
        Self::try_from_declassify_be_bytes(t)
    }
}


/// A trait that capture potentially-truncating conversions
///
/// This is equivalent to the "as" keyword used on integer types normally
pub trait FromCast<T> {
    fn from_cast(t: T) -> Self;
}

/// FromCast implemented for all types that support From
impl<T, U> FromCast<U> for T
where
    T: From<U>,
{
    #[inline]
    fn from_cast(u: U) -> T {
        T::from(u)
    }
}

/// Cast is the equivalent of Into, but for FromCast
pub trait Cast<T> {
    fn cast(self) -> T;
}

/// Cast implemented for all types that support FromCast
impl<T, U> Cast<T> for U
where
    T: FromCast<U>
{
    #[inline]
    fn cast(self) -> T {
        T::from_cast(self)
    }
}

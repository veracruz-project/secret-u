//! Traits implemented by secret types

use secret_u_opcode::Error;
use std::borrow::Cow;


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
    fn eval(&self) -> Self {
        self.try_eval().unwrap()
    }

    /// Same as eval but propagating internal VM errors
    fn try_eval(&self) -> Result<Self, Error>;
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

    /// Get internal tree, we can do this without worry
    /// since we internally ensure the value is only ever zeros or ones
    fn tree<'a>(&'a self) -> Cow<'a, Self::Tree>;
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

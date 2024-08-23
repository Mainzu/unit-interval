#![deny(missing_docs)]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(rustdoc::invalid_rust_codeblocks)]
#![deny(rustdoc::missing_crate_level_docs)]
#![warn(rustdoc::invalid_codeblock_attributes)]
//! A small crate for working with numbers in the unit interval.
//!
//! This crate currently only provides the [`UnitInterval`] type, which represents a number
//! constrained to the closed interval between 0 and 1, inclusive. It offers
//! operations, bounds checking, and utilities for working with
//! values in this range.
//!
//! ## Quick Start
//!
//! To get started, create a `UnitInterval` using one of the many constructor methods:
//!
//! ```rust
//! use unit_interval::UnitInterval;
//!
//! // Create a UnitInterval, panics if out of bounds
//! let a = UnitInterval::new(0.5);
//!
//! // Create a UnitInterval, returns a Result
//! let b = UnitInterval::new_checked(0.75).unwrap();
//!
//! // Create a UnitInterval, clamping the value to [0, 1]
//! let c = UnitInterval::new_clamped(1.5);
//! assert_eq!(c.into_inner(), 1.0);
//! ```
//!
//! Perform operations on `UnitInterval` values:
//!
//! ```rust
//! use unit_interval::UnitInterval;
//!
//! let a = UnitInterval::new(0.3);
//! let b = UnitInterval::new(0.5);
//!
//! // Multiplication always stays within [0, 1]
//! let product = a * b;
//! assert_eq!(product.into_inner(), 0.15);
//!
//! // Other operations may need checking or clamping
//! let sum = a.checked_add(b).unwrap();
//! let difference = a.clamped_sub(b);
//! ```

use core::borrow::Borrow;
use core::error;
use core::fmt::{self, Debug, Display};
use core::ops::{Add, Div, Mul, Sub};

use num_traits::{float::FloatCore, One, Zero};

/// A number in the closed [unit interval](https://en.wikipedia.org/wiki/Unit_interval) \[0, 1\]
///
/// The precise invariant is that for an underlying value `v` of type `T` is
/// `T::zero() <= v` and `v <= T::one()` where [`Zero`] and [`One`] are traits
/// from from the [num-traits] crate.
///
/// Unlike [`NonZero`](core::num::NonZero) types, this type does not reserve any bit-patterns
/// and simply guarantee that the value inside will not exceed the bounds via construction.
/// Unsoundly constructing a value of this type that exceed its bounds will not result in immediate
/// undefined behavior.
///
/// # Examples
/// ```
/// use unit_interval::UnitInterval;
///
/// let full = UnitInterval::one();
/// let half = UnitInterval::new(0.5);
///
/// assert_eq!(full + half, 1.5);
/// assert_eq!(half - full, -0.5);
/// assert_eq!(half * full, UnitInterval::new(0.5));
/// assert_eq!(full / half, 2.0);
///
/// assert_eq!(full.into_inner(), 1.0);
/// assert_eq!(half.into_inner(), 0.5);
/// ```
///
/// [`num-traits`]: https://crates.io/crates/num-traits
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct UnitInterval<T>(T);

/// An error type representing a value that falls outside the closed unit interval \[0, 1\]
///
/// This type is returned by operations that may produce values outside the unit interval,
/// providing information about how the value exceeds the bounds.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct BoundError<T> {
    kind: BoundErrorKind,
    val: T,
}
impl<T> BoundError<T> {
    #[inline]
    const fn new(kind: BoundErrorKind, val: T) -> Self {
        Self { kind, val }
    }
    #[inline]
    const fn less_than_zero(val: T) -> Self {
        Self::new(BoundErrorKind::LessThanZero, val)
    }
    #[inline]
    const fn greater_than_one(val: T) -> Self {
        Self::new(BoundErrorKind::GreaterThanOne, val)
    }
    #[inline]
    const fn neither(val: T) -> Self {
        Self::new(BoundErrorKind::Neither, val)
    }

    /// The way in which the value is out of bounds.
    ///
    /// For more detail, see [BoundErrorKind].
    #[inline]
    pub const fn kind(&self) -> BoundErrorKind {
        self.kind
    }
    /// The value that caused the error.
    ///
    /// The same one used in the attempted creation of a [`UnitInterval`].
    #[inline]
    pub fn value(self) -> T {
        self.val
    }
}
impl<T: Debug> Debug for BoundError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            BoundErrorKind::LessThanZero => {
                write!(f, "{:?} compares less than 0", self.val)
            }
            BoundErrorKind::GreaterThanOne => {
                write!(f, "{:?} compares greater than 1", self.val)
            }
            BoundErrorKind::Neither => write!(
                f,
                "{:?} compares neither greater than or equal to 0 nor less than or equal to 1",
                self.val
            ),
        }
    }
}
impl<T: Display> Display for BoundError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            BoundErrorKind::LessThanZero => write!(f, "{} compares less than 0", self.val),
            BoundErrorKind::GreaterThanOne => {
                write!(f, "{} compares greater than 1", self.val)
            }
            BoundErrorKind::Neither => write!(
                f,
                "{} compares neither greater than or equal to 0 nor less than or equal to 1",
                self.val
            ),
        }
    }
}

impl<T: Debug + Display> error::Error for BoundError<T> {}

/// Describes how a value falls outside the closed unit interval [0, 1]
///
/// # Examples
/// ```
/// use unit_interval::{UnitInterval, BoundErrorKind};
///
/// let result = UnitInterval::new_checked(-0.5);
/// assert_eq!(result.unwrap_err().kind(), BoundErrorKind::LessThanZero);
///
/// let result = UnitInterval::new_checked(1.5);
/// assert_eq!(result.unwrap_err().kind(), BoundErrorKind::GreaterThanOne);
///
/// let result = UnitInterval::new_checked(f32::NAN);
/// assert_eq!(result.unwrap_err().kind(), BoundErrorKind::Neither);
/// ```

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoundErrorKind {
    /// The value is less than both 0 and 1
    ///
    /// When `T::zero() <= val` is false but `val <= T::one()` is true.
    LessThanZero,
    /// The value is greater than both 0 and 1
    ///
    /// When `T::zero() <= val` is true but `val <= T::one()` is false.
    GreaterThanOne,
    /// The value is neither greater than or equal to 0 nor less than or equal to 1
    ///
    /// When both `T::zero() <= val` and `val <= T::one()` are false.
    ///
    /// This can mean 2 things:
    /// 1. The value is [NaN]-like
    /// 2. The comparison operations ([`PartialOrd`]) or [`Zero`] or [`One`]
    ///     are incorrectly implemented for the type of the value
    ///
    /// [NaN]: https://en.wikipedia.org/wiki/NaN#Comparison_with_NaN
    Neither,
}

impl<T: Zero + One + PartialOrd> UnitInterval<T> {
    /// Guarantee the number in the closed unit interval if
    /// `T::zero() <= val` and `val <= T::one()`, else returns an error
    /// detailing which bound was crossed.
    #[inline]
    pub fn new_checked(val: T) -> Result<Self, BoundError<T>> {
        match (T::zero() <= val, val <= T::one()) {
            (true, true) => Ok(Self(val)),
            (true, false) => Err(BoundError::greater_than_one(val)),
            (false, true) => Err(BoundError::less_than_zero(val)),
            (false, false) => Err(BoundError::neither(val)),
        }
    }
    /// Guarantee the number in the closed unit interval, clamping the value
    /// if it exceed the bounds in either direction.
    ///
    /// # Panics
    /// Panics if the value exceed the bounds in both direction
    /// (see [`BoundErrorKind::Neither`]).
    ///
    /// # Examples
    /// ```
    /// use unit_interval::UnitInterval;
    ///
    /// assert_eq!(UnitInterval::new_clamped(2).into_inner(), 1);
    /// assert_eq!(UnitInterval::new_clamped(-5).into_inner(), 0);
    /// ```
    ///
    /// NaN is an example of when this function panics
    /// ```should_panic
    /// use unit_interval::UnitInterval;
    ///
    /// let _ = UnitInterval::new_clamped(f32::NAN);
    /// ```
    #[inline]
    #[must_use]
    pub fn new_clamped(val: T) -> Self {
        let zero = T::zero();
        let one = T::one();
        match (zero <= val, val <= one) {
            (true, true) => Self(val),
            (true, false) => Self(one),
            (false, true) => Self(zero),
            (false, false) => panic!("Value must compare greater equal to 0 OR less equal to 1"),
        }
    }
    /// Guarantee the number in the closed unit interval, panicking if not.
    ///
    /// # Panics
    /// Panics if the number is not within the unit interval.
    #[inline]
    #[must_use]
    pub fn new(val: T) -> Self
    where
        T: Debug,
    {
        Self::new_checked(val).expect("Value must be in the interval [0, 1]")
    }
}
impl<T: FloatCore> UnitInterval<T> {
    /// Guarantee the number in the closed unit interval by taking only
    /// its fractional part.
    ///
    /// This cannot fail as the fractional part of a number is off the range [0, 1),
    /// which is a subset of \[0, 1\].
    #[inline]
    #[must_use]
    pub fn new_fract(val: T) -> Self {
        Self(val.fract())
    }
}
impl<T> UnitInterval<T> {
    /// Assumes that the number is in the closed unit interval.
    ///
    /// # Safety
    /// Improper usage of this function should only lead to logic error and not undefined behavior
    /// as long as no further unsafe code rely on the guarantee granted by this type.
    #[inline]
    #[must_use]
    pub const unsafe fn new_unchecked(val: T) -> Self {
        Self(val)
    }

    /// Returns a reference to the inner value.
    #[inline]
    pub const fn as_inner(&self) -> &T {
        &self.0
    }
    /// Consumes the `UnitInterval` and returns the inner value.
    #[inline]
    pub fn into_inner(self) -> T {
        self.0
    }
}
impl<T: Zero> UnitInterval<T> {
    /// Creates a new `UnitInterval` with a value of zero.
    ///
    /// # Examples
    /// ```
    /// use unit_interval::UnitInterval;
    ///
    /// let zero = UnitInterval::<f32>::zero();
    /// assert_eq!(zero.into_inner(), 0.0);
    /// ```
    #[inline]
    pub fn zero() -> Self {
        Self(T::zero())
    }
}
impl<T: One> UnitInterval<T> {
    /// Creates a new `UnitInterval` with a value of one.
    ///
    /// # Examples
    /// ```
    /// use unit_interval::UnitInterval;
    ///
    /// let one = UnitInterval::<f32>::one();
    /// assert_eq!(one.into_inner(), 1.0);
    /// ```
    #[inline]
    pub fn one() -> Self {
        Self(T::one())
    }
    /// Returns the complement of the currently held value.
    ///
    /// # Examples
    /// ```
    /// use unit_interval::UnitInterval;
    ///
    /// let a = UnitInterval::new(0.2);
    /// assert_eq!(a.complement(), UnitInterval::new(0.8));
    /// ```
    #[inline]
    pub fn complement(self) -> UnitInterval<<T as Sub>::Output>
    where
        T: Sub,
    {
        UnitInterval(T::one() - self.0)
    }
}

impl<T: Add> UnitInterval<T>
where
    T::Output: Zero + One + PartialOrd,
{
    /// Adds a value inside the close unit interval to produce another.
    ///
    /// Equivalent to adding the inner values then using [`UnitInterval::new_checked`].
    ///
    /// # Examples
    /// ```
    /// use unit_interval::{UnitInterval, BoundErrorKind};
    ///
    /// let a = UnitInterval::new(0.5);
    /// let b = UnitInterval::new(0.75);
    /// let result = a.checked_add(b);
    /// assert_eq!(result, UnitInterval::new_checked(0.5 + 0.75));
    /// let err = result.unwrap_err();
    /// assert_eq!(err.kind(), BoundErrorKind::GreaterThanOne);
    /// assert_eq!(err.value(), 1.25);
    /// ```
    #[inline]
    pub fn checked_add(self, rhs: Self) -> Result<UnitInterval<T::Output>, BoundError<T::Output>> {
        UnitInterval::new_checked(self.0 + rhs.0)
    }
    /// Adds two `UnitInterval` values, clamping the result to the unit interval.
    ///
    /// # Examples
    /// ```
    /// use unit_interval::UnitInterval;
    ///
    /// let a = UnitInterval::new(0.7);
    /// let b = UnitInterval::new(0.6);
    /// let result = a.clamped_add(b);
    /// assert_eq!(result.into_inner(), 1.0);
    /// ```
    #[inline]
    pub fn clamped_add(self, rhs: Self) -> UnitInterval<T::Output> {
        UnitInterval::new_clamped(self.0 + rhs.0)
    }
}
impl<T: Sub> UnitInterval<T>
where
    T::Output: Zero + One + PartialOrd,
{
    /// Subtracts a value inside the close unit interval to produce another.
    ///
    /// Equivalent to subtracting the inner values then using [`UnitInterval::new_checked`].
    ///
    /// # Examples
    /// ```
    /// use unit_interval::{UnitInterval, BoundErrorKind};
    ///
    /// let a = UnitInterval::new(0.4);
    /// let b = UnitInterval::new(0.8);
    /// let result = a.checked_sub(b);
    /// assert_eq!(result, UnitInterval::new_checked(0.4 - 0.8));
    /// let err = result.unwrap_err();
    /// assert_eq!(err.kind(), BoundErrorKind::LessThanZero);
    /// assert_eq!(err.value(), -0.4);
    /// ```
    #[inline]
    pub fn checked_sub(self, rhs: Self) -> Result<UnitInterval<T::Output>, BoundError<T::Output>> {
        UnitInterval::new_checked(self.0 - rhs.0)
    }
    /// Subtracts one `UnitInterval` from another, clamping the result to the unit interval.
    ///
    /// # Examples
    /// ```
    /// use unit_interval::UnitInterval;
    ///
    /// let a = UnitInterval::new(0.3);
    /// let b = UnitInterval::new(0.6);
    /// let result = a.clamped_sub(b);
    /// assert_eq!(result.into_inner(), 0.0);
    /// ```
    #[inline]
    pub fn clamped_sub(self, rhs: Self) -> UnitInterval<T::Output> {
        UnitInterval::new_clamped(self.0 - rhs.0)
    }
}
impl<T: Mul> UnitInterval<T>
where
    T::Output: Zero + One + PartialOrd,
{
    /// Multiplies a value inside the close unit interval to produce another.
    ///
    /// Equivalent to multiplying the inner values then using [`UnitInterval::new_checked`].
    ///
    /// Note: Multiplication of two values in [0, 1] always results in a value in [0, 1],
    /// so checking is not strictly necessary for this operation.
    ///
    /// # Examples
    /// ```
    /// use unit_interval::UnitInterval;
    ///
    /// let a = UnitInterval::new(0.5);
    /// let b = UnitInterval::new(0.6);
    /// let result = a.checked_mul(b);
    /// assert_eq!(result, UnitInterval::new_checked(0.5 * 0.6));
    /// let ok = result.unwrap();
    /// assert_eq!(ok.into_inner(), 0.3);
    /// ```
    #[inline]
    pub fn checked_mul(self, rhs: Self) -> Result<UnitInterval<T::Output>, BoundError<T::Output>> {
        UnitInterval::new_checked(self.0 * rhs.0)
    }
    /// Multiplies two `UnitInterval` values, clamping the result to the unit interval.
    ///
    /// Note: Multiplication of two values in [0, 1] always results in a value in [0, 1],
    /// so clamping is not strictly necessary for this operation.
    ///
    /// # Examples
    /// ```
    /// use unit_interval::UnitInterval;
    ///
    /// let a = UnitInterval::new(0.5);
    /// let b = UnitInterval::new(0.6);
    /// let result = a.clamped_mul(b);
    /// assert_eq!(result.into_inner(), 0.3);
    /// ```
    #[inline]
    pub fn clamped_mul(self, rhs: Self) -> UnitInterval<T::Output> {
        UnitInterval::new_clamped(self.0 * rhs.0)
    }
}
impl<T: Div> UnitInterval<T>
where
    T::Output: Zero + One + PartialOrd,
{
    /// Divides a value inside the close unit interval to produce another.
    ///
    /// Equivalent to dividing the inner values then using [`UnitInterval::new_checked`].
    ///
    /// # Examples
    /// ```
    /// use unit_interval::{UnitInterval, BoundErrorKind};
    ///
    /// let a = UnitInterval::new(0.8);
    /// let b = UnitInterval::new(0.4);
    /// let result = a.checked_div(b);
    /// assert_eq!(result, UnitInterval::new_checked(0.8 / 0.4));
    /// let err = result.unwrap_err();
    /// assert_eq!(err.kind(), BoundErrorKind::GreaterThanOne);
    /// assert_eq!(err.value(), 2.0);
    /// ```
    #[inline]
    pub fn checked_div(self, rhs: Self) -> Result<UnitInterval<T::Output>, BoundError<T::Output>> {
        UnitInterval::new_checked(self.0 / rhs.0)
    }
    /// Divides one `UnitInterval` by another, clamping the result to the unit interval.
    ///
    /// # Examples
    /// ```
    /// use unit_interval::UnitInterval;
    ///
    /// let a = UnitInterval::new(0.8);
    /// let b = UnitInterval::new(0.4);
    /// let result = a.clamped_div(b);
    /// assert_eq!(result.into_inner(), 1.0);
    /// ```
    #[inline]
    pub fn clamped_div(self, rhs: Self) -> UnitInterval<T::Output> {
        UnitInterval::new_clamped(self.0 / rhs.0)
    }
}

impl<T: One> One for UnitInterval<T> {
    #[inline]
    fn one() -> Self {
        UnitInterval::one()
    }
}

impl<T: Add> Add<T> for UnitInterval<T> {
    type Output = T::Output;

    #[inline]
    fn add(self, rhs: T) -> Self::Output {
        self.0 + rhs
    }
}
impl<T: Sub> Sub<T> for UnitInterval<T> {
    type Output = T::Output;

    #[inline]
    fn sub(self, rhs: T) -> Self::Output {
        self.0 - rhs
    }
}
impl<T: Mul> Mul<T> for UnitInterval<T> {
    type Output = T::Output;

    #[inline]
    fn mul(self, rhs: T) -> Self::Output {
        self.0 * rhs
    }
}
impl<T: Div> Div<T> for UnitInterval<T> {
    type Output = T::Output;

    #[inline]
    fn div(self, rhs: T) -> Self::Output {
        self.0 / rhs
    }
}

impl<T: Add> Add for UnitInterval<T> {
    type Output = T::Output;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        self.0 + rhs.0
    }
}
impl<T: Sub> Sub for UnitInterval<T> {
    type Output = T::Output;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        self.0 - rhs.0
    }
}
impl<T: Mul> Mul for UnitInterval<T> {
    type Output = UnitInterval<T::Output>;

    #[inline]
    fn mul(self, rhs: UnitInterval<T>) -> Self::Output {
        UnitInterval(self.0 * rhs.0)
    }
}
impl<T: Div> Div for UnitInterval<T> {
    type Output = T::Output;

    #[inline]
    fn div(self, rhs: Self) -> Self::Output {
        self.0 / rhs.0
    }
}

impl<T> AsRef<T> for UnitInterval<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        self.as_inner()
    }
}
impl<T> Borrow<T> for UnitInterval<T> {
    #[inline]
    fn borrow(&self) -> &T {
        self.as_inner()
    }
}

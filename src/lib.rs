//! `no_std` array helpers available without nightly.
//!
//! ## Description
//!
//! Many useful array and slice methods are currently gated by nightly
//! features, though their general functionality and interface is essentially
//! stable. As such this crate provides stable alternatives to the following
//! features, often the same underlying implementation as the current nightly
//! version:
//!
//! - [`array_try_from_fn`]
//! - [`array_try_map`]
//! - [`array_chunks`]
//! - [`slice_as_chunks`]
//! - [`slice_flatten`]
//!
//! ## Usage
//!
//! Users can either import an `Ext` trait (`SliceExt`, `ArrayExt`, or
//! `SliceOfArrayExt`) traits to bring in the desired methods, or use the bare
//! functions. Note that trait methods have the `_ext` suffix to avoid
//! collision with the core library methods.
//!
//! ```
//! use array_util::ArrayExt;
//!
//! let a = ["1", "2", "3"];
//! let b = a.try_map_ext(|v| v.parse::<u32>()).unwrap().map(|v| v + 1);
//! assert_eq!(b, [2, 3, 4]);
//!
//! let a = ["1", "2a", "3"];
//! let b = a.try_map_ext(|v| v.parse::<u32>());
//! assert!(b.is_err());
//! ```
//!
//! ```
//! let a = ["1", "2", "3"];
//! let b = array_util::try_map(a, |v| v.parse::<u32>()).unwrap().map(|v| v + 1);
//! assert_eq!(b, [2, 3, 4]);
//!
//! let a = ["1", "2a", "3"];
//! let b = array_util::try_map(a, |v| v.parse::<u32>());
//! assert!(b.is_err());
//! ```
//!
//! ## Limitations
//!
//! These functions aren't stabilized because they rely on undecided behaviors.
//! For example, "should compile-time errors be generated for `0` length
//! arrays?" or "What should the associated types and traits of `Try` be?". As
//! these questions remain unresolved, reliance on the particular answers
//! this crate has chosen in it's implementation may make porting to the
//! eventual stabilized version more painful. If you're just calling functions,
//! you'll probably be fine, but try to avoid using the `Ext` traits as bounds.
//!  
//! [`array_try_from_fn`]: https://github.com/rust-lang/rust/issues/89379
//! [`array_try_map`]: https://github.com/rust-lang/rust/issues/79711
//! [`array_chunks`]: https://github.com/rust-lang/rust/issues/74985
//! [`slice_as_chunks`]: https://github.com/rust-lang/rust/issues/74985
//! [`slice_flatten`]: https://github.com/rust-lang/rust/issues/95629
#![no_std]
#![warn(missing_docs)]

use core::{array, iter::FusedIterator, mem::size_of, ops::ControlFlow, slice};

use arrayvec::ArrayVec;

#[doc(hidden)]
mod try_helper;

use try_helper::*;

/// A fallible function `f` applied to each element on array `self` in order to
/// return an array the same size as `self` or the first error encountered.
///
/// The return type of this function depends on the return type of the closure.
/// If you return `Result<T, E>` from the closure, you'll get a `Result<[T; N], E>`.
/// If you return `Option<T>` from the closure, you'll get an `Option<[T; N]>`.
///
/// # Examples
///
/// ```
/// let a = ["1", "2", "3"];
/// let b = array_util::try_map(a, |v| v.parse::<u32>()).unwrap().map(|v| v + 1);
/// assert_eq!(b, [2, 3, 4]);
///
/// let a = ["1", "2a", "3"];
/// let b = array_util::try_map(a, |v| v.parse::<u32>());
/// assert!(b.is_err());
///
/// use std::num::NonZeroU32;
/// let z = [1, 2, 0, 3, 4];
/// assert_eq!(array_util::try_map(z, NonZeroU32::new), None);
/// let a = [1, 2, 3];
/// let b = array_util::try_map(a, NonZeroU32::new);
/// let c = b.map(|x| x.map(NonZeroU32::get));
/// assert_eq!(c, Some(a));
/// ```
pub fn try_map<T, const N: usize, F, R>(
    vals: [T; N],
    mut f: F,
) -> <<R as Try>::Residual as Residual<[<R as Try>::Output; N]>>::TryType
where
    F: FnMut(T) -> R,
    R: Try,
    <R as Try>::Residual: Residual<[<R as Try>::Output; N]>,
{
    let mut output = ArrayVec::new();
    for val in vals {
        match f(val).branch() {
            ControlFlow::Break(b) => return FromResidual::from_residual(b),

            // SAFETY: `val` is len N and `output` has capacity N
            ControlFlow::Continue(c) => unsafe { output.push_unchecked(c) },
        }
    }
    // SAFETY: `output` can only be len N if we got here
    unsafe { Try::from_output(output.into_inner_unchecked()) }
}

/// Creates an array `[T; N]` where each fallible array element `T` is returned by the `cb` call.
/// Unlike [`from_fn`], where the element creation can't fail, this version will return an error
/// if any element creation was unsuccessful.
///
/// The return type of this function depends on the return type of the closure.
/// If you return `Result<T, E>` from the closure, you'll get a `Result<[T; N], E>`.
/// If you return `Option<T>` from the closure, you'll get an `Option<[T; N]>`.
///
/// # Arguments
///
/// * `cb`: Callback where the passed argument is the current array index.
///
/// # Example
///
/// ```rust
/// # use core::convert::TryInto;
/// let array: Result<[u8; 5], _> = array_util::try_from_fn(|i| i.try_into());
/// assert_eq!(array, Ok([0, 1, 2, 3, 4]));
///
/// let array: Result<[i8; 200], _> = array_util::try_from_fn(|i| i.try_into());
/// assert!(array.is_err());
///
/// let array: Option<[_; 4]> = array_util::try_from_fn(|i| i.checked_add(100));
/// assert_eq!(array, Some([100, 101, 102, 103]));
///
/// let array: Option<[_; 4]> = array_util::try_from_fn(|i| i.checked_sub(100));
/// assert_eq!(array, None);
/// ```
///
/// [`from_fn`]: core::array::from_fn
#[inline]
pub fn try_from_fn<R, const N: usize, F>(
    cb: F,
) -> <<R as Try>::Residual as Residual<[R::Output; N]>>::TryType
where
    F: FnMut(usize) -> R,
    R: Try,
    R::Residual: Residual<[R::Output; N]>,
{
    try_map(array::from_fn(|i| i), cb)
}

/// An iterator over a slice in (non-overlapping) chunks (`N` elements at a
/// time), starting at the beginning of the slice.
///
/// When the slice len is not evenly divided by the chunk size, the last
/// up to `N-1` elements will be omitted but can be retrieved from
/// the [`remainder`] function from the iterator.
///
/// This struct is created by the [`array_chunks`] method on [slices].
///
/// # Example
///
/// ```
/// let slice = ['l', 'o', 'r', 'e', 'm'];
/// let iter = array_util::array_chunks::<_, 2>(&slice);
/// ```
///
/// [`remainder`]: ArrayChunks::remainder
/// [slices]: prim@slice
#[derive(Debug)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct ArrayChunks<'a, T: 'a, const N: usize> {
    iter: slice::Iter<'a, [T; N]>,
    rem: &'a [T],
}

impl<'a, T, const N: usize> ArrayChunks<'a, T, N> {
    #[inline]
    pub(crate) fn new(slice: &'a [T]) -> Self {
        let (array_slice, rem) = as_chunks(slice);
        Self {
            iter: array_slice.iter(),
            rem,
        }
    }

    /// Returns the remainder of the original slice that is not going to be
    /// returned by the iterator. The returned slice has at most `N-1`
    /// elements.
    #[must_use]
    pub fn remainder(&self) -> &'a [T] {
        self.rem
    }
}

impl<T, const N: usize> Clone for ArrayChunks<'_, T, N> {
    fn clone(&self) -> Self {
        ArrayChunks {
            iter: self.iter.clone(),
            rem: self.rem,
        }
    }
}

impl<'a, T, const N: usize> Iterator for ArrayChunks<'a, T, N> {
    type Item = &'a [T; N];

    #[inline]
    fn next(&mut self) -> Option<&'a [T; N]> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    #[inline]
    fn count(self) -> usize {
        self.iter.count()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.iter.nth(n)
    }

    #[inline]
    fn last(self) -> Option<Self::Item> {
        self.iter.last()
    }
}

impl<'a, T, const N: usize> DoubleEndedIterator for ArrayChunks<'a, T, N> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a [T; N]> {
        self.iter.next_back()
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.iter.nth_back(n)
    }
}

impl<T, const N: usize> ExactSizeIterator for ArrayChunks<'_, T, N> {}

impl<T, const N: usize> FusedIterator for ArrayChunks<'_, T, N> {}

/// Returns an iterator over `N` elements of the slice at a time, starting at the
/// beginning of the slice.
///
/// The chunks are array references and do not overlap. If `N` does not divide the
/// length of the slice, then the last up to `N-1` elements will be omitted and can be
/// retrieved from the `remainder` function of the iterator.
///
/// This method is the const generic equivalent of [`chunks_exact`].
///
/// # Panics
///
/// Panics if `N` is 0. This check will most probably get changed to a compile time
/// error before this method gets stabilized.
///
/// # Examples
///
/// ```
/// let slice = ['l', 'o', 'r', 'e', 'm'];
/// let mut iter = array_util::array_chunks(&slice);
/// assert_eq!(iter.next().unwrap(), &['l', 'o']);
/// assert_eq!(iter.next().unwrap(), &['r', 'e']);
/// assert!(iter.next().is_none());
/// assert_eq!(iter.remainder(), &['m']);
/// ```
///
/// [`chunks_exact`]: prim@slice#method.chunks_exact
#[inline]
pub fn array_chunks<T, const N: usize>(vals: &[T]) -> ArrayChunks<'_, T, N> {
    assert!(N != 0, "chunk size must be non-zero");
    ArrayChunks::new(vals)
}

/// An iterator over a slice in (non-overlapping) mutable chunks (`N` elements
/// at a time), starting at the beginning of the slice.
///
/// When the slice len is not evenly divided by the chunk size, the last
/// up to `N-1` elements will be omitted but can be retrieved from
/// the [`into_remainder`] function from the iterator.
///
/// This struct is created by the [`array_chunks_mut`] method on [slices].
///
/// # Example
///
/// ```
/// let mut slice = ['l', 'o', 'r', 'e', 'm'];
/// let iter = array_util::array_chunks_mut::<_, 2>(&mut slice);
/// ```
///
/// [`into_remainder`]: ArrayChunksMut::into_remainder
/// [slices]: prim@slice
#[derive(Debug)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct ArrayChunksMut<'a, T: 'a, const N: usize> {
    iter: slice::IterMut<'a, [T; N]>,
    rem: &'a mut [T],
}

impl<'a, T, const N: usize> ArrayChunksMut<'a, T, N> {
    #[inline]
    pub(crate) fn new(slice: &'a mut [T]) -> Self {
        let (array_slice, rem) = as_chunks_mut(slice);
        Self {
            iter: array_slice.iter_mut(),
            rem,
        }
    }

    /// Returns the remainder of the original slice that is not going to be
    /// returned by the iterator. The returned slice has at most `N-1`
    /// elements.
    #[must_use]
    pub fn into_remainder(self) -> &'a mut [T] {
        self.rem
    }
}

impl<'a, T, const N: usize> Iterator for ArrayChunksMut<'a, T, N> {
    type Item = &'a mut [T; N];

    #[inline]
    fn next(&mut self) -> Option<&'a mut [T; N]> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    #[inline]
    fn count(self) -> usize {
        self.iter.count()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.iter.nth(n)
    }

    #[inline]
    fn last(self) -> Option<Self::Item> {
        self.iter.last()
    }
}

impl<'a, T, const N: usize> DoubleEndedIterator for ArrayChunksMut<'a, T, N> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a mut [T; N]> {
        self.iter.next_back()
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.iter.nth_back(n)
    }
}

impl<T, const N: usize> ExactSizeIterator for ArrayChunksMut<'_, T, N> {}

impl<T, const N: usize> FusedIterator for ArrayChunksMut<'_, T, N> {}

/// Returns an iterator over `N` elements of the slice at a time, starting at the
/// beginning of the slice.
///
/// The chunks are mutable array references and do not overlap. If `N` does not divide
/// the length of the slice, then the last up to `N-1` elements will be omitted and
/// can be retrieved from the `into_remainder` function of the iterator.
///
/// This method is the const generic equivalent of [`chunks_exact_mut`].
///
/// # Panics
///
/// Panics if `N` is 0. This check will most probably get changed to a compile time
/// error before this method gets stabilized.
///
/// # Examples
///
/// ```
/// let v = &mut [0, 0, 0, 0, 0];
/// let mut count = 1;
///
/// for chunk in array_util::array_chunks_mut(v) {
///     *chunk = [count; 2];
///     count += 1;
/// }
/// assert_eq!(v, &[1, 1, 2, 2, 0]);
/// ```
///
/// [`chunks_exact_mut`]: prim@slice#method.chunks_exact_mut
#[inline]
pub fn array_chunks_mut<T, const N: usize>(vals: &mut [T]) -> ArrayChunksMut<'_, T, N> {
    assert!(N != 0, "chunk size must be non-zero");
    ArrayChunksMut::new(vals)
}

/// Splits the slice into a slice of `N`-element arrays,
/// starting at the beginning of the slice,
/// and a remainder slice with length strictly less than `N`.
///
/// # Panics
///
/// Panics if `N` is 0. This check will most probably get changed to a compile time
/// error before this method gets stabilized.
///
/// # Examples
///
/// ```
/// let slice = ['l', 'o', 'r', 'e', 'm'];
/// let (chunks, remainder) = array_util::as_chunks(&slice);
/// assert_eq!(chunks, &[['l', 'o'], ['r', 'e']]);
/// assert_eq!(remainder, &['m']);
/// ```
///
/// If you expect the slice to be an exact multiple, you can combine
/// `let`-`else` with an empty slice pattern:
/// ```
/// let slice = ['R', 'u', 's', 't'];
/// let (chunks, []) = array_util::as_chunks::<_, 2>(&slice) else {
///     panic!("slice didn't have even length")
/// };
/// assert_eq!(chunks, &[['R', 'u'], ['s', 't']]);
/// ```
#[inline]
#[must_use]
pub const fn as_chunks<T, const N: usize>(vals: &[T]) -> (&[[T; N]], &[T]) {
    assert!(N != 0, "chunk size must be non-zero");
    let len = vals.len() / N;
    let (multiple_of_n, remainder) = vals.split_at(len * N);
    // SAFETY: We already panicked for zero, and ensured by construction
    // that the length of the subslice is a multiple of N.
    let array_slice = unsafe { as_chunks_unchecked(multiple_of_n) };
    (array_slice, remainder)
}

/// Splits the slice into a slice of `N`-element arrays,
/// assuming that there's no remainder.
///
/// # Safety
///
/// This may only be called when
/// - The slice splits exactly into `N`-element chunks (aka `self.len() % N == 0`).
/// - `N != 0`.
///
/// # Examples
///
/// ```
/// let slice: &[char] = &['l', 'o', 'r', 'e', 'm', '!'];
/// let chunks: &[[char; 1]] =
///     // SAFETY: 1-element chunks never have remainder
///     unsafe { array_util::as_chunks_unchecked(&slice) };
/// assert_eq!(chunks, &[['l'], ['o'], ['r'], ['e'], ['m'], ['!']]);
/// let chunks: &[[char; 3]] =
///     // SAFETY: The slice length (6) is a multiple of 3
///     unsafe { array_util::as_chunks_unchecked(&slice) };
/// assert_eq!(chunks, &[['l', 'o', 'r'], ['e', 'm', '!']]);
///
/// // These would be unsound:
/// // let chunks: &[[_; 5]] = array_util::as_chunks_unchecked(slice) // The slice length is not a multiple of 5
/// // let chunks: &[[_; 0]] = array_util::as_chunks_unchecked(slice) // Zero-length chunks are never allowed
/// ```
#[inline]
#[must_use]
pub const unsafe fn as_chunks_unchecked<T, const N: usize>(vals: &[T]) -> &[[T; N]] {
    debug_assert!(
        N != 0 && vals.len() % N == 0,
        "slice::as_chunks_unchecked requires `N != 0` and the slice to split exactly into `N`-element chunks",
    );
    let new_len = vals.len() / N;
    // SAFETY: We cast a slice of `new_len * N` elements into
    // a slice of `new_len` many `N` elements chunks.
    unsafe { slice::from_raw_parts(vals.as_ptr().cast(), new_len) }
}

/// Splits the slice into a slice of `N`-element arrays,
/// starting at the beginning of the slice,
/// and a remainder slice with length strictly less than `N`.
///
/// # Panics
///
/// Panics if `N` is 0. This check will most probably get changed to a compile time
/// error before this method gets stabilized.
///
/// # Examples
///
/// ```
/// let v = &mut [0, 0, 0, 0, 0];
/// let mut count = 1;
///
/// let (chunks, remainder) = array_util::as_chunks_mut(v);
/// remainder[0] = 9;
/// for chunk in chunks {
///     *chunk = [count; 2];
///     count += 1;
/// }
/// assert_eq!(v, &[1, 1, 2, 2, 9]);
/// ```
#[inline]
#[must_use]
pub fn as_chunks_mut<T, const N: usize>(vals: &mut [T]) -> (&mut [[T; N]], &mut [T]) {
    assert!(N != 0, "chunk size must be non-zero");
    let len = vals.len() / N;
    let (multiple_of_n, remainder) = vals.split_at_mut(len * N);
    // SAFETY: We already panicked for zero, and ensured by construction
    // that the length of the subslice is a multiple of N.
    let array_slice = unsafe { as_chunks_unchecked_mut(multiple_of_n) };
    (array_slice, remainder)
}

/// Splits the slice into a slice of `N`-element arrays,
/// assuming that there's no remainder.
///
/// # Safety
///
/// This may only be called when
/// - The slice splits exactly into `N`-element chunks (aka `self.len() % N == 0`).
/// - `N != 0`.
///
/// # Examples
///
/// ```
/// let slice: &mut [char] = &mut ['l', 'o', 'r', 'e', 'm', '!'];
/// let chunks: &mut [[char; 1]] =
///     // SAFETY: 1-element chunks never have remainder
///     unsafe { array_util::as_chunks_unchecked_mut(slice) };
/// chunks[0] = ['L'];
/// assert_eq!(chunks, &[['L'], ['o'], ['r'], ['e'], ['m'], ['!']]);
/// let chunks: &mut [[char; 3]] =
///     // SAFETY: The slice length (6) is a multiple of 3
///     unsafe { array_util::as_chunks_unchecked_mut(slice) };
/// chunks[1] = ['a', 'x', '?'];
/// assert_eq!(slice, &['L', 'o', 'r', 'a', 'x', '?']);
///
/// // These would be unsound:
/// // let chunks: &[[_; 5]] = array_util::as_chunks_unchecked_mut(slice) // The slice length is not a multiple of 5
/// // let chunks: &[[_; 0]] = array_util::as_chunks_unchecked_mut(slice) // Zero-length chunks are never allowed
/// ```
#[inline]
#[must_use]
pub unsafe fn as_chunks_unchecked_mut<T, const N: usize>(vals: &mut [T]) -> &mut [[T; N]] {
    debug_assert!(
        N != 0 && vals.len() % N == 0,
        "slice::as_chunks_unchecked requires `N != 0` and the slice to split exactly into `N`-element chunks",
    );
    let new_len = vals.len() / N;
    // SAFETY: We cast a slice of `new_len * N` elements into
    // a slice of `new_len` many `N` elements chunks.
    unsafe { slice::from_raw_parts_mut(vals.as_mut_ptr().cast(), new_len) }
}

/// Splits the slice into a slice of `N`-element arrays,
/// starting at the end of the slice,
/// and a remainder slice with length strictly less than `N`.
///
/// # Panics
///
/// Panics if `N` is 0. This check will most probably get changed to a compile time
/// error before this method gets stabilized.
///
/// # Examples
///
/// ```
/// let slice = ['l', 'o', 'r', 'e', 'm'];
/// let (remainder, chunks) = array_util::as_rchunks(&slice);
/// assert_eq!(remainder, &['l']);
/// assert_eq!(chunks, &[['o', 'r'], ['e', 'm']]);
/// ```
#[inline]
#[must_use]
pub const fn as_rchunks<T, const N: usize>(vals: &[T]) -> (&[T], &[[T; N]]) {
    assert!(N != 0, "chunk size must be non-zero");
    let len = vals.len() / N;
    let (remainder, multiple_of_n) = vals.split_at(vals.len() - len * N);
    // SAFETY: We already panicked for zero, and ensured by construction
    // that the length of the subslice is a multiple of N.
    let array_slice = unsafe { as_chunks_unchecked(multiple_of_n) };
    (remainder, array_slice)
}

/// Splits the slice into a slice of `N`-element arrays,
/// starting at the end of the slice,
/// and a remainder slice with length strictly less than `N`.
///
/// # Panics
///
/// Panics if `N` is 0. This check will most probably get changed to a compile time
/// error before this method gets stabilized.
///
/// # Examples
///
/// ```
/// let v = &mut [0, 0, 0, 0, 0];
/// let mut count = 1;
///
/// let (remainder, chunks) = array_util::as_rchunks_mut(v);
/// remainder[0] = 9;
/// for chunk in chunks {
///     *chunk = [count; 2];
///     count += 1;
/// }
/// assert_eq!(v, &[9, 1, 1, 2, 2]);
/// ```
#[inline]
#[must_use]
pub fn as_rchunks_mut<T, const N: usize>(vals: &mut [T]) -> (&mut [T], &mut [[T; N]]) {
    assert!(N != 0, "chunk size must be non-zero");
    let len = vals.len() / N;
    let (remainder, multiple_of_n) = vals.split_at_mut(vals.len() - len * N);
    // SAFETY: We already panicked for zero, and ensured by construction
    // that the length of the subslice is a multiple of N.
    let array_slice = unsafe { as_chunks_unchecked_mut(multiple_of_n) };
    (remainder, array_slice)
}

/// Takes a `&[[T; N]]`, and flattens it to a `&[T]`.
///
/// # Panics
///
/// This panics if the length of the resulting slice would overflow a `usize`.
///
/// This is only possible when flattening a slice of arrays of zero-sized
/// types, and thus tends to be irrelevant in practice. If
/// `size_of::<T>() > 0`, this will never panic.
///
/// # Examples
///
/// ```
/// assert_eq!(array_util::flatten(&[[1, 2, 3], [4, 5, 6]]), &[1, 2, 3, 4, 5, 6]);
///
/// assert_eq!(
///     array_util::flatten(&[[1, 2, 3], [4, 5, 6]]),
///     array_util::flatten(&[[1, 2], [3, 4], [5, 6]]),
/// );
///
/// let slice_of_empty_arrays: &[[i32; 0]] = &[[], [], [], [], []];
/// assert!(array_util::flatten(&slice_of_empty_arrays).is_empty());
///
/// let empty_slice_of_arrays: &[[u32; 10]] = &[];
/// assert!(array_util::flatten(&empty_slice_of_arrays).is_empty());
/// ```
pub const fn flatten<T, const N: usize>(vals: &[[T; N]]) -> &[T] {
    let len = if size_of::<T>() == 0 {
        match vals.len().checked_mul(N) {
            Some(v) => v,
            None => panic!("slice len overflow"),
        }
    } else {
        vals.len() * N
    };
    // SAFETY: `[T]` is layout-identical to `[T; N]`
    unsafe { slice::from_raw_parts(vals.as_ptr().cast(), len) }
}

/// Takes a `&mut [[T; N]]`, and flattens it to a `&mut [T]`.
///
/// # Panics
///
/// This panics if the length of the resulting slice would overflow a `usize`.
///
/// This is only possible when flattening a slice of arrays of zero-sized
/// types, and thus tends to be irrelevant in practice. If
/// `size_of::<T>() > 0`, this will never panic.
///
/// # Examples
///
/// ```
/// fn add_5_to_all(slice: &mut [i32]) {
///     for i in slice {
///         *i += 5;
///     }
/// }
///
/// let mut array = [[1, 2, 3], [4, 5, 6], [7, 8, 9]];
/// add_5_to_all(array_util::flatten_mut(&mut array));
/// assert_eq!(array, [[6, 7, 8], [9, 10, 11], [12, 13, 14]]);
/// ```
pub fn flatten_mut<T, const N: usize>(vals: &mut [[T; N]]) -> &mut [T] {
    let len = if size_of::<T>() == 0 {
        vals.len().checked_mul(N).expect("slice len overflow")
    } else {
        vals.len() * N
    };
    // SAFETY: `[T]` is layout-identical to `[T; N]`
    unsafe { slice::from_raw_parts_mut(vals.as_mut_ptr().cast(), len) }
}

/// A helper extension trait for arrays
pub trait ArrayExt {
    #[doc(hidden)]
    type T;
    #[doc(hidden)]
    type TN<U>: ArrayExt<T = U, TN<Self::T> = Self>;

    /// A fallible function `f` applied to each element on array `self` in order to
    /// return an array the same size as `self` or the first error encountered.
    ///
    /// The return type of this function depends on the return type of the closure.
    /// If you return `Result<T, E>` from the closure, you'll get a `Result<[T; N], E>`.
    /// If you return `Option<T>` from the closure, you'll get an `Option<[T; N]>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use array_util::ArrayExt;
    ///
    /// let a = ["1", "2", "3"];
    /// let b = a.try_map_ext(|v| v.parse::<u32>()).unwrap().map(|v| v + 1);
    /// assert_eq!(b, [2, 3, 4]);
    ///
    /// let a = ["1", "2a", "3"];
    /// let b = a.try_map_ext(|v| v.parse::<u32>());
    /// assert!(b.is_err());
    ///
    /// use std::num::NonZeroU32;
    /// let z = [1, 2, 0, 3, 4];
    /// assert_eq!(z.try_map_ext(NonZeroU32::new), None);
    /// let a = [1, 2, 3];
    /// let b = a.try_map_ext(NonZeroU32::new);
    /// let c = b.map(|x| x.map(NonZeroU32::get));
    /// assert_eq!(c, Some(a));
    /// ```
    fn try_map_ext<F, R>(
        self,
        f: F,
    ) -> <<R as Try>::Residual as Residual<Self::TN<<R as Try>::Output>>>::TryType
    where
        F: FnMut(Self::T) -> R,
        R: Try,
        <R as Try>::Residual: Residual<Self::TN<<R as Try>::Output>>;
}

impl<T, const N: usize> ArrayExt for [T; N] {
    type T = T;
    type TN<U> = [U; N];

    /// A fallible function `f` applied to each element on array `self` in order to
    /// return an array the same size as `self` or the first error encountered.
    ///
    /// The return type of this function depends on the return type of the closure.
    /// If you return `Result<T, E>` from the closure, you'll get a `Result<[T; N], E>`.
    /// If you return `Option<T>` from the closure, you'll get an `Option<[T; N]>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use array_util::ArrayExt;
    ///
    /// let a = ["1", "2", "3"];
    /// let b = a.try_map_ext(|v| v.parse::<u32>()).unwrap().map(|v| v + 1);
    /// assert_eq!(b, [2, 3, 4]);
    ///
    /// let a = ["1", "2a", "3"];
    /// let b = a.try_map_ext(|v| v.parse::<u32>());
    /// assert!(b.is_err());
    ///
    /// use std::num::NonZeroU32;
    /// let z = [1, 2, 0, 3, 4];
    /// assert_eq!(z.try_map_ext(NonZeroU32::new), None);
    /// let a = [1, 2, 3];
    /// let b = a.try_map_ext(NonZeroU32::new);
    /// let c = b.map(|x| x.map(NonZeroU32::get));
    /// assert_eq!(c, Some(a));
    /// ```
    #[inline]
    fn try_map_ext<F, R>(
        self,
        f: F,
    ) -> <<R as Try>::Residual as Residual<[<R as Try>::Output; N]>>::TryType
    where
        F: FnMut(T) -> R,
        R: Try,
        <R as Try>::Residual: Residual<[<R as Try>::Output; N]>,
    {
        try_map(self, f)
    }
}

/// A helper extension trait for slices
pub trait SliceExt {
    #[doc(hidden)]
    type T;

    /// Returns an iterator over `N` elements of the slice at a time, starting at the
    /// beginning of the slice.
    ///
    /// The chunks are array references and do not overlap. If `N` does not divide the
    /// length of the slice, then the last up to `N-1` elements will be omitted and can be
    /// retrieved from the `remainder` function of the iterator.
    ///
    /// This method is the const generic equivalent of [`chunks_exact`].
    ///
    /// # Panics
    ///
    /// Panics if `N` is 0. This check will most probably get changed to a compile time
    /// error before this method gets stabilized.
    ///
    /// # Examples
    ///
    /// ```
    /// use array_util::SliceExt;
    ///
    /// let slice = ['l', 'o', 'r', 'e', 'm'];
    /// let mut iter = slice.array_chunks_ext();
    /// assert_eq!(iter.next().unwrap(), &['l', 'o']);
    /// assert_eq!(iter.next().unwrap(), &['r', 'e']);
    /// assert!(iter.next().is_none());
    /// assert_eq!(iter.remainder(), &['m']);
    /// ```
    ///
    /// [`chunks_exact`]: prim@slice#method.chunks_exact
    fn array_chunks_ext<const N: usize>(&self) -> ArrayChunks<'_, Self::T, N>;

    /// Returns an iterator over `N` elements of the slice at a time, starting at the
    /// beginning of the slice.
    ///
    /// The chunks are mutable array references and do not overlap. If `N` does not divide
    /// the length of the slice, then the last up to `N-1` elements will be omitted and
    /// can be retrieved from the `into_remainder` function of the iterator.
    ///
    /// This method is the const generic equivalent of [`chunks_exact_mut`].
    ///
    /// # Panics
    ///
    /// Panics if `N` is 0. This check will most probably get changed to a compile time
    /// error before this method gets stabilized.
    ///
    /// # Examples
    ///
    /// ```
    /// use array_util::SliceExt;
    ///
    /// let v = &mut [0, 0, 0, 0, 0];
    /// let mut count = 1;
    ///
    /// for chunk in v.array_chunks_mut_ext() {
    ///     *chunk = [count; 2];
    ///     count += 1;
    /// }
    /// assert_eq!(v, &[1, 1, 2, 2, 0]);
    /// ```
    ///
    /// [`chunks_exact_mut`]: prim@slice#method.chunks_exact_mut
    fn array_chunks_mut_ext<const N: usize>(&mut self) -> ArrayChunksMut<'_, Self::T, N>;

    /// Splits the slice into a slice of `N`-element arrays,
    /// starting at the beginning of the slice,
    /// and a remainder slice with length strictly less than `N`.
    ///
    /// # Panics
    ///
    /// Panics if `N` is 0. This check will most probably get changed to a compile time
    /// error before this method gets stabilized.
    ///
    /// # Examples
    ///
    /// ```
    /// use array_util::SliceExt;
    ///
    /// let slice = ['l', 'o', 'r', 'e', 'm'];
    /// let (chunks, remainder) = slice.as_chunks_ext();
    /// assert_eq!(chunks, &[['l', 'o'], ['r', 'e']]);
    /// assert_eq!(remainder, &['m']);
    /// ```
    ///
    /// If you expect the slice to be an exact multiple, you can combine
    /// `let`-`else` with an empty slice pattern:
    /// ```
    /// use array_util::SliceExt;
    ///
    /// let slice = ['R', 'u', 's', 't'];
    /// let (chunks, []) = slice.as_chunks_ext::<2>() else {
    ///     panic!("slice didn't have even length")
    /// };
    /// assert_eq!(chunks, &[['R', 'u'], ['s', 't']]);
    /// ```
    #[must_use]
    fn as_chunks_ext<const N: usize>(&self) -> (&[[Self::T; N]], &[Self::T]);

    /// Splits the slice into a slice of `N`-element arrays,
    /// assuming that there's no remainder.
    ///
    /// # Safety
    ///
    /// This may only be called when
    /// - The slice splits exactly into `N`-element chunks (aka `self.len() % N == 0`).
    /// - `N != 0`.
    ///
    /// # Examples
    ///
    /// ```
    /// use array_util::SliceExt;
    ///
    /// let slice: &[char] = &['l', 'o', 'r', 'e', 'm', '!'];
    /// let chunks: &[[char; 1]] =
    ///     // SAFETY: 1-element chunks never have remainder
    ///     unsafe { slice.as_chunks_unchecked_ext() };
    /// assert_eq!(chunks, &[['l'], ['o'], ['r'], ['e'], ['m'], ['!']]);
    /// let chunks: &[[char; 3]] =
    ///     // SAFETY: The slice length (6) is a multiple of 3
    ///     unsafe { slice.as_chunks_unchecked_ext() };
    /// assert_eq!(chunks, &[['l', 'o', 'r'], ['e', 'm', '!']]);
    ///
    /// // These would be unsound:
    /// // let chunks: &[[_; 5]] = slice.as_chunks_unchecked_ext() // The slice length is not a multiple of 5
    /// // let chunks: &[[_; 0]] = slice.as_chunks_unchecked_ext() // Zero-length chunks are never allowed
    /// ```
    #[must_use]
    unsafe fn as_chunks_unchecked_ext<const N: usize>(&self) -> &[[Self::T; N]];

    /// Splits the slice into a slice of `N`-element arrays,
    /// starting at the beginning of the slice,
    /// and a remainder slice with length strictly less than `N`.
    ///
    /// # Panics
    ///
    /// Panics if `N` is 0. This check will most probably get changed to a compile time
    /// error before this method gets stabilized.
    ///
    /// # Examples
    ///
    /// ```
    /// use array_util::SliceExt;
    ///
    /// let v = &mut [0, 0, 0, 0, 0];
    /// let mut count = 1;
    ///
    /// let (chunks, remainder) = v.as_chunks_mut_ext();
    /// remainder[0] = 9;
    /// for chunk in chunks {
    ///     *chunk = [count; 2];
    ///     count += 1;
    /// }
    /// assert_eq!(v, &[1, 1, 2, 2, 9]);
    /// ```
    #[must_use]
    fn as_chunks_mut_ext<const N: usize>(&mut self) -> (&mut [[Self::T; N]], &mut [Self::T]);

    /// Splits the slice into a slice of `N`-element arrays,
    /// assuming that there's no remainder.
    ///
    /// # Safety
    ///
    /// This may only be called when
    /// - The slice splits exactly into `N`-element chunks (aka `self.len() % N == 0`).
    /// - `N != 0`.
    ///
    /// # Examples
    ///
    /// ```
    /// use array_util::SliceExt;
    ///
    /// let slice: &mut [char] = &mut ['l', 'o', 'r', 'e', 'm', '!'];
    /// let chunks: &mut [[char; 1]] =
    ///     // SAFETY: 1-element chunks never have remainder
    ///     unsafe { slice.as_chunks_unchecked_mut_ext() };
    /// chunks[0] = ['L'];
    /// assert_eq!(chunks, &[['L'], ['o'], ['r'], ['e'], ['m'], ['!']]);
    /// let chunks: &mut [[char; 3]] =
    ///     // SAFETY: The slice length (6) is a multiple of 3
    ///     unsafe { slice.as_chunks_unchecked_mut_ext() };
    /// chunks[1] = ['a', 'x', '?'];
    /// assert_eq!(slice, &['L', 'o', 'r', 'a', 'x', '?']);
    ///
    /// // These would be unsound:
    /// // let chunks: &[[_; 5]] = slice.as_chunks_unchecked_mut_ext() // The slice length is not a multiple of 5
    /// // let chunks: &[[_; 0]] = slice.as_chunks_unchecked_mut_ext() // Zero-length chunks are never allowed
    /// ```
    #[must_use]
    unsafe fn as_chunks_unchecked_mut_ext<const N: usize>(&mut self) -> &mut [[Self::T; N]];

    /// Splits the slice into a slice of `N`-element arrays,
    /// starting at the end of the slice,
    /// and a remainder slice with length strictly less than `N`.
    ///
    /// # Panics
    ///
    /// Panics if `N` is 0. This check will most probably get changed to a compile time
    /// error before this method gets stabilized.
    ///
    /// # Examples
    ///
    /// ```
    /// use array_util::SliceExt;
    ///
    /// let slice = ['l', 'o', 'r', 'e', 'm'];
    /// let (remainder, chunks) = slice.as_rchunks_ext();
    /// assert_eq!(remainder, &['l']);
    /// assert_eq!(chunks, &[['o', 'r'], ['e', 'm']]);
    /// ```
    #[must_use]

    fn as_rchunks_ext<const N: usize>(&self) -> (&[Self::T], &[[Self::T; N]]);
    /// Splits the slice into a slice of `N`-element arrays,
    /// starting at the end of the slice,
    /// and a remainder slice with length strictly less than `N`.
    ///
    /// # Panics
    ///
    /// Panics if `N` is 0. This check will most probably get changed to a compile time
    /// error before this method gets stabilized.
    ///
    /// # Examples
    ///
    /// ```
    /// use array_util::SliceExt;
    ///
    /// let v = &mut [0, 0, 0, 0, 0];
    /// let mut count = 1;
    ///
    /// let (remainder, chunks) = v.as_rchunks_mut_ext();
    /// remainder[0] = 9;
    /// for chunk in chunks {
    ///     *chunk = [count; 2];
    ///     count += 1;
    /// }
    /// assert_eq!(v, &[9, 1, 1, 2, 2]);
    /// ```
    #[must_use]
    fn as_rchunks_mut_ext<const N: usize>(&mut self) -> (&mut [Self::T], &mut [[Self::T; N]]);
}

impl<T> SliceExt for [T] {
    type T = T;

    /// Returns an iterator over `N` elements of the slice at a time, starting at the
    /// beginning of the slice.
    ///
    /// The chunks are array references and do not overlap. If `N` does not divide the
    /// length of the slice, then the last up to `N-1` elements will be omitted and can be
    /// retrieved from the `remainder` function of the iterator.
    ///
    /// This method is the const generic equivalent of [`chunks_exact`].
    ///
    /// # Panics
    ///
    /// Panics if `N` is 0. This check will most probably get changed to a compile time
    /// error before this method gets stabilized.
    ///
    /// # Examples
    ///
    /// ```
    /// use array_util::SliceExt;
    ///
    /// let slice = ['l', 'o', 'r', 'e', 'm'];
    /// let mut iter = slice.array_chunks_ext();
    /// assert_eq!(iter.next().unwrap(), &['l', 'o']);
    /// assert_eq!(iter.next().unwrap(), &['r', 'e']);
    /// assert!(iter.next().is_none());
    /// assert_eq!(iter.remainder(), &['m']);
    /// ```
    ///
    /// [`chunks_exact`]: prim@slice#method.chunks_exact
    #[inline]
    fn array_chunks_ext<const N: usize>(&self) -> ArrayChunks<'_, Self::T, N> {
        array_chunks(self)
    }

    /// Returns an iterator over `N` elements of the slice at a time, starting at the
    /// beginning of the slice.
    ///
    /// The chunks are mutable array references and do not overlap. If `N` does not divide
    /// the length of the slice, then the last up to `N-1` elements will be omitted and
    /// can be retrieved from the `into_remainder` function of the iterator.
    ///
    /// This method is the const generic equivalent of [`chunks_exact_mut`].
    ///
    /// # Panics
    ///
    /// Panics if `N` is 0. This check will most probably get changed to a compile time
    /// error before this method gets stabilized.
    ///
    /// # Examples
    ///
    /// ```
    /// use array_util::SliceExt;
    ///
    /// let v = &mut [0, 0, 0, 0, 0];
    /// let mut count = 1;
    ///
    /// for chunk in v.array_chunks_mut_ext() {
    ///     *chunk = [count; 2];
    ///     count += 1;
    /// }
    /// assert_eq!(v, &[1, 1, 2, 2, 0]);
    /// ```
    ///
    /// [`chunks_exact_mut`]: prim@slice#method.chunks_exact_mut
    #[inline]
    fn array_chunks_mut_ext<const N: usize>(&mut self) -> ArrayChunksMut<'_, Self::T, N> {
        array_chunks_mut(self)
    }

    /// Splits the slice into a slice of `N`-element arrays,
    /// starting at the beginning of the slice,
    /// and a remainder slice with length strictly less than `N`.
    ///
    /// # Panics
    ///
    /// Panics if `N` is 0. This check will most probably get changed to a compile time
    /// error before this method gets stabilized.
    ///
    /// # Examples
    ///
    /// ```
    /// use array_util::SliceExt;
    ///
    /// let slice = ['l', 'o', 'r', 'e', 'm'];
    /// let (chunks, remainder) = slice.as_chunks_ext();
    /// assert_eq!(chunks, &[['l', 'o'], ['r', 'e']]);
    /// assert_eq!(remainder, &['m']);
    /// ```
    ///
    /// If you expect the slice to be an exact multiple, you can combine
    /// `let`-`else` with an empty slice pattern:
    /// ```
    /// use array_util::SliceExt;
    ///
    /// let slice = ['R', 'u', 's', 't'];
    /// let (chunks, []) = slice.as_chunks_ext::<2>() else {
    ///     panic!("slice didn't have even length")
    /// };
    /// assert_eq!(chunks, &[['R', 'u'], ['s', 't']]);
    /// ```
    #[inline]
    #[must_use]
    fn as_chunks_ext<const N: usize>(&self) -> (&[[Self::T; N]], &[Self::T]) {
        as_chunks(self)
    }

    /// Splits the slice into a slice of `N`-element arrays,
    /// assuming that there's no remainder.
    ///
    /// # Safety
    ///
    /// This may only be called when
    /// - The slice splits exactly into `N`-element chunks (aka `self.len() % N == 0`).
    /// - `N != 0`.
    ///
    /// # Examples
    ///
    /// ```
    /// use array_util::SliceExt;
    ///
    /// let slice: &[char] = &['l', 'o', 'r', 'e', 'm', '!'];
    /// let chunks: &[[char; 1]] =
    ///     // SAFETY: 1-element chunks never have remainder
    ///     unsafe { slice.as_chunks_unchecked_ext() };
    /// assert_eq!(chunks, &[['l'], ['o'], ['r'], ['e'], ['m'], ['!']]);
    /// let chunks: &[[char; 3]] =
    ///     // SAFETY: The slice length (6) is a multiple of 3
    ///     unsafe { slice.as_chunks_unchecked_ext() };
    /// assert_eq!(chunks, &[['l', 'o', 'r'], ['e', 'm', '!']]);
    ///
    /// // These would be unsound:
    /// // let chunks: &[[_; 5]] = slice.as_chunks_unchecked_ext() // The slice length is not a multiple of 5
    /// // let chunks: &[[_; 0]] = slice.as_chunks_unchecked_ext() // Zero-length chunks are never allowed
    /// ```
    #[inline]
    #[must_use]
    unsafe fn as_chunks_unchecked_ext<const N: usize>(&self) -> &[[Self::T; N]] {
        as_chunks_unchecked(self)
    }

    /// Splits the slice into a slice of `N`-element arrays,
    /// starting at the beginning of the slice,
    /// and a remainder slice with length strictly less than `N`.
    ///
    /// # Panics
    ///
    /// Panics if `N` is 0. This check will most probably get changed to a compile time
    /// error before this method gets stabilized.
    ///
    /// # Examples
    ///
    /// ```
    /// use array_util::SliceExt;
    ///
    /// let v = &mut [0, 0, 0, 0, 0];
    /// let mut count = 1;
    ///
    /// let (chunks, remainder) = v.as_chunks_mut_ext();
    /// remainder[0] = 9;
    /// for chunk in chunks {
    ///     *chunk = [count; 2];
    ///     count += 1;
    /// }
    /// assert_eq!(v, &[1, 1, 2, 2, 9]);
    /// ```
    #[inline]
    #[must_use]
    fn as_chunks_mut_ext<const N: usize>(&mut self) -> (&mut [[Self::T; N]], &mut [Self::T]) {
        as_chunks_mut(self)
    }

    /// Splits the slice into a slice of `N`-element arrays,
    /// assuming that there's no remainder.
    ///
    /// # Safety
    ///
    /// This may only be called when
    /// - The slice splits exactly into `N`-element chunks (aka `self.len() % N == 0`).
    /// - `N != 0`.
    ///
    /// # Examples
    ///
    /// ```
    /// use array_util::SliceExt;
    ///
    /// let slice: &mut [char] = &mut ['l', 'o', 'r', 'e', 'm', '!'];
    /// let chunks: &mut [[char; 1]] =
    ///     // SAFETY: 1-element chunks never have remainder
    ///     unsafe { slice.as_chunks_unchecked_mut_ext() };
    /// chunks[0] = ['L'];
    /// assert_eq!(chunks, &[['L'], ['o'], ['r'], ['e'], ['m'], ['!']]);
    /// let chunks: &mut [[char; 3]] =
    ///     // SAFETY: The slice length (6) is a multiple of 3
    ///     unsafe { slice.as_chunks_unchecked_mut_ext() };
    /// chunks[1] = ['a', 'x', '?'];
    /// assert_eq!(slice, &['L', 'o', 'r', 'a', 'x', '?']);
    ///
    /// // These would be unsound:
    /// // let chunks: &[[_; 5]] = slice.as_chunks_unchecked_mut_ext() // The slice length is not a multiple of 5
    /// // let chunks: &[[_; 0]] = slice.as_chunks_unchecked_mut_ext() // Zero-length chunks are never allowed
    /// ```
    #[inline]
    #[must_use]
    unsafe fn as_chunks_unchecked_mut_ext<const N: usize>(&mut self) -> &mut [[Self::T; N]] {
        as_chunks_unchecked_mut(self)
    }

    /// Splits the slice into a slice of `N`-element arrays,
    /// starting at the end of the slice,
    /// and a remainder slice with length strictly less than `N`.
    ///
    /// # Panics
    ///
    /// Panics if `N` is 0. This check will most probably get changed to a compile time
    /// error before this method gets stabilized.
    ///
    /// # Examples
    ///
    /// ```
    /// use array_util::SliceExt;
    ///
    /// let slice = ['l', 'o', 'r', 'e', 'm'];
    /// let (remainder, chunks) = slice.as_rchunks_ext();
    /// assert_eq!(remainder, &['l']);
    /// assert_eq!(chunks, &[['o', 'r'], ['e', 'm']]);
    /// ```
    #[inline]
    #[must_use]
    fn as_rchunks_ext<const N: usize>(&self) -> (&[Self::T], &[[Self::T; N]]) {
        as_rchunks(self)
    }

    /// Splits the slice into a slice of `N`-element arrays,
    /// starting at the end of the slice,
    /// and a remainder slice with length strictly less than `N`.
    ///
    /// # Panics
    ///
    /// Panics if `N` is 0. This check will most probably get changed to a compile time
    /// error before this method gets stabilized.
    ///
    /// # Examples
    ///
    /// ```
    /// use array_util::SliceExt;
    ///
    /// let v = &mut [0, 0, 0, 0, 0];
    /// let mut count = 1;
    ///
    /// let (remainder, chunks) = v.as_rchunks_mut_ext();
    /// remainder[0] = 9;
    /// for chunk in chunks {
    ///     *chunk = [count; 2];
    ///     count += 1;
    /// }
    /// assert_eq!(v, &[9, 1, 1, 2, 2]);
    /// ```
    #[inline]
    #[must_use]
    fn as_rchunks_mut_ext<const N: usize>(&mut self) -> (&mut [Self::T], &mut [[Self::T; N]]) {
        as_rchunks_mut(self)
    }
}

/// A helper extension trait for slices of arrays
pub trait SliceOfArrayExt {
    #[doc(hidden)]
    type T;

    /// Takes a `&[[T; N]]`, and flattens it to a `&[T]`.
    ///
    /// # Panics
    ///
    /// This panics if the length of the resulting slice would overflow a `usize`.
    ///
    /// This is only possible when flattening a slice of arrays of zero-sized
    /// types, and thus tends to be irrelevant in practice. If
    /// `size_of::<T>() > 0`, this will never panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use array_util::SliceOfArrayExt;
    ///
    /// assert_eq!([[1, 2, 3], [4, 5, 6]].flatten_ext(), &[1, 2, 3, 4, 5, 6]);
    ///
    /// assert_eq!(
    ///     [[1, 2, 3], [4, 5, 6]].flatten_ext(),
    ///     [[1, 2], [3, 4], [5, 6]].flatten_ext(),
    /// );
    ///
    /// let slice_of_empty_arrays: &[[i32; 0]] = &[[], [], [], [], []];
    /// assert!(slice_of_empty_arrays.flatten_ext().is_empty());
    ///
    /// let empty_slice_of_arrays: &[[u32; 10]] = &[];
    /// assert!(empty_slice_of_arrays.flatten_ext().is_empty());
    /// ```
    fn flatten_ext(&self) -> &[Self::T];

    /// Takes a `&mut [[T; N]]`, and flattens it to a `&mut [T]`.
    ///
    /// # Panics
    ///
    /// This panics if the length of the resulting slice would overflow a `usize`.
    ///
    /// This is only possible when flattening a slice of arrays of zero-sized
    /// types, and thus tends to be irrelevant in practice. If
    /// `size_of::<T>() > 0`, this will never panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use array_util::SliceOfArrayExt;
    ///
    /// fn add_5_to_all(slice: &mut [i32]) {
    ///     for i in slice {
    ///         *i += 5;
    ///     }
    /// }
    ///
    /// let mut array = [[1, 2, 3], [4, 5, 6], [7, 8, 9]];
    /// add_5_to_all(array.flatten_mut_ext());
    /// assert_eq!(array, [[6, 7, 8], [9, 10, 11], [12, 13, 14]]);
    /// ```
    fn flatten_mut_ext(&mut self) -> &mut [Self::T];
}

impl<T, const N: usize> SliceOfArrayExt for [[T; N]] {
    type T = T;

    /// Takes a `&[[T; N]]`, and flattens it to a `&[T]`.
    ///
    /// # Panics
    ///
    /// This panics if the length of the resulting slice would overflow a `usize`.
    ///
    /// This is only possible when flattening a slice of arrays of zero-sized
    /// types, and thus tends to be irrelevant in practice. If
    /// `size_of::<T>() > 0`, this will never panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use array_util::SliceOfArrayExt;
    ///
    /// assert_eq!([[1, 2, 3], [4, 5, 6]].flatten_ext(), &[1, 2, 3, 4, 5, 6]);
    ///
    /// assert_eq!(
    ///     [[1, 2, 3], [4, 5, 6]].flatten_ext(),
    ///     [[1, 2], [3, 4], [5, 6]].flatten_ext(),
    /// );
    ///
    /// let slice_of_empty_arrays: &[[i32; 0]] = &[[], [], [], [], []];
    /// assert!(slice_of_empty_arrays.flatten_ext().is_empty());
    ///
    /// let empty_slice_of_arrays: &[[u32; 10]] = &[];
    /// assert!(empty_slice_of_arrays.flatten_ext().is_empty());
    /// ```
    fn flatten_ext(&self) -> &[Self::T] {
        flatten(self)
    }

    /// Takes a `&mut [[T; N]]`, and flattens it to a `&mut [T]`.
    ///
    /// # Panics
    ///
    /// This panics if the length of the resulting slice would overflow a `usize`.
    ///
    /// This is only possible when flattening a slice of arrays of zero-sized
    /// types, and thus tends to be irrelevant in practice. If
    /// `size_of::<T>() > 0`, this will never panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use array_util::SliceOfArrayExt;
    ///
    /// fn add_5_to_all(slice: &mut [i32]) {
    ///     for i in slice {
    ///         *i += 5;
    ///     }
    /// }
    ///
    /// let mut array = [[1, 2, 3], [4, 5, 6], [7, 8, 9]];
    /// add_5_to_all(array.flatten_mut_ext());
    /// assert_eq!(array, [[6, 7, 8], [9, 10, 11], [12, 13, 14]]);
    /// ```
    fn flatten_mut_ext(&mut self) -> &mut [Self::T] {
        flatten_mut(self)
    }
}

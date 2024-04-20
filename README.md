# array-util

`no_std` array helpers available without nightly.

### Description

Many useful array and slice methods are currently gated by nightly
features, though their general functionality and interface is essentially
stable. As such this crate provides stable alternatives to the following
features, often the same underlying implementation as the current nightly
version:

- [`array_try_from_fn`]
- [`array_try_map`]
- [`array_chunks`]
- [`slice_as_chunks`]
- [`slice_flatten`]

### Usage

Users can either import an `Ext` trait (`SliceExt`, `ArrayExt`, or
`SliceOfArrayExt`) traits to bring in the desired methods, or use the bare
functions. Note that trait methods have the `_ext` suffix to avoid
collision with the core library methods.

```rust
use array_util::ArrayExt;

let a = ["1", "2", "3"];
let b = a.try_map_ext(|v| v.parse::<u32>()).unwrap().map(|v| v + 1);
assert_eq!(b, [2, 3, 4]);

let a = ["1", "2a", "3"];
let b = a.try_map_ext(|v| v.parse::<u32>());
assert!(b.is_err());
```

```rust
let a = ["1", "2", "3"];
let b = array_util::try_map(a, |v| v.parse::<u32>()).unwrap().map(|v| v + 1);
assert_eq!(b, [2, 3, 4]);

let a = ["1", "2a", "3"];
let b = array_util::try_map(a, |v| v.parse::<u32>());
assert!(b.is_err());
```

### Limitations

These functions aren't stabilized because they rely on undecided behaviors.
For example, "should compile-time errors be generated for `0` length
arrays?" or "What should the associated types and traits of `Try` be?". As
these questions remain unresolved, reliance on the particular answers
this crate has chosen in it's implementation may make porting to the
eventual stabilized version more painful. If you're just calling functions,
you'll probably be fine, but try to avoid using the `Ext` traits as bounds.

[`array_try_from_fn`]: https://github.com/rust-lang/rust/issues/89379
[`array_try_map`]: https://github.com/rust-lang/rust/issues/79711
[`array_chunks`]: https://github.com/rust-lang/rust/issues/74985
[`slice_as_chunks`]: https://github.com/rust-lang/rust/issues/74985
[`slice_flatten`]: https://github.com/rust-lang/rust/issues/95629

License: MIT

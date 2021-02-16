# reusable-box-future

[![license][license badge]][license]
[![crates.io][crate badge]][crate]
[![docs][docs badge]][docs]

A reusable `Pin<Box<dyn Future<Output = T> + Send>>`.

This lets you replace the future stored in the box without reallocating
when the size and alignment permits it.

This code was extracted from [tokio-util] crate.

# License

[MIT][license]


[license]: LICENSE
[license badge]: https://img.shields.io/github/license/oblique/reusable-box-future
[crate]: https://crates.io/crates/reusable-box-future
[crate badge]: https://img.shields.io/crates/v/reusable-box-future
[docs]: https://docs.rs/reusable-box-future
[docs badge]: https://docs.rs/reusable-box-future/badge.svg
[tokio-util]: https://github.com/tokio-rs/tokio/tree/master/tokio-util

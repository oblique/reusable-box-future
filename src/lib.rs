//! A reusable `Pin<Box<dyn Future<Output = T> + Send>>`.
//!
//! This lets you replace the future stored in the box without reallocating
//! when the size and alignment permits it.
//!
//! This code was extracted from [tokio-util] crate.
//!
//! [tokio-util]: https://docs.rs/tokio-util

#![cfg_attr(not(test), no_std)]
extern crate alloc;

mod box_future;
mod local_box_future;

pub use crate::box_future::ReusableBoxFuture;
pub use crate::local_box_future::ReusableLocalBoxFuture;

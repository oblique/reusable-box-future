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

use alloc::alloc::Layout;
use alloc::boxed::Box;
use core::fmt;
use core::future::Future;
use core::mem::ManuallyDrop;
use core::pin::Pin;
use core::ptr::{self, NonNull};
use core::task::{Context, Poll};

macro_rules! reusable_box_future {
    ($desc:literal, $name:ident) => {
        reusable_box_future!($desc, $name:);
    };
    ($desc:literal, $name:ident: $($traits:tt)*) => {
        #[doc = $desc]
        ///
        /// This type lets you replace the future stored in the box without
        /// reallocating when the size and alignment permits this.
        pub struct $name<T> {
            boxed: NonNull<dyn Future<Output = T> + $($traits)*>,
        }

        impl<T> $name<T> {
            /// Create a new reusable boxed future.
            pub fn new<F>(future: F) -> Self
            where
                F: Future<Output = T> + 'static + $($traits)*,
            {
                let boxed: Box<dyn Future<Output = T> + $($traits)*> = Box::new(future);
                let boxed = Box::into_raw(boxed);

                // SAFETY: Box::into_raw does not return null pointers.
                let boxed = unsafe { NonNull::new_unchecked(boxed) };

                Self { boxed }
            }

            /// Replace the future currently stored in this box.
            ///
            /// This reallocates if and only if the layout of the provided future is
            /// different from the layout of the currently stored future.
            pub fn set<F>(&mut self, future: F)
            where
                F: Future<Output = T> + 'static + $($traits)*,
            {
                if let Err(future) = self.try_set(future) {
                    *self = Self::new(future);
                }
            }

            /// Replace the future currently stored in this box.
            ///
            /// This function never reallocates, but returns an error if the provided
            /// future has a different size or alignment from the currently stored
            /// future.
            pub fn try_set<F>(&mut self, future: F) -> Result<(), F>
            where
                F: Future<Output = T> + 'static + $($traits)*,
            {
                // SAFETY: The pointer is not dangling.
                let self_layout = {
                    let dyn_future: &(dyn Future<Output = T> + $($traits)*) = unsafe { self.boxed.as_ref() };
                    Layout::for_value(dyn_future)
                };

                if Layout::new::<F>() == self_layout {
                    // SAFETY: We just checked that the layout of F is correct.
                    unsafe {
                        self.set_same_layout(future);
                    }

                    Ok(())
                } else {
                    Err(future)
                }
            }

            /// Set the current future.
            ///
            /// # Safety
            ///
            /// This function requires that the layout of the provided future is the
            /// same as `self.boxed` layout.
            unsafe fn set_same_layout<F>(&mut self, future: F)
            where
                F: Future<Output = T> + 'static + $($traits)*,
            {
                struct SetLayout<'a, F, T>
                where
                    F: Future<Output = T> + 'static + $($traits)*,
                {
                    rbf: &'a mut $name<T>,
                    new_future: ManuallyDrop<F>,
                }

                impl<'a, F, T> Drop for SetLayout<'a, F, T>
                where
                    F: Future<Output = T> + 'static + $($traits)*,
                {
                    fn drop(&mut self) {
                        // By doing the replacement on `drop` we make sure the change
                        // will happen even if the existing future panics on drop.
                        //
                        // We could use `catch_unwind`, but it is not available in `no_std`.
                        unsafe {
                            // Overwrite the future behind the pointer. This is safe because the
                            // allocation was allocated with the same size and alignment as the type F.
                            let fut_ptr: *mut F = self.rbf.boxed.as_ptr() as *mut F;
                            ptr::write(fut_ptr, ManuallyDrop::take(&mut self.new_future));

                            // Update the vtable of self.boxed. The pointer is not null because we
                            // just got it from self.boxed, which is not null.
                            self.rbf.boxed = NonNull::new_unchecked(fut_ptr);
                        }
                    }
                }

                let set_layout = SetLayout {
                    rbf: self,
                    new_future: ManuallyDrop::new(future),
                };

                // Drop the existing future.
                ptr::drop_in_place(set_layout.rbf.boxed.as_ptr());
                // Now `set_layout` will be dropped and do the replacement.
            }

            /// Get a pinned reference to the underlying future.
            pub fn get_pin(&mut self) -> Pin<&mut (dyn Future<Output = T> + $($traits)*)> {
                // SAFETY: The user of this box cannot move the box, and we do not move it
                // either.
                unsafe { Pin::new_unchecked(self.boxed.as_mut()) }
            }

            /// Poll the future stored inside this box.
            pub fn poll(&mut self, cx: &mut Context<'_>) -> Poll<T> {
                self.get_pin().poll(cx)
            }
        }

        impl<T> Future for $name<T> {
            type Output = T;

            /// Poll the future stored inside this box.
            fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<T> {
                Pin::into_inner(self).get_pin().poll(cx)
            }
        }

        // Just like a Pin<Box<dyn Future>> is always Unpin, so is this type.
        impl<T> Unpin for $name<T> {}

        impl<T> Drop for $name<T> {
            fn drop(&mut self) {
                unsafe {
                    drop(Box::from_raw(self.boxed.as_ptr()));
                }
            }
        }

        impl<T> fmt::Debug for $name<T> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_struct(stringify!($name)).finish()
            }
        }
    };
}

reusable_box_future!(
    "A reusable `Pin<Box<dyn Future<Output = T> + Send>>`.",
    ReusableBoxFuture: Send
);
reusable_box_future!(
    "A reusable `Pin<Box<dyn Future<Output = T>>>`.",
    ReusableLocalBoxFuture
);

// The future stored inside ReusableBoxFuture<T> must be Send.
unsafe impl<T> Send for ReusableBoxFuture<T> {}

// The only method called on self.boxed is poll, which takes &mut self, so this
// struct being Sync does not permit any invalid access to the Future, even if
// the future is not Sync.
unsafe impl<T> Sync for ReusableBoxFuture<T> {}

#[cfg(test)]
mod tests {
    use super::*;
    use futures_executor::block_on;
    use static_assertions::{assert_impl_all, assert_not_impl_all};
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use std::sync::Arc;

    struct TestFut<T: Unpin> {
        polled_nr: u32,
        ready_val: u32,
        dropped: Arc<AtomicBool>,
        _buf: Option<T>,
    }

    impl<T: Unpin> TestFut<T> {
        fn new(ready_val: u32) -> Self {
            TestFut {
                polled_nr: 0,
                ready_val,
                dropped: Arc::new(AtomicBool::new(false)),
                _buf: None,
            }
        }
    }

    impl<T: Unpin> Future for TestFut<T> {
        type Output = u32;

        fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
            self.polled_nr += 1;

            match self.polled_nr {
                1 => {
                    // First poll, simulate pending
                    cx.waker().wake_by_ref();
                    Poll::Pending
                }
                2 => {
                    // Second poll, simulate ready
                    Poll::Ready(self.ready_val)
                }
                _ => panic!("Future completed"),
            }
        }
    }

    impl<T: Unpin> Drop for TestFut<T> {
        fn drop(&mut self) {
            self.dropped.store(true, Ordering::SeqCst);
        }
    }

    #[test]
    fn alloc() {
        block_on(async {
            let test_fut = TestFut::<[u8; 32]>::new(1);
            let dropped = Arc::clone(&test_fut.dropped);

            let mut fut = ReusableBoxFuture::new(test_fut);
            assert!(!dropped.load(Ordering::SeqCst));

            assert_eq!((&mut fut).await, 1);
            assert!(!dropped.load(Ordering::SeqCst));

            let ptr = fut.boxed.as_ptr();
            let test_fut = TestFut::<[u8; 32]>::new(2);
            let dropped_2 = Arc::clone(&test_fut.dropped);
            assert!(fut.try_set(test_fut).is_ok());
            assert!(dropped.load(Ordering::SeqCst));
            assert!(!dropped_2.load(Ordering::SeqCst));
            assert_eq!(
                ptr as *const _ as *mut u8,
                fut.boxed.as_ptr() as *const _ as *mut u8
            );

            assert_eq!((&mut fut).await, 2);
            assert!(!dropped_2.load(Ordering::SeqCst));

            let test_fut = TestFut::<[u8; 256]>::new(3);
            let dropped_3 = Arc::clone(&test_fut.dropped);
            assert!(fut.try_set(test_fut).is_err());
            assert!(!dropped_2.load(Ordering::SeqCst));
            assert!(dropped_3.load(Ordering::SeqCst));

            let test_fut = TestFut::<[u8; 256]>::new(4);
            let dropped_4 = Arc::clone(&test_fut.dropped);
            fut.set(test_fut);
            assert!(dropped_2.load(Ordering::SeqCst));
            assert!(!dropped_4.load(Ordering::SeqCst));
            assert_ne!(
                ptr as *const _ as *mut u8,
                fut.boxed.as_ptr() as *const _ as *mut u8
            );

            assert_eq!((&mut fut).await, 4);
            assert!(!dropped_4.load(Ordering::SeqCst));
        })
    }

    #[test]
    fn static_assertion() {
        assert_impl_all!(ReusableBoxFuture<()>: Sync, Send, Unpin);
        assert_impl_all!(ReusableLocalBoxFuture<()>: Unpin);
        assert_not_impl_all!(ReusableLocalBoxFuture<()>: Sync, Send);
    }

    #[test]
    fn panicking_drop() {
        struct PanicDrop(Arc<AtomicUsize>);

        impl Future for PanicDrop {
            type Output = ();

            fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
                Poll::Ready(())
            }
        }

        impl Drop for PanicDrop {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::Relaxed);

                if !std::thread::panicking() {
                    panic!(1u32);
                }
            }
        }

        // We use this second type to verify that we replace vtable by having a different
        // drop implementation (i.e. adding 100 instead of 1)
        struct NonPanicDrop(Arc<AtomicUsize>);

        impl Future for NonPanicDrop {
            type Output = ();

            fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
                Poll::Ready(())
            }
        }

        impl Drop for NonPanicDrop {
            fn drop(&mut self) {
                self.0.fetch_add(100, Ordering::Relaxed);
            }
        }

        let drop1 = Arc::new(AtomicUsize::new(0));
        let drop2 = Arc::new(AtomicUsize::new(0));

        let result = std::panic::catch_unwind({
            let drop1 = Arc::clone(&drop1);
            let drop2 = Arc::clone(&drop2);

            move || {
                let mut fut = ReusableBoxFuture::new(PanicDrop(drop1));

                match fut.try_set(NonPanicDrop(drop2)) {
                    Ok(_) => panic!(2u32),
                    Err(_) => panic!(3u32),
                }
            }
        });

        // Make sure that panic was propagated correctly
        assert_eq!(*result.err().unwrap().downcast::<u32>().unwrap(), 1);

        // Make sure we drop only once per item
        assert_eq!(drop1.load(Ordering::Relaxed), 1);
        assert_eq!(drop2.load(Ordering::Relaxed), 100);
    }
}

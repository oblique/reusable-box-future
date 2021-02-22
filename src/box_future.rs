use alloc::alloc::Layout;
use alloc::boxed::Box;
use core::fmt;
use core::future::Future;
use core::mem::ManuallyDrop;
use core::pin::Pin;
use core::ptr::{self, NonNull};
use core::task::{Context, Poll};

/// A reusable `Pin<Box<dyn Future<Output = T> + Send>>`.
///
/// This type lets you replace the future stored in the box without
/// reallocating when the size and alignment permits this.
pub struct ReusableBoxFuture<T> {
    boxed: NonNull<dyn Future<Output = T> + Send>,
}

impl<T> ReusableBoxFuture<T> {
    /// Create a new `ReusableBoxFuture<T>` containing the provided future.
    pub fn new<F>(future: F) -> Self
    where
        F: Future<Output = T> + Send + 'static,
    {
        let boxed: Box<dyn Future<Output = T> + Send> = Box::new(future);
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
        F: Future<Output = T> + Send + 'static,
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
        F: Future<Output = T> + Send + 'static,
    {
        // SAFETY: The pointer is not dangling.
        let self_layout = {
            let dyn_future: &(dyn Future<Output = T> + Send) = unsafe { self.boxed.as_ref() };
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
        F: Future<Output = T> + Send + 'static,
    {
        struct SetLayout<'a, F, T>
        where
            F: Future<Output = T> + Send + 'static,
        {
            rbf: &'a mut ReusableBoxFuture<T>,
            new_future: ManuallyDrop<F>,
        }

        impl<'a, F, T> Drop for SetLayout<'a, F, T>
        where
            F: Future<Output = T> + Send + 'static,
        {
            fn drop(&mut self) {
                // By doing the replacement on `drop` we make sure the change
                // will happen even if the existing future panics on drop.
                //
                // We chould use `catch_unwind`, but it is not available in `no_std`.
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
    pub fn get_pin(&mut self) -> Pin<&mut (dyn Future<Output = T> + Send)> {
        // SAFETY: The user of this box cannot move the box, and we do not move it
        // either.
        unsafe { Pin::new_unchecked(self.boxed.as_mut()) }
    }

    /// Poll the future stored inside this box.
    pub fn poll(&mut self, cx: &mut Context<'_>) -> Poll<T> {
        self.get_pin().poll(cx)
    }
}

impl<T> Future for ReusableBoxFuture<T> {
    type Output = T;

    /// Poll the future stored inside this box.
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<T> {
        Pin::into_inner(self).get_pin().poll(cx)
    }
}

// The future stored inside ReusableBoxFuture<T> must be Send.
unsafe impl<T> Send for ReusableBoxFuture<T> {}

// The only method called on self.boxed is poll, which takes &mut self, so this
// struct being Sync does not permit any invalid access to the Future, even if
// the future is not Sync.
unsafe impl<T> Sync for ReusableBoxFuture<T> {}

// Just like a Pin<Box<dyn Future>> is always Unpin, so is this type.
impl<T> Unpin for ReusableBoxFuture<T> {}

impl<T> Drop for ReusableBoxFuture<T> {
    fn drop(&mut self) {
        unsafe {
            drop(Box::from_raw(self.boxed.as_ptr()));
        }
    }
}

impl<T> fmt::Debug for ReusableBoxFuture<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ReusableBoxFuture").finish()
    }
}

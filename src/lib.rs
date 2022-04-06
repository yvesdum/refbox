//! A smart pointer with many reference-counted weak references.
//!
//! A [`RefBox`] is a smart pointer that owns the data, just like a [`Box`].
//! Similarly, a RefBox cannot be cloned cheaply, and when it is dropped, the
//! data it points to is dropped as well. However, a RefBox may have many
//! [`Ref`] pointers to the same data. These pointers don't own the data and are
//! reference counted, comparable to [`Weak`]. Which means, as long as the
//! RefBox is alive, Refs can be used to access the data from multiple places
//! without lifetime parameters.
//!
//! A RefBox could be seen as a lighter alternative to the standard library's
//! [`Rc`], [`Weak`] and [`RefCell`] combination, which has more features but
//! also a larger memory overhead.
//!
//! A RefBox does not differentiate between strong and weak pointers and
//! immutable and mutable borrows. There is always a *single* strong pointer,
//! zero, one or many weak pointers and all borrows are mutable. This means
//! there can only be one borrow active at any given time. But in return,
//! RefBox uses less memory, is faster to borrow from, and a Ref does not need
//! to be upgraded to a RefBox in order to access the data. In fact, upgrading
//! is not possible at all.
//!
//! Note: this crate is currently **experimental** and requires Nightly Rust.
//!
//! [`Rc`]: std::rc::Rc
//! [`Weak`]: std::rc::Weak
//! [`RefCell`]: std::cell::RefCell
//!
//! # Rc<RefCell<T>> vs RefBox<T>
//!
//! |                  | `Rc<RefCell<T>>`                                               | `RefBox<T>`                                     |
//! |------------------|----------------------------------------------------------------|-------------------------------------------------|
//! | Pointer kinds    | Many strong pointers and many weak pointers                    | One strong owner and many weak pointers         |
//! | Clonable         | Both `Rc` and `Weak` are cheap to clone                        | Only `Ref` can be cheaply cloned                |
//! | Up-/Downgrading  | `Rc` is downgradable, `Weak` is upgradable                     | No up- or downgrading, but `RefBox::create_ref` |
//! | Data access      | `RefCell::try_borrow_mut`                                      | `RefBox::try_borrow_mut`                        |
//! | Weak data access | 1. `Weak::upgrade`<br>2. `RefCell::try_borrow_mut`<br>3. `Rc::drop` | `Ref::try_borrow_mut`                      |
//! | Active borrows   | One mutable or many immutable                                  | One (mutable or immutable)                      |
//! | `T::drop`        | When all `Rc`s are dropped                                     | When owner `RefBox` is dropped                  |
//! | Max no. `Weak`s  | `usize::MAX`                                                   | `u32::MAX`                                      |
//! | Heap overhead    | 64-bit: 24 bytes<br>32-bit: 12 bytes                           | 8 bytes                                         |
//!
//! # Examples
//!
//! ```
//! use refbox::RefBox;
//!
//! fn main() {
//!     // Create a RefBox.
//!     let owner = RefBox::new(100);
//!
//!     // Create a weak reference.
//!     let weak = owner.create_ref();
//!
//!     // Access the data.
//!     let borrow = weak.try_borrow_mut().unwrap();
//!     assert_eq!(*borrow, 100);
//! }
//! ```

// The optional "cyclic" feature, which activates the `RefBox::<T>::new_cyclic()`
// method, requires the Nightly feature "layout_for_ptr", as we need to be able
// to get the layout of `T` through a raw pointer in order to deallocate it.
#![feature(layout_for_ptr)]

mod internals;

use core::fmt;
use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};
use core::ptr::NonNull;
use std::error;

use internals::{RefBoxHeap, RefBoxHeapInner, RefCount, Status};

///////////////////////////////////////////////////////////////////////////////
// Helpers
///////////////////////////////////////////////////////////////////////////////

/// Coerces a `RefBox<T>` into a `RefBox<dyn Trait>` on stable Rust.
///
/// Normally, performing custom coercions requires the [`CoerceUnsized`] trait
/// which is only available on Nightly Rust. This macro bypasses this trait by
/// performing the actual coercion in the raw pointer domain, which is
/// perfectly possible on Stable Rust.
///
/// [`CoerceUnsized`]: std::ops::CoerceUnsized
#[macro_export]
macro_rules! coerce {
    ($rc:expr => $into:ty) => {{
        let __raw = $crate::RefBox::into_raw($rc);
        let __out: $crate::RefBox<$into> = unsafe { $crate::RefBox::from_raw(__raw) };
        __out
    }};
}

/// Coerces a `Ref<T>` into a `Ref<dyn Trait>` on stable Rust.
///
/// Normally, performing custom coercions requires the [`CoerceUnsized`] trait
/// which is only available on Nightly Rust. This macro bypasses this trait by
/// performing the actual coercion in the raw pointer domain, which is
/// perfectly possible on Stable Rust.
///
/// [`CoerceUnsized`]: std::ops::CoerceUnsized
#[macro_export]
macro_rules! coerce_ref {
    ($rc:expr => $into:ty) => {{
        let __raw = $crate::Ref::into_raw($rc);
        let __out: $crate::Ref<$into> = unsafe { $crate::Ref::from_raw(__raw) };
        __out
    }};
}

///////////////////////////////////////////////////////////////////////////////
// Rc
///////////////////////////////////////////////////////////////////////////////

/// A smart pointer with many reference-counted weak references.
///
/// See the [module](crate) documentation for more information.
pub struct RefBox<T: ?Sized> {
    ptr: NonNull<RefBoxHeap<T>>,
    /// A RefBox owns the data and may call `T::drop`.
    _p: PhantomData<RefBoxHeap<T>>,
}

impl<T: ?Sized> Drop for RefBox<T> {
    fn drop(&mut self) {
        unsafe { internals::drop_refbox(self.ptr) };
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for RefBox<T> {
    /// Tries to access the data and write a debug representation of it.
    /// If accessing fails, it only writes the pointer value.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.try_borrow_mut() {
            Ok(this) => f
                .debug_tuple("RefBox")
                .field(&self.ptr)
                .field(&&*this)
                .finish(),
            Err(_) => f.debug_tuple("RefBox").field(&self.ptr).finish(),
        }
    }
}

impl<T: ?Sized> PartialEq<Ref<T>> for RefBox<T> {
    fn eq(&self, other: &Ref<T>) -> bool {
        other.is(self)
    }
}

impl<T> RefBox<T> {
    /// Creates a new `RefBox` reference counted pointer.
    pub fn new(value: T) -> Self {
        internals::new_refbox(value)
    }

    /// Creates a new `RefBox` through a closure which receives a
    /// `Ref` to the same data. Use this to create data structures
    /// that contain weak references to themselves.
    ///
    /// Note: if you try to borrow the data in the closure, you will get a
    /// [`BorrowError::Dropped`] error.
    ///
    /// # Examples
    ///
    /// ```
    /// use refbox::{Ref, RefBox};
    ///
    /// struct Node {
    ///     parent: Option<Ref<Node>>,
    ///     child: Option<RefBox<Node>>,
    /// }
    ///
    /// let node = RefBox::new_cyclic(|me| {
    ///     let child = RefBox::new(Node {
    ///         parent: Some(me.clone()),
    ///         child: None,
    ///     });
    ///
    ///     Node {
    ///         parent: None,
    ///         child: Some(child),
    ///     }
    /// });
    /// ```
    pub fn new_cyclic<F: FnOnce(&Ref<T>) -> T>(op: F) -> Self {
        internals::new_cyclic_refbox(op)
    }
}

impl<T: ?Sized> RefBox<T> {
    /// Returns a read-only reference to the heap part of the `RefBox`.
    #[inline(always)]
    fn heap(&self) -> &RefBoxHeapInner {
        // SAFETY (1): RefBox guarantees the heap memory stays alive at least
        // as long as the RefBox is alive.
        // SAFETY (2): We only ever access this through a shared reference so
        // we don't have to account for possible mutable references.
        // SAFETY (3): Because this is a RefBox we know the data field
        // is initialized.
        let ptr = self.ptr.as_ptr();
        unsafe { &(*ptr).inner }
    }

    /// Tries to borrow the data mutably.
    ///
    /// # Returns
    ///
    /// * `Ok(Borrow)` if the borrow was successful
    /// * `Err(BorrowError::Borrowed)` if the data was already borrowed
    #[inline]
    pub fn try_borrow_mut<'b>(&'b self) -> Result<Borrow<'b, T>, BorrowError> {
        self.try_borrow_mut_or_else(|| BorrowError::Borrowed)
    }

    /// Tries to borrow the data mutably and returns a custom error if
    /// borrowing fails.
    pub fn try_borrow_mut_or_else<'b, E>(
        &'b self,
        err_borrowed: impl FnOnce() -> E,
    ) -> Result<Borrow<'b, T>, E> {
        match self.heap().status() {
            Status::Available => Ok(unsafe { Borrow::new(self.ptr.as_ref()) }),
            Status::Borrowed => Err(err_borrowed()),
            Status::Dropped | Status::DroppedWhileBorrowed => unreachable!(),
        }
    }

    /// Creates a weak reference to the data.
    ///
    /// # Panics
    ///
    /// Panics if the number of Refs overflows `u32::MAX`.
    pub fn create_ref(&self) -> Ref<T> {
        self.heap().increase_refcount();
        Ref { ptr: self.ptr }
    }

    /// Tries to create a weak reference to the data.
    ///
    /// # Returns
    ///
    /// * `Some(Ref)` if it was succesful.
    /// * `None` if the number of Refs overflowed `u32::MAX`.
    pub fn try_create_ref(&self) -> Option<Ref<T>> {
        if self.heap().try_increase_refcount() {
            Some(Ref { ptr: self.ptr })
        } else {
            None
        }
    }

    /// Returns the number of [`Ref`]s pointing to this RefBox.
    pub fn refcount(&self) -> RefCount {
        self.heap().refcount()
    }

    /// Returns an immutable reference to the data without checking if
    /// the data is already mutably borrowed.
    ///
    /// # Safety
    ///
    /// Ensure there are no mutable references to `T`.
    pub unsafe fn get_unchecked(&self) -> &T {
        self.ptr.as_ref().data_ref()
    }

    /// Returns a mutable reference to the data without checking if
    /// the data is already mutably borrowed.
    ///
    /// # Safety
    ///
    /// Ensure there are no other references to `T`.
    pub unsafe fn get_mut_unchecked(&mut self) -> &mut T {
        self.ptr.as_ref().data_mut()
    }

    /// Turns the `RefBox` into a raw pointer.
    pub fn into_raw(self) -> *mut RefBoxHeap<T> {
        let ptr = self.ptr.as_ptr();
        std::mem::forget(self);
        ptr
    }

    /// Creates a `RefBox` from a raw pointer.
    pub unsafe fn from_raw(ptr: *mut RefBoxHeap<T>) -> Self {
        Self {
            ptr: NonNull::new_unchecked(ptr),
            _p: PhantomData,
        }
    }

    /// Casts a `RefBox<T>` to a `RefBox<U>`.
    pub unsafe fn cast<U>(self) -> RefBox<U> {
        let raw_ptr = self.into_raw();
        RefBox::from_raw(raw_ptr as _)
    }

    /// Returns the current status of the heap part for testing purposes.
    #[cfg(test)]
    fn status(&self) -> Status {
        self.heap().status()
    }
}

///////////////////////////////////////////////////////////////////////////////
// RcRef
///////////////////////////////////////////////////////////////////////////////

/// A weak reference-counted reference to a [`RefBox`].
///
/// See the [module](crate) documentation for more information.
pub struct Ref<T: ?Sized> {
    ptr: NonNull<RefBoxHeap<T>>,
}

impl<T: ?Sized> Drop for Ref<T> {
    fn drop(&mut self) {
        // SAFETY: the `Ref` cannot be used anymore after this point.
        unsafe { internals::drop_ref(self.ptr) };
    }
}

impl<T: ?Sized> Clone for Ref<T> {
    /// Copies the reference and increases the reference counter.
    ///
    /// # Panics
    ///
    /// Panics if the number of Refs overflows `u32::MAX`.
    fn clone(&self) -> Self {
        self.heap().increase_refcount();
        Ref { ptr: self.ptr }
    }
}

impl<T: ?Sized> fmt::Debug for Ref<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Ref").field(&self.ptr).finish()
    }
}

impl<T: ?Sized> PartialEq for Ref<T> {
    /// Returns true if both `Ref`s point to the same instance.
    ///
    /// This compares the pointers, not the actual object itself, which
    /// means it is very fast.
    fn eq(&self, other: &Self) -> bool {
        self.ptr.as_ptr() == other.ptr.as_ptr()
    }
}

impl<T: ?Sized> PartialEq<RefBox<T>> for Ref<T> {
    fn eq(&self, other: &RefBox<T>) -> bool {
        self.is(other)
    }
}

impl<T: ?Sized> Eq for Ref<T> {}

impl<T: ?Sized> Ref<T> {
    /// Returns a read-only reference to the heap part of the `RefBox`.
    #[inline(always)]
    fn heap(&self) -> &RefBoxHeapInner {
        // SAFETY (1): Ref guarantees the heap memory stays alive at
        // least as long as the Ref is alive.
        // SAFETY (2): We only ever access this through a shared reference so
        // we don't have to account for possible mutable references.
        // SAFETY (3): We make sure not to create a reference covering the
        // `data` field of `RefBoxHeap` as it may contain uninitialized data.
        let ptr = self.ptr.as_ptr();
        unsafe { &(*ptr).inner }
    }

    /// Tries to borrow the data mutably.
    ///
    /// # Returns
    ///
    /// * `Ok(Borrow)` if the borrow was successful
    /// * `Err(BorrowError::Borrowed)` if the data was already borrowed
    /// * `Err(BorrowError::Dropped)` if the owning [`RefBox`] was dropped
    #[inline]
    pub fn try_borrow_mut<'rc>(&'rc self) -> Result<Borrow<'rc, T>, BorrowError> {
        self.try_borrow_mut_or_else(|| BorrowError::Borrowed, || BorrowError::Dropped)
    }

    /// Tries to borrow the data mutably and returns a custom error if
    /// borrowing fails.
    pub fn try_borrow_mut_or_else<'rc, E>(
        &'rc self,
        err_borrowed: impl FnOnce() -> E,
        err_dropped: impl FnOnce() -> E,
    ) -> Result<Borrow<'rc, T>, E> {
        match self.heap().status() {
            Status::Available => Ok(unsafe { Borrow::new(self.ptr.as_ref()) }),
            Status::Borrowed => Err(err_borrowed()),
            Status::Dropped | Status::DroppedWhileBorrowed => Err(err_dropped()),
        }
    }

    /// Tries to clone the weak reference to the data.
    ///
    /// # Returns
    ///
    /// * `Some(Ref)` if it was succesful.
    /// * `None` if the number of weaks overflowed `u32::MAX`.
    pub fn try_clone(&self) -> Option<Ref<T>> {
        if self.heap().try_increase_refcount() {
            Some(Ref { ptr: self.ptr })
        } else {
            None
        }
    }

    /// Returns the number of [`Ref`]s that point to the same data as this Ref.
    pub fn refcount(&self) -> RefCount {
        self.heap().refcount()
    }

    /// Returns true if the owner of the data is alive.
    pub fn is_alive(&self) -> bool {
        self.heap().is_alive()
    }

    /// Returns true if the data is currently mutably borrowed.
    pub fn is_borrowed(&self) -> bool {
        self.heap().is_borrowed()
    }

    /// Returns true if this `Ref` and the supplied [`RefBox`]
    /// point to the same instance.
    pub fn is(&self, owner: &RefBox<T>) -> bool {
        self.ptr.as_ptr() == owner.ptr.as_ptr()
    }

    /// Returns an immutable reference to the data without checking if
    /// the data is already mutably borrowed or dropped.
    ///
    /// # Safety
    ///
    /// 1. Ensure there are no mutable references to `T`.
    /// 2. Ensure `T` is fully initialized (don't use this in
    ///    [`RefBox::new_cyclic`]).
    /// 3. Ensure the owning `RefBox` is alive for the entire lifetime
    ///    of the returned reference.
    pub unsafe fn get_unchecked(&self) -> &T {
        self.ptr.as_ref().data_ref()
    }

    /// Returns a mutable reference to the data without checking if
    /// the data is already mutably borrowed or dropped.
    ///
    /// # Safety
    ///
    /// 1. Ensure there are no other references to `T`.
    /// 2. Ensure `T` is fully initialized (don't use this in
    ///    [`RefBox::new_cyclic`]).
    /// 3. Ensure the owning `RefBox` is alive for the entire lifetime
    ///    of the returned reference.
    pub unsafe fn get_mut_unchecked(&mut self) -> &mut T {
        self.ptr.as_ref().data_mut()
    }

    /// Turns the `Ref` into a raw pointer.
    pub fn into_raw(self) -> *mut RefBoxHeap<T> {
        let ptr = self.ptr.as_ptr();
        std::mem::forget(self);
        ptr
    }

    /// Creates a `Ref` from a raw pointer.
    pub unsafe fn from_raw(ptr: *mut RefBoxHeap<T>) -> Self {
        let ptr = NonNull::new_unchecked(ptr);
        Self { ptr }
    }

    /// Casts a `Ref<T>` to a `Ref<U>`.
    pub unsafe fn cast<U>(self) -> Ref<U> {
        let raw_ptr = self.into_raw();
        Ref::from_raw(raw_ptr as _)
    }

    /// Returns the current status of the heap part for testing purposes.
    #[cfg(test)]
    fn status(&self) -> internals::Status {
        self.heap().status()
    }
}

///////////////////////////////////////////////////////////////////////////////
// Borrow
///////////////////////////////////////////////////////////////////////////////

/// A mutable borrow as a RAII-guard of a [`RefBox`] or [`Ref`].
///
/// See the [module](crate) documentation for more information.
#[derive(Debug)]
pub struct Borrow<'rc, T: ?Sized> {
    pub(crate) heap: &'rc RefBoxHeap<T>,
    /// A borrow is a mutable reference to the data.
    pub(crate) _p: PhantomData<&'rc mut T>,
}

impl<'rc, T: ?Sized> Borrow<'rc, T> {
    /// Creates a new borrow.
    #[inline]
    unsafe fn new(heap: &'rc RefBoxHeap<T>) -> Self {
        heap.inner.start_borrow();
        Self {
            heap,
            _p: PhantomData,
        }
    }
}

impl<'rc, T: ?Sized> Drop for Borrow<'rc, T> {
    fn drop(&mut self) {
        // SAFETY: The borrow cannot be used anymore after this point.
        unsafe { internals::drop_borrow(self.heap) };
    }
}

impl<'rc, T: ?Sized> Deref for Borrow<'rc, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY: There can only ever be one `Borrow` to the same
        // data so we're sure there are no mutable references.
        unsafe { self.heap.data_ref() }
    }
}

impl<'rc, T: ?Sized> DerefMut for Borrow<'rc, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: There can only ever be one `Borrow` to the same
        // data so we're sure there are no other references.
        unsafe { self.heap.data_mut() }
    }
}

///////////////////////////////////////////////////////////////////////////////
// Errors
///////////////////////////////////////////////////////////////////////////////

/// An error that may occur during borrowing of [`RefBox`] or [`Ref`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BorrowError {
    Borrowed,
    Dropped,
}

impl fmt::Display for BorrowError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BorrowError::Borrowed => write!(f, "already borrowed"),
            BorrowError::Dropped => write!(f, "owner dropped"),
        }
    }
}

impl error::Error for BorrowError {}

///////////////////////////////////////////////////////////////////////////////
// Tests
///////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::panic;
    use std::rc::Rc;

    use crate::internals::Status;
    use crate::RefBox;

    #[test]
    fn rc_new() {
        let rc = RefBox::new(123456);
        assert_eq!(unsafe { *rc.get_unchecked() }, 123456);
        drop(rc);
    }

    /// The refcount after creation should be 0.
    #[test]
    fn rc_new_refcount() {
        let rc = RefBox::new(123456);
        assert_eq!(rc.refcount(), 0);
        drop(rc);
    }

    #[test]
    fn rc_new_cyclic() {
        let rc = RefBox::new_cyclic(|_weak| 13579);
        assert_eq!(unsafe { *rc.get_unchecked() }, 13579);
        drop(rc);
    }

    /// The refcount in the closure should be 1, and the refcount after
    /// creation should be 0.
    #[test]
    fn rc_new_cyclic_refcount() {
        let rc = RefBox::new_cyclic(|weak| {
            assert_eq!(weak.refcount(), 1);
        });
        assert_eq!(rc.refcount(), 0);
        drop(rc);
    }

    /// The Ref in the closure should point to the same instance as the
    /// returned RefBox.
    #[test]
    fn rc_new_cyclic_ptr_eq() {
        let mut out_weak = None;
        let rc = RefBox::new_cyclic(|weak| out_weak = Some(weak.clone()));
        assert_eq!(rc.ptr.as_ptr(), out_weak.unwrap().ptr.as_ptr());
        drop(rc);
    }

    /// MIRI: A panic in the closure of `new_cyclic` should not leak memory.
    #[test]
    #[should_panic]
    fn rc_new_cyclic_does_not_leak() {
        let rc1 = RefBox::new_cyclic(|_weak| {
            panic!("panic in closure!");
        });
        drop(rc1);
    }

    /// A weak returned from RefBox::create_weak should point to the same
    /// instance as the RefBox.
    #[test]
    fn create_weak_ptr_eq() {
        let val = 123456;
        let rc = RefBox::new(val);
        let weak = RefBox::create_ref(&rc);
        assert_eq!(rc.ptr.as_ptr(), weak.ptr.as_ptr());
    }

    /// RefBox::create_weak should increase the weak reference count.
    #[test]
    fn create_weak_increases_refcount() {
        let val = 123456;
        let rc = RefBox::new(val);
        assert_eq!(rc.refcount(), 0);
        let weak = RefBox::create_ref(&rc);
        assert_eq!(rc.refcount(), 1);
        assert_eq!(weak.refcount(), 1);
    }

    /// RefBox::create_weak should panic if the refcount overflows u32::MAX.
    #[test]
    fn create_weak_panics_on_max() {
        let val = 123456;
        let rc = RefBox::new(val);
        rc.heap().set_refcount(u32::MAX);

        // Use catch unwind and reset refcount, otherwise MIRI will report memory leak.
        let result = panic::catch_unwind(panic::AssertUnwindSafe(|| {
            let weak = RefBox::create_ref(&rc);
            drop(weak);
        }));
        assert!(result.is_err());

        rc.heap().set_refcount(0);
        drop(rc);
    }

    /// RefBox::try_create_weak should return None if the refcount overflows
    /// u32::MAX.
    #[test]
    fn try_create_weak_returns_none_on_max() {
        let val = 123456;
        let rc = RefBox::new(val);
        rc.heap().set_refcount(u32::MAX);
        let weak = RefBox::try_create_ref(&rc);
        assert!(weak.is_none());
        drop(weak);
        rc.heap().set_refcount(0);
        drop(rc);
    }

    /// Ref::clone should increase the weak reference count.
    #[test]
    fn cloning_weak_increases_refcount() {
        let val = 123456;
        let rc = RefBox::new(val);
        assert_eq!(rc.refcount(), 0);
        let weak = RefBox::create_ref(&rc);
        assert_eq!(rc.refcount(), 1);
        let weak2 = weak.clone();
        assert_eq!(rc.refcount(), 2);
        drop(weak2);
        drop(weak);
    }

    /// Ref::clone should panic if the refcount overflows u32::MAX.
    #[test]
    fn cloning_weak_panics_on_max() {
        let rc = RefBox::new(123456);
        let weak = RefBox::create_ref(&rc);
        weak.heap().set_refcount(u32::MAX);

        // Use catch unwind and reset refcount, otherwise MIRI will report memory leak.
        let result = panic::catch_unwind(panic::AssertUnwindSafe(|| {
            let weak2 = weak.clone();
            drop(weak2);
        }));
        assert!(result.is_err());

        drop(weak);
        rc.heap().set_refcount(0);
        drop(rc);
    }

    #[test]
    fn dropping_weak_decreases_refcount() {
        let val = 123456;
        let rc = RefBox::new(val);
        let weak = RefBox::create_ref(&rc);
        assert_eq!(rc.refcount(), 1);
        drop(weak);
        assert_eq!(rc.refcount(), 0);
    }

    #[test]
    fn owner_is_alive() {
        let val = 123456;
        let rc = RefBox::new(val);
        let weak = RefBox::create_ref(&rc);
        assert_eq!(weak.is_alive(), true);
        drop(rc);
    }

    #[test]
    fn owner_is_not_alive_after_dropped() {
        let val = 123456;
        let rc = RefBox::new(val);
        let weak = RefBox::create_ref(&rc);
        assert_eq!(weak.is_alive(), true);
        drop(rc);
        assert_eq!(weak.is_alive(), false);
    }

    #[test]
    fn dropping_rc_drops_data() {
        struct DropThing(Rc<Cell<bool>>);

        impl Drop for DropThing {
            fn drop(&mut self) {
                self.0.set(true);
            }
        }

        let thing = Rc::new(Cell::new(false));
        let rc = RefBox::new(DropThing(thing.clone()));
        assert_eq!(thing.get(), false);
        drop(rc);
        assert_eq!(thing.get(), true);
    }

    #[test]
    fn dropping_rc_with_weaks_drops_data() {
        struct DropThing(Rc<Cell<bool>>);

        impl Drop for DropThing {
            fn drop(&mut self) {
                self.0.set(true);
            }
        }

        let thing = Rc::new(Cell::new(false));
        let rc = RefBox::new(DropThing(thing.clone()));
        let weak = RefBox::create_ref(&rc);
        assert_eq!(thing.get(), false);
        drop(rc);
        assert_eq!(thing.get(), true);
        drop(weak);
    }

    #[test]
    fn dropping_weak_does_not_drop_data() {
        struct DropThing(Rc<Cell<bool>>);

        impl Drop for DropThing {
            fn drop(&mut self) {
                self.0.set(true);
            }
        }

        let thing = Rc::new(Cell::new(false));
        let rc = RefBox::new(DropThing(thing.clone()));
        let weak = RefBox::create_ref(&rc);
        assert_eq!(thing.get(), false);
        drop(weak);
        assert_eq!(thing.get(), false);
        drop(rc);
        assert_eq!(thing.get(), true);
    }

    #[test]
    fn owner_is_borrowable() {
        let rc = RefBox::new(123456);
        let borrow = rc.try_borrow_mut_or_else(|| "was borrowed");
        assert!(borrow.is_ok());
        drop(borrow);
        drop(rc);
    }

    #[test]
    fn owner_is_not_borrowable_twice() {
        let rc = RefBox::new(123456);
        let borrow = rc.try_borrow_mut_or_else(|| "was borrowed");
        assert!(borrow.is_ok());
        let borrow2 = rc.try_borrow_mut_or_else(|| "was borrowed");
        assert!(matches!(borrow2, Err("was borrowed")));
        drop(borrow);
        drop(borrow2);
        drop(rc);
    }

    #[test]
    fn weak_is_borrowable() {
        let rc = RefBox::new(123456);
        let weak = RefBox::create_ref(&rc);
        let borrow = weak.try_borrow_mut_or_else(|| "was borrowed", || "was dropped");
        assert!(matches!(borrow, Ok(_)));
        drop(borrow);
        drop(weak);
        drop(rc);
    }

    #[test]
    fn weak_is_not_borrowable_twice() {
        let rc = RefBox::new(123456);
        let weak = RefBox::create_ref(&rc);
        let borrow = weak.try_borrow_mut_or_else(|| "was borrowed", || "was dropped");
        assert!(matches!(borrow, Ok(_)));
        let borrow2 = weak.try_borrow_mut_or_else(|| "was borrowed", || "was dropped");
        assert!(matches!(borrow2, Err("was borrowed")));
        drop(borrow);
        drop(borrow2);
        drop(weak);
        drop(rc);
    }

    #[test]
    fn weak_is_not_borrowable_if_owner_borrowed() {
        let rc = RefBox::new(123456);
        let weak = RefBox::create_ref(&rc);
        let borrow = rc.try_borrow_mut_or_else(|| "was borrowed");
        assert!(matches!(borrow, Ok(_)));
        let borrow2 = weak.try_borrow_mut_or_else(|| "was borrowed", || "was dropped");
        assert!(matches!(borrow2, Err("was borrowed")));
        drop(borrow);
        drop(borrow2);
        drop(weak);
        drop(rc);
    }

    #[test]
    fn weak_is_not_borrowable_if_owner_dropped() {
        let rc = RefBox::new(123456);
        let weak = RefBox::create_ref(&rc);
        drop(rc);
        let borrow = weak.try_borrow_mut_or_else(|| "was borrowed", || "was dropped");
        assert!(matches!(borrow, Err("was dropped")));
        drop(borrow);
        drop(weak);
    }

    #[test]
    fn dropping_owner_while_borrowed_delays_drops() {
        let rc = RefBox::new(123456);
        let weak = RefBox::create_ref(&rc);
        let borrow = weak.try_borrow_mut_or_else(|| "was borrowed", || "was dropped");
        assert_eq!(weak.status(), Status::Borrowed);
        drop(rc);
        assert_eq!(weak.status(), Status::DroppedWhileBorrowed);
        drop(borrow);
        assert_eq!(weak.status(), Status::Dropped);
        drop(weak);
    }

    #[test]
    fn borrowing_changes_status() {
        let rc = RefBox::new(123456);
        assert_eq!(rc.status(), Status::Available);
        let borrow = rc.try_borrow_mut_or_else(|| "was borrowed");
        assert_eq!(rc.status(), Status::Borrowed);
        drop(borrow);
        assert_eq!(rc.status(), Status::Available);
        drop(rc);
    }

    #[test]
    fn dropping_owner_changes_status() {
        let rc = RefBox::new(123456);
        let weak = RefBox::create_ref(&rc);
        assert_eq!(weak.status(), Status::Available);
        drop(rc);
        assert_eq!(weak.status(), Status::Dropped);
        drop(weak);
    }

    #[test]
    fn borrowing_in_cyclic_fails() {
        let rc = RefBox::new_cyclic(|weak| {
            let borrow = weak.try_borrow_mut_or_else(|| "was borrowed", || "was dropped");
            assert!(borrow.is_err());
        });
        drop(rc);
    }

    #[test]
    fn cloning_weak_in_cyclic_increases_refcount() {
        let rc = RefBox::new_cyclic(|weak| {
            let weak2 = weak.clone();
            assert_eq!(weak.refcount(), 2);
            drop(weak2);
        });
        drop(rc);
    }

    #[test]
    fn calling_getters_while_having_mutable_ref() {
        let rc = RefBox::new(123456);
        let mut borrow = rc.try_borrow_mut_or_else(|| "was borrowed").unwrap();
        let mut_ref = &mut *borrow;
        assert_eq!(rc.refcount(), 0);
        *mut_ref = 654321;
        let weak = RefBox::create_ref(&rc);
        assert_eq!(rc.refcount(), 1);
        *mut_ref = 13579;
        drop(mut_ref);
        drop(borrow);
        drop(weak);
        drop(rc);
    }

    #[test]
    fn single_rcs_are_distinct() {
        let rc1 = RefBox::new(123456);
        let rc2 = RefBox::new(654321);

        let borrow1 = rc1.try_borrow_mut().unwrap();
        let borrow2 = rc2.try_borrow_mut().unwrap();

        assert_ne!(*borrow1, *borrow2);
        assert_eq!(*borrow1, 123456);
        assert_eq!(*borrow2, 654321);

        drop(borrow1);
        drop(borrow2);
        drop(rc1);
        drop(rc2);
    }
}

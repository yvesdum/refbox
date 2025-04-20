//! Contains the internal state machine and heap part of a `RefBox`.

use core::cell::{Cell, UnsafeCell};
use core::marker::PhantomData;
use core::ptr::{self, NonNull};
use std::alloc;

use crate::RefBox;

///////////////////////////////////////////////////////////////////////////////
// Heap Part Types
///////////////////////////////////////////////////////////////////////////////

/// The reference counter.
// Note: when changing this also change the public documentation.
pub(crate) type RefCount = u32;

/// The current status of a `RefBox`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Status {
    Available,
    Borrowed,
    Dropped,
    DroppedWhileBorrowed,
}

/// The status part of the RefBoxHeap.
#[derive(Debug)]
pub(crate) struct RefBoxHeapInner {
    /// The current status of the data.
    status: Cell<Status>,
    /// The number of weak references to the data.
    refcount: Cell<RefCount>,
}

/// The part of a `RefBox` that is stored on the heap.
// repr(C) because we are casting in `new_cyclic`.
#[repr(C)]
#[derive(Debug)]
pub struct RefBoxHeap<T: ?Sized> {
    pub(crate) inner: RefBoxHeapInner,
    pub(crate) data: UnsafeCell<T>,
}

impl RefBoxHeapInner {
    /// Returns the current status.
    #[inline]
    pub(crate) fn status(&self) -> Status {
        self.status.get()
    }

    /// Returns the current weak reference count.
    #[inline]
    pub(crate) fn refcount(&self) -> RefCount {
        self.refcount.get()
    }

    /// Sets the weak reference count. Used in tests.
    #[inline]
    #[cfg(test)]
    pub(crate) fn set_refcount(&self, count: RefCount) {
        self.refcount.set(count);
    }

    /// Increases the reference counter by 1.
    ///
    /// # Panics
    ///
    /// Panics if the number of `Weak`s overflows `RefCount::MAX`.
    #[inline]
    pub(crate) fn increase_refcount(&self) {
        let refcount = self.refcount();

        if refcount == RefCount::MAX {
            cold_panic();
        } else {
            self.refcount.set(refcount + 1);
        }
    }

    /// Increases the reference counter by 1.
    ///
    /// Returns false if the refcount overflowed.
    #[inline]
    pub(crate) fn try_increase_refcount(&self) -> bool {
        let refcount = self.refcount();

        if refcount == RefCount::MAX {
            cold_false()
        } else {
            self.refcount.set(refcount + 1);
            true
        }
    }

    /// Decreases the reference counter by 1.
    #[inline]
    fn decrease_refcount(&self) -> RefCount {
        let refcount = self.refcount() - 1;
        self.refcount.set(refcount);
        refcount
    }

    /// Returns true if the owner is alive.
    #[inline]
    pub(crate) fn is_alive(&self) -> bool {
        matches!(self.status(), Status::Available | Status::Borrowed)
    }

    /// Returns true if the data is currently borrowed.
    #[inline]
    pub(crate) fn is_borrowed(&self) -> bool {
        matches!(self.status(), Status::Borrowed)
    }

    /// Sets the status to `Borrowed`.
    #[inline]
    pub(crate) fn start_borrow(&self) {
        self.status.set(Status::Borrowed);
    }
}

impl<T: ?Sized> RefBoxHeap<T> {
    /// Returns a shared reference to the data.
    ///
    /// # Safety
    ///
    /// 1. Ensure there are no mutable references to `T`.
    /// 2. Ensure `T` is initialized.
    /// 3. Ensure `T` is not dropped.
    #[inline]
    pub(crate) unsafe fn data_ref(&self) -> &T {
        // SAFETY: the caller must uphold the safety requirements
        unsafe { &*self.data.get() }
    }

    /// Returns a unique reference to the data.
    ///
    /// # Safety
    ///
    /// 1. Ensure there are no other references to `T`.
    /// 2. Ensure `T` is initialized.
    /// 3. Ensure `T` is not dropped.
    #[inline]
    pub(crate) unsafe fn data_mut(&self) -> &mut T {
        // SAFETY: this goes through UnsafeCell, and its documentation
        // states it is allowed to have a shared reference to the cell and
        // a mutable reference to the content of the cell simultaneously, as
        // long as there are no other references to the content of the cell.
        unsafe { &mut *self.data.get() }
    }

    /// Runs the destructor of the data.
    ///
    /// # Safety
    ///
    /// 1. Ensure there are no references to `T`.
    /// 2. Ensure `T` is initialized.
    /// 3. Ensure `T` is not already dropped.
    pub(crate) unsafe fn drop_data(&self) {
        // SAFETY: the caller must uphold the safety requirements
        unsafe { ptr::drop_in_place(self.data.get()) };
        self.inner.status.set(Status::Dropped);
    }
}

/// Panics.
///
/// Is unlikely to be called, so it has a 'cold' attribute for optimization.
#[cold]
#[inline(never)]
fn cold_panic() {
    panic!()
}

/// Returns false.
///
/// Is unlikely to be called, so it has a 'cold' attribute for optimization.
#[cold]
#[inline(never)]
fn cold_false() -> bool {
    false
}

///////////////////////////////////////////////////////////////////////////////
// Constructors
///////////////////////////////////////////////////////////////////////////////

/// Creates a new pointer.
#[inline]
pub(crate) fn new_ref_box<T>(value: T) -> RefBox<T> {
    let heap = Box::into_raw(Box::new(RefBoxHeap {
        inner: RefBoxHeapInner {
            status: Cell::new(Status::Available),
            refcount: Cell::new(0),
        },
        data: UnsafeCell::new(value),
    }));

    // SAFETY: `Box::into_raw` ensures the pointer is non-null.
    let ptr = unsafe { NonNull::new_unchecked(heap) };

    RefBox {
        ptr,
        _p: PhantomData,
    }
}

/// Creates a new `RefBox` through a closure which receives a
/// `RefBoxRef` to the same data.
#[cfg(feature = "cyclic")]
#[inline]
pub(crate) fn new_cyclic_ref_box<T, F: FnOnce(&crate::Ref<T>) -> T>(op: F) -> RefBox<T> {
    // Allocate the heap data with uninitialized T data.
    // SAFETY: `status` is set to `Dropped` to avoid being able to access
    // the uninitialized data in the closure.
    let heap = Box::into_raw(Box::new(RefBoxHeap {
        inner: RefBoxHeapInner {
            status: Cell::new(Status::Dropped),
            refcount: Cell::new(1),
        },
        data: UnsafeCell::new(core::mem::MaybeUninit::<T>::uninit()),
    }));

    // SAFETY: `Box::into_raw` ensures the pointer is non-null.
    let ptr = unsafe { NonNull::new_unchecked(heap.cast()) };
    let rc_weak = crate::Ref { ptr };

    // We get the real instance by executing the closure.
    // SAFETY (1): The weak reference is passed by reference to make sure the
    // memory is not deallocated at the end of the closure.
    // SAFETY (2): If this panics, `Ref` will deallocate the heap
    // memory, but since the status was set to `Dropped`, it will not run
    // drop on the uninitialized memory.
    let data = op(&rc_weak);

    // We write the data without reading the old one.
    // SAFETY: we cannot create a reference to the data on the heap as it
    // is uninitialized, so we use `addr_of_mut`.
    unsafe {
        ptr::addr_of_mut!((*ptr.as_ptr()).data).write(UnsafeCell::new(data));
    }

    // Decrease the reference count and forget the weak reference without
    // deallocating or running the destructor of `T`.
    {
        std::mem::forget(rc_weak);
        let heap = unsafe { ptr.as_ref() };
        heap.inner.decrease_refcount();
        heap.inner.status.set(Status::Available);
    }

    RefBox {
        ptr,
        _p: PhantomData,
    }
}

///////////////////////////////////////////////////////////////////////////////
// Dropping & Deallocating
///////////////////////////////////////////////////////////////////////////////

/// Deallocates the heap part of the `RefBox`.
unsafe fn dealloc_heap<T: ?Sized>(heap: NonNull<RefBoxHeap<T>>) {
    // In case of a panic in new_cyclic, `heap` contains partially
    // uninitialized memory. It is UB to have a reference to uninitialized
    // memory, so we need to get the layout through a raw pointer. This
    // requires Nightly feature 'layout_for_ptr'.

    #[cfg(feature = "cyclic")]
    let layout = alloc::Layout::for_value_raw(heap.as_ptr());
    #[cfg(not(feature = "cyclic"))]
    let layout = alloc::Layout::for_value(unsafe { heap.as_ref() });

    unsafe { alloc::dealloc(heap.as_ptr().cast(), layout); }
}

/// Called when the owning RefBox is dropped.
#[inline]
pub(crate) unsafe fn drop_ref_box<T: ?Sized>(heap: NonNull<RefBoxHeap<T>>) {
    // SAFETY: the data of the owner is always initialized,
    // so we can create references to the RefBoxHeap.

    match unsafe { heap.as_ref() }.inner.status() {
        Status::Available => {
            // If there is no active borrow, the data should
            // be dropped when the owner is dropped.
            // SAFETY: the status is `Available`, so the `RefBoxHeap` is initialized, there are no
            // other references to it, and it is not yet dropped.
            unsafe { heap.as_ref().drop_data() };

            // If there are no weak references, the heap
            // part should be deallocated as well.
            if unsafe { heap.as_ref() }.inner.refcount() == 0 {
                // SAFETY: there are no more references to the data.
                unsafe { dealloc_heap(heap) };
            }
        }
        Status::Borrowed => {
            // It is possible to drop the owner of the data while
            // a borrow is active. In that case, dropping of the data is
            // delayed until the borrow is dropped.
            unsafe { heap.as_ref() }.inner.status.set(Status::DroppedWhileBorrowed);
        }
        Status::DroppedWhileBorrowed | Status::Dropped => {
            // SAFETY: if the status is `DroppedWhileBorrowed` or `Dropped` it means
            // the RefBox is dropped a second time which is already UB.
            unsafe { std::hint::unreachable_unchecked() };
        }
    }
}

/// Called when a weak Ref is dropped.
#[inline]
pub(crate) unsafe fn drop_ref<T: ?Sized>(heap: NonNull<RefBoxHeap<T>>) {
    // SAFETY: the data of a Ref may be uninitialized, so we have to
    // make sure not to create a reference that covers the `data` field
    // of RefBoxHeap.

    // Decrease the reference count.
    let refcount = unsafe { &(*heap.as_ptr()).inner }.decrease_refcount();

    // If there are no more references and the owner is dropped,
    // the data needs to be deallocated.
    if refcount == 0 {
        if unsafe { &(*heap.as_ptr()).inner }.status() == Status::Dropped {
            // SAFETY: there are no more references to the heap part.
            unsafe { dealloc_heap(heap) };
        }
    }
}

/// Called when a Borrow is dropped.
#[inline]
pub(crate) unsafe fn drop_borrow<T: ?Sized>(heap: &RefBoxHeap<T>) {
    match heap.inner.status() {
        Status::Borrowed => {
            heap.inner.status.set(Status::Available);
        }
        Status::DroppedWhileBorrowed => {
            // The owner was dropped during the lifetime of the borrow.
            // Dropping is delayed till the end of the borrow.
            // SAFETY: after this the data cannot be accessed anymore,
            // because drop_data sets the status to `Dropped`.
            unsafe { heap.drop_data() };
        }
        Status::Available | Status::Dropped => {
            // SAFETY: It is not possible to create a borrow if the status is `Dropped`,
            // and it is not possible for the status to become `Dropped` while a
            // `Borrow` exists, because if the owner is dropped during an active
            // borrow, the status is set to `DroppedWhileBorrowed`.
            // It is also not possible for the status to be `Available`, as it is
            // set to `Borrowed` when the `Borrow` is created.
            unsafe { std::hint::unreachable_unchecked() };
        }
    }
}

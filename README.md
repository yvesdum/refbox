# RefBox

A smart pointer with many reference-counted weak references.

A `RefBox` is a smart pointer that owns the data, just like a standard `Box`. Similarly, a RefBox cannot be cloned cheaply, and when it is dropped, the data it points to is dropped as well. However, a RefBox may have many `Ref` pointers to the same data. These pointers don’t own the data and are reference counted, comparable to the standard library's `Weak`. Which means, as long as the RefBox is alive, Refs can be used to access the data from multiple places without lifetime parameters.

A RefBox could be seen as a lighter alternative to the standard library’s `Rc`, `Weak` and `RefCell` combination in cases where there is one Rc with many Weaks to the same data.

A RefBox does not differentiate between strong and weak pointers and immutable and mutable borrows. There is always a single strong pointer, zero, one or many weak pointers and all borrows are mutable. This means there can only be one borrow active at any given time. But in return, RefBox uses less memory, is faster to borrow from, and a Ref does not need to be upgraded to a RefBox in order to access the data. In fact, upgrading is not possible at all.

Note: this crate is currently **experimental** and requires Nightly Rust.

## Rc<RefCell<T>> vs RefBox<T>

|                  | `Rc<RefCell<T>>`                                               | `RefBox<T>`                                     |
|------------------|----------------------------------------------------------------|-------------------------------------------------|
| Pointer kinds    | Many strong pointers and many weak pointers                    | One strong owner and many weak pointers         |
| Clonable         | Both `Rc` and `Weak` are cheap to clone                        | Only `Ref` can be cheaply cloned                |
| Up-/Downgrading  | `Rc` is downgradable, `Weak` is upgradable                     | No up- or downgrading, but `RefBox::create_ref` |
| Data access      | `RefCell::try_borrow_mut`                                      | `RefBox::try_borrow_mut`                        |
| Weak data access | 1. `Weak::upgrade`<br>2. `RefCell::try_borrow_mut`<br>3. `Rc::drop` | `Ref::try_borrow_mut`                      |
| Active borrows   | One mutable or many immutable                                  | One (mutable or immutable)                      |
| `T::drop`        | When all `Rc`s are dropped                                     | When owner `RefBox` is dropped                  |
| Max no. `Weak`s  | `usize::MAX`                                                   | `u32::MAX`                                      |
| Heap overhead    | 64-bit: 24 bytes<br>32-bit: 12 bytes                           | 8 bytes                                         |
| Performance      | Cloning is fast, mutating is slow             | Cloning references is a tiny bit slower, mutating is much faster |

## Examples

```rust
use refbox::RefBox;

fn main() {
    // Create a RefBox.
    let owner = RefBox::new(100);

    // Create a weak reference.
    let weak = owner.create_ref();

    // Access the data.
    let borrow = weak.try_borrow_mut().unwrap();
    assert_eq!(*borrow, 100);
}
```

## Performance comparison

A number of benchmarks are included to compare the performance of `RefBox` vs `Rc`. Each benchmark follows the same process:

1. An `Rc` or `RefBox` is created, with optionally a weak reference;
2. An operation is performed for x number of times;
3. The Rc or RefBox is dropped.

The horizontal axes show the number of times the operation was performed. The vertical axes show the average time it took to complete the entire process described above.

The benchmarks are performed on an HP Intel Core i7-7700HQ CPU @ 2.80GHz, Windows 10 64-bit. You are encouraged to perform the benchmarks yourself as well.

**Mutating through the owner takes less time (only ~80%):**

![Benchmark: mutate through owner, RefBox is faster.](./bench_results/20220406_mutate_through_owner.svg)

**Mutating through a weak reference takes much less time (only ~36%):**

![Benchmark: mutate through weak reference, RefBox is much faster.](./bench_results/20220406_mutate_through_weak_reference.svg)

**However, creating, cloning and dropping weak references takes a little bit more time:**

![Benchmark: create and drop first reference, Rc is slightly faster.](./bench_results/20220406_create_and_drop_weak_reference.svg)

![Benchmark: clone and drop references, Rc is slightly faster.](./bench_results/20220406_clone_and_drop_weak_reference.svg)
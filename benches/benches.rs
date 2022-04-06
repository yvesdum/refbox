use std::cell::RefCell;
use std::rc::Rc;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use refbox::RefBox;

const BORROWS: [usize; 5] = [1, 100, 1000, 5000, 10000];

pub fn mutate_through_owner(c: &mut Criterion) {
    let mut group = c.benchmark_group("Mutate through owner");

    for i in BORROWS.into_iter() {
        group.bench_with_input(BenchmarkId::new("Rc + RefCell", i), &i, |b, _| {
            b.iter(|| {
                let rc = Rc::new(RefCell::new(0));
                for _ in 0..i {
                    let mut borrow = rc.try_borrow_mut().unwrap();
                    *borrow = 100;
                    drop(black_box(borrow));
                }
                rc
            })
        });

        group.bench_with_input(BenchmarkId::new("RefBox", i), &i, |b, _| {
            b.iter(|| {
                let rc = RefBox::new(0);
                for _ in 0..i {
                    let mut borrow = rc.try_borrow_mut().unwrap();
                    *borrow = 100;
                    drop(black_box(borrow));
                }
                rc
            })
        });
    }

    group.finish();
}

pub fn mutate_through_weak(c: &mut Criterion) {
    let mut group = c.benchmark_group("Mutate through weak reference");

    for i in BORROWS.into_iter() {
        group.bench_with_input(BenchmarkId::new("Rc + Weak + RefCell", i), &i, |b, _| {
            b.iter(|| {
                let rc = Rc::new(RefCell::new(0));
                let weak = Rc::downgrade(&rc);
                for _ in 0..i {
                    let upgraded = weak.upgrade().unwrap();
                    let mut borrow = upgraded.try_borrow_mut().unwrap();
                    *borrow = 100;
                    drop(black_box(borrow));
                    drop(upgraded);
                }
                drop(weak);
                rc
            })
        });

        group.bench_with_input(BenchmarkId::new("RefBox + Ref", i), &i, |b, _| {
            b.iter(|| {
                let rc = RefBox::new(0);
                let weak = rc.create_ref();
                for _ in 0..i {
                    let mut borrow = weak.try_borrow_mut().unwrap();
                    *borrow = 100;
                    drop(black_box(borrow));
                }
                drop(weak);
                rc
            })
        });
    }

    group.finish();
}

pub fn create_weak(c: &mut Criterion) {
    let mut group = c.benchmark_group("Create and drop weak reference");

    for i in BORROWS.into_iter() {
        group.bench_with_input(BenchmarkId::new("Rc + Weak + RefCell", i), &i, |b, _| {
            b.iter(|| {
                let rc = Rc::new(RefCell::new(0));
                for _ in 0..i {
                    let weak = Rc::downgrade(&rc);
                    drop(black_box(weak));
                }
                rc
            })
        });

        group.bench_with_input(BenchmarkId::new("RefBox + Ref", i), &i, |b, _| {
            b.iter(|| {
                let rc = RefBox::new(0);
                for _ in 0..i {
                    let weak = rc.create_ref();
                    drop(black_box(weak));
                }
                rc
            })
        });
    }

    group.finish();
}

pub fn clone_weak(c: &mut Criterion) {
    let mut group = c.benchmark_group("Clone and drop weak reference");

    for i in BORROWS.into_iter() {
        group.bench_with_input(BenchmarkId::new("Rc + Weak + RefCell", i), &i, |b, _| {
            b.iter(|| {
                let rc = Rc::new(RefCell::new(0));
                let weak = Rc::downgrade(&rc);
                for _ in 0..i {
                    let clone = weak.clone();
                    drop(black_box(clone));
                }
                drop(weak);
                rc
            })
        });

        group.bench_with_input(BenchmarkId::new("RefBox + Ref", i), &i, |b, _| {
            b.iter(|| {
                let rc = RefBox::new(0);
                let weak = rc.create_ref();
                for _ in 0..i {
                    let clone = weak.clone();
                    drop(black_box(clone));
                }
                drop(weak);
                rc
            })
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    mutate_through_owner,
    mutate_through_weak,
    create_weak,
    clone_weak
);
criterion_main!(benches);

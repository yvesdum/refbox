# Changelog

## 0.4.0

* Added `cyclic_stable` feature
* Changed the Rust edition to 2024
* Changed `Ref` to `Weak` to resemble the types in the standard library
* Changed `create_ref()` to `downgrade()` to resemble the method in the standard library
* 

## 0.3.0

* Added optional feature `cyclic`
* Changed: `RefBox::new_cyclic` is now behind optional feature `cyclic`
* Fixed: crate now compiles on stable Rust, except `cyclic` feature

## 0.2.0

* Added `RefBox::as_ptr` and `Ref::as_ptr` methods
* Added tests for `RefBox::as_ptr` and `Ref::as_ptr`

## 0.1.0

Initial Release
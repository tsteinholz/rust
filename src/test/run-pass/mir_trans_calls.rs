// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(rustc_attrs)]
use std::os::raw;

#[rustc_mir]
fn test1(a: isize, b: (i32, i32), c: &[i32]) -> (isize, (i32, i32), &[i32]) {
    // Test passing a number of arguments including a fat pointer.
    // Also returning via an out pointer
    fn callee(a: isize, b: (i32, i32), c: &[i32]) -> (isize, (i32, i32), &[i32]) {
        (a, b, c)
    }
    callee(a, b, c)
}

#[rustc_mir]
fn test2(a: isize) -> isize {
    // Test passing a single argument.
    // Not using out pointer.
    fn callee(a: isize) -> isize {
        a
    }
    callee(a)
}

struct Foo;
impl Foo {
    fn inherent_method(&self, a: isize) -> isize { a }
}

#[rustc_mir]
fn test3(x: &Foo, a: isize) -> isize {
    // Test calling inherent method
    x.inherent_method(a)
}

trait Bar {
    fn extension_method(&self, a: isize) -> isize { a }
}
impl Bar for Foo {}

#[rustc_mir]
fn test4(x: &Foo, a: isize) -> isize {
    // Test calling extension method
    x.extension_method(a)
}

#[rustc_mir]
fn test5(x: &Bar, a: isize) -> isize {
    // Test calling method on trait object
    x.extension_method(a)
}

#[rustc_mir]
fn test6<T: Bar>(x: &T, a: isize) -> isize {
    // Test calling extension method on generic callee
    x.extension_method(a)
}

trait One<T = Self> {
    fn one() -> T;
}
impl One for isize {
    fn one() -> isize { 1 }
}

#[rustc_mir]
fn test7() -> isize {
    // Test calling trait static method
    <isize as One>::one()
}

struct Two;
impl Two {
    fn two() -> isize { 2 }
}

#[rustc_mir]
fn test8() -> isize {
    // Test calling impl static method
    Two::two()
}

extern fn simple_extern(x: u32, y: (u32, u32)) -> u32 {
    x + y.0 * y.1
}

#[rustc_mir]
fn test9() -> u32 {
    simple_extern(41, (42, 43))
}

extern {
    #[cfg_attr(windows, link_name="wsprintfA")]
    fn sprintf(_: *mut raw::c_char, _: *const raw::c_char, ...) -> raw::c_int;
}

#[rustc_mir]
fn test10(i: i32, j: i32, k: i32) -> Vec<raw::c_char> {
    let mut x: Vec<raw::c_char> = Vec::with_capacity(512);
    unsafe {
        let out = sprintf(x.as_mut_ptr(), b"%d %d %d\0".as_ptr() as *const raw::c_char, i, j, k);
        assert!(out > 0);
        x.set_len(out as usize);
    }
    x
}


#[rustc_mir]
fn test_closure<F>(f: &F, x: i32, y: i32) -> i32
    where F: Fn(i32, i32) -> i32
{
    f(x, y)
}

#[rustc_mir]
fn test_fn_object(f: &Fn(i32, i32) -> i32, x: i32, y: i32) -> i32 {
    f(x, y)
}

#[rustc_mir]
fn test_fn_impl(f: &&Fn(i32, i32) -> i32, x: i32, y: i32) -> i32 {
    // This call goes through the Fn implementation for &Fn provided in
    // core::ops::impls. It expands to a static Fn::call() that calls the
    // Fn::call() implemenation of the object shim underneath.
    f(x, y)
}

fn main() {
    assert_eq!(test1(1, (2, 3), &[4, 5, 6]), (1, (2, 3), &[4, 5, 6][..]));
    assert_eq!(test2(98), 98);
    assert_eq!(test3(&Foo, 42), 42);
    assert_eq!(test4(&Foo, 970), 970);
    assert_eq!(test5(&Foo, 8576), 8576);
    assert_eq!(test6(&Foo, 12367), 12367);
    assert_eq!(test7(), 1);
    assert_eq!(test8(), 2);
    assert_eq!(test9(), 41 + 42 * 43);
    assert_eq!(&test10(0, 42, 31415), &[48, 32, 52, 50, 32, 51, 49, 52, 49, 53]);

    let closure = |x: i32, y: i32| { x + y };
    assert_eq!(test_closure(&closure, 100, 1), 101);
    let function_object = &closure as &Fn(i32, i32) -> i32;
    assert_eq!(test_fn_object(function_object, 100, 2), 102);
    assert_eq!(test_fn_impl(&function_object, 100, 3), 103);
}

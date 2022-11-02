// https://verus-lang.github.io/verus/guide

#![no_main]
#![allow(macro_expanded_macro_exports_accessed_by_absolute_paths)]

extern crate core;
extern crate alloc;

extern crate builtin;
extern crate builtin_macros;

use builtin_macros::verus;
use builtin::*;
mod pervasive;
use pervasive::*;

verus! {

fn octuple(x1: i8) -> (x8: i8)
    requires
        -16 <= x1,
        x1 < 16,
    ensures
        x8 == 8 * x1,
{
    let x2 = x1 + x1;
    let x4 = x2 + x2;
    x4 + x4
}

}

fn main() {
    let n = octuple(10);
    assert(n == 80);
}

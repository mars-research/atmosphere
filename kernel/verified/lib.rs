#![no_std]

use vstd::prelude::verus;

pub mod define;
pub mod trap;
pub mod array;
pub mod array_set;
pub mod array_vec;
pub mod slinkedlist;
pub mod pagetable;
pub mod allocator;
pub mod process_manager;
pub mod memory_manager;
pub mod va_range;

pub mod kernel;

pub mod lemma;
pub mod util;

pub mod user_level_isolation;

verus! {

global size_of usize == 8;

}

fn main(){

}

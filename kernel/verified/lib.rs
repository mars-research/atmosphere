#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(verus_keep_ghost), allow(unused_variables, dead_code))]

#![feature(const_maybe_uninit_zeroed)]

pub mod array;
pub mod array_vec;
pub mod bridge;
pub mod linked_list;
pub mod mem;
pub mod page_arena;
// pub mod paging;
pub mod iommutable;
pub mod kernel;
pub mod page_alloc;
pub mod pagetable;
pub mod proc;
// pub mod pcid_alloc;
pub mod cpu;
pub mod mars_array;
pub mod mars_staticlinkedlist;
pub mod mmu;
// pub mod setters;
pub mod define;
pub mod trap;
// pub mod proc_getters;

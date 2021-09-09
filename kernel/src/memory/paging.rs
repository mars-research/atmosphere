//! Paging.
//!
//! We support 4KiB pages as well as 2MiB and 1GiB huge/large pages.
//!

#[repr(align(4096))]
#[repr(C)]
pub struct PageDirectory {

}

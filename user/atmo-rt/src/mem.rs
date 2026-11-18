//! Page-granular memory for stacks and queue storage.
//!
//! The kernel has no call to return pages, so freed ranges are kept and given
//! out again to requests of the same size.

use core::cell::UnsafeCell;

use crate::sys::{self, PAGE_SIZE};

/// The address range that the runtime maps pages in. The image and the first
/// stack are below it.
const REGION_BASE: usize = 0xa0_0000_0000;
const REGION_END: usize = REGION_BASE + (4 << 30);

const MAX_FREE: usize = 128;

struct Pages {
    next: usize,
    free: [(usize, usize); MAX_FREE],
    free_len: usize,
}

struct Shared(UnsafeCell<Pages>);
unsafe impl Sync for Shared {}

static PAGES: Shared =
    Shared(UnsafeCell::new(Pages { next: REGION_BASE, free: [(0, 0); MAX_FREE], free_len: 0 }));

/// Returns the address of `pages` zeroed pages, or `None` if there is no
/// memory left.
pub fn alloc_pages(pages: usize) -> Option<usize> {
    if pages == 0 {
        return None;
    }
    let p = unsafe { &mut *PAGES.0.get() };
    let mut addr = None;
    for i in 0..p.free_len {
        if p.free[i].1 == pages {
            addr = Some(p.free[i].0);
            p.free_len -= 1;
            p.free[i] = p.free[p.free_len];
            break;
        }
    }
    let addr = match addr {
        Some(addr) => addr,
        None => {
            let bytes = pages.checked_mul(PAGE_SIZE)?;
            let addr = p.next;
            if bytes > REGION_END - addr || !sys::map_pages(addr, pages) {
                return None;
            }
            p.next = addr + bytes;
            addr
        }
    };
    unsafe { core::ptr::write_bytes(addr as *mut u8, 0, pages * PAGE_SIZE) };
    Some(addr)
}

/// Gives back a range that `alloc_pages` returned.
pub fn free_pages(addr: usize, pages: usize) {
    let p = unsafe { &mut *PAGES.0.get() };
    if p.free_len < MAX_FREE {
        p.free[p.free_len] = (addr, pages);
        p.free_len += 1;
    }
    // Otherwise the range stays mapped and unused.
}

/// Skips `pages` pages of address space and leaves them unmapped. A stack that
/// overflows into them faults.
pub fn reserve_gap(pages: usize) {
    let p = unsafe { &mut *PAGES.0.get() };
    p.next += pages * PAGE_SIZE;
}

/// Maps `pages` zeroed pages and returns their address, or null.
#[no_mangle]
pub extern "C" fn art_pages_alloc(pages: usize) -> *mut u8 {
    match alloc_pages(pages) {
        Some(addr) => addr as *mut u8,
        None => core::ptr::null_mut(),
    }
}

/// Gives back pages from `art_pages_alloc`.
#[no_mangle]
pub extern "C" fn art_pages_free(addr: *mut u8, pages: usize) {
    if !addr.is_null() && pages != 0 {
        free_pages(addr as usize, pages);
    }
}

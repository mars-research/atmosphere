//! Simple bump allocator.
//!
//! Since our only purpose is to load the microkernel and the
//! initial task, we can keep this simple.

use super::println;
use core::alloc::{GlobalAlloc, Layout};
use core::ptr;
use core::sync::atomic::{AtomicUsize, Ordering};

#[global_allocator]
pub static mut ALLOCATOR: BumpAllocator = BumpAllocator {
    base: 0 as *mut u8,
    size: 0,
    watermark: AtomicUsize::new(0),
};

pub struct BumpAllocator {
    base: *mut u8,
    size: usize,
    watermark: AtomicUsize,
}

unsafe impl Sync for BumpAllocator {}

unsafe impl GlobalAlloc for BumpAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let mut allocated = ptr::null_mut();

        self.watermark
            .fetch_update(Ordering::SeqCst, Ordering::SeqCst, |mut watermark| {
                let mut required_size = layout.size();
                let mut obj_start = self.base.addr() + watermark;
                let mask = layout.align() - 1;

                if obj_start & mask != 0 {
                    let aligned = (obj_start | mask) + 1;
                    required_size += aligned - obj_start;
                    obj_start = aligned;
                }

                if watermark + required_size > self.size {
                    log::error!("Out of memory");
                    return None;
                }

                // Sizes larger than isize::MAX are dangerous in unsafe Rust because
                // methods in the pointer primitive type make the assumption that
                // any offset never overflows an isize, even when the method accepts
                // usize as the argument.
                //
                // We do not allow such allocations in Atmosphere.
                //
                // <https://doc.rust-lang.org/std/primitive.pointer.html#method.add>
                if required_size > isize::MAX as usize {
                    log::error!(
                        "Allocation size {} ({} after round-up) too big",
                        layout.size(),
                        required_size
                    );
                    return None;
                }

                allocated = self.base.with_addr(obj_start);
                watermark += required_size;
                Some(watermark)
            })
            .unwrap();

        allocated
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {
        // it's a bump allocator :)
    }
}

impl BumpAllocator {
    /// Reserves a region, returning a new BumpAllocator.
    pub fn reserve(&mut self, size: usize) -> BumpAllocator {
        let layout = Layout::from_size_align(size, 4096).expect("Invalid layout");
        let base = unsafe { self.alloc(layout) };

        Self {
            base,
            size,
            watermark: AtomicUsize::new(0),
        }
    }

    /// Returns the base of the allocation.
    pub fn base(&self) -> *mut u8 {
        self.base
    }
}

/// Initializes the allocator.
///
/// This is not thread-safe and should only be called once.
pub unsafe fn init(base: *mut u8, size: usize) {
    ALLOCATOR.base = base;
    ALLOCATOR.size = size;
    log::info!(
        "Init allocator with base {:x} and size {}",
        base as u64,
        size
    )
}

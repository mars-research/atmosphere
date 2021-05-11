//! Untyped memory.
//!
//! ## Untyped in seL4
//!
//! A very high-level overview of how Untypeds work in seL4 can be found on
//! [https://docs.sel4.systems/Tutorials/untyped.html](the seL4 website). Here we will
//! summarize some of the implementation details for those new to the seL4 codebase
//! and would like to see a comparison.
//!
//! In seL4, the Untyped capability is defined in [`structures_32.bf`](https://github.com/seL4/seL4/blob/41497c6e60eda3eb7dbc38baf3d9677a1132c624/include/object/structures_32.bf#L19-L26)
//! in seL4's bitfield IDL (the 64-bit version is in `structures_64.bf`, and is slightly less
//! readable due to the preprocessor directives). When an Untyped is invoked,
//! `untyped.c` [does the checking procedure](https://github.com/seL4/seL4/blob/41497c6e60eda3eb7dbc38baf3d9677a1132c624/src/object/untyped.c#L26-L27)
//! then [performs the actual retyping](https://github.com/seL4/seL4/blob/41497c6e60eda3eb7dbc38baf3d9677a1132c624/src/object/untyped.c#L273-L277),
//! moving `capFreeIndex` (the watermark) forward in the process.

use core::alloc::Layout;

use astd::capability::{CapError, CapResult};
use super::DowncastedCap;

/// A capability to an untyped memory region.
#[derive(Debug)]
pub struct UntypedCap {
    /// The size of the memory region.
    size: usize,

    /// The watermark as an offset to base.
    ///
    /// Addresses before the watermark are already retyped, and addresses after
    /// the watermark are available. In seL4, this is stored in the `capFreeIndex`
    /// bitfield ([source](https://github.com/seL4/seL4/blob/41497c6e60eda3eb7dbc38baf3d9677a1132c624/include/object/structures_32.bf#L19-L26)).
    watermark: usize,
}

impl UntypedCap {
    pub unsafe fn new(size: usize) -> Self {
        Self {
            size,
            watermark: 0,
        }
    }

    /// Performs an allocation, moving the watermark forward.
    ///
    /// This is the low-level method used by the retype operation. In seL4,
    /// the watermark is first moved to the alignment of the object before
    /// incremented by the size of the object.
    fn allocate(self: &mut DowncastedCap<Self>, layout: Layout) -> CapResult<*mut u8> {
        let mut required_size = layout.size();
        let mut obj_start = self.watermark_ptr() as usize;
        let mask = layout.align() - 1;

        if obj_start & mask != 0 {
            let aligned = (obj_start | mask) + 1;
            required_size += aligned - obj_start;
            obj_start = aligned;
        }

        if self.watermark + required_size > self.size {
            return Err(CapError::InsufficientMemory);
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
            return Err(CapError::InsufficientMemory);
        }

        self.watermark += required_size;
        Ok(obj_start as *mut u8)
    }

    /// Returns the watermark as a pointer.
    #[inline]
    fn watermark_ptr(self: &DowncastedCap<Self>) -> *const u8 {
        unsafe { self.capability().object.add(self.watermark) }
    }
}

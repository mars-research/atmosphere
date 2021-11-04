//! Untyped memory.
//!
//! ## Untyped in seL4
//!
//! A very high-level overview of how Untypeds work in seL4 can be found on
//! [the seL4 website](https://docs.sel4.systems/Tutorials/untyped.html). Here we will
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
use core::ptr;

use astd::capability::{CapError, CapResult};
use super::{Capability, CapPointer, CapType, CSpace, DowncastedCap};

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

    /// Performs a retype, creating a new capability.
    pub fn retype(mut self: DowncastedCap<Self>,
        capability_type: CapType,
        this_cspace: &CSpace,
        destination_cap: CapPointer
    ) -> CapResult<()> {
        let layout = super::kernel_layout(capability_type)
            .ok_or(CapError::NotRetypable)?;

        let cslot = this_cspace.resolve(destination_cap)
            .ok_or(CapError::InvalidPointer)?;

        if cslot.is_some() {
            return Err(CapError::SlotInUse);
        }

        let object = self.allocate(layout)?;
        let data = super::new_capability(capability_type, object)?;
        let capability = Capability {
            object,
            data,
            // permissions: PermissionSet::maximum(),
            prev: ptr::null(),
            next: ptr::null(),
            depth: self.capability().depth + 1,
        };

        cslot.replace(capability);

        let cap_mem = cslot.as_mut().unwrap() as *mut Capability;

        unsafe { self.capability().as_mut().insert_child(cap_mem) }
    }

    /// Returns the watermark as a pointer.
    #[inline]
    fn watermark_ptr(self: &DowncastedCap<Self>) -> *const u8 {
        unsafe { self.capability().object.add(self.watermark) }
    }
}

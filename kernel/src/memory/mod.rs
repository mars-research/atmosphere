//! Memory management.

use x86::bits64::paging::{PAddr, VAddr};

use astd::collections::vec::Vec;
use astd::sync::Mutex;

/// A list of usable RAM regions as (base, size) tuples.
pub static RAM_REGIONS: Mutex<Vec<(u64, u64), 10>> = Mutex::new(Vec::new());

/*
/// Returns the virtual address for a physical address in the kernel.
pub fn get_virtual(physical: PAddr) -> VAddr {
    physical.as_usize().into()
}
*/

/// Returns the physical address for a virtual address in the kernel.
pub fn get_physical(r#virtual: VAddr) -> PAddr {
    r#virtual.as_usize().into()
}

/// Returns the end of the kernel.
pub fn get_kernel_end() -> u64 {
    extern "C" {
        static __end: u8;
    }
    unsafe { &__end as *const _ as u64 }
}

/// Initializes memory.
///
/// This should be called only once.
pub unsafe fn init() {
    let mut ram_regions = RAM_REGIONS.lock();
    let bootinfo = crate::boot::get_bootinfo();
    let memory_map = bootinfo.memory_regions().expect("Could not find valid memory map");
    let kernel_end = get_kernel_end();

    log::info!("Physical RAM map:");
    for entry in memory_map {
        let mut size = entry.length();
        let mut start = entry.base_address();
        let end = start + size;
        log::info!("[mem {:#016x}-{:#016x}] {:?}", start, end + 1, entry.memory_type());

        if start < kernel_end {
            if end <= kernel_end {
                continue;
            }

            size -= kernel_end - start;
            start = kernel_end;
        }

        ram_regions.push((start, size)).unwrap();
    }
}

/// Initializes memory.
///
/// This should be called only once per CPU.
pub unsafe fn init_cpu() {
}

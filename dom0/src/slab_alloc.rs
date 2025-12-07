use core::alloc::{GlobalAlloc, Layout};
use core::mem::transmute;
use core::ptr;
use core::ptr::NonNull;
use log::trace;
use slabmalloc::*;
use spin::Mutex;
use constants::*;

/// SLAB_ALLOC is set as the system's default allocator, it's implementation follows below.
///
/// It's a ZoneAllocator wrapped inside a Mutex.
#[global_allocator]
static SLAB_ALLOC: SafeZoneAllocator = SafeZoneAllocator(Mutex::new(ZoneAllocator::new()));

struct Pager;

static BASE_ADDR: Mutex<usize> = Mutex::new(0xA0_0001_0000);

impl Pager {
    const BASE_PAGE_SIZE: usize = 4096;
    const LARGE_PAGE_SIZE: usize = 2 * 1024 * 1024;

    /// Allocates a given `page_size`.
    fn alloc_page(&mut self, page_size: usize) -> Option<*mut u8> {
        trace!("alloc_page {}", page_size);
        let r = unsafe {
            let mut mmap_base = BASE_ADDR.lock();
            let num_pages = page_size / Self::BASE_PAGE_SIZE;

            if page_size == Self::LARGE_PAGE_SIZE {
                // fix alignment of the base address
                let off_by = *mmap_base & (Self::LARGE_PAGE_SIZE - 1);
                *mmap_base += Self::LARGE_PAGE_SIZE - off_by;
            }
            // FIXME: 2MiB pages are a bunch of 4KiB virtual pages stacked together
            match asys::sys_mmap(*mmap_base, 0x0000_0000_0000_0002u64 as usize, num_pages) {
                0 => {
                    let _mmap_addr = *mmap_base;
                    *mmap_base += page_size;
                    let error_code = asys::sys_io_mmap(_mmap_addr, 0x0000_0000_0000_0002u64 as usize, num_pages);
                    if error_code != 0 {
                        log::error!("sys_io_mmap failed {:?}", error_code);
                        0 as *mut u8
                    } else {
                        // log::info!("Invalidate_iotlb for {:>02x}:{:>02x}.{:01x}", NVME_PCI_DEV.0, NVME_PCI_DEV.1, NVME_PCI_DEV.2);
                        log::info!("Invalidate_iotlb for {:>02x}:{:>02x}.{:01x}", 0x17, 0x00, 0);
                        if page_size == Self::LARGE_PAGE_SIZE {
                            let base_addr = _mmap_addr as usize;
                            let num_4k_pages = Self::LARGE_PAGE_SIZE / Self::BASE_PAGE_SIZE;
                            for i in 0..num_4k_pages {
                                asys::sys_invalidate_iotlb(0x17, 0x00, 0, _mmap_addr as u64);
                                // asys::sys_invalidate_iotlb(NVME_PCI_DEV.0, NVME_PCI_DEV.1, NVME_PCI_DEV.2, (base_addr + i * Self::BASE_PAGE_SIZE) as u64);
                            }
                        } else {
                            asys::sys_invalidate_iotlb(0x17, 0x00, 0, _mmap_addr as u64);
                            // asys::sys_invalidate_iotlb(NVME_PCI_DEV.0, NVME_PCI_DEV.1, NVME_PCI_DEV.2, _mmap_addr as u64);
                        }
                        _mmap_addr as *mut u8
                    }
                }
                _ => {
                    trace!("sys_mmap failure");
                    0 as *mut u8
                }
            }
            //System.alloc(Layout::from_size_align(page_size, page_size).unwrap())
        };

        if !r.is_null() {
            Some(r)
        } else {
            None
        }
    }

    /// De-allocates a given `page_size`.
    fn dealloc_page(&mut self, _ptr: *mut u8, page_size: usize) {
        let _layout = match page_size {
            Pager::BASE_PAGE_SIZE => {
                Layout::from_size_align(Pager::BASE_PAGE_SIZE, Pager::BASE_PAGE_SIZE).unwrap()
            }
            Pager::LARGE_PAGE_SIZE => {
                Layout::from_size_align(Pager::LARGE_PAGE_SIZE, Pager::LARGE_PAGE_SIZE).unwrap()
            }
            _ => unreachable!("invalid page-size supplied"),
        };

        //unsafe { System.dealloc(ptr, layout) };
    }

    /// Allocates a new ObjectPage from the System.
    fn allocate_page(&mut self) -> Option<&'static mut ObjectPage<'static>> {
        trace!("allocate_page {}", Pager::BASE_PAGE_SIZE);
        self.alloc_page(Pager::BASE_PAGE_SIZE)
            .map(|r| unsafe { transmute(r as usize) })
    }

    /// Release a ObjectPage back to the System.
    #[allow(unused)]
    fn release_page(&mut self, p: &'static mut ObjectPage<'static>) {
        self.dealloc_page(p as *const ObjectPage as *mut u8, Pager::BASE_PAGE_SIZE);
    }

    /// Allocates a new LargeObjectPage from the system.
    fn allocate_large_page(&mut self) -> Option<&'static mut LargeObjectPage<'static>> {
        trace!("allocate_large_page {}", Pager::LARGE_PAGE_SIZE);
        self.alloc_page(Pager::LARGE_PAGE_SIZE)
            .map(|r| unsafe { transmute(r as usize) })
    }

    /// Release a LargeObjectPage back to the System.
    #[allow(unused)]
    fn release_large_page(&mut self, p: &'static mut LargeObjectPage<'static>) {
        self.dealloc_page(
            p as *const LargeObjectPage as *mut u8,
            Pager::LARGE_PAGE_SIZE,
        );
    }
}

/// A pager for GlobalAlloc.
static mut PAGER: Pager = Pager;

/// A SafeZoneAllocator that wraps the ZoneAllocator in a Mutex.
///
/// Note: This is not very scalable since we use a single big lock
/// around the allocator. There are better ways make the ZoneAllocator
/// thread-safe directly, but they are not implemented yet.
pub struct SafeZoneAllocator(Mutex<ZoneAllocator<'static>>);

unsafe impl GlobalAlloc for SafeZoneAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        trace!("alloc {}", layout.size());
        match layout.size() {
            0..=ZoneAllocator::MAX_ALLOC_SIZE => {
                let mut zone_allocator = self.0.lock();
                match zone_allocator.allocate(layout) {
                    Ok(nptr) => {
                        trace!("success");
                        nptr.as_ptr()
                    }
                    Err(AllocationError::OutOfMemory) => {
                        if layout.size() <= ZoneAllocator::MAX_BASE_ALLOC_SIZE {
                            PAGER.allocate_page().map_or(ptr::null_mut(), |page| {
                                zone_allocator
                                    .refill(layout, page)
                                    .expect("Could not refill?");
                                zone_allocator
                                    .allocate(layout)
                                    .expect("Should succeed after refill")
                                    .as_ptr()
                            })
                        } else {
                            // layout.size() <= ZoneAllocator::MAX_ALLOC_SIZE
                            PAGER
                                .allocate_large_page()
                                .map_or(ptr::null_mut(), |large_page| {
                                    zone_allocator
                                        .refill_large(layout, large_page)
                                        .expect("Could not refill?");
                                    zone_allocator
                                        .allocate(layout)
                                        .expect("Should succeed after refill")
                                        .as_ptr()
                                })
                        }
                    }
                    Err(AllocationError::InvalidLayout) => panic!("Can't allocate this size"),
                }
            }
            _ => unimplemented!("Can't handle it, probably needs another allocator."),
        }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        match layout.size() {
            0..=ZoneAllocator::MAX_ALLOC_SIZE => {
                if let Some(nptr) = NonNull::new(ptr) {
                    self.0
                        .lock()
                        .deallocate(nptr, layout)
                        .expect("Couldn't deallocate");
                } else {
                    // Nothing to do (don't dealloc null pointers).
                }

                // An proper reclamation strategy could be implemented here
                // to release empty pages back from the ZoneAllocator to the PAGER
            }
            _ => unimplemented!("Can't handle it, probably needs another allocator."),
        }
    }
}

// 05/26/2025 - stubbed implementation 2.0
//
// memory/mod.rs
// Memory wrapper for the mlx5 driver
// Converting between driver familiar interface and Atmos memory functions

use log::debug;
use verified::define::PAGE_SZ;
use verified::page_alloc::page_alloc_impl::*;
use crate::mlx_ethernet::initialization_segment::InitializationSegment;

pub type PhysicalAddress = usize;

// Requirements
// Owns virtual pages and physical frames
// AUtomatically unmaps when dropped
// Can be converted to slices for CPU access
// Provides virtual address for CPU use
pub struct MappedPages {
        size: usize,
        page_ptr: Option<usize>,
}

impl MappedPages {
    pub fn into_borrowed_slice_mut(
        self,
        _offset: usize,
        _count: usize,
    ) -> Result<Self, (Self, &'static str)> {
        // Just return self for now during stubbing
        Ok(self)
    }
}

#[derive(Clone, Copy)]
pub struct BorrowedMappedPages<T, N> {
    _phantom_t: core::marker::PhantomData<T>,
    _phantom_n: core::marker::PhantomData<N>,
}

impl BorrowedMappedPages<InitializationSegment, Mutable> {
        pub fn start_address(self) -> u8 {
                0
        }
}

#[derive(Clone, Copy)]
pub struct Mutable;
pub const MMIO_FLAGS: usize = 0; // TODO: FIX THIS!!

fn debug_print(msg: &str) {
        unsafe {
                asys::sys_print(msg.as_ptr(), msg.len());
        }
}

// Fix function signatures to match usage

// Function requirements
// Allocates both virtual pages and physical pages
// maps them together in the page table
// Returns the physical address for DMA
// Handles MMIO flags for device memory
pub fn create_contiguous_mapping(_size: usize, _flags: usize) -> Result<(MappedPages, PhysicalAddress), &'static str> {
        // Fake integration calls
        let mapped_pages = MappedPages {
                size: _size,
                page_ptr: None
        };

        let phys_addr = 0x1;
        debug_print("inside create_contiguous_mapping!\n");
        
        Ok((mapped_pages, phys_addr))
}

pub fn map_frame_range(_start: usize, _count: usize, abc: usize) -> Result<MappedPages, &'static str> {
    Ok(MappedPages { size: 0, page_ptr: None })
}

impl MappedPages {
    pub fn empty() -> Self {
        MappedPages { size: 0, page_ptr: None }
    }
    pub fn start_address(&self) -> usize {
        0
    }
    pub fn split(
        &self,
        _page: crate::memory_structs::Page,
    ) -> Result<(
        BorrowedMappedPages<
            crate::mlx_ethernet::initialization_segment::InitializationSegment,
            Mutable,
        >,
        BorrowedMappedPages<
            crate::mlx_ethernet::initialization_segment::InitializationSegment,
            Mutable,
        >,
    ), &'static str> {
        Ok((
            BorrowedMappedPages {
                _phantom_t: core::marker::PhantomData,
                _phantom_n: core::marker::PhantomData,
            },
            BorrowedMappedPages {
                _phantom_t: core::marker::PhantomData,
                _phantom_n: core::marker::PhantomData,
            },
        ))
    }
    pub fn into_borrowed_mut(
        self,
        _offset: usize,
    ) -> Result<BorrowedMappedPages<
        crate::mlx_ethernet::initialization_segment::InitializationSegment,
        Mutable,
    >, (MappedPages, &'static str)> {
        Ok(BorrowedMappedPages {
            _phantom_t: core::marker::PhantomData,
            _phantom_n: core::marker::PhantomData,
        })
    }
}

impl<T, N> BorrowedMappedPages<T, N> {
    pub fn num_cmdq_entries(&self) -> u32 {
        16
    }
    pub fn cmdq_entry_stride(&self) -> u32 {
        64
    }
    pub fn set_physical_address_of_cmdq(&mut self, _addr: usize) -> Result<(), &'static str> {
        Ok(())
    }
    pub fn device_is_initializing(&self) -> bool {
        false
    }
}

impl<T, N> core::ops::Deref for BorrowedMappedPages<T, N> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        unsafe { core::mem::zeroed() }
    }
}

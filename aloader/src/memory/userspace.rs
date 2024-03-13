use x86::current::paging::{PAddr, VAddr};

use crate::memory::{
    AddressSpace, ContiguousMapping, PageProtection, PhysicalAllocator, VirtualMapper,
};
use crate::PAGE_SIZE;

/// The virtual base address userspace programs are loaded to.
pub const USERSPACE_BASE: u64 = 0x80_0000_0000;

pub struct UserspaceMapper<'a, 'b, PGA, PA>
where
    PGA: PhysicalAllocator,
    PA: PhysicalAllocator,
{
    address_space: &'a mut AddressSpace,
    allocator: &'b mut PA,
    page_table_allocator: &'a mut PGA,
    phys_base: u64,
}

impl<'a, 'b, PGA, PA> UserspaceMapper<'a, 'b, PGA, PA>
where
    PGA: PhysicalAllocator,
    PA: PhysicalAllocator,
{
    pub fn new(
        address_space: &'a mut AddressSpace,
        allocator: &'b mut PA,
        page_table_allocator: &'a mut PGA,
    ) -> Self {
        Self {
            address_space,
            allocator,
            page_table_allocator,
            phys_base: 0,
        }
    }
}

impl<'a, 'b, PGA, PA> VirtualMapper for UserspaceMapper<'a, 'b, PGA, PA>
where
    PGA: PhysicalAllocator,
    PA: PhysicalAllocator,
{
    unsafe fn map_anonymous(
        &mut self,
        base: VAddr,
        size: usize,
        _protection: PageProtection,
    ) -> ContiguousMapping {
        if base.0 != 0 {
            ContiguousMapping {
                vaddr: base,
                paddr: PAddr(base.0 - USERSPACE_BASE + self.phys_base),
            }
        } else {
            let paddr = self.allocator.allocate_physical(size);
            self.phys_base = paddr.0 as u64;

            let phys_base = self.phys_base;
            let virt_base = USERSPACE_BASE;

            let mut cur = phys_base;
            while cur < phys_base + size as u64 {
                unsafe {
                    self.address_space.map(
                        self.page_table_allocator,
                        cur - phys_base + virt_base,
                        cur,
                        true,
                        false,
                        false,
                    );

                    cur = cur + PAGE_SIZE as u64;
                }
            }

            ContiguousMapping {
                vaddr: VAddr(virt_base),
                paddr,
            }
        }
    }
}

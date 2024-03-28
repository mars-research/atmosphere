mod allocator;
mod map;
mod paging;
mod userspace;

use core::num::NonZeroU64;
use core::{fmt, ops::DerefMut};

use num_derive::{FromPrimitive, ToPrimitive};
use x86::current::paging::{PAddr, VAddr};

use astd::{boot::PhysicalMemoryType, sync::Mutex};

pub use map::MemoryMap;
pub use paging::{AddressSpace, HUGE_PAGE_SIZE, PAGE_SIZE};
pub use userspace::{UserspaceMapper, USERSPACE_BASE};

pub const MAX_PHYSICAL_MEMORY: usize = 16 * 1024 * 1024 * 1024; // 16 GiB
pub const BOOTSTRAP_SIZE: usize = 512 * 1024 * 1024; // 512 MiB
pub const ALLOCATOR_SIZE: usize = 2 * 1024 * 1024 * 1024; // 2 GiB

/// The physical memory map.
static PHYSICAL_MEMORY_MAP: Mutex<MemoryMap<BootMemoryType>> = Mutex::new(MemoryMap::empty());

/// The memory region reserved for the initial allocator.
static ALLOCATOR_MEMORY_REGION: Mutex<Option<MemoryRange>> = Mutex::new(None);

pub trait VirtualMapper {
    /// Allocates and maps virtual memory.
    ///
    /// If base is null, then the mapping can be at an arbitary address.
    unsafe fn map_anonymous(
        &mut self,
        base: VAddr,
        size: usize,
        protection: PageProtection,
    ) -> ContiguousMapping;
}

pub trait PhysicalAllocator {
    /// Allocates physical memory.
    unsafe fn allocate_physical(&mut self, size: usize) -> PAddr;
}

pub struct ContiguousMapping {
    pub vaddr: VAddr,
    pub paddr: PAddr,
}

#[derive(Debug, Clone, Copy)]
pub struct PageProtection {
    pub read: bool,
    pub write: bool,
    pub execute: bool,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BootMemoryType {
    Bios,
    Loader,
    LoaderAllocator,
    Kernel,
    Domain,
    DomainImage,
    PageTable,
    KernelPageTable,
    Pci,
    Other(AcpiMemoryType),
}

impl From<BootMemoryType> for PhysicalMemoryType {
    fn from(value: BootMemoryType) -> Self {
        use BootMemoryType as BMT;
        use PhysicalMemoryType as PMT;
        match value {
            // free up loader and domain image for unlimited use
            BMT::Loader | BMT::LoaderAllocator => PMT::Available,
            BMT::DomainImage => PMT::Reserved, // tmp

            BMT::Kernel => PMT::Kernel,
            BMT::Domain => PMT::Domain,
            BMT::PageTable => PMT::PageTable,

            BMT::Bios => PMT::Reserved,
            _ => PMT::Reserved,
        }
    }
}

/// Type of a physical address range.
///
/// As defined in ACPI, Table 14-1 Address Range Types:
/// <https://uefi.org/sites/default/files/resources/ACPI_4_Errata_A.pdf>
#[repr(u32)]
#[derive(Debug, PartialEq, Eq, Clone, Copy, FromPrimitive, ToPrimitive)]
#[non_exhaustive]
pub enum AcpiMemoryType {
    /// This range is available RAM usable by the operating system.
    Memory = 1,

    /// This range of addresses is in use or reserved by the system and is not to be included in the allocatable memory pool of the operating system's memory manager.
    Reserved = 2,

    /// ACPI Reclaim Memory.
    ///
    /// This range is available RAM usable by the OS after it reads the ACPI tables.
    Acpi = 3,

    /// ACPI NVS Memory.
    ///
    /// This range of addresses is in use or reserve by the system and must not be used by the operating system. This range is required to be saved and restored across an NVS sleep.
    Nvs = 4,

    /// This range of addresses contains memory in which errors have been detected. This range must not be used by OSPM.
    Unusable = 5,

    /// This range of addresses contains memory that is not enabled. This range must not be used by OSPM.
    Disabled = 6,
}

/// A range of memory, denoted by the base address and size.
#[derive(Debug, Clone, PartialEq)]
pub struct MemoryRange {
    base: u64,
    size: NonZeroU64,
}

impl MemoryRange {
    pub fn new(base: u64, size: u64) -> Self {
        Self {
            base,
            size: NonZeroU64::new(size).unwrap(),
        }
    }

    pub fn set_size(&mut self, size: u64) {
        self.size = NonZeroU64::new(size).unwrap();
    }

    pub const fn base(&self) -> u64 {
        self.base
    }

    pub const fn size(&self) -> u64 {
        self.size.get()
    }

    pub const fn end_inclusive(&self) -> u64 {
        self.base + self.size.get() - 1
    }

    pub const fn intersects(&self, other: &MemoryRange) -> bool {
        (self.base <= other.end_inclusive()) && (self.end_inclusive() >= other.base)
    }

    pub const fn contains(&self, address: u64) -> bool {
        (self.base <= address) && (address <= self.end_inclusive())
    }

    pub const fn fully_contains(&self, other: &MemoryRange) -> bool {
        (self.base <= other.base) && (self.end_inclusive() >= other.end_inclusive())
    }
}

impl fmt::Display for MemoryRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{:#016x}-{:#016x} ({:#x})",
            self.base(),
            self.end_inclusive(),
            self.size()
        )
    }
}

pub fn init_physical_memory_map(
    regions: impl Iterator<Item = (MemoryRange, AcpiMemoryType)>,
    loader_range: MemoryRange,
    image_ranges: impl Iterator<Item = MemoryRange>,
) {
    let mut map = PHYSICAL_MEMORY_MAP.lock();
    let filtered_regions = regions.filter(|(r, _)| {
        r.base() < MAX_PHYSICAL_MEMORY as u64
    });
    *map = MemoryMap::new(filtered_regions.map(|(r, t)| (r, BootMemoryType::Other(t))));

    map.relabel(MemoryRange::new(0, 1024 * 1024), BootMemoryType::Bios);
    map.relabel(loader_range, BootMemoryType::Loader);
    map.relabel(allocator::get_bootstrap_range(), BootMemoryType::PageTable);

    for image in image_ranges {
        map.relabel(image, BootMemoryType::DomainImage);
    }

    map.sort();

    // Reserve region for bump allocator
    let mut reserved_region = ALLOCATOR_MEMORY_REGION.lock();
    let first_memory = map
        .regions
        .iter()
        .find(|(r, t)| {
            t == &BootMemoryType::Other(AcpiMemoryType::Memory) && r.size() > ALLOCATOR_SIZE as u64
        })
        .expect("No usable memory region");

    let allocator_region = MemoryRange::new(first_memory.0.base(), ALLOCATOR_SIZE as u64);
    map.relabel(allocator_region.clone(), BootMemoryType::LoaderAllocator);

    log::debug!(
        "Reserved region for dynamic allocator: {:#x?}",
        allocator_region,
    );
    *reserved_region = Some(allocator_region.clone());
}

pub fn dump_physical_memory_map() {
    let mut map = PHYSICAL_MEMORY_MAP.lock();

    map.sort();

    for (region, label) in &map.regions {
        log::info!("{:<100} {:?}", region, label);
    }
}

pub unsafe fn init() {
    if let Some(reserved_region) = get_allocator_region() {
        allocator::init(
            reserved_region.base() as *mut u8,
            reserved_region.size() as usize,
        );
    } else {
        panic!("No region was reserved for the allocator");
    }
}

pub fn bootstrap_allocator() -> &'static mut (impl PhysicalAllocator + VirtualMapper) {
    unsafe { &mut allocator::BOOTSTRAP_ALLOCATOR }
}

pub fn allocator() -> &'static mut (impl PhysicalAllocator + VirtualMapper) {
    unsafe { &mut allocator::ALLOCATOR }
}

pub fn reserve(
    size: usize,
    label: BootMemoryType,
) -> (*mut u8, impl PhysicalAllocator + VirtualMapper) {
    let allocator = unsafe { allocator::ALLOCATOR.reserve(size) };

    let mut map = PHYSICAL_MEMORY_MAP.lock();
    map.relabel(allocator.range(), label);

    (allocator.base(), allocator)
}

pub fn get_allocator_region() -> Option<MemoryRange> {
    ALLOCATOR_MEMORY_REGION.lock().clone()
}

pub fn get_physical_memory_map() -> impl DerefMut<Target = MemoryMap<BootMemoryType>> {
    PHYSICAL_MEMORY_MAP.lock()
}

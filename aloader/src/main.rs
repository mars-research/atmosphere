//! The Atmosphere early loader.

#![cfg_attr(not(test), no_std, no_main, feature(start))]
#![feature(alloc_error_handler, strict_provenance, abi_x86_interrupt, asm_const)]
#![deny(
    asm_sub_register,
    deprecated,
    missing_abi,
    unused_macros,
    unused_must_use,
    unused_unsafe
)]
#![deny(clippy::from_over_into, clippy::needless_question_mark)]
#![deny(rustdoc::bare_urls, rustdoc::broken_intra_doc_links)]
#![cfg_attr(not(debug_assertions), deny(dead_code))]

pub mod acpi;
pub mod boot;
pub mod console;
pub mod debugger;
pub mod logging;
pub mod memory;

use core::arch::asm;
use core::slice;

#[cfg(not(test))]
use core::panic::PanicInfo;

use x86::cpuid::cpuid;

use aelf::ElfHandle;
use astd::boot::{BootInfo, DomainMapping, Payload, PhysicalMemoryType};
use astd::io::{Cursor, Read, Seek, SeekFrom};
use astd::memory::{USERSPACE_BASE, USERSPACE_PAYLOAD_BASE};
use constants::*;

use memory::{
    AddressSpace, BootMemoryType, PhysicalAllocator, UserspaceMapper, HUGE_PAGE_SIZE, PAGE_SIZE,
};

const KERNEL_RESERVATION: usize = 1024 * 1024 * 1024; // 1 GiB
const DOM0_RESERVATION: usize = 256 * 1024 * 1024; // 256 MiB

/// Loader entry point.
#[cfg_attr(not(test), start, no_mangle)]
fn main(_argc: isize, _argv: *const *const u8) -> ! {
    unsafe {
        console::init();
        logging::init();
    }

    log::info!("** Atmosphere Loader **");

    unsafe {
        boot::init();
        memory::init();
    }

    let bootstrap_allocator = memory::bootstrap_allocator();

    let mut address_space = AddressSpace::new(bootstrap_allocator);

    let mut address_space_iommu = AddressSpace::new(bootstrap_allocator);

    let mut cur = 0xFEBD4000;
    let virt_base = USERSPACE_BASE;
    while cur < 0xFEBD4000 + 0x4000 {
        unsafe {
            address_space_iommu.map(bootstrap_allocator, cur + virt_base, cur, true, false, true);
            cur = cur + PAGE_SIZE as u64;
        }
    }

    log::info!("Mapping all physical memory");
    let mut cur = 0;
    while cur < 0x240000000 {
        // FIXME
        unsafe {
            address_space.map(bootstrap_allocator, cur, cur, false, false, false);
        }
        cur = cur + PAGE_SIZE as u64;
    }

    let mut boot_info = BootInfo::empty(); // stays on stack
    boot_info.pcide = cpu_has_pcid();

    if boot_info.pcide {
        log::info!("Enabling Tagged TLB");
        unsafe {
            asm!(
                "mov {cr4}, cr4",
                "or {cr4}, {cr4_pcide}",
                "mov cr4, {cr4}",
                cr4 = out(reg) _,
                cr4_pcide = const (1 << 17),
            );
        }
    } else {
        log::warn!("CPU does not support Tagged TLB");
    }

    log::info!("Switching to PML4 @ {:x?}", address_space.pml4());
    unsafe {
        asm!(
            "mov cr3, {pml4}",
            pml4 = inout(reg) address_space.pml4() => _,
        );
    }

    boot_info.pml4 = address_space.pml4();
    boot_info.iommu_base = acpi::probe_iommu();

    let (jumbo_file, jumbo_size) = {
        let range = boot::get_kernel_image_range().expect("No kernel image was passed");

        let f = unsafe { slice::from_raw_parts(range.base() as *const _, range.size() as usize) };
        (Cursor::new(f), f.len())
    };

    let kernel_elf = ElfHandle::parse(jumbo_file, 4096).unwrap();
    let kernel_end = kernel_elf.elf_len();

    let (_, mut kernel_allocator) = memory::reserve(KERNEL_RESERVATION, BootMemoryType::Kernel);
    let (kernel_map, mut jumbo_file) = kernel_elf.load(&mut kernel_allocator).unwrap();

    // Allocate kernel stack
    let stack_size = 16 * 1024 * 1024;
    let stack_base = unsafe { kernel_allocator.allocate_physical(stack_size as usize).0 };

    debugger::add_binary("kernel", kernel_map.load_bias);

    // Load dom0
    jumbo_file
        .seek(SeekFrom::Start(kernel_end as u64))
        .expect("Kernel file incomplete");

    log::info!("After parsing ELF:");
    memory::dump_physical_memory_map();

    match load_domain("dom0", jumbo_file, &mut address_space, bootstrap_allocator) {
        Ok(mut domain) => {
            boot_info.dom0 = Some(domain.mapping);

            // Copy payload as-is into dom0
            let payload_size = jumbo_size as u64 - domain.remaining_file.pos();
            if payload_size != 0 {
                log::info!("Loading payload ({})", payload_size);
                boot_info.payload = Some(Payload {
                    base: USERSPACE_PAYLOAD_BASE as *mut u8,
                    size: payload_size as usize,
                });

                let phys_base =
                    unsafe { domain.allocator.allocate_physical(payload_size as usize).0 };
                let virt_base = USERSPACE_PAYLOAD_BASE;
                let mut cur = virt_base;
                while cur < virt_base + payload_size {
                    unsafe {
                        let paddr = cur - virt_base + phys_base;
                        let page = slice::from_raw_parts_mut(paddr as *mut u8, PAGE_SIZE);

                        address_space.map(bootstrap_allocator, cur, paddr, true, false, false);

                        domain
                            .remaining_file
                            .read(page)
                            .expect("Failed to copy payload page");
                    }
                    cur = cur + PAGE_SIZE as u64;
                }
            }
        }
        Err(e) => {
            log::warn!("No valid Dom0: {:?}", e);
        }
    }

    let mut free_page_count = 0;
    let mut cur = 0;
    log::info!("Populating physical page list");
    for (region, label) in memory::get_physical_memory_map().regions.iter() {
        if boot_info.pages.is_full() {
            break;
        }

        let page_type: PhysicalMemoryType = (*label).into();
        log::info!(
            "region.base() {:x}, region.end_inclusive() {:x}, page_type {:?}, label {:?}",
            region.base(),
            region.end_inclusive(),
            page_type,
            *label
        );
        while cur < region.base() {
            if boot_info.pages.is_full() {
                break;
            }

            boot_info
                .pages
                .push((cur, PhysicalMemoryType::Reserved))
                .expect("Too many pages");
            cur += PAGE_SIZE as u64;
        }
        while cur < region.end_inclusive() {
            if boot_info.pages.is_full() {
                break;
            }

            if page_type == PhysicalMemoryType::Available {
                free_page_count = free_page_count + 1;
            }
            boot_info
                .pages
                .push((cur, page_type))
                .expect("Too many pages");
            cur += PAGE_SIZE as u64;
        }
    }
    while cur < 4 * 1024 * 1024 * 4096 {
        if boot_info.pages.is_full() {
            break;
        }

        boot_info
            .pages
            .push((cur, PhysicalMemoryType::Reserved))
            .expect("Too many pages");
        cur += PAGE_SIZE as u64;
    }

    log::info!("ALoader: Num of free pages --> {:?}", free_page_count);

    debugger::on_ready();

    log::info!("Calling into kernel @ {:x?}", kernel_map.entry_point);
    let ret: usize;
    unsafe {
        asm!(
            // save state
            "mov r15w, ds; push r15w",
            "mov r15w, fs; push r15w",
            "mov r15w, gs; push r15w",
            "mov r15w, ss; push r15w",

            // clear state
            // rdi = &boot_info
            "xor rsi, rsi",
            "xor r15, r15",
            "mov ds, r15w",
            "mov fs, r15w",
            "mov gs, r15w",
            "mov ss, r15w",

            "push rsp",
            "mov rsp, rdi",

            // call entry
            "call rax",

            // restore state
            "pop rsp",
            "pop r15w; mov ss, r15w",
            "pop r15w; mov gs, r15w",
            "pop r15w; mov fs, r15w",
            "pop r15w; mov ds, r15w",

            inout("rax") kernel_map.entry_point => ret,
            inout("rdi") &boot_info as *const _ => _,
            inout("rsi") stack_base + stack_size => _,
            out("r15") _,
        );
    }

    log::info!("Returned from kernel: 0x{:x}", ret);

    loop {}
}

struct Domain<F, A> {
    mapping: DomainMapping,
    remaining_file: F,
    allocator: A,
}

fn load_domain<F, A>(
    name: &'static str,
    mut elf: F,
    address_space: &mut AddressSpace,
    page_table_allocator: &mut A,
) -> Result<Domain<F, impl PhysicalAllocator>, aelf::Error>
where
    F: Read + Seek,
    F::Error: Into<aelf::Error>,
    A: PhysicalAllocator,
{
    let dom_start = elf.stream_position().unwrap() as usize;
    let parsed = ElfHandle::parse(elf, PAGE_SIZE)?;
    let dom_end = dom_start + parsed.elf_len();
    log::info!("Loading {}...", name);

    let (reserved_start, mut allocator) = memory::reserve(DOM0_RESERVATION, BootMemoryType::Domain); // FIXME: Use AddressSpace as allocator

    let mut userspace_mapper =
        UserspaceMapper::new(address_space, &mut allocator, page_table_allocator);
    let (dom_map, mut elf) = parsed
        .load(&mut userspace_mapper)
        .expect("Failed to map Dom0");

    // Allocate and map stack
    // FIXME: Use GNU_STACK
    let stack_size = 16 * 1024 * 1024;
    let phys_base = unsafe { allocator.allocate_physical(stack_size as usize).0 };
    let virt_base = USERSPACE_BASE + DOM0_RESERVATION as u64 - stack_size;

    let mut cur = virt_base;
    while cur < virt_base + stack_size {
        unsafe {
            address_space.map(
                page_table_allocator,
                cur,
                cur - virt_base + phys_base,
                true,
                false,
                false,
            );
        }
        cur = cur + PAGE_SIZE as u64;
    }

    // Nvme bar region
    let mut cur = NVME_BAR_BASE;
    let virt_base = USERSPACE_BASE;
    while cur < NVME_BAR_BASE + NVME_BAR_SIZE as u64 {
        unsafe {
            address_space.map(
                page_table_allocator,
                cur + virt_base,
                cur,
                true,
                false,
                true,
            );
            cur = cur + PAGE_SIZE as u64;
        }
    }

    // Ixgbe bar region
    let mut cur = 0xFE000000;
    let virt_base = USERSPACE_BASE;
    while cur < 0xFE000000 + 0x100000 {
        // while cur < 0xfebf_0000 + 0x1000 {
        unsafe {
            address_space.map(
                page_table_allocator,
                cur + virt_base,
                cur,
                true,
                false,
                true,
            );
            cur = cur + PAGE_SIZE as u64;
        }
    }

    // E810 bar region
    let mut cur = 0xFA000000;
    let virt_base = USERSPACE_BASE;
    while cur < 0xFA000000 + 0x2000000 {
        // while cur < 0xfebf_0000 + 0x1000 {
        unsafe {
            address_space.map(
                page_table_allocator,
                cur + virt_base,
                cur,
                true,
                false,
                true,
            );
            cur = cur + PAGE_SIZE as u64;
        }
    }

    // E810 bar region 2
    let mut cur = 0xFD000000;
    let virt_base = USERSPACE_BASE;
    while cur < 0xFD000000 + 0x10000 {
        // while cur < 0xfebf_0000 + 0x1000 {
        unsafe {
            address_space.map(
                page_table_allocator,
                cur + virt_base,
                cur,
                true,
                false,
                true,
            );
            cur = cur + PAGE_SIZE as u64;
        }
    }

    elf.seek(SeekFrom::Start(dom_end as u64))
        .expect("dom0 incomplete");

    log::debug!("Dom0 end: {}", dom_end);

    debugger::add_binary(name, dom_map.load_bias);

    let mapping = DomainMapping {
        reserved_start,
        reserved_size: DOM0_RESERVATION,
        virt_start: USERSPACE_BASE as *mut u8,
        entry_point: dom_map.entry_point,
        load_bias: dom_map.load_bias,
    };

    Ok(Domain {
        mapping,
        remaining_file: elf,
        allocator,
    })
}

fn cpu_has_pcid() -> bool {
    let cpuid_1 = cpuid!(0x1);
    (cpuid_1.ecx & (1 << 17)) != 0
}

/// The kernel panic handler.
#[cfg(not(test))]
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    log::info!("panic! {:?}", info);
    loop {}
}

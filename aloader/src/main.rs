//! The Atmosphere early loader.

#![cfg_attr(not(test), no_std, no_main, feature(start))]
#![feature(alloc_error_handler, strict_provenance, abi_x86_interrupt)]
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
#![cfg_attr(
    not(debug_assertions),
    deny(dead_code, unused_imports, unused_mut, unused_variables)
)]

pub mod boot;
pub mod console;
pub mod debugger;
pub mod elf;
pub mod logging;
pub mod memory;

use core::arch::asm;
use core::slice;

#[cfg(not(test))]
use core::panic::PanicInfo;

use astd::boot::{BootInfo, DomainMapping, PhysicalMemoryType};
use astd::io::{Cursor, Read, Seek, SeekFrom};

use elf::ElfHandle;
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

    log::info!("Mapping all physical memory");
    let mut cur = 0;
    while cur < 0x240000000 {
        // FIXME
        unsafe {
            address_space.map(bootstrap_allocator, cur, cur, false, true, false);
        }
        cur = cur + HUGE_PAGE_SIZE as u64;
    }

    log::info!("Switching to PML4 @ {:x?}", address_space.pml4());
    unsafe {
        asm!(
            "mov cr3, {pml4}",
            pml4 = inout(reg) address_space.pml4() => _,
        );
    }

    let mut boot_info = BootInfo::empty(); // stays on stack
    boot_info.pml4 = address_space.pml4();

    let kernel_file = {
        let range = boot::get_kernel_image_range().expect("No kernel image was passed");

        let f = unsafe { slice::from_raw_parts(range.base() as *const _, range.size() as usize) };
        Cursor::new(f)
    };

    let kernel_elf = ElfHandle::parse(kernel_file, 4096).unwrap();
    let kernel_end = kernel_elf.elf_end();

    let (_, mut kernel_allocator) = memory::reserve(KERNEL_RESERVATION, BootMemoryType::Kernel);
    let (kernel_map, mut kernel_file) = kernel_elf.load(&mut kernel_allocator).unwrap();
    debugger::add_binary("kernel", kernel_map.load_bias);

    // Also load dom0 if it exists
    kernel_file
        .seek(SeekFrom::Start(kernel_end as u64))
        .expect("Kernel file incomplete");

    log::info!("After parsing ELF:");
    memory::dump_physical_memory_map();

    match load_domain("dom0", kernel_file, &mut address_space, bootstrap_allocator) {
        Ok(dom0) => {
            boot_info.dom0 = Some(dom0);
        }
        Err(e) => {
            log::warn!("No valid Dom0: {:?}", e);
        }
    }

    let mut cur = 0;
    log::info!("Populating physical page list");
    for (region, label) in memory::get_physical_memory_map().regions.iter() {
        let page_type: PhysicalMemoryType = (*label).into();
        log::info!(
            "region.base() {:x}, region.end_inclusive() {:x}, page_type {:?}",
            region.base(),
            region.end_inclusive(),
            page_type
        );
        while cur < region.base() {
            boot_info
                .pages
                .push((cur, PhysicalMemoryType::Reserved))
                .expect("Too many pages");
            cur += PAGE_SIZE as u64;
        }
        while cur < region.end_inclusive() {
            boot_info
                .pages
                .push((cur, page_type))
                .expect("Too many pages");
            cur += PAGE_SIZE as u64;
        }
    }
    while cur < 4 * 1024 * 1024 * 4096 {
        boot_info
            .pages
            .push((cur, PhysicalMemoryType::Reserved))
            .expect("Too many pages");
        cur += PAGE_SIZE as u64;
    }

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

            // call entry
            "call rax",

            // restore state
            "pop r15w; mov ss, r15w",
            "pop r15w; mov gs, r15w",
            "pop r15w; mov fs, r15w",
            "pop r15w; mov ds, r15w",

            inout("rax") kernel_map.entry_point => ret,
            inout("rdi") &boot_info as *const _ => _,
            out("rsi") _,
            out("r15") _,
        );
    }

    log::info!("Returned from kernel: 0x{:x}", ret);

    loop {}
}

fn load_domain<T, A>(
    name: &'static str,
    elf: T,
    address_space: &mut AddressSpace,
    page_table_allocator: &mut A,
) -> Result<DomainMapping, elf::Error>
where
    T: Read + Seek,
    T::Error: Into<elf::Error>,
    A: PhysicalAllocator,
{
    let parsed = ElfHandle::parse(elf, PAGE_SIZE)?;
    log::info!("Loading {}...", name);

    let (reserved_start, mut allocator) = memory::reserve(DOM0_RESERVATION, BootMemoryType::Domain); // FIXME: Use AddressSpace as allocator

    let mut userspace_mapper =
        UserspaceMapper::new(address_space, &mut allocator, page_table_allocator);
    let (dom_map, _) = parsed
        .load(&mut userspace_mapper)
        .expect("Failed to map Dom0");

    // Allocate and map stack
    // FIXME: Use GNU_STACK
    let stack_size = 16 * 1024 * 1024;
    let phys_base = unsafe { allocator.allocate_physical(stack_size as usize).0 };
    let virt_base = memory::USERSPACE_BASE + DOM0_RESERVATION as u64 - stack_size;

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

    debugger::add_binary(name, dom_map.load_bias);

    let mut cur = 0xfedf_0000;
    while cur < 0xfedf_0000 + 0x4000 {
        unsafe {
            address_space.map(page_table_allocator, cur + virt_base, cur, true, false, true);
            cur = cur + PAGE_SIZE as u64;
        }
    }
>>>>>>> 42d53b9 (fix map)

    Ok(DomainMapping {
        reserved_start,
        reserved_size: DOM0_RESERVATION,
        virt_start: memory::USERSPACE_BASE as *mut u8,
        entry_point: dom_map.entry_point,
        load_bias: dom_map.load_bias,
    })
}

/// The kernel panic handler.
#[cfg(not(test))]
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    log::info!("panic! {:?}", info);
    loop {}
}

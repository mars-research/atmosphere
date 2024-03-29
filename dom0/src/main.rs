#![no_std]
#![no_main]
#![feature(start, strict_provenance, asm_const, alloc_layout_extra)]

extern crate alloc;

//mod allocator;
mod nvme;
mod slab_alloc;
use crate::nvme::nvme_test;
pub use asys::sys_mresolve;
pub use nvme::device::NvmeDevice;

use alloc::format;
use alloc::string::String;
pub use alloc::vec::Vec;
use core::arch::asm;
use core::arch::x86_64::_rdtsc;
use core::panic::PanicInfo;
use log::Level;

pub use log::info as println;

pub const USERSPACE_BASE: u64 = 0x80_0000_0000;

const REGION_SIZE: usize = 10 << 20;
static mut MEMORY_REGION: [u8; REGION_SIZE] = [0u8; REGION_SIZE];

use pci::{Pci, PciClass, PciHeader, PciHeaderError, PciHeaderType};
mod pci;

fn handle_parsed_header(pci: &Pci, bus_num: u8, dev_num: u8, func_num: u8, header: PciHeader) {
    let raw_class: u8 = header.class().into();
    let mut string = format!(
        "PCI {:>02X}/{:>02X}/{:>02X} {:>04X}:{:>04X} {:>02X}.{:>02X}.{:>02X}.{:>02X} {:?}",
        bus_num,
        dev_num,
        func_num,
        header.vendor_id(),
        header.device_id(),
        raw_class,
        header.subclass(),
        header.interface(),
        header.revision(),
        header.class()
    );

    /*match header.class() {
        PciClass::Storage => match header.subclass() {
            0x01 => {
                string.push_str(" IDE");
            }
            0x06 => {
                string.push_str(" SATA");
            }
            _ => (),
        },
        PciClass::SerialBus => match header.subclass() {
            0x03 => match header.interface() {
                0x00 => {
                    string.push_str(" UHCI");
                }
                0x10 => {
                    string.push_str(" OHCI");
                }
                0x20 => {
                    string.push_str(" EHCI");
                }
                0x30 => {
                    string.push_str(" XHCI");
                }
                _ => (),
            },
            _ => (),
        },
        _ => (),
    }*/

    for (i, bar) in header.bars().iter().enumerate() {
        if !bar.is_none() {
            string.push_str(&format!("\n\t{} => {}", i, bar.unwrap()));
        }
    }

    println!("{}", string);
}

fn scan_pci_devs() {
    let pci = Pci::new();
    for bus in pci.buses() {
        for dev in bus.devs() {
            for func in dev.funcs() {
                match pci::utils::get_config(bus.num, dev.num, func.num) {
                    Ok(header) => {
                        handle_parsed_header(&pci, bus.num, dev.num, func.num, header.pci_hdr.hdr);
                    }
                    Err(_) => {}
                }
            }
        }
    }
}

#[start]
#[no_mangle]
fn main() -> isize {
    asys::init_logging_with_level(Level::Info);
    log::info!("hello {}", "world");

    unsafe {
        /*allocator::init(
            &mut MEMORY_REGION as *mut [u8; REGION_SIZE] as *mut u8,
            REGION_SIZE,
        );*/
        asys::sys_print("meow".as_ptr(), 4);
        log::info!(
            "sys_mmap {:?}",
            asys::sys_mmap(0xA0_0000_0000, 0x0000_0000_0000_0002u64 as usize, 1)
        );
        log::info!("sys_mresolve {:x?}", asys::sys_mresolve(0xA000000000));
    }
    // test_null_syscall();

    log::info!("Scanning pci devs");

    scan_pci_devs();

    log::info!("Done Scanning");

    loop {}

    let mut nvme_dev = unsafe {
        NvmeDevice::new(crate::pci::utils::PciBarAddr::new(
            USERSPACE_BASE + 0xfebf_0000,
            0x4000,
        ))
    };
    nvme_dev.init();

    nvme_test::run_blocktest_raw_with_delay(&mut nvme_dev, 30, 16, true, false, 0);

    unsafe {
        //println!("{:08x}", core::ptr::read_volatile(0xFEBF0000 as *const u32));
        println!("meow");
        //println!("{:08x}", *(0xFEBF0004 as *const u32));
        //println!("{:08x}", *(0xFEBF0008 as *const u32));
    }
    loop {}
}

#[panic_handler]
pub fn panic(_info: &PanicInfo) -> ! {
    loop {}
}

pub fn rdtsc() -> u64 {
    unsafe { x86::time::rdtsc() }
}

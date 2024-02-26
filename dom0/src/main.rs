#![no_std]
#![no_main]
#![feature(start, strict_provenance)]

extern crate alloc;

use alloc::format;
pub use alloc::string::String;
use alloc::vec;
pub use alloc::vec::Vec;
use core::arch::asm;
use core::panic::PanicInfo;

pub use log::info as println;

mod allocator;

static mut MEMORY_REGION: [u8; 4096] = [0u8; 4096];

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

    match header.class() {
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
    }

    for (i, bar) in header.bars().iter().enumerate() {
        if !bar.is_none() {
            string.push_str(&format!(" {}={}", i, bar));
        }
    }

    println!("{}", string);
}

fn dump_pci_bus() {
    let pci = Pci::new();
    for bus in pci.buses() {
        for dev in bus.devs() {
            for func in dev.funcs() {
                let func_num = func.num;
                match PciHeader::from_reader(func) {
                    Ok(header) => {
                        handle_parsed_header(&pci, bus.num, dev.num, func_num, header);
                    }
                    Err(PciHeaderError::NoDevice) => {}
                    Err(PciHeaderError::UnknownHeaderType(id)) => {
                        log::info!("pcid: unknown header type: {}", id);
                    }
                }
            }
        }
    }
}

#[start]
#[no_mangle]
fn main() -> isize {
    asys::init_logging();
    log::info!("hello {}", "world");

    unsafe {
        allocator::init(&mut MEMORY_REGION as *mut [u8; 4096] as *mut u8, 4096);
        asys::sys_print("meow".as_ptr(), 4);
        log::info!("sys_mmap {:?}", asys::sys_mmap(0xA000000000, 0x0000_0000_0000_0002u64 as usize, 20));
    }
    // for i in 0..20{
    //     let mut user_value: usize = 0;
    //     unsafe {
    //         log::info!("write {:x?}", (0xA000000000usize + i * 4096));
    //         *((0xA000000000usize + i * 4096) as *mut usize) = 0x233;
    //         log::info!("read {:x?}", (0xA000000000usize + i * 4096));
    //         user_value = *((0xA000000000usize + i * 4096) as *const usize);
    //     }
    //     log::info!("*{:x?} = {:x?}", (0xA000000000usize + i * 4096), user_value);
    // }

    dump_pci_bus();
    loop {}
}

/// The kernel panic handler.
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}

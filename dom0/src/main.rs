#![no_std]
#![no_main]
#![feature(start, strict_provenance)]

extern crate alloc;

use alloc::vec::Vec;
use core::panic::PanicInfo;

pub use log::info as println;

mod allocator;

static mut MEMORY_REGION: [u8; 4096] = [0u8; 4096];

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

    let mut v1: Vec<u64> = Vec::with_capacity(10);

    for i in 0..10 {
        v1.push(0xdead);
    }

    loop {}
}

/// The kernel panic handler.
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}

//! The Atmosphere microkernel.
//!
//! ## Kernel Command Line
//!
//! Supported kernel command line parameters:
//! - `nocolor`: Disable colored serial output
//! - `serial=[com1|com2|com3|com4]`: Log to a specified serial port
//! - `script=NAME`: Run a debug script

#![no_std]
#![feature(
    asm,
    abi_x86_interrupt,
    alloc_error_handler,
    arbitrary_self_types,
    const_fn_fn_ptr_basics,
    const_mut_refs,
    const_slice_from_raw_parts,
    naked_functions,
    pattern,
    start,
)]

#![deny(
    asm_sub_register,
    deprecated,
    missing_abi,
    unused_imports,
    unused_must_use,
    unused_mut,
    unused_unsafe,
)]

mod boot;
mod capability;
mod console;
mod cpu;
mod interrupt;
mod logging;
mod memory;
mod scripts;
mod utils;
mod vmx;

use core::panic::PanicInfo;

#[start]
/// CPU 0 entry point.
///
/// This entry point is jumped to at the end of
/// `boot/crt0.asm`.
fn main(_argc: isize, _argv: *const *const u8) -> isize {
    unsafe {
        boot::init();
        logging::init_early();
        console::init();
    }

    print_logo();
    log::info!("Command line: {}", boot::get_command_line());
    #[cfg(debug_assertions)]
    {
        log::info!("Atmosphere was built in debug mode.");
    }

    unsafe {
        memory::init();
        memory::init_cpu();
        interrupt::init();
        interrupt::init_cpu();
        capability::init();
    }
    
    unsafe {
        scripts::run_script_from_command_line();
    }

    loop {}
}

/// Prints the Atmosphere logo.
fn print_logo() {
    let logo = include_str!("logo.txt");
    for line in logo.split("\n") {
        log::info!("{}", line);
    }
}

/// The kernel panic handler.
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    log::error!("panic! {:#?}", info);

    // FIXME: Signal all other CPUs to halt

    loop {}
}

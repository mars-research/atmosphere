//! The Atmosphere microkernel.
//!
//! ## Kernel Command Line
//!
//! Supported kernel command line parameters:
//! - `nologo`: Disable the logo
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
    const_ptr_offset,
    const_raw_ptr_deref,
    const_slice_from_raw_parts,
    custom_test_frameworks,
    naked_functions,
    pattern,
    start,
)]

#![deny(
    asm_sub_register,
    deprecated,
    missing_abi,
    rustdoc::bare_urls,
    unused_must_use,
    unused_unsafe,
)]

#![cfg_attr(not(debug_assertions), deny(
    dead_code,
    unused_imports,
    unused_mut,
    unused_variables,
))]

#![reexport_test_harness_main = "test_main"]
#![test_runner(crate::test_runner)]
#![no_main]

mod boot;
mod capability;
mod console;
mod cpu;
mod error;
mod interrupt;
mod logging;
mod memory;
mod scripts;
mod utils;
mod vmx;

use core::panic::PanicInfo;

static mut SHUTDOWN_ON_PANIC: bool = false;

/// CPU 0 entry point.
///
/// This entry point is jumped to at the end of
/// `boot/crt0.asm`.
#[start]
#[no_mangle]
fn main(_argc: isize, _argv: *const *const u8) -> isize {
    unsafe {
        console::early_init();
        logging::early_init();

        boot::init();
        console::init();
        logging::init();
    }

    if !boot::command_line::get_flag("nologo") {
        print_logo();
    }

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

    #[cfg(test)]
    {
        log::info!("Atmosphere was built with the test harness");
        test_main();
    }

    unsafe {
        scripts::run_script_from_command_line();
    }

    loop {}
}

/// Runs all tests.
#[cfg(test)]
fn test_runner(tests: &[&dyn Fn()]) -> ! {
    unsafe {
        SHUTDOWN_ON_PANIC = true;
    }

    log::info!("Running {} tests", tests.len());

    for test in tests {
        test();
    }

    log::info!("All good!");

    unsafe {
        boot::shutdown(true);
    }
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

    unsafe {
        if SHUTDOWN_ON_PANIC {
            boot::shutdown(false);
        }
    }

    // FIXME: Signal all other CPUs to halt

    loop {}
}

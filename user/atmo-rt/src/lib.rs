//! A C runtime for Atmosphere.
//!
//! The runtime is linked into one Atmosphere process as a static library.
//! It provides what a small real-time C program expects from an operating
//! system: a program entry, a console, a clock, tasks, and synchronization
//! objects. The C interface is declared in `include/atmo_rt.h`.
//!
//! The only code that talks to the kernel is in [`sys`]. Everything else is
//! written against that module, so that the runtime can move to another kernel
//! interface without changes to the code above it.

#![no_std]

pub mod capi;
pub mod console;
pub mod fs;
pub mod mem;
pub mod sync;
pub mod sys;
pub mod task;
pub mod time;

use core::panic::PanicInfo;
use core::sync::atomic::{AtomicUsize, Ordering};

extern "C" {
    /// The entry of the C program.
    fn main() -> i32;
}

/// The entry of the process.
///
/// The kernel enters the first process with `rdi` and `rsi` holding the base
/// and the size of the boot payload, and with a stack pointer that is not
/// aligned as the C ABI expects at a function entry.
#[unsafe(naked)]
#[no_mangle]
pub unsafe extern "C" fn _start() -> ! {
    core::arch::naked_asm!(
        "and rsp, -16",
        "xor ebp, ebp",
        "call {entry}",
        "ud2",
        entry = sym rt_entry,
    )
}

/// The boot payload: whatever follows the image in the boot module.
static PAYLOAD_BASE: AtomicUsize = AtomicUsize::new(0);
static PAYLOAD_SIZE: AtomicUsize = AtomicUsize::new(0);

extern "C" fn rt_entry(payload_base: *mut u8, payload_size: usize) -> ! {
    PAYLOAD_BASE.store(payload_base as usize, Ordering::Relaxed);
    PAYLOAD_SIZE.store(payload_size, Ordering::Relaxed);
    time::init();
    task::init();
    let code = unsafe { main() };
    console::flush();
    sys::exit(code as u32)
}

/// Returns the boot payload. The size is zero if there is none.
#[no_mangle]
pub unsafe extern "C" fn art_boot_payload(size: *mut usize) -> *const u8 {
    if !size.is_null() {
        size.write(PAYLOAD_SIZE.load(Ordering::Relaxed));
    }
    PAYLOAD_BASE.load(Ordering::Relaxed) as *const u8
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    use core::fmt::Write;
    let mut out = console::Writer;
    let _ = writeln!(out, "\natmo-rt: panic: {}", info);
    console::flush();
    sys::exit(101)
}

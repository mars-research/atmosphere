//! Bootloader integration.
//!
//! We are loaded by the boot manager which implements Xen PVH and Multiboot v2.

pub mod ap_start;
pub mod command_line;

use core::arch::asm;

use astd::boot::BootInfo;
use x86::io::{outb, outw};

pub use command_line::get_command_line;

static mut BOOT_INFO: BootInfo = BootInfo::empty();

pub unsafe fn init(boot_info: *const BootInfo) {
    BOOT_INFO = (&*boot_info).clone();

    command_line::init(BOOT_INFO.command_line.as_str()).expect("Invalid kernel command-line");
}

pub fn get_boot_info() -> &'static BootInfo {
    unsafe { &BOOT_INFO }
}

/// Returns the raw kernel command line.
pub fn get_raw_command_line() -> &'static str {
    unsafe { BOOT_INFO.command_line.as_str() }
}

/// Shutdown the system.
///
/// On virtual platforms it's possible to set an exit code to
/// be returned by the hypervisor.
pub unsafe fn shutdown(success: bool) -> ! {
    log::info!("The system is shutting down...");

    let cmdline = get_command_line();

    // QEMU isa-debug-exit
    //
    // <https://github.com/qemu/qemu/blob/bd662023e683850c085e98c8ff8297142c2dd9f2/hw/misc/debugexit.c>
    if let Some(io_base) = cmdline.qemu_debug_exit_io_base {
        if !success {
            log::debug!(
                "Trying QEMU isa-debug-exit shutdown (IO Port {:#x})",
                io_base
            );

            // QEMU will exit with (val << 1) | 1
            outw(io_base, 0x0);
        }
    }

    // Bochs APM
    if let Some(io_base) = cmdline.bochs_apm_io_base {
        let success_marker = if success {
            "BOCHS_SUCCESS"
        } else {
            "BOCHS_FAILURE"
        };
        log::debug!(
            "Trying Bochs APM shutdown (IO Port {:#x}) - {}",
            io_base,
            success_marker
        );

        let shutdown = "Shutdown";

        for ch in shutdown.chars() {
            outb(io_base, ch as u8);
        }
    }

    // QEMU
    outw(0x604, 0x2000);

    log::info!("It is now safe to turn off your computer"); // ;)

    spin_forever();
}

/// Enters a busy loop.
pub unsafe fn spin_forever() -> ! {
    loop {
        asm!("hlt");
    }
}

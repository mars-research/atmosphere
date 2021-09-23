//! Bootloader integration.
//!
//! We implement the Multiboot v1 specification.

pub mod command_line;

use multiboot2::BootInformation;
use x86::io::{outb, outw};
// use qemu_exit::{QEMUExit, X86 as QemuExitHandle};

extern "C" {
    static bootinfo: u64;
    // static stack_bottom: u64;
    // static stack_top: u64;
}

static mut COMMAND_LINE: &'static str = "";

pub unsafe fn init() {
    let info = get_bootinfo();

    if let Some(command_line) = info.command_line_tag() {
        let ptr = command_line.command_line() as *const str;
        COMMAND_LINE = &*ptr; // We won't touch the boot information region
    }
}

/// Returns the kernel command line.
pub fn get_command_line() -> &'static str {
    unsafe { COMMAND_LINE }
}

/// Returns the bootloader info.
pub unsafe fn get_bootinfo() -> BootInformation {
    match multiboot2::load(bootinfo as usize) {
        Ok(info) => info,
        Err(e) => panic!("Could not retrieve valid boot information: {:?}", e),
    }
}

/// Shutdown the system.
///
/// On virtual platforms it's possible to set an exit code to
/// be returned by the hypervisor.
pub unsafe fn shutdown(success: bool) -> ! {
    log::info!("The system is shutting down...");

    // QEMU isa-debug-exit
    //
    // <https://github.com/qemu/qemu/blob/bd662023e683850c085e98c8ff8297142c2dd9f2/hw/misc/debugexit.c>
    if let Some(io_base) = command_line::get_first_value("qemu_debug_exit_io_base") {
        let io_base = io_base.parse::<u16>()
            .expect("Failed to parse qemu_debug_exit_io_base");

        if !success {
            log::debug!("Trying QEMU isa-debug-exit shutdown (IO Port {:#x})", io_base);

            // QEMU will exit with (val << 1) | 1
            outw(io_base, 0x0);
        }
    }

    // Bochs APM
    if let Some(io_base) = command_line::get_first_value("bochs_apm_io_base") {
        let io_base = io_base.parse::<u16>()
            .expect("Failed to parse qemu_debug_exit_io_base");

        let success_marker = if success { "BOCHS_SUCCESS" } else { "BOCHS_FAILURE" };
        log::debug!("Trying Bochs APM shutdown (IO Port {:#x}) - {}", io_base, success_marker);

        let shutdown = "Shutdown";

        for ch in shutdown.chars() {
            outb(io_base, ch as u8);
        }
    }

    // ACPI shutdown
    //
    // PM1a_CNT <- SLP_TYPa | SLP_EN
    outw(0x604, 0x2000 | 0x0);

    log::info!("It is now safe to turn off your computer"); // ;)

    asm!("hlt");
    loop {}
}

//! Bootloader integration.
//!
//! We implement the Multiboot v1 specification.

pub mod command_line;

use multiboot::information::{MemoryManagement, Multiboot, PAddr};
use x86::io::outw;
// use qemu_exit::{QEMUExit, X86 as QemuExitHandle};

extern "C" {
    static bootinfo: u64;
    // static stack_bottom: u64;
    // static stack_top: u64;
}

static mut IDENT_MAP: IdentMap = IdentMap {};
static mut COMMAND_LINE: &'static str = "";

pub unsafe fn init() {
    let info = get_bootinfo();
    if let Some(command_line) = info.command_line() {
        COMMAND_LINE = command_line;
    }
}

/// Returns the kernel command line.
pub fn get_command_line() -> &'static str {
    unsafe { COMMAND_LINE }
}

/// Returns the bootloader info.
pub unsafe fn get_bootinfo() -> Multiboot<'static, 'static> {
    match Multiboot::from_ptr(bootinfo, &mut IDENT_MAP) {
        Some(info) => info,
        None => panic!("Could not retrieve valid boot information"),
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
            // QEMU will exit with (val << 1) | 1
            outw(io_base, 0x0);
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

/*
/// Returns the initial stack for the bootstrap processor.
pub const unsafe fn get_bsp_initial_stack() -> *const [u8] {
    let ptr = stack_top as *const u8;
    let len = (stack_top - stack_bottom) as usize;
    core::ptr::slice_from_raw_parts(ptr, len)
}
*/

struct IdentMap {}
impl MemoryManagement for IdentMap {
    unsafe fn paddr_to_slice(&self, addr: PAddr, length: usize) -> Option<&'static [u8]> {
        let ptr = addr as *const u8;
        Some(core::slice::from_raw_parts(ptr, length))
    }

    unsafe fn allocate(&mut self, _length: usize) -> Option<(PAddr, &mut [u8])> {
        // Not supported
        None
    }

    unsafe fn deallocate(&mut self, _addr: PAddr) {
        // No-op
    }
}

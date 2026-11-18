//! The kernel interface of the runtime.
//!
//! This is the only module that makes system calls or touches hardware.

use core::arch::asm;

/// The size of a page.
pub const PAGE_SIZE: usize = 4096;

/// The I/O port of the QEMU `isa-debug-exit` device.
const DEBUG_EXIT_PORT: u16 = 0xf4;

/// Writes one line to the kernel console. The kernel adds the line break.
pub fn console_line(line: &[u8]) {
    unsafe {
        asys::sys_log(line.as_ptr(), line.len(), log::Level::Info);
    }
}

/// Maps `pages` fresh, zeroed, writable pages at `va`. Returns `false` if the
/// kernel refuses.
pub fn map_pages(va: usize, pages: usize) -> bool {
    const WRITABLE: usize = 0x2;
    unsafe { asys::sys_mmap(va, WRITABLE, pages) == 0 }
}

/// Reads the timestamp counter.
pub fn rdtsc() -> u64 {
    unsafe { core::arch::x86_64::_rdtsc() }
}

/// Ends the program.
///
/// Under QEMU, the `isa-debug-exit` device ends the emulator with the status
/// `code << 1 | 1`. The first process runs with I/O privilege, so the port
/// write is allowed. On hardware without the device, the write has no effect
/// and the processor spins.
pub fn exit(code: u32) -> ! {
    unsafe {
        asm!("out dx, eax", in("dx") DEBUG_EXIT_PORT, in("eax") code, options(nomem, nostack));
    }
    loop {
        core::hint::spin_loop();
    }
}

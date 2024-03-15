#![no_std]

pub mod logger;

use core::arch::asm;

pub use logger::init_logging;

pub const MAX_SYSCALLS: usize = 64;
pub const __NR_PRINT: usize = 0;
pub const __NR_MMAP: usize = 1;
pub const __NR_MRESOLVE: usize = 2;

macro_rules! syscall {
    ($nr:expr, $a:expr, $b:expr, $c:expr) => {{
        let ret: isize;
        asm!(
            "syscall",
            inout("rax") $nr => ret,
            inout("rdi") $a => _,
            inout("rsi") $b => _,
            inout("rdx") $c => _,
            out("rcx") _,
            out("r8")  _,
            out("r9") _,
            out("r10") _,
            out("r11") _,
        );
        ret
    }}
}

pub unsafe fn sys_print(data: *const u8, len: usize) -> isize {
    syscall!(__NR_PRINT, data, len, 0)
}

pub unsafe fn sys_mmap(va: usize, perm_bits: usize, range: usize) -> usize {
    return syscall!(__NR_MMAP, va, perm_bits, range) as usize;
}

pub unsafe fn sys_mresolve(va: usize) -> (usize, usize) {
    let va_masked = va & 0xFFFFFFFFFFFFF000u64 as usize;
    let low_bits = va & 0xFFFu64 as usize;
    let ret = syscall!(__NR_MRESOLVE, va_masked, 0, 0) as usize;
    return (
        (ret & 0xFFFFFFFFFFFFF000u64 as usize) | low_bits,
        ret & 0xFusize,
    );
}

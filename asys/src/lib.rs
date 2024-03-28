#![no_std]

pub mod logger;

use core::arch::asm;

pub use logger::init_logging;
pub use logger::init_logging_with_level;

pub const MAX_SYSCALLS: usize = 64;
pub const __NR_PRINT: usize = 0;
pub const __NR_MMAP: usize = 1;
pub const __NR_MRESOLVE: usize = 2;
pub const __NR_NEW_END: usize = 3;
pub const __NR_NEW_PROC: usize = 4;
pub const __NR_NEW_PROC_W_IO: usize = 5;
pub const __NR_NEW_THREAD: usize = 6;
pub const __NR_SEND_EMPTY_NW: usize = 7;
pub const __NR_LOG: usize = 8;
pub const __NR_SEND_EMPTY: usize = 9;
pub const __NR_RECEIVE_EMPTY: usize = 10;
pub const __NR_NEW_PROC_W_IO_MEM: usize = 11;
pub const __NR_SEND_PAGE_NW: usize = 12;
pub const __NR_RECEIVE_PAGE: usize = 13;

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
    }};
    ($nr:expr, $a:expr, $b:expr, $c:expr, $d:expr, $e:expr) => {{
        let ret: isize;
        asm!(
            "syscall",
            inout("rax") $nr => ret,
            inout("rdi") $a => _,
            inout("rsi") $b => _,
            inout("rdx") $c => _,
            out("rcx") _,
            inout("r8") $d => _,
            inout("r9") $e => _,
            out("r10") _,
            out("r11") _,
        );
        ret
    }};
}

pub unsafe fn sys_print(data: *const u8, len: usize) -> isize {
    syscall!(__NR_PRINT, data, len, 0)
}

pub unsafe fn sys_log(data: *const u8, len: usize, level: log::Level) -> isize {
    syscall!(__NR_LOG, data, len, level as usize)
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
        ret & 0xFFFusize,
    );
}

pub unsafe fn sys_new_endpoint(endpoint_index: usize) -> usize {
    return syscall!(__NR_NEW_END, endpoint_index, 0, 0) as usize;
}

pub unsafe fn sys_new_proc(endpoint_index: usize, ip: usize) -> usize {
    return syscall!(__NR_NEW_PROC, endpoint_index, ip, 0) as usize;
}

pub unsafe fn sys_new_proc_with_iommu(endpoint_index: usize, ip: usize) -> usize {
    return syscall!(__NR_NEW_PROC_W_IO, endpoint_index, ip, 0) as usize;
}

pub unsafe fn sys_new_thread(endpoint_index: usize, ip: usize, sp: usize) -> usize {
    return syscall!(__NR_NEW_THREAD, endpoint_index, ip, sp) as usize;
}

pub unsafe fn sys_send_empty_no_wait(endpoint_index: usize) -> usize {
    return syscall!(__NR_SEND_EMPTY_NW, endpoint_index, 0, 0) as usize;
}

pub unsafe fn sys_send_empty(endpoint_index: usize) -> usize {
    return syscall!(__NR_SEND_EMPTY, endpoint_index, 0, 0) as usize;
}

pub unsafe fn sys_receive_empty(endpoint_index: usize) -> usize {
    return syscall!(__NR_RECEIVE_EMPTY, endpoint_index, 0, 0) as usize;
}

pub unsafe fn sys_new_proc_with_iommu_pass_mem(
    endpoint_index: usize,
    ip: usize,
    sp: usize,
    va: usize,
    range: usize,
) -> usize {
    return syscall!(__NR_NEW_PROC_W_IO_MEM, endpoint_index, ip, sp, va, range) as usize;
}

pub unsafe fn sys_send_pages_no_wait(endpoint_index: usize, va: usize, range: usize) -> usize {
    return syscall!(__NR_SEND_PAGE_NW, endpoint_index, va, range) as usize;
}

pub unsafe fn sys_receive_pages(endpoint_index: usize, va: usize, range: usize) -> usize {
    return syscall!(__NR_RECEIVE_PAGE, endpoint_index, va, range) as usize;
}

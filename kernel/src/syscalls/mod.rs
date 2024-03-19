//! Syscalls.

use core::arch::asm;

use asys::MAX_SYSCALLS;
use x86::segmentation::SegmentSelector;
use x86::{msr, Ring};

use crate::gdt::GlobalDescriptorTable;
use crate::kernel;

const SYSCALL32_ENTRY: u64 = 0; // nein
const SYSCALL32_ENTRY_EIP: u32 = 0; // nein

static mut SYSCALLS: [u64; MAX_SYSCALLS] = [0; MAX_SYSCALLS];

static mut CPU0_SYSCALL_STACK: [u8; 4 * 1024 * 1024] = [0; 4 * 1024 * 1024];
static mut CPU0_SYSCALL_SP: u64 = 0;

/// Initializes syscalls.
///
/// This must be called only once for each CPU reset.
pub unsafe fn init_cpu() {
    use GlobalDescriptorTable as GDT;

    // index - 1 because syscall and sysret will add 8 (cs) or 16 (ss) to those values
    let kernel_seg = SegmentSelector::new(GDT::KERNEL_CODE_INDEX - 1, Ring::Ring0);
    let user_seg = SegmentSelector::new(GDT::USER_CODE_INDEX - 1, Ring::Ring3);

    // Set STAR
    let star = ((kernel_seg.bits() as u64) << 48)
        | ((user_seg.bits() as u64) << 32)
        | (SYSCALL32_ENTRY_EIP as u64);
    msr::wrmsr(msr::IA32_STAR, star);

    // Set LSTAR - 64-bit syscall entry
    msr::wrmsr(msr::IA32_LSTAR, sys_entry as *const () as u64);

    // Set LSTAR - 32-bit syscall entry
    msr::wrmsr(msr::IA32_CSTAR, SYSCALL32_ENTRY);

    // Enable EFER Bit 0 - System Call Extensions
    let mut efer = msr::rdmsr(msr::IA32_EFER);
    efer |= 0x1;
    msr::wrmsr(msr::IA32_EFER, efer);

    CPU0_SYSCALL_SP = CPU0_SYSCALL_STACK.as_ptr().add(CPU0_SYSCALL_STACK.len()) as u64;

    SYSCALLS[asys::__NR_PRINT] = sys_print as u64;
    SYSCALLS[asys::__NR_MMAP] = kernel::sys_mmap as u64;
    SYSCALLS[asys::__NR_MRESOLVE] = kernel::sys_resolve as u64;
    SYSCALLS[asys::__NR_NEW_END] = kernel::sys_new_endpoint as u64;
    SYSCALLS[asys::__NR_NEW_PROC] = kernel::sys_new_proc as u64;
    SYSCALLS[asys::__NR_NEW_PROC_W_IO] = kernel::sys_new_proc_with_iommu as u64;
    SYSCALLS[asys::__NR_NEW_THREAD] = kernel::sys_new_thread as u64;
    SYSCALLS[asys::__NR_SEND_EMPTY_NW] = kernel::sys_send_empty_no_wait as u64;
    SYSCALLS[asys::__NR_LOG] = sys_log as u64;
}

// rax - syscall number
// rdi - arg #1
// rsi - arg #2
// rdx - arg #3
//
// rcx - return address (implicit)
#[naked]
unsafe extern "C" fn sys_entry() -> ! {
    asm!(
        // We may not have a valid rsp
        // rax, r10, r11

        "mov r10, rsp",
        "mov rsp, [rip + {saved_sp}]", // FIXME: per-CPU stack

        "push r10", // original rsp
        "push r11", // original rflags
        "push rcx", // return address

        "cmp rax, {max_syscalls}",
        "jae 2f",

        // In-range syscall
        "shl rax, 3",
        "lea r11, [rip + {syscalls}]",
        "add r11, rax",
        "mov r11, [r11]",
        "cmp r11, 0",
        "jz 2f",

        // rdi, rsi, rdx, rcx, r8, r9
        "call r11",

        "jmp 3f",

        // Invalid syscall
        "2:",
        "mov rax, -1",

        // Cleanup
        "3:",
        "pop rcx",
        "pop r11",
        "pop rsp",
        "sysretq",

        saved_sp = sym CPU0_SYSCALL_SP,
        max_syscalls = const MAX_SYSCALLS,
        syscalls = sym SYSCALLS,
        options(noreturn),
    );
}

extern "C" fn sys_print(data: *const u8, len: usize) -> isize {
    let s = unsafe {
        let slice = core::slice::from_raw_parts(data, len);
        core::str::from_utf8_unchecked(slice)
    };
    log::info!("print: {}", s);
    0
}

extern "C" fn sys_log(data: *const u8, len: usize, level: log::Level) -> isize {
    let s = unsafe {
        let slice = core::slice::from_raw_parts(data, len);
        core::str::from_utf8_unchecked(slice)
    };
    log::log!(level, "{}", s);
    0
}

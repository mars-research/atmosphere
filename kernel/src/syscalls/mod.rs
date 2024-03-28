//! Syscalls.

use core::arch::{asm, global_asm};

use asys::MAX_SYSCALLS;
use memoffset::offset_of;
use x86::segmentation::SegmentSelector;
use x86::{msr, Ring};

use crate::cpu::Cpu;
use crate::gdt::GlobalDescriptorTable;
use crate::kernel;
use crate::thread::SwitchDecision;
use verified::trap::Registers;

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
    SYSCALLS[asys::__NR_SEND_EMPTY] = kernel::sys_send_empty as u64;
    SYSCALLS[asys::__NR_RECEIVE_EMPTY] = kernel::sys_receive_empty as u64;
    SYSCALLS[asys::__NR_NEW_PROC_W_IO_MEM] = kernel::sys_new_proc_with_iommu_pass_mem as u64;
    SYSCALLS[asys::__NR_SEND_PAGE_NW] = kernel::sys_send_pages_no_wait as u64;
    SYSCALLS[asys::__NR_RECEIVE_PAGE] = kernel::sys_receive_pages as u64;
}

#[cfg(debug_assertions)]
global_asm!(
    ".macro push_dummy_caller_saved",
    "push 0", // rax
    "push 0", // rdi
    "push 0", // rsi
    "push 0", // rdx
    "push 0", // rcx (taken by original rip)
    "push 0", // r8
    "push 0", // r9
    "push 0", // r10 (taken by original rsp)
    "push 0", // r11 (taken by original rflags across syscall)
    ".endm",
);

#[cfg(not(debug_assertions))]
global_asm!(".macro push_dummy_caller_saved", "sub rsp, 9*8", ".endm",);

// Syscall ABI
//
// Register | User           | Kernel Handler
// ------------------------------------------
// rax      | Syscall Number | Return Value
// rdi      | Arg #1         | Arg #1
// rsi      | Arg #2         | Arg #2
// rdx      | Arg #3         | Arg #3
// rcx      | N/A            | Registers (Arg #4)
// r8       | Arg #4         | Arg #5
// r9       | Arg #5         | Arg #6
//
// All caller-saved registers are considered clobbered once invoked
#[naked]
unsafe extern "C" fn sys_entry() -> ! {
    asm!(
        // We may not have a valid rsp
        // rax, r10, r11

        "mov r10, rsp",
        "mov rsp, gs:{syscall_sp_offset}",

        // Here we construct the Registers struct and only save
        // a subset of registers
        "push {user_ss}", // ss
        "push r10",       // rsp
        "push r11",       // rflags
        "push {user_cs}", // cs
        "push rcx",       // rip
        "push 0",         // error_code

        "push_dummy_caller_saved",

        "push rbx",       // rbx
        "push rbp",       // rbp
        "push r12",       // r12
        "push r13",       // r13
        "push r14",       // r14
        "push r15",       // r15

        "mov rcx, rsp",

        "cmp rax, {max_syscalls}",
        "jae 2f",

        // In-range syscall
        "shl rax, 3",
        "lea r11, [rip + {syscalls}]",
        "add r11, rax",
        "mov r11, [r11]",
        "cmp r11, 0",
        "jz 2f",

        // handler(arg1, arg2, arg3, registers, arg4, arg5)
        // rdi, rsi, rdx, (rcx), r8, r9
        "call r11",

        "jmp 3f",

        // Invalid syscall
        "2:",
        "mov rax, -1",

        // Cleanup
        "3:",

        // Three cases:
        // 1. Switch to another thread that was suspended due to a syscall
        //    ("clean" thread)
        // 2. Return to the same thread
        // 3. Switch to a different preempted thread
        //
        // For 1, we can directly skip over restoring most registers since
        // we trust the handler to have already restored callee-saved registers
        //
        // TODO: Clear registers?

        "mov r10, gs:{switch_decision_offset}",
        "cmp r10, {decision_no_switching}",
        "je 22f",
        "cmp r10, {decision_switch_to_preempted}",
        "je 23f",

        // 1. Switch to another clean thread
        // Fast return that clobbers rcx, r11
        "21:",
        "pop r15",
        "pop r14",
        "pop r13",
        "pop r12",
        "pop rbp",
        "pop rbx",
        "add rsp, 8*8", // skip r11~rdi (8 registers)
        "pop rax",      // rax
        "add rsp, 8",   // error_code
        "pop rcx",      // rip
        "add rsp, 8",   // skip cs
        "pop r11",      // rflags
        "pop rsp",      // rsp
        "sti",
        "sysretq",

        // 2. Return to the same thread
        "22:",
        "add rsp, 14*8", // skip r15~rdi (14 registers)
        "pop rax",       // rax
        "add rsp, 8",    // skip error_code
        "pop rcx",       // rip
        "add rsp, 8",    // skip cs
        "pop r11",       // rflags
        "pop rsp",       // rsp
        "sti",
        "sysretq",

        // 3. Switch to a preempted thread (slow)
        "23:",
        "pop r15",
        "pop r14",
        "pop r13",
        "pop r12",
        "pop rbp",
        "pop rbx",
        "pop r11",
        "pop r10",
        "pop r9",
        "pop r8",
        "pop rcx",
        "pop rdx",
        "pop rsi",
        "pop rdi",
        "pop rax",
        "add rsp, 8",
        "iretq",

        user_ss = const GlobalDescriptorTable::USER_SS,
        user_cs = const GlobalDescriptorTable::USER_CS,
        syscall_sp_offset = const offset_of!(Cpu, syscall_sp),
        max_syscalls = const MAX_SYSCALLS,
        syscalls = sym SYSCALLS,

        switch_decision_offset = const offset_of!(Cpu, switch_decision),
        decision_no_switching = const SwitchDecision::NoSwitching as u64,
        decision_switch_to_preempted = const SwitchDecision::SwitchToPreempted as u64,
        options(noreturn),
    );
}

extern "C" fn sys_print(data: *const u8, len: usize, _: usize, regs: &mut Registers) -> isize {
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

//! Threading.

use core::mem;

use x86::{segmentation, Ring};

use crate::gdt::GlobalDescriptorTable;
use crate::interrupt::{self, Cycles};
use verified::trap::Registers;
use core::arch::asm;
use crate::cpu;
use crate::kernel;
pub use verified::bridge::SwitchDecision;

const TIME_SLICE: Cycles = Cycles(1_000_000);

/// Starts a thread.
pub unsafe fn start_thread(code: u64, stack: u64, ring: Ring) {
    log::info!("Starting thread code={:#x} stack={:#x}", code, stack);

    let cpu = cpu::get_current();
    let mut regs = Registers::zeroed();

    let (cs, ss) = match ring {
        Ring::Ring0 => (GlobalDescriptorTable::KERNEL_CS, GlobalDescriptorTable::KERNEL_SS),
        Ring::Ring3 => (GlobalDescriptorTable::USER_CS, GlobalDescriptorTable::USER_SS),
        _ => panic!("Unsupported ring"),
    };

    regs.rip = code;
    regs.rsp = stack;
    regs.cs = cs as u64;
    regs.ss = ss as u64;
    regs.flags = 1 << 9; // Interrupt Enable

    cpu.parked = regs;

    interrupt::set_timer(TIME_SLICE);
}

/// Arms the timer for the first time slice of this CPU.
pub fn start_time_slices() {
    interrupt::set_timer(TIME_SLICE);
}

/// Handles the end of a time slice, returning the next one.
///
/// `regs` is the interrupted context. If the kernel switches threads, it replaces `regs` with the
/// context of the next thread, and the interrupt return resumes that thread.
pub fn schedule(regs: &mut Registers) -> Option<Cycles> {
    // Only a thread in user mode is preempted. The kernel runs syscalls with interrupts off, so an
    // interrupted kernel context is boot code or an idle loop, and it has no thread to save.
    if regs.cs & 3 == Ring::Ring3 as u64 {
        kernel::timer_preempt(regs);
    }
    Some(TIME_SLICE)
}

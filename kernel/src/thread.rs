//! Threading.

use core::mem;

use x86::{segmentation, Ring};

use crate::cpu;
use crate::gdt::GlobalDescriptorTable;
use crate::interrupt::{self, Cycles};
use crate::kernel;
use core::arch::asm;
pub use verified::bridge::SwitchDecision;
use verified::trap::Registers;

const TIME_SLICE: Cycles = Cycles(1_000_000);

/// Starts a thread.
pub unsafe fn start_thread(code: u64, stack: u64, ring: Ring) {
    log::info!("Starting thread code={:#x} stack={:#x}", code, stack);

    let cpu = cpu::get_current();
    let mut regs = Registers::zeroed();

    let (cs, ss) = match ring {
        Ring::Ring0 => (
            GlobalDescriptorTable::KERNEL_CS,
            GlobalDescriptorTable::KERNEL_SS,
        ),
        Ring::Ring3 => (
            GlobalDescriptorTable::USER_CS,
            GlobalDescriptorTable::USER_SS,
        ),
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

/// Schedules the next thread, returning its time slice.
pub fn schedule(regs: &mut Registers) -> Option<Cycles> {
    // crate::debugger::breakpoint(1);
    // let cpu = cpu::get_current();
    // mem::swap(&mut cpu.parked, regs);
    // Some(TIME_SLICE)

    log::info!("hello from cpu 1 scheduler");
    loop {
        unsafe {
            let has_next_thread = kernel::sched_get_next_thread(regs);
            if has_next_thread == false {
                for i in 0..1000 {
                    asm!("nop");
                }
            } else {
                break;
            }
        }
    }
    None
}

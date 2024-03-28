//! Interrupt handling.

// Copyright 2021 Zhaofeng Li
// Copyright 2017 Philipp Oppermann
//
// Licensed under the MIT license <http://opensource.org/licenses/MIT>.
// See top-level LICENSE.

mod exception;
mod idt;
mod ioapic;
mod lapic;
mod mps;
pub mod x86_xapic;

use core::arch::asm;
use core::convert::{Into, TryFrom};
use core::mem::MaybeUninit;

use bit_field::BitField;
use x86::bits64::paging::VAddr;
use x86::io::{inb, outb};

use crate::boot::spin_forever;
pub use exception::Exception;
use exception::EXCEPTION_MAX;
use idt::Idt;
pub use lapic::{boot_ap, end_of_interrupt, set_timer};
use verified::trap::Registers;

/// The IRQ offset.
pub const IRQ_OFFSET: usize = 32;

pub const IST_EXCEPTION: usize = 1;
pub const IST_IRQ: usize = 2;

/// The global IDT.
static mut GLOBAL_IDT: Idt = Idt::new();

const PIC1_DATA: u16 = 0x21;
const PIC2_DATA: u16 = 0xa1;

/// An amount of cycles.
#[derive(Debug)]
#[repr(transparent)]
pub struct Cycles(pub usize);

#[repr(C)]
struct TrampolineMarker(());

macro_rules! wrap_interrupt_with_error_code {
    ($handler:path) => {{
        let _: unsafe extern "C" fn(&mut Registers) = $handler;

        /// Interrupt trampoline
        #[naked]
        unsafe extern "C" fn trampoline(_: TrampolineMarker) {
            // Figure 6-7. Stack Usage on Transfers to Interrupt and Exception Handling Routines

            // Here rsp is at an InterruptStackFrame
            // [rip][cs][eflags][esp][ss]
            core::arch::asm!(
                "cli",
                //"call {breakpoint}",

                "cld",
                "push rax",
                "push rdi",
                "push rsi",
                "push rdx",
                "push rcx",
                "push r8",
                "push r9",
                "push r10",
                "push r11",
                "push rbx",
                "push rbp",
                "push r12",
                "push r13",
                "push r14",
                "push r15",

                // fn handler(registers: &mut Registers)
                "mov rdi, rsp",
                "call {handler}",

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

                "sti",
                "iretq",

                //breakpoint = sym crate::debugger::breakpoint,
                handler = sym $handler,
                options(noreturn),
            );
        }

        trampoline
    }}
}

macro_rules! wrap_interrupt {
    ($handler:path) => {{
        let _: unsafe extern "C" fn(&mut Registers) = $handler;

        /// Interrupt trampoline
        #[naked]
        unsafe extern "C" fn trampoline(_: TrampolineMarker) {
            // Figure 6-7. Stack Usage on Transfers to Interrupt and Exception Handling Routines

            // Here rsp is at an InterruptStackFrame
            // [rip][cs][eflags][esp][ss]
            core::arch::asm!(
                "cli",
                //"call {breakpoint}",

                "cld",

                "push 0", // error_code

                "push rax",
                "push rdi",
                "push rsi",
                "push rdx",
                "push rcx",
                "push r8",
                "push r9",
                "push r10",
                "push r11",
                "push rbx",
                "push rbp",
                "push r12",
                "push r13",
                "push r14",
                "push r15",

                // fn handler(registers: &mut Registers)
                "mov rdi, rsp",
                "call {handler}",

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

                "add rsp, 8", // error_code

                "sti",
                "iretq",

                //breakpoint = sym crate::debugger::breakpoint,
                handler = sym $handler,
                options(noreturn),
            );
        }

        trampoline
    }}
}

// "x86-interrupt" is gated behind #![feature(abi_x86_interrupt)].

/// A handler function for an interrupt or an exception without error code.
pub type HandlerFunc = unsafe extern "C" fn(&mut PtRegs);

/// A handler function for an exception that pushes an error code.
pub type HandlerFuncWithErrCode = unsafe extern "x86-interrupt" fn(&mut InterruptStackFrame, u64);

/// A handler function wrapped by the interrupt trampoline.
pub type TrampolineHandlerFunc = unsafe extern "C" fn(TrampolineMarker);

/// A page fault handler function that pushes a page fault error code.
pub type PageFaultHandlerFunc =
    unsafe extern "x86-interrupt" fn(&mut InterruptStackFrame, PageFaultErrorCode);

/// Invalid Opcode handler.
unsafe extern "C" fn invalid_opcode(regs: &mut PtRegs) {
    log::error!(
        "CPU {}, Invalid Opcode: {:#x?}",
        crate::cpu::get_cpu_id(),
        regs
    );
    crate::debugger::breakpoint(2);
    spin_forever();
}

/// Double Fault handler.
unsafe extern "C" fn double_fault(regs: &mut PtRegs) {
    log::error!(
        "CPU {}: Double Fault: {:#x?}",
        crate::cpu::get_cpu_id(),
        regs
    );
    crate::debugger::breakpoint(2);
    spin_forever();
}

/// Breakpoint handler.
unsafe extern "C" fn breakpoint(regs: &mut Registers) {
    log::warn!("CPU {}: Breakpoint: {:#x?}", crate::cpu::get_cpu_id(), regs);
    crate::debugger::breakpoint(2);
}

/// Stack Segment Fault handler
unsafe extern "x86-interrupt" fn stack_segment_fault(
    frame: &mut InterruptStackFrame,
    error_code: u64,
) {
    log::error!(
        "Stack Segment Fault (error code {:#b}): {:#x?}",
        error_code,
        frame,
    );
    crate::debugger::breakpoint(2);
    spin_forever();
}

/// General Protection Fault handler.
unsafe extern "C" fn general_protection_fault(regs: &mut Registers) {
    log::error!(
        "CPU {}: General Protection Fault (error code {:#b}): {:#x?}",
        crate::cpu::get_cpu_id(),
        regs.error_code,
        regs,
    );
    crate::debugger::breakpoint(2);
    spin_forever();
}

/// Page Fault handler.
unsafe extern "C" fn page_fault(regs: &mut Registers) {
    let address: u64;
    asm!("mov {}, cr2", out(reg) address);
    log::info!(
        "CPU {}: Page Fault (address {:#x}, error code {:?}): {:#x?}",
        crate::cpu::get_cpu_id(),
        address,
        regs.error_code,
        regs,
    );
    crate::debugger::breakpoint(2);
    spin_forever();
}

/// Timer handler.
unsafe extern "C" fn timer(regs: &mut Registers) {
    if let Some(slice) = crate::thread::schedule(regs) {
        set_timer(slice);
    }

    end_of_interrupt();
}

/// An interrupt.
#[derive(Copy, Clone, Debug)]
pub enum Interrupt {
    /// An exception.
    Exception(Exception),

    /// An IRQ.
    Irq(usize),
}

impl From<Interrupt> for usize {
    fn from(interrupt: Interrupt) -> usize {
        match interrupt {
            Interrupt::Exception(ex) => ex.into(),
            Interrupt::Irq(num) => IRQ_OFFSET + num,
        }
    }
}

impl TryFrom<usize> for Interrupt {
    type Error = &'static str;

    fn try_from(num: usize) -> Result<Self, Self::Error> {
        match num {
            0..=EXCEPTION_MAX => TryFrom::try_from(num).map(Self::Exception),
            IRQ_OFFSET..=255 => Ok(Self::Irq(num)),
            _ => Err("Invalid interrupt line"),
        }
    }
}

/// Registers passed to the ISR.
#[repr(C)]
#[derive(Debug)]
pub struct PtRegs {
    pub r15: u64,
    pub r14: u64,
    pub r13: u64,
    pub r12: u64,
    pub rbp: u64,
    pub rbx: u64,
    pub r11: u64,
    pub r10: u64,
    pub r9: u64,
    pub r8: u64,
    pub rcx: u64,
    pub rdx: u64,
    pub rsi: u64,
    pub rdi: u64,
    pub rax: u64,
}

/// An interrupt stack frame.
#[derive(Debug, Clone)]
#[repr(C)]
pub struct InterruptStackFrame {
    /// This value points to the instruction that should be executed when the interrupt
    /// handler returns. For most interrupts, this value points to the instruction immediately
    /// following the last executed instruction. However, for some exceptions (e.g., page faults),
    /// this value points to the faulting instruction, so that the instruction is restarted on
    /// return. See the documentation of the `InterruptDescriptorTable` fields for more details.
    pub instruction_pointer: VAddr,

    /// The code segment selector, padded with zeros.
    pub code_segment: u64,

    /// The flags register before the interrupt handler was invoked.
    pub cpu_flags: u64,

    /// The stack pointer at the time of the interrupt.
    pub stack_pointer: VAddr,

    /// The stack segment descriptor at the time of the interrupt (often zero in 64-bit mode).
    pub stack_segment: u64,
}

/// A page fault error code.
///
/// Some ASCII art courtesy of osdev.org:
///
/// ```
///  31              4   3   2   1   0
/// +---+--  --+---+---+---+---+---+---+
/// |   Reserved   | I | R | U | W | P |
/// +---+--  --+---+---+---+---+---+---+
/// ```
///
/// - P: Present. If not set, the accessed page does not have the Present bit set.
/// - W: Write. If not set, the fault was caused by a read access.
/// - U: User. If set, the fault was caused when in Ring 3.
/// - R: Reserved Write. When set, one or more page directory entries contain reserved bits which are set to 1.
/// - I: Instruction Fetch. When set, the fault was caused by an instruction fetch.
///
/// <https://wiki.osdev.org/Exceptions#Page_Fault>
#[repr(transparent)]
#[derive(Debug)]
pub struct PageFaultErrorCode(u64);

#[allow(dead_code)]
impl PageFaultErrorCode {
    /// Returns whether the fault was caused by a non-present page.
    pub fn caused_by_non_present(&self) -> bool {
        !self.0.get_bit(0)
    }

    /// Returns whether the fault was caused by a write operation.
    pub fn caused_by_write(&self) -> bool {
        self.0.get_bit(1)
    }

    /// Returns whether the fault occurred in CPL 3.
    pub fn caused_in_user_mode(&self) -> bool {
        self.0.get_bit(2)
    }

    /// Returns whether the fault was caused by an instruction fetch.
    pub fn caused_by_instruction_fetch(&self) -> bool {
        self.0.get_bit(4)
    }
}

/// Initializes global interrupt controllers.
///
/// This should be called only once.
pub unsafe fn init() {
    let pic1 = inb(PIC1_DATA);
    let pic2 = inb(PIC2_DATA);

    log::debug!("PIC masks: PIC1={:#x?}, PIC2={:#x?}", pic1, pic2);

    // Disable 8259 PIC
    outb(PIC1_DATA, 0xff);
    outb(PIC2_DATA, 0xff);

    let idt = &mut GLOBAL_IDT;
    idt.invalid_opcode.set_handler_fn(invalid_opcode);
    idt.breakpoint.set_handler_fn(wrap_interrupt!(breakpoint));
    idt.double_fault.set_handler_fn(double_fault);
    idt.stack_segment_fault.set_handler_fn(stack_segment_fault);
    idt.general_protection_fault
        .set_handler_fn(wrap_interrupt_with_error_code!(general_protection_fault));
    idt.page_fault
        .set_handler_fn(wrap_interrupt_with_error_code!(page_fault));

    idt.interrupts[0].set_handler_fn(wrap_interrupt!(timer));

    let ioapic_base = mps::probe_ioapic();
    ioapic::init(ioapic_base);
}

/// Initializes per-CPU interrupt controllers.
///
/// This should be called only once per CPU.
pub unsafe fn init_cpu() {
    lapic::init();
    ioapic::init_cpu();

    GLOBAL_IDT.load();

    asm!("sti");
}

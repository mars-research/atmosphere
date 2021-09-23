//! Interrupt handling.

// Copyright 2021 Zhaofeng Li
// Copyright 2017 Philipp Oppermann
//
// Licensed under the MIT license <http://opensource.org/licenses/MIT>.
// See top-level LICENSE.

mod exception;
mod lapic;
mod idt;

use x86::io::{inb, outb};

use core::convert::{Into, TryFrom};

use bit_field::BitField;
use x86::bits64::paging::VAddr;

use astd::sync::Mutex;
pub use exception::Exception;
use exception::EXCEPTION_MAX;
use idt::Idt;

/// The IRQ offset.
pub const IRQ_OFFSET: usize = 32;

/// The global IDT.
static GLOBAL_IDT: Mutex<Idt> = Mutex::new(Idt::new());

const PIC1_DATA: u16 = 0x21;
const PIC2_DATA: u16 = 0xa1;


// "x86-interrupt" is gated behind #![feature(abi_x86_interrupt)].

/// A handler function for an interrupt or an exception without error code.
pub type HandlerFunc = unsafe extern "C" fn(&mut PtRegs);

/// A handler function for an exception that pushes an error code.
pub type HandlerFuncWithErrCode =
    extern "x86-interrupt" fn(&mut InterruptStackFrame, u64);

/// A page fault handler function that pushes a page fault error code.
pub type PageFaultHandlerFunc =
    extern "x86-interrupt" fn(&mut InterruptStackFrame, PageFaultErrorCode);

/// Invalid Opcode handler.
unsafe extern "C" fn invalid_opcode(regs: &mut PtRegs) {
    log::error!("Invalid Opcode: {:#x?}", regs);
    loop {}
}

/// Double Fault handler.
unsafe extern "C" fn double_fault(regs: &mut PtRegs) {
    log::error!("Double Fault: {:#x?}", regs);
    loop {}
}

/// Stack Segment Fault handler
extern "x86-interrupt" fn stack_segment_fault(frame: &mut InterruptStackFrame, error_code: u64) {
    log::error!("General Protection Fault (error code {:#b}): {:#x?}", error_code, frame);
    loop {}
}

/// General Protection Fault handler.
extern "x86-interrupt" fn general_protection_fault(frame: &mut InterruptStackFrame, error_code: u64) {
    log::error!("General Protection Fault (error code {:#b}): {:#x?}", error_code, frame);
    loop {}
}

/// Page Fault handler.
extern "x86-interrupt" fn page_fault(frame: &mut InterruptStackFrame, error_code: PageFaultErrorCode) {
    log::info!("Page Fault (error code {:?}): {:#x?}", error_code, frame);

    // FIXME

    loop {}
}

/// An interrupt.
#[derive(Copy, Clone, Debug)]
pub enum Interrupt {
    /// An exception.
    Exception(Exception),

    /// An IRQ.
    Irq(usize),
}

impl Into<usize> for Interrupt {
    fn into(self) -> usize {
        match self {
            Interrupt::Exception(ex) => ex.into(),
            Interrupt::Irq(num) => IRQ_OFFSET + num,
        }
    }
}

impl TryFrom<usize> for Interrupt {
    type Error = &'static str;

    fn try_from(num: usize) -> Result<Self, Self::Error> {
        match num {
            0..=EXCEPTION_MAX => TryFrom::try_from(num).map(|e| Self::Exception(e)),
            IRQ_OFFSET..=255 => Ok(Self::Irq(num)),
            _ => Err("Invalid interrupt line"),
        }
    }
}

/// Registers passed to the ISR.
#[repr(C)]
#[derive(Debug)]
pub struct PtRegs {
    /*
     * C ABI says these regs are callee-preserved. They aren't saved on kernel entry
     * unless syscall needs a complete, fully filled "struct pt_regs".
     */
    pub r15: u64,
    pub r14: u64,
    pub r13: u64,
    pub r12: u64,
    pub rbp: u64,
    pub rbx: u64,
    /* These regs are callee-clobbered. Always saved on kernel entry. */
    pub r11: u64,
    pub r10: u64,
    pub r9: u64,
    pub r8: u64,
    pub rax: u64,
    pub rcx: u64,
    pub rdx: u64,
    pub rsi: u64,
    pub rdi: u64,
    /*
     * On syscall entry, this is syscall#. On CPU exception, this is error code.
     * On hw interrupt, it's IRQ number:
     */
    pub orig_ax: u64,
    /* Return frame for iretq */
    pub rip: u64,
    pub rcs: u64,
    pub rflags: u64,
    pub rsp: u64,
    pub ss: u64,
    /* top of stack page */
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
}

/// Initializes per-CPU interrupt controllers.
///
/// This should be called only once per CPU.
pub unsafe fn init_cpu() {
    lapic::init();

    let mut idt = GLOBAL_IDT.lock();
    idt.invalid_opcode.set_handler_fn(invalid_opcode);
    idt.double_fault.set_handler_fn(double_fault);
    idt.stack_segment_fault.set_handler_fn(stack_segment_fault);
    idt.general_protection_fault.set_handler_fn(general_protection_fault);
    idt.page_fault.set_handler_fn(page_fault);
    idt.load();
}

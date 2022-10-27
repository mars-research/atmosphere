//! X86-64 IDT abstractions.
//!
//! Most of this is borrowed from Philipp Oppermann's BlogOS, with
//! several adjustments for clarity.
//!
//! References:
//! - <https://wiki.osdev.org/Interrupt_Descriptor_Table>

// Copyright 2021 Zhaofeng Li
// Copyright 2017 Philipp Oppermann
//
// Licensed under the MIT license <http://opensource.org/licenses/MIT>.
// See top-level LICENSE.

use core::marker::PhantomData;
use core::mem;

use bit_field::BitField;
use x86::{segmentation, Ring};

use super::{HandlerFunc, HandlerFuncWithErrCode, PageFaultHandlerFunc};

/// An X86-64 Interrupt Descriptor Table.
#[derive(Clone)]
#[repr(align(8))]
#[repr(C)]
pub struct Idt {
    /// Device-By-Zero (`#DE`).
    pub divide_by_zero: Entry<HandlerFunc>,

    /// Debug (`#DB`)
    pub debug: Entry<HandlerFunc>,

    /// Non-Maskable Exception.
    pub non_maskable_interrupt: Entry<HandlerFunc>,

    /// Breakpoint (`#BP`)
    pub breakpoint: Entry<HandlerFunc>,

    /// Overflow (`#OF`)
    pub overflow: Entry<HandlerFunc>,

    /// Bound-Range Exception (`#BR`)
    pub bound_range_exceeded: Entry<HandlerFunc>,

    /// Invalid Opcode (`#UD`)
    pub invalid_opcode: Entry<HandlerFunc>,

    /// Device Not Available (`#NM`)
    pub device_not_available: Entry<HandlerFunc>,

    /// Double Fault (`#DF`)
    pub double_fault: Entry<HandlerFunc>,

    /// Obsolete
    exception_9: Entry<HandlerFunc>,

    /// Invalid TSS (`#TS`)
    pub invalid_tss: Entry<HandlerFuncWithErrCode>,

    /// Segment Not Present (`#NP`)
    pub segment_not_present: Entry<HandlerFuncWithErrCode>,

    /// Stack Segment Fault (`#SS`)
    pub stack_segment_fault: Entry<HandlerFuncWithErrCode>,

    /// General Protection Fault (`#GP`)
    pub general_protection_fault: Entry<HandlerFuncWithErrCode>,

    /// Page Fault (`#PF`)
    pub page_fault: Entry<PageFaultHandlerFunc>,

    /// Reserved
    exception_15: Entry<HandlerFunc>,

    /// X87 Floating-Point Exception (`#MF`)
    pub x87_floating_point: Entry<HandlerFunc>,

    /// Alignment Check (`#AC`)
    pub alignment_check: Entry<HandlerFunc>,

    /// Machine Check (`#MC`)
    pub machine_check: Entry<HandlerFunc>,

    /// SIMD Floating-Point (`#XM`)
    pub simd_floating_point: Entry<HandlerFunc>,

    /// Virtualization (`#VE`)
    pub virtualization: Entry<HandlerFunc>,

    /// Reserved
    reserved_2: [Entry<HandlerFunc>; 9],

    /// Security (`#SX`)
    pub security_exception: Entry<HandlerFunc>,

    /// Reserved
    reserved_3: Entry<HandlerFunc>,

    /// Other interrupts
    interrupts: [Entry<HandlerFunc>; 256 - 32],
}

impl Idt {
    pub const fn new() -> Self {
        Self {
            divide_by_zero: Entry::missing(),
            debug: Entry::missing(),
            non_maskable_interrupt: Entry::missing(),
            breakpoint: Entry::missing(),
            overflow: Entry::missing(),
            bound_range_exceeded: Entry::missing(),
            invalid_opcode: Entry::missing(),
            device_not_available: Entry::missing(),
            double_fault: Entry::missing(),
            exception_9: Entry::missing(),
            invalid_tss: Entry::missing(),
            segment_not_present: Entry::missing(),
            stack_segment_fault: Entry::missing(),
            general_protection_fault: Entry::missing(),
            page_fault: Entry::missing(),
            exception_15: Entry::missing(),
            x87_floating_point: Entry::missing(),
            alignment_check: Entry::missing(),
            machine_check: Entry::missing(),
            simd_floating_point: Entry::missing(),
            virtualization: Entry::missing(),
            reserved_2: [Entry::missing(); 9],
            security_exception: Entry::missing(),
            reserved_3: Entry::missing(),
            interrupts: [Entry::missing(); 256 - 32],
        }
    }

    /// Loads the IDT in the CPU using the `lidt` command.
    ///
    /// The IDT must live forever.
    pub unsafe fn load(&self) {
        use x86::dtables::{lidt, DescriptorTablePointer};

        let ptr = DescriptorTablePointer {
            base: self as *const _,
            limit: (mem::size_of::<Self>() - 1) as u16,
        };

        lidt(&ptr);
    }
}

/// An entry in an X86-64 Interrupt Descriptor Table.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Entry<F> {
    /// Bits 0 to 15 of the ISR entrypoint.
    entry_low: u16,

    /// GDT selector.
    selector: u16,

    /// The Interrupt Stack Table offset.
    ///
    /// Only the 3 least-significant bits are used.
    ist: u8,

    /// IDT attributes.
    pub attributes: EntryAttributes,

    /// Bits 16 to 31 of the ISR entrypoint.
    entry_mid: u16,

    /// Bits 32 to 63 of the ISR entrypoint.
    entry_hi: u32,

    /// Reserved.
    _reserved: u32,

    _phantom: PhantomData<F>,
}

#[allow(dead_code)]
impl<F> Entry<F> {
    /// Creates a non-present IDT entry.
    pub const fn missing() -> Self {
        Self {
            entry_low: 0,
            entry_mid: 0,
            entry_hi: 0,
            selector: 0,
            ist: 0,
            attributes: EntryAttributes::missing(),
            _reserved: 0,
            _phantom: PhantomData,
        }
    }

    /// Sets the handler address for the IDT entry and sets the present bit.
    ///
    /// For the code selector field, this function uses the code segment selector currently
    /// active in the CPU.
    fn set_handler_addr(&mut self, addr: u64) {
        self.entry_low = addr as u16;
        self.entry_mid = (addr >> 16) as u16;
        self.entry_hi = (addr >> 32) as u32;

        self.attributes.set_present(true);
        self.attributes.set_gate_type(GateType::Int32);
        self.selector = segmentation::cs().bits();
    }
}

macro_rules! impl_set_handler_fn {
    ($h:ty) => {
        #[cfg(target_arch = "x86_64")]
        impl Entry<$h> {
            /// Set the handler function for the IDT entry and sets the present bit.
            ///
            /// For the code selector field, this function uses the code segment selector currently
            /// active in the CPU.
            ///
            /// The function returns a mutable reference to the entry's options that allows
            /// further customization.
            #[allow(dead_code)]
            pub fn set_handler_fn(&mut self, handler: $h) {
                self.set_handler_addr(handler as u64)
            }
        }
    };
}

impl_set_handler_fn!(HandlerFunc);
impl_set_handler_fn!(HandlerFuncWithErrCode);
impl_set_handler_fn!(PageFaultHandlerFunc);

/// Attributes of an IDT entry.
///
/// Some ASCII art courtesy of osdev.org:
///
/// ```
///   7   6   5   4   3   2   1   0
/// +---+---+---+---+---+---+---+---+
/// | P |  DPL  | Z |    GateType   |
/// +---+---+---+---+---+---+---+---+
/// ```
///
/// - P: Present.
/// - DPL: Descriptor Privilege Level.
/// - Z: Zero.
/// - GateType: Type of the IDT gate (see `GateType`).
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct EntryAttributes(u8);

#[allow(dead_code)]
impl EntryAttributes {
    /// Returns an empty IDT entry (Not Present).
    const fn missing() -> Self {
        Self(0)
    }

    /// Sets or clears the Present bit.
    pub fn set_present(&mut self, present: bool) -> &mut Self {
        self.0.set_bit(7, present);
        self
    }

    /// Sets the Descriptor Privilege Level.
    pub fn set_privilege_level(&mut self, dpl: Ring) -> &mut Self {
        self.0.set_bits(5..7, dpl as u8);
        self
    }

    /// Sets the gate type.
    pub fn set_gate_type(&mut self, gate_type: GateType) -> &mut Self {
        self.0.set_bits(0..4, gate_type.into());
        self
    }
}

/// Type of an IDT gate.
///
/// This is succinctly summarized by osdev.org:
///
/// > Trap and Interrupt gates are similar, and their descriptors are structurally the
/// > same, they differ only in the "type" field. The difference is that for interrupt
/// > gates, interrupts are automatically disabled upon entry and reenabled upon IRET
/// > which restores the saved EFLAGS.
///
/// We mostly deal with `Int32` and `Trap32`. The GateType field is 4-bit wide.
#[allow(dead_code)]
pub enum GateType {
    /// 32-bit interrupt gate (0b1110).
    ///
    /// Interrupts are automatically disabled upon entry.
    Int32,

    /// 16-bit interrupt gate (0b0110).
    ///
    /// Interrupts are automatically disabled upon entry.
    Int16,

    /// 32-bit trap gate (0b1111).
    ///
    /// Interrupts are not disabled upon entry.
    Trap32,

    /// 16-bit trap gate (0b0111).
    ///
    /// Interrupts are not disabled upon entry.
    Trap16,
}

impl From<GateType> for u8 {
    fn from(gate_type: GateType) -> u8 {
        match gate_type {
            GateType::Int32 => 0b1110,
            GateType::Trap32 => 0b1111,

            GateType::Int16 => 0b0110,
            GateType::Trap16 => 0b0111,
        }
    }
}

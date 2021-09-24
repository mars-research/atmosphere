//! Per-CPU data structures.
//!
//! Currently consists of the following:
//!
//! - VMXON region
//! - GDT
//! - TSS
//! - IST stack spaces
//!
//! We preallocate the structure for CPU 0, and the space for
//! other CPUs are provided by Cpu capabilities.

use crate::vmx::vmcs::Vmxon;
use crate::gdt::{GlobalDescriptorTable, TaskStateSegment};

/// Size of an IST stack.
pub const IST_STACK_SIZE: usize = 4096;

pub type IstStack = [u8; IST_STACK_SIZE];

/// Per-processor data for CPU 0.
pub static mut CPU0: Cpu = Cpu::new();

/// Returns a mutable handle to the current CPU's data structure.
pub unsafe fn get_current_cpu() -> &'static mut Cpu {
    let id = crate::interrupt::cpu_id();

    if id != 0 {
        unimplemented!()
    }

    &mut CPU0
}

/// Per-processor data for a CPU.
#[repr(align(4096))]
pub struct Cpu {
    /// The VMXON region.
    pub vmxon: Vmxon,

    /// The Global Descriptor Table.
    ///
    /// See [crate::interrupt::gdt] for a list of indices and their associated usages.
    pub gdt: GlobalDescriptorTable,

    /// The Task State Segment.
    pub tss: TaskStateSegment,

    /// The Interrupt Stacks.
    pub ist: [IstStack; 7],
}

impl Cpu {
    pub const fn new() -> Self {
        Self {
            vmxon: Vmxon::new(),
            gdt: GlobalDescriptorTable::empty(),
            tss: TaskStateSegment::new(),
            ist: [[0u8; IST_STACK_SIZE]; 7],
        }
    }
}

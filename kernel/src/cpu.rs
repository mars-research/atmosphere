//! Per-CPU data structures.
//!
//! Currently consists of the following:
//!
//! - VMXON region
//! - GDT
//! - TSS
//! - IST stack spaces
//!
//! We preallocate the structure for CPU 0, and the space for other
//! CPUs are provided by Cpu capabilities.

use core::ops::{Deref, DerefMut};

use spin::RwLock;

use crate::vmx::vmcs::Vmxon;
use crate::gdt::{GlobalDescriptorTable, IstStack, TaskStateSegment};

/// Per-processor data for CPU 0.
static CPU0: RwLock<Cpu> = RwLock::new(Cpu::new());

/// Returns an immutable handle to the current CPU's data structure.
pub fn get_current() -> impl Deref<Target = Cpu> {
    let id = crate::interrupt::cpu_id();

    if id != 0 {
        panic!("SMP is not implemented (CPU {})", id)
    }

    CPU0.read()
}

/// Returns a mutable handle to the current CPU's data structure.
pub fn get_current_mut() -> impl DerefMut<Target = Cpu> {
    let id = crate::interrupt::cpu_id();

    if id != 0 {
        panic!("SMP is not implemented (CPU {})", id)
    }

    CPU0.write()
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
            ist: [
                IstStack::new(),
                IstStack::new(),
                IstStack::new(),
                IstStack::new(),
                IstStack::new(),
                IstStack::new(),
                IstStack::new(),
            ],
        }
    }
}

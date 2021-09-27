//! The per-CPU data structure.
//!
//! The [`Cpu`] data structure is set as the `GS` base on the CPU.
//! It currently consists of the following:
//!
//! - VMXON region
//! - GDT
//! - TSS
//! - IST stack spaces
//!
//! We preallocate the structure for CPU 0, and the space for other
//! CPUs are provided by Cpu capabilities.

use core::mem::{self, MaybeUninit};
use core::ptr;

use x86::msr;
use x86::apic::xapic::XAPIC;

use crate::gdt::{GlobalDescriptorTable, IstStack, TaskStateSegment};
use crate::vmx::vmcs::Vmxon;

/// Per-processor data for CPU 0.
static mut CPU0: Cpu = Cpu::new();

/// Offset of GS where the pointer to `Cpu` is stored.
const GS_SELF_PTR_OFFSET: usize = mem::size_of::<Vmxon>() as usize;

/// Returns a handle to the current CPU's data structure.
pub fn get_current() -> &'static mut Cpu {
    let address: u64;

    unsafe {
        asm!(
            "mov rax, gs:[{gs_offset}]",
            gs_offset = const GS_SELF_PTR_OFFSET,
            lateout("rax") address,
        );
    }

    let address = address as *mut Cpu;

    unsafe { &mut *address }
}

/// Per-processor data for a CPU.
#[repr(align(4096))]
pub struct Cpu {
    // WARNING: If you change the position of `self_ptr`, you must also
    // change `GS_SELF_PTR_OFFSET` above!

    /// The VMXON region.
    pub vmxon: Vmxon,

    // WARNING: If you change the position of `self_ptr`, you must also
    // change `GS_SELF_PTR_OFFSET` above!

    /// A pointer to ourselves.
    ///
    /// We do a `mov rax, gs:[CPU_GS_OFFSET]` to get our own address.
    /// We also want to be able to easily access other fields directly.
    pub self_ptr: *const Cpu,

    /// State for the xAPIC driver.
    pub xapic: MaybeUninit<XAPIC>,

    /// The Global Descriptor Table.
    ///
    /// See [crate::gdt] for a list of indices and their associated usages.
    pub gdt: GlobalDescriptorTable,

    /// The Task State Segment.
    pub tss: TaskStateSegment,

    /// The Interrupt Stacks.
    pub ist: [IstStack; 7],
}

unsafe impl Send for Cpu {}
unsafe impl Sync for Cpu {}

impl Cpu {
    pub const fn new() -> Self {
        Self {
            vmxon: Vmxon::new(),
            self_ptr: ptr::null(),
            xapic: MaybeUninit::uninit(),
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

/// Initialize the CPU-local data structure for CPU 0.
///
/// This should only be called once.
pub unsafe fn init_cpu0() {
    let address = &CPU0 as *const Cpu;

    CPU0.self_ptr = address;

    msr::wrmsr(msr::IA32_GS_BASE, address as u64);
}

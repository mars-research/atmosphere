//! The per-CPU data structure.
//!
//! The [`Cpu`] data structure is set as the `GS` base on the CPU.
//! It currently consists of the following:
//!
//! - GDT
//! - TSS
//! - IST stack spaces

use core::arch::asm;
use core::mem::MaybeUninit;
use core::ptr;

use x86::apic::xapic::XAPIC;
use x86::msr;

use crate::gdt::{GlobalDescriptorTable, IstStack, TaskStateSegment};

const NEW_CPU: Cpu = Cpu::new();

/// Per-processor data.
static mut CPUS: [Cpu; 16] = [NEW_CPU; 16];

/// Offset of GS where the pointer to `Cpu` is stored.
const GS_SELF_PTR_OFFSET: usize = 0;

/// Offset of GS where the CPU ID is located.
const GS_CPU_ID_OFFSET: usize = 8;

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
#[repr(C, align(4096))]
pub struct Cpu {
    // WARNING: If you change the position of `self_ptr`, you must also
    // change `GS_SELF_PTR_OFFSET` above!

    // WARNING: If you change the position of `self_ptr`, you must also
    // change `GS_SELF_PTR_OFFSET` above!
    /// A pointer to ourselves.
    ///
    /// We do a `mov rax, gs:[GS_SELF_PTR_OFFSET]` to get our own address.
    /// We also want to be able to easily access other fields directly.
    pub self_ptr: *const Cpu,

    pub id: usize,

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
            self_ptr: ptr::null(),
            id: 0,
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

/// Initialize the CPU-local data structure.
///
/// This should only be called once.
pub unsafe fn init_cpu(cpu_id: usize) {
    let mut cpu = &mut CPUS[cpu_id];
    let address = cpu as *const Cpu;

    log::info!("CPU{} @ {:?}", cpu_id, address);

    let self_ptr_ptr = &mut cpu.self_ptr as *mut *const Cpu;
    cpu.self_ptr = address;
    cpu.id = cpu_id;

    msr::wrmsr(msr::IA32_GS_BASE, address as u64);
}

pub fn get_cpu_id() -> usize {
    let cpu_id;

    unsafe {
        asm!(
            "mov {result}, gs:{offset}",
            offset = const GS_CPU_ID_OFFSET,
            result = out(reg) cpu_id,
        );
    }

    cpu_id
}

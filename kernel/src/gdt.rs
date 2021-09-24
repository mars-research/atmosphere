//! The Global Descriptor Table and related stuff.
//!
//! During boot, we do the following:
//!
//! 1. The bootstrap assembly code loads a temporary GDT.
//! 2. On CPU 0, we initialize and load the GDT in Rust using preallocated space.
//! 3. On other CPUs, we initialize and load the GDT using space provided by
//!    Cpu capabilities.
//!
//! ## GDT Entries
//!
//! * 0 - Null
//! * 1 - Kernel Code
//! * 2 - Kernel Data
//! * 3,4 - TSS

use core::cmp::min;
use core::mem;

use x86::Ring;
pub use x86::bits64::task::TaskStateSegment;
use x86::bits64::segmentation::load_cs;
use x86::dtables::{lgdt, DescriptorTablePointer};
use x86::segmentation::{load_ds, load_es, load_fs, load_gs, load_ss, SegmentSelector};
use x86::task::load_tr;

/// Size of an IST stack.
const IST_STACK_SIZE: usize = 4096;

// GDT access flags
const GDT_A_PRESENT: u8 = 1 << 7;
const GDT_A_RING_0: u8 = 0 << 5;
// const GDT_A_RING_1: u8 = 1 << 5;
// const GDT_A_RING_2: u8 = 2 << 5;
const GDT_A_RING_3: u8 = 3 << 5;
const GDT_A_SYSTEM: u8 = 1 << 4;
const GDT_A_EXECUTABLE: u8 = 1 << 3;
// const GDT_A_CONFORMING: u8 = 1 << 2;
const GDT_A_READABLE: u8 = 1 << 1;
// const GDT_A_DIRTY: u8 = 1;

const GDT_A_TSS_AVAIL: u8 = 0x9;
// const GDT_A_TSS_BUSY: u8 = 0xB;

// GDT flags
// const GDT_F_PAGE_SIZE: u8 = 1 << 7;
// const GDT_F_PROTECTED_MODE: u8 = 1 << 6;
const GDT_F_LONG_MODE: u8 = 1 << 5;

/// Initializes and loads the GDT.
///
/// This must be called only once for each CPU reset.
pub unsafe fn init_cpu() {
    let mut cpu = crate::cpu::get_current_mut();

    // Initialize TSS
    let tss_addr = {
        for i in 0..min(cpu.ist.len(), 7) {
            let ist_addr = &cpu.ist[i] as *const IstStack;
            cpu.tss.set_ist(i, ist_addr as u64);
        }

        &cpu.tss as *const TaskStateSegment
    };

    // Initialize GDT
    let mut gdt = &mut cpu.gdt;

    gdt.kernel_code = GdtEntry::new(
        0,
        0,
        GDT_A_PRESENT | GDT_A_RING_0 | GDT_A_SYSTEM | GDT_A_EXECUTABLE | GDT_A_READABLE,
        GDT_F_LONG_MODE,
    );

    gdt.kernel_data = GdtEntry::new(
        0,
        0,
        GDT_A_PRESENT | GDT_A_RING_0 | GDT_A_SYSTEM | GDT_A_READABLE,
        GDT_F_LONG_MODE,
    );

    gdt.tss = BigGdtEntry::new(
        tss_addr as u64,
        mem::size_of::<TaskStateSegment>() as u32,
        GDT_A_PRESENT | GDT_A_RING_3 | GDT_A_TSS_AVAIL,
        0,
    );

    // Load GDT
    lgdt(&gdt.get_pointer());

    load_cs(SegmentSelector::new(1, Ring::Ring0));
    load_ds(SegmentSelector::new(2, Ring::Ring0));
    load_es(SegmentSelector::new(2, Ring::Ring0));
    load_fs(SegmentSelector::new(2, Ring::Ring0));
    load_gs(SegmentSelector::new(2, Ring::Ring0));
    load_ss(SegmentSelector::new(2, Ring::Ring0));
    load_tr(SegmentSelector::new(3, Ring::Ring0));
}

/// A Global Descriptor Table.
#[derive(Debug)]
#[repr(packed)]
pub struct GlobalDescriptorTable {
    /// Null entry.
    _null: GdtEntry,

    /// Kernel code.
    pub kernel_code: GdtEntry,

    /// Kernel data.
    pub kernel_data: GdtEntry,

    /// TSS.
    ///
    /// This is 16 bytes in Long Mode.
    pub tss: BigGdtEntry,
}

impl GlobalDescriptorTable {
    /// Zero-initializes the GDT.
    ///
    /// It must be correctly initialized before being loaded.
    pub const fn empty() -> Self {
        Self {
            _null: GdtEntry::empty(),
            kernel_code: GdtEntry::empty(),
            kernel_data: GdtEntry::empty(),
            tss: BigGdtEntry::empty(),
        }
    }

    /// Returns a pointer to this GDT.
    fn get_pointer(&self) -> DescriptorTablePointer<Self> {
        let limit = mem::size_of::<Self>().try_into()
            .expect("GDT too big");

        DescriptorTablePointer {
            limit,
            base: self as *const GlobalDescriptorTable,
        }
    }
}

/// A 8-byte GDT entry.
#[derive(Copy, Clone, Debug)]
#[repr(packed)]
pub struct GdtEntry {
    limitl: u16,
    offsetl: u16,
    offsetm: u8,
    access_type: u8,
    flags_limith: u8,
    offseth: u8,
}

impl GdtEntry {
    /// Creates an empty (not present) entry.
    pub const fn empty() -> Self {
        Self::new(0, 0, 0, 0)
    }

    /// Creates a GDT entry.
    pub const fn new(offset: u32, limit: u32, access_type: u8, flags: u8) -> Self {
        Self {
            limitl: limit as u16,
            offsetl: offset as u16,
            offsetm: (offset >> 16) as u8,
            access_type,
            flags_limith: flags & 0xF0 | ((limit >> 16) as u8) & 0x0F,
            offseth: (offset >> 24) as u8,
        }
    }

    /// Returns the "Access Bytes" that VMX wants.
    pub fn access_bytes(&self) -> u32 {
        let flags = self.flags_limith & 0b11110000;
        (self.access_type as u32) | ((flags as u32) << 8)
    }
}

/// A 16-byte GDT entry.
///
/// This is described in Figure 4-22 in AMD Vol. 2.
#[derive(Copy, Clone, Debug)]
#[repr(packed)]
pub struct BigGdtEntry {
    limitl: u16,
    offsetl: u16,
    offsetm: u8,
    access_type: u8,
    flags_limith: u8,
    offseth: u8,
    offsetx: u32,
    reserved: u32,
}

impl BigGdtEntry {
    /// Creates an empty (not present) entry.
    pub const fn empty() -> Self {
        Self::new(0, 0, 0, 0)
    }

    /// Creates a 16-byte GDT entry.
    pub const fn new(offset: u64, limit: u32, access_type: u8, flags: u8) -> Self {
        Self {
            limitl: limit as u16,
            offsetl: offset as u16,
            offsetm: (offset >> 16) as u8,
            access_type,
            flags_limith: flags & 0xF0 | ((limit >> 16) as u8) & 0x0F,
            offsetx: (offset >> 32) as u32,
            offseth: (offset >> 24) as u8,
            reserved: 0,
        }
    }

    /// Returns the "Access Bytes" that VMX wants.
    pub fn access_bytes(&self) -> u32 {
        let flags = self.flags_limith & 0b11110000;
        (self.access_type as u32) | ((flags as u32) << 8)
    }
}

/// An IST stack.
#[repr(transparent)]
pub struct IstStack([u8; IST_STACK_SIZE]);

impl IstStack {
    pub const fn new() -> Self {
        Self([0u8; IST_STACK_SIZE])
    }
}

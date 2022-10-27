//! LAPIC.
//!
//! We just use the xAPIC implementation in the x86 crate.

use core::slice;

use x86::apic::xapic::XAPIC;
use x86::apic::ApicControl;
use x86::msr;

use crate::cpu;

/// Returns the 4KiB LAPIC region.
unsafe fn probe_apic() -> &'static mut [u32] {
    let msr27: u32 = msr::rdmsr(msr::APIC_BASE) as u32;
    let lapic = (msr27 & 0xffff_0000) as usize as *mut u32;

    slice::from_raw_parts_mut(lapic, 4096 / 4)
}

/// Initializes LAPIC in xAPIC mode.
pub unsafe fn init() {
    let cpu = cpu::get_current();

    let apic_region = probe_apic();
    let xapic = cpu.xapic.assume_init_mut();
    *xapic = XAPIC::new(apic_region);

    xapic.attach();
}

/// Returns the current processor's APIC ID.
#[allow(dead_code)]
pub fn cpu_id() -> u32 {
    let xapic = unsafe { cpu::get_current().xapic.assume_init_ref() };
    xapic.id()
}

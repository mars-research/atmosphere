//! LAPIC.
//!
//! We just use the xAPIC implementation in the x86 crate.

use core::arch::asm;
use core::slice;

use x86::apic::xapic::XAPIC;
use x86::apic::{ApicControl, ApicId};
use x86::msr;

use crate::boot::ap_start::StartTrampoline;
use crate::{boot, cpu};

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
    log::info!("APIC region: {:?}", apic_region as *mut _ as *mut u8);

    let mut xapic = XAPIC::new(apic_region);
    xapic.attach();

    cpu.xapic.write(xapic);
}

/// Boots an application processor.
pub unsafe fn boot_ap(cpu_id: u32, stack: u64, code: u64) {
    let cpu = cpu::get_current();
    let xapic = cpu.xapic.assume_init_mut();

    let start_page = StartTrampoline::new(0x7000)
        .unwrap()
        .with_code(code)
        .with_cr3(boot::get_boot_info().pml4 as u64)
        .with_stack(stack)
        .with_arg(cpu_id as u64)
        .start_page();

    log::info!("page = {:#x}", start_page);

    // FIXME: X2APIC APIC ID
    let apic_id = ApicId::XApic(cpu_id as u8);
    xapic.ipi_init(apic_id);
    xapic.ipi_startup(apic_id, start_page);
}

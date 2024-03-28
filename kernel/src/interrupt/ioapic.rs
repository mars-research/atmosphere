//! IOAPIC.

use core::mem::MaybeUninit;

use x86::apic::{ioapic::IoApic, ApicControl};

pub static mut IOAPIC: MaybeUninit<IoApic> = MaybeUninit::zeroed();

pub unsafe fn init(ioapic_base: usize) {
    log::debug!("IOAPIC base: {:#x}", ioapic_base);
    let mut ioapic = IoApic::new(ioapic_base);
    IOAPIC.write(ioapic);
}

pub unsafe fn init_cpu() {
    let mut cpu = crate::cpu::get_current();

    let ioapic = IOAPIC.assume_init_mut();
    ioapic.enable(0, crate::cpu::get_cpu_id() as u8);

    let xapic = cpu.xapic.assume_init_mut();

    log::debug!("Init CPU {} {} {}", cpu.id, xapic.id(), xapic.logical_id());
}

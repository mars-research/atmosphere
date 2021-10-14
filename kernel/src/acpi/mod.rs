pub mod sdt;

use self::sdt::{SdtHeader, Signature};
use crate::boot::get_bootinfo;
use crate::utils::bochs_magic_breakpoint;
use core::mem::size_of;
use core::usize;

/// Pulls the RSDP from the Multiboot v2 BootInfo.
/// Checks that the pointer is valid and using ACPI v2
pub unsafe fn init() {
    let boot_info = get_bootinfo();

    let tag = boot_info.rsdp_v1_tag();

    log::debug!("{:#?}", &tag);

    if tag.is_none() {
        panic!("RSDP v1 required!");
    }

    let rsdp_tag = tag.unwrap();
    if !rsdp_tag.checksum_is_valid() {
        panic!("RSDP Tag has Invalid Checksum!");
    }
    log::debug!("OEM ID: {}", rsdp_tag.oem_id().unwrap_or("None"));

    // Print out tables
    let handler = |signature: Signature, header: &SdtHeader| {
        log::debug!("{:#?}", signature);

        match signature {
            Signature::FADT => {
                log::debug!("{:#?}", header);
            }
            _ => {}
        }
    };

    iterate_acpi_tables(&handler);
}

unsafe fn get_rsdp() -> *const SdtHeader {
    let boot_info = get_bootinfo();
    let tag = boot_info.rsdp_v1_tag().unwrap();

    tag.rsdt_address() as *const SdtHeader
}

/// Iterates over the RDST passing all signatures and headers into the provided handler
pub unsafe fn iterate_acpi_tables<F: Fn(Signature, &SdtHeader)>(handler: &F) {
    let rdsp = get_rsdp();

    // Make sure we're looking at RDST
    let rdst = *rdsp;

    log::debug!("{:#?}", rdst);

    let res = rdst.validate(Signature::RSDT);

    if res.is_err() {
        panic!("{:#?}", res.unwrap_err());
    }

    // The RDST table is formatted as so:
    // ------------------------------------
    // | SDT Header with Signature "RDST" |
    // ------------------------------------
    // |  Pointers to other SDTHeaders    |
    // ------------------------------------
    // This is why we're dividing by `size_of::<u32>`, it is the size
    // of the pointers to the other SDT Headers
    let num_tables = (rdst.length as usize - size_of::<SdtHeader>()) / size_of::<u32>();
    let table_base = ((rdsp as usize) + size_of::<SdtHeader>()) as *const u32;

    for i in 0..num_tables {
        let ptr = *table_base.add(i) as *const SdtHeader;
        let header = *ptr;
        handler(header.signature, &header);
    }
}

use core::ptr;

const EBDA_BASE: usize = 0x80000;
const EBDA_MAX_SIZE: usize = 128 * 1024;
const BIOS_BASE: usize = 0xf0000;
const BIOS_MAX_SIZE: usize = 64 * 1024;

const FP_SIGNATURE: &[u8] = b"_MP_";
const CONF_SIGNATURE: &[u8] = b"PCMP";

const ENTRY_IOAPIC: u8 = 2;

#[derive(Debug)]
#[repr(C)]
struct FloatingPointer {
    signature: [u8; 4],
    phys_addr: u32,
}

#[derive(Debug)]
#[repr(C)]
struct ConfigurationTable {
    signature: [u8; 4],
    len: u16,
    spec_rev: u8,
    checksum: u8,
    oem_id: [u8; 8],
    product_id: [u8; 12],
    oem_table_ptr: u32,
    oem_table_size: u16,
    entry_count: u16,
    lapic_base: u32,
}

#[derive(Debug)]
#[repr(C)]
struct IoApicEntry {
    entry_type: u8,
    id: u8,
    version: u8,
    flags: u8,
    base: u32,
}

impl FloatingPointer {
    fn get_config_table(&self) -> &'static ConfigurationTable {
        let config: &ConfigurationTable = unsafe { &*(self.phys_addr as *const _) };
        if config.signature != CONF_SIGNATURE {
            panic!("Invalid configuration table");
        }
        config
    }
}

impl ConfigurationTable {
    const HEADER_SIZE: usize = 44;

    fn oem_id_str(&self) -> Option<&str> {
        core::str::from_utf8(&self.oem_id).ok()
    }

    fn product_id_str(&self) -> Option<&str> {
        core::str::from_utf8(&self.product_id).ok()
    }

    fn get_ioapic_entry(&self) -> Option<&'static IoApicEntry> {
        let mut cur = (self as *const ConfigurationTable as usize) + Self::HEADER_SIZE;
        let mut i = 0;

        while i < self.entry_count {
            let entry_type = unsafe { ptr::read_volatile(cur as *const u8) };
            let entry_len = match entry_type {
                0 => 20, // Processor
                1 | 2 | 3 | 4 => 8,
                _ => panic!("Invalid MPS entry type {}", entry_type),
            };

            if entry_type == ENTRY_IOAPIC {
                let entry = unsafe { &*(cur as *const IoApicEntry) };
                return Some(entry);
            }

            cur += entry_len;
            i += 1;
        }

        None
    }
}

pub unsafe fn probe_ioapic() -> usize {
    let fp_p = find_fp(EBDA_BASE, EBDA_MAX_SIZE).or_else(|| find_fp(BIOS_BASE, BIOS_MAX_SIZE));

    let fp = if let Some(fp_p) = fp_p {
        log::info!("MPS Floating Pointer: {:#x?}", fp_p);
        &*fp_p
    } else {
        panic!("MPS Floating Pointer not found");
    };

    let config = fp.get_config_table();
    let ioapic = config.get_ioapic_entry().expect("No IOAPIC entry found");
    return ioapic.base as usize;
}

unsafe fn find_fp(base: usize, size: usize) -> Option<*const FloatingPointer> {
    let mut cur = base;
    let search_end = cur + size - 16;
    while cur < search_end {
        let signature = ptr::read_volatile(cur as *const [u8; FP_SIGNATURE.len()]);
        if signature == FP_SIGNATURE {
            return Some(cur as *const FloatingPointer);
        }
        cur += 16;
    }
    None
}

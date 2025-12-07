use crate::class::PciClass;
use crate::header::{read_config_space, PciDeviceHeader};
use crate::println;
use crate::PciHeaderType;
use alloc::vec::Vec;
use byteorder::{ByteOrder, LittleEndian};
use core::fmt;
use heapless::Vec as AVec;

use core::arch::asm;

const PCI_ADDR_PORT: u16 = 0xCF8;
const PCI_DATA_PORT: u16 = 0xCFC;

const BASE_PAGE_SIZE: u32 = 4096;

macro_rules! round_up {
    ($num:expr, $s:expr) => {
        (($num + $s - 1) / $s) * $s
    };
}

#[derive(Debug)]
pub struct PciDevice {
    pub pci_addr: PciAddress,
    pub pci_hdr: PciDeviceHeader,
}

impl PciDevice {
    pub unsafe fn new(pci_addr: PciAddress, pci_hdr: PciDeviceHeader) -> PciDevice {
        PciDevice { pci_addr, pci_hdr }
    }

    pub fn class(&self) -> PciClass {
        self.pci_hdr.class()
    }

    pub fn subclass(&self) -> u8 {
        self.pci_hdr.subclass()
    }

    pub fn vendor_id(&self) -> u16 {
        self.pci_hdr.vendor_id()
    }

    pub fn device_id(&self) -> u16 {
        self.pci_hdr.device_id()
    }
}

#[derive(Copy, Clone, Debug)]
pub struct PciBarAddr {
    base: u64,
    size: usize,
}

impl fmt::Display for PciBarAddr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.size > 0 {
            write!(
                f,
                "Memory base = 0x{:08X}, size = 0x{:04X}",
                self.base, self.size
            )
        } else {
            write!(f, "Port = 0x{:04X}", self.base)
        }
    }
}

impl PartialEq for PciBarAddr {
    fn eq(&self, other: &Self) -> bool {
        self.base == other.base
    }
}

impl PciBarAddr {
    pub fn base(&self) -> u64 {
        self.base
    }
    pub fn size(&self) -> usize {
        self.size
    }
    pub unsafe fn new(base: u64, size: usize) -> PciBarAddr {
        PciBarAddr { base, size }
    }

    pub unsafe fn get_base(&self) -> u64 {
        self.base
    }

    pub unsafe fn get_size(&self) -> usize {
        self.size
    }
}

#[derive(Debug, Copy, Clone)]
pub struct PciAddress {
    bus: u8,
    dev: u8,
    func: u8,
}

impl PciAddress {
    fn new(bus: u8, dev: u8, func: u8) -> Result<PciAddress, &'static str> {
        // bus is implicitly checked because it's u8
        if
        /* bus <= 255 && */
        dev < 32 && func < 8 {
            Ok(PciAddress { bus, dev, func })
        } else {
            Err("Invalid pci address")
        }
    }
}

impl Into<(u8, u8, u8)> for PciAddress {
    fn into(self) -> (u8, u8, u8) {
        (self.bus, self.dev, self.func)
    }
}

pub fn get_config(bus: u8, dev: u8, func: u8) -> Result<PciDevice, &'static str> {
    // Check if the pci address is valid
    let pci_addr = match PciAddress::new(bus, dev, func) {
        Err(e) => return Err(e),
        Ok(a) => a,
    };

    match read_config_space(&pci_addr) {
        Ok(hdr) => unsafe { Ok(PciDevice::new(pci_addr, hdr)) },
        _ => Err("Invalid pci address"),
    }
}

pub fn pci_read_bars(pci: &PciAddress, hdr_type: PciHeaderType) -> AVec<Option<PciBarAddr>, 6> {
    let mut bar_vec: AVec<Option<PciBarAddr>, 6> = AVec::<_, 6>::new();

    // Baraddresses start from offset 0x10 in the config space and there can be a 2-6 bars each
    // 32-bit in size depending on the PCI device type
    let start = 0x10;
    let end: u8;
    match hdr_type & PciHeaderType::HEADER_TYPE {
        PciHeaderType::GENERAL => {
            end = start + 6 * 4;
        }

        PciHeaderType::PCITOPCI => {
            end = start + 2 * 4;
        }

        _ => end = start,
    }

    for off in (start..end).step_by(4) {
        let mut addr = pci_read(pci, off);
        if addr & 0xFFFF_FFFC == 0 {
            bar_vec.push(None).unwrap();
        } else if addr & 1 == 0 {
            addr &= 0xFFFF_FFF0;
            // Write all 1's to the pci config space
            pci_write(pci, off, 0xFFFF_FFFF);
            // Read it back, unmask, add 1 to determine size
            let size = round_up!((!pci_read(pci, off)) + 1, BASE_PAGE_SIZE);
            // Restore the original bar address
            pci_write(pci, off, addr);
            unsafe {
                bar_vec
                    .push(Some(PciBarAddr::new(
                        addr as u64 & 0xFFFF_FFF0,
                        size as usize,
                    )))
                    .unwrap();
            }
            //println!("BarAddr {:x} size {:x}", addr, size);
        } else {
            unsafe {
                bar_vec
                    .push(Some(PciBarAddr::new(addr as u64 & 0xFFFC, 0usize)))
                    .unwrap();
            }
            //println!("Bar I/O Addr {:x} size {:x}", addr, size);
        }
    }
    bar_vec
}

pub fn pci_read_range(pci: &PciAddress, offset: u8, len: u8) -> Vec<u8> {
    assert!(len > 3 && len % 4 == 0);
    let mut ret = Vec::with_capacity(len as usize);
    let results = (offset..offset + len)
        .step_by(4)
        .fold(Vec::new(), |mut acc, offset| {
            let val = pci_read(pci, offset);
            acc.push(val);
            acc
        });
    unsafe {
        ret.set_len(len as usize);
    }
    LittleEndian::write_u32_into(&*results, &mut ret);
    ret
}

pub fn pci_read(pci: &PciAddress, offset: u8) -> u32 {
    let address = 0x80000000
        | ((pci.bus as u32) << 16)
        | ((pci.dev as u32) << 11)
        | ((pci.func as u32) << 8)
        | ((offset as u32) & 0xFC);
    let value: u32;
    unsafe {
        asm!("mov dx, {aport}",
          "out dx, eax",
          "mov dx, ${dport}",
          "in eax, dx",
        aport = const { PCI_ADDR_PORT },
        dport = const { PCI_DATA_PORT },
        inout("eax") address => value, out("edx") _, options(nomem, nostack, preserves_flags));
    }
    value
}

pub fn pci_write(pci: &PciAddress, offset: u8, value: u32) {
    let address = 0x80000000
        | ((pci.bus as u32) << 16)
        | ((pci.dev as u32) << 11)
        | ((pci.func as u32) << 8)
        | ((offset as u32) & 0xFC);

    unsafe {
        asm!("mov dx, {aport}",
          "out dx, eax",
            aport = const { PCI_ADDR_PORT },
        in("eax") address, out ("edx") _, options(nostack, nomem, preserves_flags));
        asm!("mov dx, {dport}",
          "out dx, eax",
        dport = const { PCI_DATA_PORT },
              in("eax") value, out("edx") _, options(nostack, nomem, preserves_flags));
    }
}

pub fn pci_enable_bus_mastering(pci_addr: &PciAddress) {
    let cmd_status = pci_read(pci_addr, 4);
    let mut command = cmd_status & 0xFFFF;
    let status = (cmd_status >> 16) & 0xFFFF;
    command |= 1 << 2;
    let value = u32::from(command) | (u32::from(status) << 16);
    pci_write(pci_addr, 4, value);
    log::trace!("Enable bus mastering for device");
}

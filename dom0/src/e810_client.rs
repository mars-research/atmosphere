// dom0/src/e810_client.rs (no VFIO, no std)
use crate::USERSPACE_BASE;
use pcid::utils::PciBarAddr;
use e810_driver::device::{E810Device, Result as E810Result};
pub const E810_PCI_DEV: (usize, usize, usize) = (0x17, 0, 0);

unsafe fn attach_e810_iommu() {
    let io_pml4 = asys::sys_rd_io_cr3() as u64;
    log::info!("E810 IOMMU root @ {:#x}", io_pml4);

    // Attach 0000:17:00.0 to this IO page-table
    asys::sys_set_device_iommu(
        E810_PCI_DEV.0, // bus = 0x17
        E810_PCI_DEV.1, // dev = 0
        E810_PCI_DEV.2, // func = 0
        io_pml4,
    );
}

pub fn test_e810_driver() -> E810Result<()> {
    unsafe {
        attach_e810_iommu();
    }
    let bar0_phys: u64 = 0xFA00_0000;
    let bar0_size: usize = 0x0200_0000;

    let bar0 = unsafe { PciBarAddr::new(USERSPACE_BASE + bar0_phys, bar0_size) };
    let mut e810_dev = unsafe { E810Device::new(bar0) };

    log::info!("Initializing E810 driver (adminq bring-up + MAC read)...");

    e810_dev.dump_startup_regs()?;
    e810_dev.wait_for_device_active(1_000_000)?;

    let mut adminq = e810_dev.init_adminq(E810_PCI_DEV, 64)?;

    let mac = e810_dev.submit_manage_mac_read_once(&mut adminq)?;
    log::info!(
        "manage-mac-read returned MAC = {:02x}:{:02x}:{:02x}:{:02x}:{:02x}:{:02x}",
        mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]
    );

    Ok(())
}

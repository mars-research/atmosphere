// // dom0/src/e810_client.rs (no VFIO, no std)
// use crate::USERSPACE_BASE;
// use pcid::utils::PciBarAddr;
// use e810_driver::device::{E810Device, Result as E810Result};
// pub const E810_PCI_DEV: (usize, usize, usize) = (0x17, 0, 0);

// unsafe fn attach_e810_iommu() {
//     let io_pml4 = asys::sys_rd_io_cr3() as u64;
//     log::info!("E810 IOMMU root @ {:#x}", io_pml4);

//     // Attach 0000:17:00.0 to this IO page-table
//     asys::sys_set_device_iommu(
//         E810_PCI_DEV.0, // bus = 0x17
//         E810_PCI_DEV.1, // dev = 0
//         E810_PCI_DEV.2, // func = 0
//         io_pml4,
//     );
// }

// pub fn test_e810_driver() -> E810Result<()> {
//     unsafe {
//         attach_e810_iommu();
//     }

//     let mut e810_dev = unsafe { E810Device::new(PciBarAddr::new(USERSPACE_BASE + 0xFA00_0000, 0x0200_0000)) };

//     log::info!("Initializing E810 driver (adminq bring-up + MAC read)...");

//     e810_dev.dump_startup_regs()?;
//     e810_dev.wait_for_device_active(1_000_000)?;

//     let mut adminq = e810_dev.init_adminq(E810_PCI_DEV, 64)?;

//     let mac = e810_dev.submit_manage_mac_read_once(&mut adminq)?;
//     log::info!(
//         "manage-mac-read returned MAC = {:02x}:{:02x}:{:02x}:{:02x}:{:02x}:{:02x}",
//         mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]
//     );

//     Ok(())
// }


use crate::USERSPACE_BASE;
use e810_driver::device::{E810Device, Error as E810Error, PciBarAddr};

pub const E810_PCI_DEV: (usize, usize, usize) = (0x17, 0, 0);

unsafe fn attach_e810_iommu() {
    let io_pml4 = asys::sys_rd_io_cr3() as u64;
    log::info!("E810 IOMMU root @ {:#x}", io_pml4);
    asys::sys_set_device_iommu(E810_PCI_DEV.0, E810_PCI_DEV.1, E810_PCI_DEV.2, io_pml4);
}

pub fn test_e810_driver() -> Result<(), E810Error> {
    unsafe { attach_e810_iommu(); }
    let nic_base = 0xFA000000;
    let nic_size = 0x2000000;
    // BAR0 is already mapped by the VMM/atmo into USERSPACE_BASE.
    let bar0_base = (USERSPACE_BASE + nic_base) as usize;
    let bar0_size = nic_size as usize;
    log::info!(
        "E810 BAR0 userspace mapping: base={:#x} size={:#x}",
        bar0_base,
        bar0_size
    );
    let bar0 = unsafe { PciBarAddr::new(bar0_base, bar0_size) };

    // If you already carved out a DMA window with a known IOVA, pass it in:
    // let dma = unsafe { DmaMemory::from_raw_parts(dma_ptr, dma_iova, dma_len) };
    // let mut dev = unsafe { E810Device::with_dma(bar0, dma)? };

    // Otherwise, use the identity-mapped allocator (requires IOVA == VA for the NIC).
    let mut dev = unsafe {
        match E810Device::new(bar0) {
            Ok(dev) => {
                log::info!("E810Device::new succeeded");
                dev
            }
            Err(e) => {
                log::error!("E810Device::new failed: {:?}", e);
                return Err(e);
            }
        }
    };

    dev.dump_startup_regs()?;
    dev.wait_for_device_active(1_000_000)?;
    dev.disable_irq0()?;

    // Map DMA, program admin queues, and post RQ buffers before sending AQ commands.
    dev.init_adminq(E810_PCI_DEV)?;

    log::info!("Issuing adminq manage-mac-read");
    let mac = dev.read_mac().map_err(|e| {
        log::error!("manage-mac-read failed: {:?}", e);
        e
    })?;
    log::info!(
        "manage-mac-read returned MAC = {:02x}:{:02x}:{:02x}:{:02x}:{:02x}:{:02x}",
        mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]
    );

    Ok(())
}

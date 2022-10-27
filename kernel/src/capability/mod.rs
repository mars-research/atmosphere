//! Capabilities.

use crate::memory::RAM_REGIONS;
use libcap::CSpace;

/// Initializes capabilities.
///
/// This should be called only once.
pub unsafe fn init() {
    let (base, size) = {
        let ram_regions = RAM_REGIONS.lock();
        ram_regions[0]
    };

    log::info!("Bootstrapping initial CSpace at {:#x}", base);

    let cspace = CSpace::bootstrap_system(base as *const u8, size as usize).unwrap();
    log::debug!("Initial CSpace: {}", cspace);
}

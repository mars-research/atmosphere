//! Untyped memory.

use super::DowncastedCap;

/// A capability to an untyped memory region.
#[derive(Debug)]
pub struct UntypedCap {
    /// The base of the memory region.
    base: *const u8,

    /// The size of the memory region.
    size: usize,

    /// The watermark as an offset to base.
    ///
    /// Addresses before the watermark are already retyped, and addresses after
    /// the watermark are available.
    watermark: usize,
}

impl UntypedCap {
    pub unsafe fn new(base: *const u8, size: usize) -> Self {
        Self {
            base,
            size,
            watermark: 0,
        }
    }

    pub fn log_info(self: DowncastedCap<Self>) {
        log::info!("UntypedCap::log_info -> {}", self.watermark);
    }
}

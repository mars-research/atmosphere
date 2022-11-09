//! Logging facilities.
//!
//! The logger is available very early in boot, before allocators
//! are initialized. After the allocator is available, it's possible
//! to configure the logger to log to multiple targets, such as a
//! file in the Filesystem.

use kernel_logger::Logger;
use crate::boot;
use crate::console::{WriterType, get_writer};

/// The global logger.
static mut LOGGER: Logger<WriterType> = Logger::uninit();

/// Initializes the early-boot logger, crashing the kernel on failure.
///
/// This should only be called once.
pub unsafe fn early_init() {
    LOGGER.init(get_writer);
    log::set_logger(&LOGGER)
        .map(|_| log::set_max_level(log::LevelFilter::Trace))
        .unwrap();
}

pub unsafe fn init() {
    let cmdline = boot::get_command_line();
    LOGGER.set_colors(!cmdline.nocolor);
}

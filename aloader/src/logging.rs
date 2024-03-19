//! Logging facilities.

use crate::console::{get_writer, WriterType};
use kernel_logger::Logger;

/// The global logger.
static mut LOGGER: Logger<WriterType> = Logger::uninit();

/// Initializes the logger.
///
/// This should only be called once.
pub unsafe fn init() {
    LOGGER.init(get_writer);
    LOGGER.set_colors(false);
    log::set_logger(&LOGGER)
        .map(|_| log::set_max_level(log::LevelFilter::Info))
        .unwrap();
}

//! Logging facilities.
//!
//! The logger is available very early in boot, before allocators
//! are initialized. After the allocator is available, it's possible
//! to configure the logger to log to multiple targets, such as a
//! file in the Filesystem.

use core::fmt::Write;

use log::{Record, Level, Metadata};

use crate::boot;

/// The global logger.
static mut LOGGER: Logger = Logger {
    log_level: Level::Debug,
    use_colors: true,
};

/// Initializes the early-boot logger, crashing the kernel on failure.
///
/// This should only be called once.
pub unsafe fn early_init() {
    log::set_logger(&LOGGER)
        .map(|_| log::set_max_level(log::LevelFilter::Trace))
        .unwrap();
}

pub unsafe fn init() {
    let cmdline = boot::get_command_line();
    if cmdline.nocolor {
        LOGGER.use_colors = false;
    }
}

/// The default logger.
pub struct Logger {
    /// The maximum log level to emit.
    log_level: Level,

    /// Whether to enable colors or not.
    ///
    /// This can be disabled via the kernel command-line with `nocolors`.
    use_colors: bool,

    ///// Target prefixes to display debug messages for.
    /////
    ///// Targets in `log` are module paths like `atmosphere::interrupt`.
    //debug_targets: Option<Vec<String>>,
}

impl Logger {
    /// Returns the color prefix for a log level.
    fn get_color(level: Level) -> &'static str {
        match level {
            Level::Error => "\x1b[31m",
            Level::Warn => "\x1b[33m",
            Level::Info => "\x1b[34m",
            Level::Debug => "\x1b[36m",
            Level::Trace => "\x1b[35m",
        }
    }
}

impl log::Log for Logger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= self.log_level
    }

    fn log(&self, record: &Record) {
        if self.enabled(record.metadata()) {
            let mut writer = crate::console::get_writer();
            if self.use_colors {
                let color = Self::get_color(record.level());
                writeln!(writer, "{}{:>5} {}\x1b[0m", color, record.level(), record.args()).unwrap();
            } else {
                writeln!(writer, "{:>5} {}", record.level(), record.args()).unwrap();
            }
        }
    }

    fn flush(&self) {}
}

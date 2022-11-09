//! The kernel logger.
//!
//! Shared logger implementation for the microkernel and the
//! loader.

#![no_std]

use core::fmt::Write;

use log::{Level, Metadata, Record};

/// The default logger.
pub struct Logger<WR> {
    /// Function to call to acquire a writer.
    acquire_writer: Option<fn() -> WR>,

    /// The maximum log level to emit.
    log_level: Level,

    /// Whether to enable colors or not.
    ///
    /// This can be disabled via the kernel command-line with `nocolors`.
    use_colors: bool,
}

impl<WR, W> Logger<WR>
    where WR: core::ops::DerefMut<Target = W>,
          W: Write,
{
    /// Creates an uninitialized logger instance.
    pub const fn uninit() -> Self {
        Self {
            acquire_writer: None,
            log_level: Level::Trace,
            use_colors: true,
        }
    }

    /// Initializes the logger instance.
    pub fn init(&mut self, acquire_writer: fn() -> WR) {
        self.acquire_writer = Some(acquire_writer);
    }

    /// Sets whether to use colors.
    pub fn set_colors(&mut self, use_colors: bool) {
        self.use_colors = use_colors;
    }

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

impl<WR, W> log::Log for Logger<WR>
    where WR: core::ops::DerefMut<Target = W>,
          W: Write,
{
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= self.log_level
    }

    fn log(&self, record: &Record) {
        if self.enabled(record.metadata()) {
            let acquire_writer = self.acquire_writer.as_ref()
                .expect("Writer acquisition function wasn't set");
            let mut writer = acquire_writer();
            if self.use_colors {
                let color = Self::get_color(record.level());
                writeln!(
                    writer,
                    "{}{:>5} {}\x1b[0m",
                    color,
                    record.level(),
                    record.args()
                )
                .unwrap();
            } else {
                writeln!(writer, "{:>5} {}", record.level(), record.args()).unwrap();
            }
        }
    }

    fn flush(&self) {}
}

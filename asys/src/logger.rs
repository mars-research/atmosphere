use log::{Level, Metadata, Record};

use astd::io::Write;

static LOGGER: Logger = Logger;

pub fn init_logging() {
    init_logging_with_level(Level::Trace);
}

pub fn init_logging_with_level(level: Level) {
    log::set_logger(&LOGGER)
        .map(|_| log::set_max_level(level.to_level_filter()))
        .unwrap();
}

pub struct Logger;

impl log::Log for Logger {
    fn enabled(&self, _metadata: &Metadata) -> bool {
        // TODO
        true
    }

    fn log(&self, record: &Record) {
        // FIXME: Dynamically allocate
        let mut buffer: [u8; 4096] = [0u8; 4096];
        let mut writer = buffer.as_mut_slice();

        writer.write_fmt(*record.args()).unwrap();
        let remaining = writer.len();
        let written = buffer.len() - remaining;

        unsafe {
            crate::sys_log(buffer.as_ptr(), written, record.level());
        }
    }

    fn flush(&self) {}
}

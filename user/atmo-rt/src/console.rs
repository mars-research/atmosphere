//! The console.
//!
//! The kernel console is line oriented, so the runtime collects bytes into a
//! line and passes each complete line to the kernel.

use core::cell::UnsafeCell;
use core::fmt;

use crate::sys;

const LINE_MAX: usize = 256;

struct Line {
    buf: [u8; LINE_MAX],
    len: usize,
}

/// The process runs on one processor and the console is not entered from
/// interrupt context, so the line buffer needs no lock.
struct Shared(UnsafeCell<Line>);
unsafe impl Sync for Shared {}

static LINE: Shared = Shared(UnsafeCell::new(Line { buf: [0; LINE_MAX], len: 0 }));

/// Writes bytes to the console.
pub fn write(bytes: &[u8]) {
    let line = unsafe { &mut *LINE.0.get() };
    for &b in bytes {
        match b {
            b'\n' => {
                sys::console_line(&line.buf[..line.len]);
                line.len = 0;
            }
            b'\r' => {}
            _ => {
                if line.len == LINE_MAX {
                    sys::console_line(&line.buf[..line.len]);
                    line.len = 0;
                }
                // The kernel prints the line as a string.
                line.buf[line.len] = if b.is_ascii() && !b.is_ascii_control() || b == b'\t' { b } else { b'?' };
                line.len += 1;
            }
        }
    }
}

/// Writes out a partial line.
pub fn flush() {
    let line = unsafe { &mut *LINE.0.get() };
    if line.len != 0 {
        sys::console_line(&line.buf[..line.len]);
        line.len = 0;
    }
}

/// A `core::fmt` writer for the console.
pub struct Writer;

impl fmt::Write for Writer {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        write(s.as_bytes());
        Ok(())
    }
}

/// Writes `len` bytes at `data` to the console.
#[no_mangle]
pub unsafe extern "C" fn art_console_write(data: *const u8, len: usize) {
    if !data.is_null() && len != 0 {
        write(core::slice::from_raw_parts(data, len));
    }
}

/// Writes out a partial line.
#[no_mangle]
pub extern "C" fn art_console_flush() {
    flush();
}

/// Ends the program with an exit code.
#[no_mangle]
pub extern "C" fn art_exit(code: i32) -> ! {
    flush();
    sys::exit(code as u32)
}

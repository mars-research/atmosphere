//! Serial console.
//!
//! Outputs from the kernel and applications are typically
//! done through [`log`] macros so verbosity can be controlled
//! as needed. `print!` and `println!` are intentionally
//! omitted from the kernel.
//!
//! The serial port defaults to COM1 (0x3F8), and can be
//! configured through the kernel command line:
//!
//! `serial=[com1|com2|com3|com4]`

mod ns16550a;

use core::fmt::Write;

use astd::sync::{Mutex, MutexGuard};
use crate::boot::command_line;
use ns16550a::PioSerial;

/// The serial device.
static SERIAL: Mutex<PioSerial> = Mutex::new(unsafe { PioSerial::new(0x3f8) });

/// Returns a writer that implements `core::fmt::Write`.
pub fn get_writer() -> MutexGuard<'static, PioSerial> {
    SERIAL.lock()
}

/// Initializes the serial console.
pub unsafe fn init() {
    let mut serial = SERIAL.lock();
    let mut invalid_serial = false;

    if let Some(port) = command_line::get_first_value("serial") {
        *serial = PioSerial::new(match port {
            "" | "com1" => 0x3f8,
            "com2" => 0x2f8,
            "com3" => 0x3e8,
            "com4" => 0x2e8,
            _ => {
                invalid_serial = true;
                0x3f8
            }
        });
    }

    serial.init();
    if invalid_serial {
        log::error!("Invalid serial port specified - Valid values for `serial` are: com1, com2, com3, com4");
    }

    // Clear the screen and move the cursor to (0,0).
    //
    // In some terminals, [2J alone does not reset the cursor position.
    write!(serial, "\x1B[2J\x1B[0;0H").unwrap();
}

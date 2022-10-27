//! Kernel command line utilities.
//!
//! See the [KernelCommandLine] struct for a list of supported
//! options.

use core::ops::Deref;

use crate::error::{Error, Result};
use astd::sync::RwLock;

static COMMAND_LINE: RwLock<KernelCommandLine> = RwLock::new(KernelCommandLine::new());

/// The kernel command-line configuration.
pub struct KernelCommandLine {
    /// Disable the logo.
    pub nologo: bool,

    /// Disable colored serial output.
    pub nocolor: bool,

    /// Log to a specified serial port.
    pub serial: &'static str,

    /// Run a debug script.
    pub script: Option<&'static str>,

    /// Shut down after the script finishes.
    pub script_shutdown: bool,

    /// QEMU isa-debug-exit I/O port base.
    pub qemu_debug_exit_io_base: Option<u16>,

    /// Bochs APM I/O port base.
    pub bochs_apm_io_base: Option<u16>,
}

impl KernelCommandLine {
    const fn new() -> Self {
        Self {
            nologo: false,
            nocolor: false,
            serial: "com1",
            script: None,
            script_shutdown: false,
            qemu_debug_exit_io_base: None,
            bochs_apm_io_base: None,
        }
    }

    fn parse(&mut self, iter: Iterator<'static>) -> Result<()> {
        for component in iter {
            match component {
                Component::Flag(flag) => match flag {
                    "nologo" => {
                        self.nologo = true;
                    }
                    "nocolor" => {
                        self.nocolor = true;
                    }
                    "script_shutdown" => {
                        self.script_shutdown = true;
                    }
                    _ => {
                        return Err(Error::InvalidCommandLineOption(component));
                    }
                },
                Component::KeyValue((key, value)) => match key {
                    "serial" => {
                        self.serial = value;
                    }
                    "script" => {
                        self.script = Some(value);
                    }
                    "qemu_debug_exit_io_base" => {
                        self.qemu_debug_exit_io_base.replace(
                            value
                                .parse()
                                .map_err(|_| Error::InvalidCommandLineOption(component))?,
                        );
                    }
                    "bochs_apm_io_base" => {
                        self.bochs_apm_io_base.replace(
                            value
                                .parse()
                                .map_err(|_| Error::InvalidCommandLineOption(component))?,
                        );
                    }
                    _ => {
                        return Err(Error::InvalidCommandLineOption(component));
                    }
                },
            }
        }

        Ok(())
    }
}

/// A command line component.
#[derive(Clone, Debug)]
pub enum Component<'a> {
    /// A flag.
    ///
    /// Example: nocolor
    Flag(&'a str),

    /// A key-value pair.
    ///
    /// Example: script=vmx_test
    KeyValue((&'a str, &'a str)),
}

impl<'a> Component<'a> {
    fn from_str(s: &'a str) -> Self {
        match s.find('=') {
            Some(index) => Self::KeyValue((&s[0..index], &s[index + 1..])),
            None => Self::Flag(s),
        }
    }
}

struct Iterator<'a> {
    split: core::str::Split<'a, char>,
}

impl<'a> core::iter::Iterator for Iterator<'a> {
    type Item = Component<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut next_component = self.split.next();

        loop {
            match next_component {
                None => {
                    return None;
                }
                Some(s) => {
                    if s.is_empty() {
                        next_component = self.split.next();
                        continue;
                    }

                    return Some(Component::from_str(s));
                }
            }
        }
    }
}

impl<'a> Iterator<'a> {
    fn new(raw: &'a str) -> Self {
        Self {
            split: raw.split(' '),
        }
    }
}

/// Returns the kernel command-line.
pub fn get_command_line() -> impl Deref<Target = KernelCommandLine> {
    COMMAND_LINE.read()
}

/// Parses a raw kernel command line, replacing the current value.
pub(super) fn init(raw: &'static str) -> Result<()> {
    let iter = Iterator::new(raw);

    let mut cmdline = COMMAND_LINE.write();
    cmdline.parse(iter)
}

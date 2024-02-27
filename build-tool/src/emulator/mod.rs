//! Emulators/Virtualizers.

// pub mod bochs;
pub mod gdb;
mod output_filter;
pub mod qemu;

use std::str::FromStr;

use anyhow::anyhow;
use async_trait::async_trait;
use byte_unit::{Byte, ByteUnit};

use crate::error::{Error, Result};
use crate::project::Binary;
//pub use bochs::Bochs;
pub use gdb::{GdbConnectionInfo, GdbServer};
pub use qemu::Qemu;

#[async_trait]
pub trait Emulator {
    /// Start the emulator.
    async fn run(&mut self) -> Result<EmulatorExit>;

    /// Returns the GDB connection info for the instance.
    fn gdb_connection_info(&self) -> Option<GdbConnectionInfo> {
        None
    }
}

/// Run configuration.
pub struct RunConfiguration {
    /// The kernel image to use.
    kernel: Binary,

    /// The early loader to use.
    loader: Binary,

    /// The Dom0 image to use.
    dom0: Option<Binary>,

    /// Memory for the virtual machine.
    memory: Byte,

    /// Use hardware-accelerated virtualization.
    ///
    /// The behavior depends on the emulator in use. Currently we only
    /// support QEMU-KVM.
    use_virtualization: bool,

    /// The emulated CPU model.
    cpu_model: CpuModel,

    /// Atmosphere script to execute.
    ///
    /// This will be prepended to the kernel command-line.
    script: Option<String>,

    /// Extra kernel command line flags.
    command_line: String,

    /// Whether to automatically shutdown when a script finishes.
    auto_shutdown: bool,

    /// GDB server configrations.
    gdb_server: Option<GdbServer>,

    /// Whether to freeze on start-up to wait for the debugger.
    freeze_on_startup: bool,

    /// Whether to suppress inital outputs from the emulator.
    ///
    /// By default, we suppress initial outputs from the emulator (BIOS, GRUB,
    /// etc.) up until the point that our kernel is first launched. This is
    /// because the BIOS and bootloader emit control sequences that reset the
    /// terminal to values that make sense when they are output to a standalone
    /// terminal, but are frustrating when run as a normal CLI program.
    suppress_initial_outputs: bool,

    /// Whether to enable emulated nvme device for development purposes
    enable_nvme: bool,
}

impl RunConfiguration {
    pub fn new(kernel: Binary, loader: Binary) -> Self {
        Self {
            kernel,
            loader,
            dom0: None,
            memory: Byte::from_unit(8.0f64, ByteUnit::GiB).unwrap(),
            use_virtualization: false,
            cpu_model: CpuModel::Haswell,
            script: None,
            command_line: String::new(),
            auto_shutdown: true,
            gdb_server: None,
            freeze_on_startup: false,
            suppress_initial_outputs: true,
            enable_nvme: true,
        }
    }

    /// Set the Dom0 to run.
    pub fn dom0(&mut self, dom0: Binary) -> &mut Self {
        self.dom0 = Some(dom0);
        self
    }

    /// Set the script to run.
    pub fn script(&mut self, script: String) -> &mut Self {
        self.script = Some(script);
        self
    }

    /// Set the kernel command-line.
    pub fn command_line(&mut self, cmdline: String) -> &mut Self {
        self.command_line = cmdline;
        self
    }

    /// Set whether to use hardware virtualization.
    pub fn use_virtualization(&mut self, use_virtualization: bool) -> &mut Self {
        self.use_virtualization = use_virtualization;
        self
    }

    /// Set whether to use Qemu's Nvme emulation.
    pub fn enable_nvme(&mut self, enable_nvme: bool) -> &mut Self {
        self.enable_nvme = enable_nvme;
        self
    }

    /// Set the CPU model.
    pub fn cpu_model(&mut self, cpu_model: CpuModel) -> &mut Self {
        self.cpu_model = cpu_model;
        self
    }

    /// Set the auto shutdown config.
    pub fn auto_shutdown(&mut self, auto_shutdown: bool) -> &mut Self {
        self.auto_shutdown = auto_shutdown;
        self
    }

    /// Set the GDB server config.
    pub fn gdb_server(&mut self, gdb_server: GdbServer) -> &mut Self {
        self.gdb_server = Some(gdb_server);
        self
    }

    /// Set the freeze on startup config.
    pub fn freeze_on_startup(&mut self, freeze_on_startup: bool) -> &mut Self {
        self.freeze_on_startup = freeze_on_startup;
        self
    }

    /// Set the initial output suppression config.
    pub fn suppress_initial_outputs(&mut self, suppress_initial_outputs: bool) -> &mut Self {
        self.suppress_initial_outputs = suppress_initial_outputs;
        self
    }

    /// Returns the full kernel command line.
    fn full_command_line(&self) -> String {
        let mut cmdline = self.command_line.clone();

        if let Some(script) = &self.script {
            cmdline = format!("script={} {}", script, cmdline);
        }

        if self.auto_shutdown {
            cmdline += " script_shutdown";
        }

        if self.suppress_initial_outputs {
            cmdline += " nologo";
        }

        cmdline
    }
}

/// Model of an emulated CPU.
///
/// This is very simplistic and different emulators handle it
/// differently. For example, QEMU only has CPU types defined
/// for each generation, while Bochs has very specific built-in
/// types that aim to accurately reflect the CPUID.
#[non_exhaustive]
#[derive(Debug, Clone)]
pub enum CpuModel {
    /// Intel Haswell.
    Haswell,

    /// Use host CPU model.
    ///
    /// This is required for QEMU-KVM.
    Host,
}

impl FromStr for CpuModel {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        match s {
            "haswell" => Ok(Self::Haswell),
            "host" => Ok(Self::Host),
            _ => Err(anyhow!("Unknown CPU type \"{}\"", s)),
        }
    }
}

/// Reason for an emulator exit.
pub enum EmulatorExit {
    /// The emulator exited normally.
    Success,

    /// The emulator was killed by a signal.
    Killed,

    /// The emulator exited with a code.
    Code(i32),
}

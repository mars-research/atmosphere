//! Emulators/Virtualizers.

pub mod bochs;
pub mod qemu;

use std::str::FromStr;

use anyhow::anyhow;
use async_trait::async_trait;
use byte_unit::{Byte, ByteUnit};
use tokio::io::{self, AsyncWrite, AsyncWriteExt, AsyncBufRead, AsyncBufReadExt};

use crate::error::{Error, Result};
use crate::project::Binary;
pub use qemu::Qemu;
pub use bochs::Bochs;

#[async_trait]
pub trait Emulator {
    /// Start the emulator.
    async fn run(&mut self, config: &RunConfiguration, kernel: &Binary) -> Result<EmulatorExit>;
}

/// Run configuration.
pub struct RunConfiguration {
    /// Memory for the virtual machine.
    memory: Byte,

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

    /// Whether to suppress inital outputs from the emulator.
    ///
    /// By default, we suppress initial outputs from the emulator (BIOS, GRUB,
    /// etc.) up until the point that our kernel is first launched. This is
    /// because the BIOS and bootloader emit control sequences that reset the
    /// terminal to values that make sense when they are output to a standalone
    /// terminal, but are frustrating when run as a normal CLI program.
    suppress_initial_outputs: bool,
}

impl RunConfiguration {
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

impl Default for RunConfiguration {
    fn default() -> Self {
        Self {
            memory: Byte::from_unit(2.0f64, ByteUnit::GiB).unwrap(),
            cpu_model: CpuModel::Haswell,
            script: None,
            command_line: String::new(),
            auto_shutdown: true,
            suppress_initial_outputs: true,
        }
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

/// A filter that suppresses initial boot outputs from the emulator.
struct InitialOutputFilter<R, W> {
    reader: R,
    writer: W,
}

impl<R, W> InitialOutputFilter<R, W>
where
    R: AsyncBufRead + Unpin + Sized,
    W: AsyncWrite + Unpin + Sized,
{
    fn new(reader: R, writer: W) -> Self {
        Self {
            reader,
            writer,
        }
    }

    /// Feed ChildStdout to the writer, skipping initial emulator outputs.
    async fn pipe(mut self) -> Result<()> {
        self.writer.write_all(b"Booting: ").await?;

        let mut lines = self.reader.lines();
        while let Some(line) = lines.next_line().await? {
            if line.contains("SeaBIOS") {
                self.writer.write_all(b"SeaBIOS... ").await?;
            }
            if line.contains("Booting `") {
                self.writer.write_all(b"GRUB...\n").await?;
                break;
            }
        }

        let mut reader = lines.into_inner();
        io::copy(&mut reader, &mut self.writer).await?;

        Ok(())
    }
}

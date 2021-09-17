//! QEMU integration.

use std::ffi::OsString;
use std::path::PathBuf;
use std::process::Stdio;

use async_trait::async_trait;
use byte_unit::ByteUnit;
use tokio::io::{self, BufReader};
use tokio::process::Command;

use crate::grub::BootableImage;
use crate::project::{ProjectHandle, Binary};
use crate::error::Result;
use super::{CpuModel, Emulator, EmulatorExit, RunConfiguration, InitialOutputFilter};

/// A QEMU instance.
pub struct Qemu {
    /// The QEMU binary to use.
    qemu_binary: PathBuf,

    /// GDB server configuration.
    gdb_server: GdbServer,

    /// I/O port for the isa-debug-exit device.
    debug_exit_io_base: u16,
}

impl Qemu {
    /// Create a QEMU instance.
    pub fn new(_project: ProjectHandle) -> Self {
        Self {
            qemu_binary: PathBuf::from("qemu-system-x86_64"),
            gdb_server: GdbServer::disabled(),
            debug_exit_io_base: 0xf4,
        }
    }
}

#[async_trait]
impl Emulator for Qemu {
    /// Start the QEMU process.
    async fn run(&mut self, config: &RunConfiguration, kernel: &Binary) -> Result<EmulatorExit> {
        let memory = config.memory.get_adjusted_unit(ByteUnit::MiB)
            .get_value() as usize;

        let command_line = config.full_command_line()
            + &format!(" qemu_debug_exit_io_base={}", self.debug_exit_io_base);

        // FIXME: Make this cachable
        let grub = BootableImage::generate(command_line, None).await?;
        let hda = format!(
            "file={},format=raw,index=0,media=disk",
            grub.iso_path().to_str().expect("Path contains non-UTF-8")
        );
        let hdb = format!(
            "file=fat:rw:{},format=raw,index=1,media=disk",
            kernel.path().parent().unwrap().to_str().expect("Path contains non-UTF-8"),
        );

        let mut command = Command::new(self.qemu_binary.as_os_str());
        command
            .arg("-enable-kvm")
            .arg("-nographic")
            .args(&["-serial", "mon:stdio"])
            // .args(&["-serial", "file:serial.log"])
            .args(&["-m", &format!("{}", memory)])
            .arg("-drive").arg(&hda)
            .arg("-drive").arg(&hdb)
            .args(&["-device", &format!("isa-debug-exit,iobase={:#x},iosize=0x04", self.debug_exit_io_base)])
            .args(config.cpu_model.to_qemu()?)
            .args(self.gdb_server.to_qemu());

        if config.suppress_initial_outputs {
            command.stdout(Stdio::piped());
        }

        if !config.auto_shutdown {
            command.arg("-no-shutdown");
        }

        log::debug!("Starting QEMU with {:?}", command);

        let mut child = command.spawn()?;

        if config.suppress_initial_outputs {
            let stdout = {
                let reader = child.stdout.take().expect("Could not capture emulator stdout");
                BufReader::new(reader)
            };

            let filter = InitialOutputFilter::new(stdout, io::stdout());
            filter.pipe().await?;
        }

        let status = child.wait_with_output().await?.status;

        if !status.success() {
            if let Some(code) = status.code() {
                log::error!("QEMU exited with code {}", code);
                Ok(EmulatorExit::Code(code))
            } else {
                log::error!("QEMU was killed by a signal");
                Ok(EmulatorExit::Killed)
            }
        } else {
            Ok(EmulatorExit::Success)
        }
    }
}

trait QemuArgs {
    fn to_qemu(&self) -> Result<Vec<OsString>>;
}

impl QemuArgs for CpuModel {
    fn to_qemu(&self) -> Result<Vec<OsString>> {
        let mut result = vec![];

        result.push("-cpu".to_string().into());

        match self {
            Self::Host => result.push("host".to_string().into()),
            Self::Haswell => result.push("Haswell-IBRS".to_string().into()),
        }

        Ok(result)
    }
}

pub struct GdbServer {
    /// Whether to enable GDB server.
    enable: bool,

    /// Whether to freeze execution at startup.
    freeze_execution: bool,

    /// Path to the Unix socket.
    ///
    /// If none, the default `tcp::1234` will be used.
    ///
    /// TODO: Support other setups.
    socket_path: Option<PathBuf>,
}

impl GdbServer {
    pub fn disabled() -> Self {
        Self {
            enable: false,
            freeze_execution: false,
            socket_path: None,
        }
    }

    /// Returns QEMU arguments.
    pub fn to_qemu(&self) -> Vec<OsString> {
        let mut result = vec![];

        if !self.enable {
            return result;
        }

        if self.freeze_execution {
            result.push("-S".to_string().into());
        }

        if self.enable {
            result.push("-gdb".to_string().into());

            if let Some(socket_path) = &self.socket_path {
                result.push(socket_path.as_os_str().to_owned());
            } else {
                result.push("tcp::1234".to_string().into());
            }
        }

        result
    }
}

//! QEMU integration.

use std::ffi::OsString;
use std::path::PathBuf;
use std::process::Stdio;

use async_trait::async_trait;
use byte_unit::ByteUnit;
use tokio::io::{self, BufReader};
use tokio::process::Command;

use super::output_filter::InitialOutputFilter;
use super::{
    CpuModel, Emulator, EmulatorExit, GdbServer, RunConfiguration, /*InitialOutputFilter*/
};
use crate::error::Result;
use crate::grub::BootableImage;
use crate::project::{Binary, ProjectHandle};

/// A QEMU instance.
pub struct Qemu {
    /// The QEMU binary to use.
    qemu_binary: PathBuf,

    /// I/O port for the isa-debug-exit device.
    debug_exit_io_base: u16,
}

impl Qemu {
    /// Create a QEMU instance.
    pub fn new(_project: ProjectHandle) -> Self {
        Self {
            qemu_binary: PathBuf::from("qemu-system-x86_64"),
            debug_exit_io_base: 0xf4,
        }
    }
}

#[async_trait]
impl Emulator for Qemu {
    /// Start the QEMU process.
    async fn run(&mut self, config: &RunConfiguration, kernel: &Binary) -> Result<EmulatorExit> {
        let memory = config.memory.get_adjusted_unit(ByteUnit::MiB).get_value() as usize;

        let command_line = config.full_command_line()
            + &format!(" qemu_debug_exit_io_base={}", self.debug_exit_io_base);

        // FIXME: Make this cachable
        let grub = BootableImage::generate(command_line, Some(kernel)).await?;
        let hda = format!(
            "file={},format=raw,index=0,media=disk",
            grub.iso_path().to_str().expect("Path contains non-UTF-8")
        );
        /*
        let hdb = format!(
            "file=fat:rw:{},format=raw,index=1,media=disk",
            kernel.path().parent().unwrap().to_str().expect("Path contains non-UTF-8"),
        );
        */

        let mut command = Command::new(self.qemu_binary.as_os_str());
        command
            .arg("-nographic")
            .args(&["-serial", "mon:stdio"])
            // .args(&["-serial", "file:serial.log"])
            .args(&["-m", &format!("{}", memory)])
            .arg("-drive")
            .arg(&hda)
            // .arg("-drive").arg(&hdb)
            .args(&[
                "-device",
                &format!(
                    "isa-debug-exit,iobase={:#x},iosize=0x04",
                    self.debug_exit_io_base
                ),
            ])
            .args(config.cpu_model.to_qemu()?);

        if config.use_virtualization {
            command.arg("-enable-kvm");
        }

        if config.suppress_initial_outputs {
            command.stdout(Stdio::piped());
        }

        if !config.auto_shutdown {
            command.arg("-no-shutdown");
        }

        if config.freeze_on_startup {
            command.arg("-S");
        }

        if let Some(server) = &config.gdb_server {
            command.args(server.to_qemu()?);
        }

        log::warn!("Starting QEMU with {:?}", command);

        let mut child = command.spawn()?;

        if config.suppress_initial_outputs {
            let stdout = {
                let reader = child
                    .stdout
                    .take()
                    .expect("Could not capture emulator stdout");
                BufReader::new(reader)
            };

            let mut filter = InitialOutputFilter::new(stdout);
            tokio::io::copy(&mut filter, &mut io::stdout()).await?;
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

impl QemuArgs for GdbServer {
    fn to_qemu(&self) -> Result<Vec<OsString>> {
        let mut result: Vec<OsString> = vec!["-gdb".to_string().into()];

        match self {
            GdbServer::Unix(path) => {
                let path = path
                    .to_str()
                    .expect("Socket path contains non-UTF-8 characters");
                result.push(format!("unix:{},server,nowait", path).into());
            }
            GdbServer::Tcp(port) => {
                result.push(format!("tcp::{}", port).into());
            }
        }

        Ok(result)
    }
}

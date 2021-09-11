//! QEMU launcher.

use std::path::PathBuf;
use std::ffi::OsString;

use byte_unit::{Byte, ByteUnit};
use tokio::process::Command;

use crate::grub::BootableImage;
use crate::project::{ProjectHandle, Binary};
use crate::error::Result;

/// A QEMU instance.
pub struct Qemu {
    /// Handle to the project.
    _project: ProjectHandle,

    /// The amount of RAM.
    memory: Byte,

    /*
    /// The bootable disk containing GRUB.
    grub_image: Option<BootableImage>,
    */

    /// Which QEMU binary to use.
    qemu_binary: PathBuf,

    /// The CPU model.
    cpu_model: CpuModel,

    /// GDB server configuration.
    gdb_server: GdbServer,

    /// I/O port for the isa-debug-exit device.
    debug_exit_io_base: u16,

    /// Whether to pass `-no-shutdown` to QEMU.
    ///
    /// This will also tell Atmosphere not to shutdown when
    /// the specified script finishes.
    no_shutdown: bool,

    /// Atmosphere script to execute.
    ///
    /// This will be prepended to the kernel command-line.
    script: Option<String>,

    /// Kernel command-line.
    command_line: String,
}

impl Qemu {
    /// Creates a QEMU instance.
    pub fn new(project: ProjectHandle) -> Self {
        Self {
            _project: project,
            memory: Byte::from_unit(8.0f64, ByteUnit::GiB).unwrap(),
            cpu_model: CpuModel::Host,
            // grub_image: None,
            qemu_binary: PathBuf::from("qemu-system-x86_64"),
            gdb_server: GdbServer::disabled(),
            debug_exit_io_base: 0xf4,
            no_shutdown: false,
            script: None,
            command_line: String::new(),
        }
    }

    /// Set the script to run.
    pub fn set_script(&mut self, script: String) {
        self.script = Some(script);
    }

    /// Set the kernelt command-line.
    pub fn set_command_line(&mut self, cmdline: String) {
        self.command_line = cmdline;
    }

    /// Set the -no-shutdown flag.
    pub fn set_no_shutdown(&mut self, val: bool) {
        self.no_shutdown = val;
    }

    /// Start the QEMU process.
    pub async fn run(&self, kernel: &Binary) -> Result<QemuExit> {
        let memory = self.memory.get_adjusted_unit(ByteUnit::MiB)
            .get_value() as usize;

        let command_line = {
            let mut s = self.command_line.clone();

            if let Some(script) = &self.script {
                s = format!("script={} {}", script, s);
            }

            if !self.no_shutdown {
                s += " script_shutdown";
            }

            s += &format!(" qemu_debug_exit_io_base={}", self.debug_exit_io_base);

            s
        };

        // FIXME: Make this cachable
        let grub = BootableImage::generate(command_line).await?;
        let hdb = format!(
            "fat:rw:{}",
            kernel.path().parent().unwrap().to_str().expect("Path contains non-UTF-8"),
        );

        let mut command = Command::new(self.qemu_binary.as_os_str());
        command
            .arg("-enable-kvm")
            .arg("-nographic")
            .args(&["-serial", "mon:stdio"])
            .args(&["-m", &format!("{}", memory)])
            .arg("-hda").arg(grub.iso_path())
            .arg("-hdb").arg(hdb)
            .args(&["-device", &format!("isa-debug-exit,iobase={:#x},iosize=0x04", self.debug_exit_io_base)])
            .args(self.cpu_model.to_qemu())
            .args(self.gdb_server.to_qemu());

        if self.no_shutdown {
            command.arg("-no-shutdown");
        }

        log::debug!("Starting QEMU with {:?}", command);

        let status = command.status().await?;

        if !status.success() {
            if let Some(code) = status.code() {
                log::error!("QEMU exited with code {}", code);
                Ok(QemuExit::Code(code))
            } else {
                log::error!("QEMU was killed by a signal");
                Ok(QemuExit::Killed)
            }
        } else {
            Ok(QemuExit::Success)
        }
    }
}

/// How QEMU has exited.
pub enum QemuExit {
    Success,
    Killed,
    Code(i32),
}

/// CPU model.
pub enum CpuModel {
    /// Host passthrough.
    Host,

    /// Freeform string for `-cpu`.
    #[allow(dead_code)]
    Freeform(String),
}

impl CpuModel {
    /// Returns QEMU arguments.
    pub fn to_qemu(&self) -> Vec<OsString> {
        let mut result = vec![];

        result.push("-cpu".to_string().into());

        match self {
            Self::Host => result.push("host".to_string().into()),
            Self::Freeform(s) => result.push(s.into()),
        }

        result
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

#[cfg(test)]
mod tests {
    use super::*;

    fn join_args(args: Vec<OsString>) -> String {
        args.iter().map(|os| os.to_str().unwrap())
            .collect::<Vec<&str>>().join(" ")
    }

    #[test]
    fn test_cpu_model() {
        let host_cpu = CpuModel::Host;
        assert_eq!("-cpu host", join_args(host_cpu.to_qemu()));

        let freeform = CpuModel::Freeform("Nehalem-v2".to_string());
        assert_eq!("-cpu Nehalem-v2", join_args(freeform.to_qemu()));
    }
}

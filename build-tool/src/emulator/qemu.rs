//! QEMU integration.

use std::ffi::OsString;
use std::fs::OpenOptions as SyncOpenOptions;
use std::path::PathBuf;
use std::process::Stdio;

use async_trait::async_trait;
use byte_unit::ByteUnit;
use tempfile::{Builder as TempfileBuilder, NamedTempFile, TempPath};
use tokio::io::{self, BufReader};
use tokio::process::Command;

use super::output_filter::InitialOutputFilter;
use super::{CpuModel, Emulator, EmulatorExit, GdbConnectionInfo, GdbServer, RunConfiguration};
use crate::error::Result;
use crate::grub::BootableImage;
use crate::project::{Binary, ProjectHandle};

/// A QEMU instance.
pub struct Qemu {
    /// The QEMU binary to use.
    qemu_binary: PathBuf,

    /// The run configuration.
    config: RunConfiguration,

    /// I/O port for the isa-debug-exit device.
    debug_exit_io_base: u16,
}

impl Qemu {
    /// Create a QEMU instance.
    pub fn new(_project: ProjectHandle, config: RunConfiguration) -> Self {
        Self {
            qemu_binary: PathBuf::from("qemu-system-x86_64"),
            config,
            debug_exit_io_base: 0xf4,
        }
    }
}

#[async_trait]
impl Emulator for Qemu {
    /// Start the QEMU process.
    async fn run(&mut self) -> Result<EmulatorExit> {
        let config = &self.config;
        let memory = config.memory.get_adjusted_unit(ByteUnit::MiB).get_value() as usize;

        let command_line = config.full_command_line()
            + &format!(" qemu_debug_exit_io_base={}", self.debug_exit_io_base);
        let suppress_initial_outputs = config.suppress_initial_outputs; // FIXME

        let mut command = Command::new("sudo");
        command.arg(self.qemu_binary.as_os_str());

        let mut initrd = JumboBinary::new()?;
        initrd.push(&config.kernel)?;

        if let Some(dom0) = &config.dom0 {
            initrd.push(dom0)?;
        }

        if let Some(payload) = &config.payload {
            initrd.push(payload)?;
        }

        let initrd = initrd.finalize();

        let iso = if config.use_grub {
            let iso = BootableImage::generate(command_line, Some(&config.loader), Some(&initrd)).await?;
            command.arg("-hda");
            command.arg(iso.iso_path());
            Some(iso)
        } else {
            command.args(&[
                "-kernel",
                config
                    .loader
                    .path()
                    .to_str()
                    .expect("Early loader path contains non-UTF-8"),
            ]);
            command.args(&[
                "-initrd",
                initrd
                    .as_os_str()
                    .to_str()
                    .expect("Kernel path contains non-UTF-8"),
            ]);
            None
        };

        command
            .arg("-nographic")
            .args(&["-serial", "chardev:char0"])
            .args(&["-mon", "chardev=char0"])
            .args(&[
                "-chardev",
                "stdio,id=char0,mux=on,logfile=serial.log,signal=off",
            ])
            .args(&["-smp", "2"])
            .args(&["-m", &format!("{}", memory)])
            .args(&[
                "-device",
                &format!(
                    "isa-debug-exit,iobase={:#x},iosize=0x04",
                    self.debug_exit_io_base
                ),
            ])
            .arg("-no-reboot")
            .arg("-no-shutdown")
            //.args(&["-d", "int"])
            .args(&["-machine", "q35,kernel_irqchip=split"])
            .args(config.cpu_model.to_qemu()?);

        if let Some(img_path) = &config.nvme_img {
            command.args(&["-drive", &format!("file={},if=none,id=nvm", img_path)]);
            command.args(&["-device", "nvme,id=nvm,serial=deadbeef,drive=nvm"]);
        }

        if config.use_iommu {
            // The intel-iommu device must come before vfio-pci, otherwise
            // shadow IOMMU tables won't be configured correctly
            command.args(&["-device", "intel-iommu,intremap=on,aw-bits=48,caching-mode=on"]); // FIXME: AMD

            command.args(&["--trace", "vfio_*"]);
            command.args(&["--trace", "vtd_*"]);
            command.args(&["--trace", "iommufd_*"]);
            command.args(&["-D", "/tmp/qemu-log.txt"]);
        }

        if !config.pci_dev.is_empty() {
            for dev in &config.pci_dev {
                //command.args(&["-object", "iommufd,id=iommufd0"]);
                command.args(&["-device", &format!("vfio-pci,host={}", dev)]);
                //command.args(&["-device", &format!("vfio-pci,host={},iommufd=iommufd0", dev)]);
                //command.args(&["-device", &format!("vfio-pci,fd=23,iommufd=iommufd0")]);
            }
        }

        if config.use_virtualization {
            command.arg("-enable-kvm");
        }

        if suppress_initial_outputs {
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

        log::error!("Starting QEMU with {:?}", command);

        let mut child = command.spawn()?;

        if suppress_initial_outputs {
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
        drop(iso);

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

    /// Returns the GDB connection info for the instance.
    fn gdb_connection_info(&self) -> Option<GdbConnectionInfo> {
        let gdb_server = self.config.gdb_server.as_ref()?;
        let mut gdb_info = GdbConnectionInfo::new(
            self.config.loader.path().to_owned(),
            gdb_server.to_owned(),
        );

        gdb_info.add_binary("kernel".to_string(), self.config.kernel.path().to_owned());

        if let Some(dom0) = &self.config.dom0 {
            gdb_info.add_binary("dom0".to_string(), dom0.path().to_owned());
        }

        Some(gdb_info)
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

/// A set of binaries.
///
/// Right now it's just a simple concatenantion of them, but
/// in the future it will be more structured.
struct JumboBinary(NamedTempFile);

impl JumboBinary {
    fn new() -> Result<Self> {
        let tmp = TempfileBuilder::new().prefix("atmo-jumbo-").tempfile()?;

        Ok(Self(tmp))
    }

    fn push(&mut self, binary: &Binary) -> Result<()> {
        let mut f = SyncOpenOptions::new()
            .read(true)
            .write(false)
            .open(binary.path())?;

        std::io::copy(&mut f, &mut self.0)?;

        Ok(())
    }

    fn finalize(self) -> TempPath {
        self.0.into_temp_path()
    }
}

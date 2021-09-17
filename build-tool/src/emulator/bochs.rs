//! Bochs integration.
//!
//! We use Bochs because of its VT-x emulation capability, which
//! actually provides meaningful error outputs for VM errors.

use std::io::Write;
use std::path::PathBuf;

use anyhow::anyhow;
use async_trait::async_trait;
use byte_unit::ByteUnit;
use tempfile::NamedTempFile;
use tokio::process::Command;

use crate::error::Result;
use crate::grub::BootableImage;
use crate::project::{ProjectHandle, Binary};
use super::{CpuModel, Emulator, EmulatorExit, RunConfiguration};

/// A Bochs instance.
#[allow(dead_code)]
pub struct Bochs {
    /// Which Bochs binary to use.
    bochs_binary: PathBuf,

    /// Bochs APM IO port.
    apm_io_base: u16,
}

impl Bochs {
    /// Create a new Bochs instance.
    pub fn new(_project: ProjectHandle) -> Self {
        Self {
            bochs_binary: PathBuf::from("bochs"),
            apm_io_base: 0x8900,
        }
    }
}

#[async_trait]
impl Emulator for Bochs {
    /// Start the Bochs process.
    async fn run(&mut self, config: &RunConfiguration, kernel: &Binary) -> Result<EmulatorExit> {
        let memory = config.memory.get_adjusted_unit(ByteUnit::MiB)
            .get_value() as usize;

        if memory > 2048 {
            return Err(anyhow!("Memory > 2 GiB is not supported by Bochs"));
        }

        let command_line = config.full_command_line()
            + &format!(" bochs_apm_io_base={}", self.apm_io_base);

        // FIXME: Make this cachable
        let grub = BootableImage::generate(command_line, Some(kernel)).await?;

        let bochsrc = {
            let mut f = NamedTempFile::new()?;

            let boshsrc = format!(r#"
                log: -
                logprefix: %t%e%d
                debugger_log: -
                print_timestamps: enabled=0
                debug: action=ignore
                info: action=ignore
                error: action=report
                panic: action=ask

                display_library: nogui

                boot: cdrom
                memory: host={memory}, guest={memory}

                cpu: count=1:1:1, ips=4000000, quantum=16, model={cpu_model}, reset_on_triple_fault=1, cpuid_limit_winnt=0, ignore_bad_msrs=1
                pci: enabled=1, chipset=i440fx
                vga: extension=vbe, update_freq=5, realtime=1
                magic_break: enabled=0
                port_e9_hack: enabled=0
                private_colormap: enabled=0
                clock: sync=none, time0=local, rtc_sync=0

                ata0: enabled=true, ioaddr1=0x1f0, ioaddr2=0x3f0, irq=14
                ata0-master: type=cdrom, path="{iso_path}", status=inserted, model="Generic 1234", biosdetect=auto
                ata0-slave: type=none

                keyboard: type=mf, serial_delay=250, paste_delay=100000, user_shortcut=none
                mouse: type=ps2, enabled=false, toggle=ctrl+mbutton

                sound: waveoutdrv=dummy, waveout=none, waveindrv=dummy, wavein=none, midioutdrv=dummy, midiout=none

                com1: enabled=true, mode=file, dev=/dev/stdout
            "#,
                memory = memory,
                cpu_model = bochs_cpu_model(&config.cpu_model)?,
                iso_path = grub.iso_path().to_str().expect("Path contains non-UTF-8"),
            );

            f.write_all(boshsrc.as_bytes())?;
            f.flush()?;
            f.into_temp_path()
        };

        let debugrc = {
            let mut f = NamedTempFile::new()?;

            let debugrc = "continue\n";

            f.write_all(debugrc.as_bytes())?;
            f.flush()?;
            f.into_temp_path()
        };

        let mut command = Command::new(self.bochs_binary.as_os_str());
        command
            .arg("-f").arg(bochsrc.as_os_str())
            .arg("-rc").arg(debugrc.as_os_str())
            .arg("-q");

        let child = command.spawn()?;

        let status = child.wait_with_output().await?.status;

        if !status.success() {
            if let Some(code) = status.code() {
                log::error!("Bochs exited with code {}", code);
                Ok(EmulatorExit::Code(code))
            } else {
                log::error!("Bochs was killed by a signal");
                Ok(EmulatorExit::Killed)
            }
        } else {
            Ok(EmulatorExit::Success)
        }
    }
}

fn bochs_cpu_model(cpu_model: &CpuModel) -> Result<String> {
    match cpu_model {
        CpuModel::Haswell => Ok("corei7_haswell_4770".to_string()),
        CpuModel::Host => Err(anyhow!("Bochs does not support host passthrough configuration")),
    }
}

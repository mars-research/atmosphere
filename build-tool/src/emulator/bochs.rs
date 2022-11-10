//! Bochs integration.
//!
//! We use Bochs because of its VT-x emulation capability, which
//! actually provides meaningful error outputs for VM errors.

use std::collections::VecDeque;
use std::io::{Result as IoResult, Write};
use std::path::PathBuf;
use std::pin::Pin;
use std::process::Stdio;
use std::task::{Context, Poll};

use anyhow::anyhow;
use async_trait::async_trait;
use byte_unit::ByteUnit;
use tempfile::NamedTempFile;
use tokio::io::{self, AsyncBufRead, AsyncRead, BufReader, ReadBuf};
use tokio::process::Command;

use super::output_filter::InitialOutputFilter;
use super::{CpuModel, Emulator, EmulatorExit, GdbServer, RunConfiguration};
use crate::error::Result;
use crate::grub::BootableImage;
use crate::project::{Binary, ProjectHandle};

/// A Bochs instance.
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
        let memory = config.memory.get_adjusted_unit(ByteUnit::MiB).get_value() as usize;

        if memory > 2048 {
            return Err(anyhow!("Memory > 2 GiB is not supported by Bochs"));
        }

        if config.early_loader.is_some() {
            return Err(anyhow!("The early loader is not yet supported by Bochs"));
        }

        let command_line =
            config.full_command_line() + &format!(" bochs_apm_io_base={}", self.apm_io_base);

        // FIXME: Make this cachable
        let grub = BootableImage::generate(command_line, Some(kernel)).await?;

        let bochsrc = {
            let mut f = NamedTempFile::new()?;

            let gdbstub = match &config.gdb_server {
                // If gdbstub support is not enabled in Bochs, the gdbstub config must not appear
                // at all (even enabled=0 will cause an error)
                None => String::new(),
                Some(GdbServer::Tcp(port)) => format!(
                    "gdbstub: enabled=1, port={}, text_base=0, data_base=0, bss_base=0",
                    port
                ),
                Some(unsupported) => {
                    return Err(anyhow!(
                        "GDB server {:?} is not supported by Bochs",
                        unsupported
                    ));
                }
            };

            let boshsrc = format!(
                r#"
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
                magic_break: enabled=1
                {gdbstub}
            "#,
                memory = memory,
                cpu_model = bochs_cpu_model(&config.cpu_model)?,
                iso_path = grub.iso_path().to_str().expect("Path contains non-UTF-8"),
                gdbstub = gdbstub,
            );

            f.write_all(boshsrc.as_bytes())?;
            f.flush()?;
            f.into_temp_path()
        };

        let nofreeze_debugrc = {
            let mut f = NamedTempFile::new()?;

            let debugrc = "continue\n";

            f.write_all(debugrc.as_bytes())?;
            f.flush()?;
            f.into_temp_path()
        };

        let mut command = Command::new(self.bochs_binary.as_os_str());
        command
            .arg("-f")
            .arg(bochsrc.as_os_str())
            .arg("-q")
            .stdout(Stdio::piped());

        if !config.freeze_on_startup {
            command.arg("-rc").arg(nofreeze_debugrc.as_os_str());
        }

        let mut child = command.spawn()?;

        let mut stdout: Box<dyn AsyncBufRead + Unpin + Send> = {
            let reader = child
                .stdout
                .take()
                .expect("Could not capture emulator stdout");
            Box::new(BufReader::new(reader))
        };

        if config.suppress_initial_outputs {
            let filter = InitialOutputFilter::new(stdout);
            stdout = Box::new(BufReader::new(filter));
        }

        let mut stdout = BochsOutputFilter::new(stdout);

        tokio::io::copy(&mut stdout, &mut io::stdout()).await?;

        let status = child.wait_with_output().await?.status;

        if !status.success() {
            if stdout.has_success_marker() {
                Ok(EmulatorExit::Success)
            } else if let Some(code) = status.code() {
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
        CpuModel::Host => Err(anyhow!(
            "Bochs does not support host passthrough configuration"
        )),
    }
}

/// A filter that catches the success marker printed by the kernel.
///
/// Bochs doesn't provide an easy way to terminate the emulator
/// with a zero exit code but we need it for our CI pipeline.
///
/// To work around this, when Atmosphere is shutting down with
/// `success == true` using Bochs APM, the kernel will print out
/// `BOCHS_SUCCESS`. We then catch this output and exit with 0.
struct BochsOutputFilter<R>
where
    R: AsyncRead + Unpin + Sized,
{
    reader: Pin<Box<R>>,
    buffer: VecDeque<u8>,
}

impl<R> AsyncRead for BochsOutputFilter<R>
where
    R: AsyncRead + Unpin + Sized,
{
    fn poll_read(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &mut ReadBuf<'_>,
    ) -> Poll<IoResult<()>> {
        let old_index = buf.filled().len();

        match self.reader.as_mut().poll_read(cx, buf) {
            Poll::Pending => Poll::Pending,
            Poll::Ready(Err(e)) => Poll::Ready(Err(e)),
            Poll::Ready(Ok(())) => {
                let new = &buf.filled()[old_index..];
                let ring_remaining = self.buffer.capacity() - self.buffer.len();

                if new.len() > ring_remaining {
                    let drain = new.len() - ring_remaining;
                    for _ in 0..drain {
                        self.buffer.pop_front();
                    }
                }

                self.buffer.extend(new);

                Poll::Ready(Ok(()))
            }
        }
    }
}

impl<R> BochsOutputFilter<R>
where
    R: AsyncRead + Unpin + Sized,
{
    fn new(reader: R) -> Pin<Box<Self>> {
        Box::pin(Self {
            reader: Box::pin(reader),
            buffer: VecDeque::with_capacity(1024),
        })
    }

    fn has_success_marker(&mut self) -> bool {
        let s = String::from_utf8_lossy(self.buffer.make_contiguous());
        s.contains("BOCHS_SUCCESS")
    }
}

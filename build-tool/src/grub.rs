//! GRUB bootable image generation.
//!
//! We use `grub-mkrescue` to generate a tiny bootable ISO
//! that boots GRUB with a config file that loads Atmosphere
//! from the first hard drive. We don't put the actual
//! kernel in the image since generating the image may
//! be slow with large files.
//!
//! To build the X86 GRUB ISO on other platforms, we pass
//! to `grub-mkrescue` the modules path containing X86 GRUB
//! modules. This path is obtained from the `GRUB_X86_MODULES`
//! environment variable.

use std::convert::AsRef;
use std::env;
use std::path::{Path, PathBuf};
use std::process::Stdio;

use anyhow::{anyhow, Context};
use tempfile::TempDir;
use tokio::fs::{self, OpenOptions};
use tokio::io::AsyncWriteExt;
use tokio::process::Command;

use crate::error::Result;
use crate::project::Binary;

/// A bootable ISO image.
pub struct BootableImage {
    /// The temporary directory that will hold all the files.
    _temp_dir: TempDir,

    /// Path to the generated ISO.
    iso_path: PathBuf,
}

impl BootableImage {
    /// Create a bootable image.
    pub async fn generate<S: AsRef<str>>(command_line: S, kernel: Option<&Binary>) -> Result<Self> {
        let temp_dir = TempDir::new()?;

        let source_dir = temp_dir.path().join("grub");
        let iso_path = temp_dir.path().join("boot.iso");

        let mut grub_cfg = {
            let path = source_dir.join("boot/grub/grub.cfg");
            fs::create_dir_all(path.parent().unwrap()).await?;

            OpenOptions::new()
                .read(false)
                .write(true)
                .create(true)
                .truncate(true) // though there should not be an existing file
                .open(path)
                .await?
        };

        let config = generate_grub_config(command_line.as_ref(), kernel.is_some());
        grub_cfg.write_all(config.as_bytes()).await?;

        if let Some(kernel) = kernel {
            verify_multiboot2(kernel.path()).await?;
            let kernel_path = source_dir.join("boot/atmosphere");
            fs::copy(kernel.path(), kernel_path).await?;
        }

        let mut command = Command::new("grub-mkrescue");
        command
            .arg("-o")
            .arg(iso_path.as_os_str())
            .arg(source_dir.as_os_str())
            .stderr(Stdio::piped());

        if let Ok(modules_path) = env::var("GRUB_X86_MODULES") {
            command.args(&["-d", &modules_path]);
        }

        // actually generate the image
        let output = command.output().await?;

        if output.status.success() {
            Ok(Self {
                iso_path,
                _temp_dir: temp_dir,
            })
        } else {
            let exit_code = output.status.code().expect("There is no exit code");
            Err(anyhow!(
                "Failed to generate GRUB image (exit code {:?}): {}",
                exit_code,
                String::from_utf8_lossy(&output.stderr),
            ))
        }
    }

    /// Returns the path to the ISO.
    pub fn iso_path(&self) -> &Path {
        &self.iso_path
    }
}

fn generate_grub_config(command_line: &str, embedded: bool) -> String {
    let root = if embedded { "/boot" } else { "(hd1,msdos1)" };

    format!(
        r#"
serial --unit=0 --speed=115200 --word=8 --parity=no --stop=1
terminal_input --append serial
terminal_output --append serial

set timeout=0
set default=0

menuentry "Atmosphere" {{
    multiboot2 {}/atmosphere {}
    boot
}}
"#,
        root, command_line
    )
}

async fn verify_multiboot2(image: &Path) -> Result<()> {
    let status = Command::new("grub-file")
        .arg("--is-x86-multiboot2")
        .arg(image)
        .status()
        .await
        .with_context(|| "Failed to run grub-file to verify the kernel image")?;

    if status.success() {
        Ok(())
    } else {
        Err(anyhow!("Not a valid multiboot2 image: {:?}", image))
    }
}

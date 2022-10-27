//! GRUB bootable image generation.
//!
//! We use `grub-mkrescue` to generate a tiny bootable ISO
//! that boots GRUB with a config file that loads Atmosphere
//! from the first hard drive. We don't put the actual
//! kernel in the image since generating the image may
//! be slow with large files.

use std::convert::AsRef;
use std::path::{Path, PathBuf};
use std::process::Stdio;

use anyhow::anyhow;
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
            let kernel_path = source_dir.join("boot/atmosphere");
            fs::copy(kernel.path(), kernel_path).await?;
        }

        // actually generate the image
        let output = Command::new("grub-mkrescue")
            .arg("-o")
            .arg(iso_path.as_os_str())
            .arg(source_dir.as_os_str())
            .stderr(Stdio::piped())
            .output()
            .await?;

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

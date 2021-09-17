//! Build the OS.

use std::env;
use std::str::FromStr;
use std::path::PathBuf;

use anyhow::anyhow;
use clap::Clap;
use tokio::fs;

use crate::error::{Error, Result};
use crate::project::{BuildOptions, Project};
use crate::grub::BootableImage;
use super::{SubCommand, GlobalOpts};

#[derive(Debug)]
enum OutputType {
    /// Bootable ISO.
    Iso,

    /// Multiboot2 image.
    Multiboot2,
}

impl FromStr for OutputType {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        match s {
            "iso" => Ok(Self::Iso),
            "multiboot2" | "mb2" => Ok(Self::Multiboot2),
            _ => Err(anyhow!("Output type is one of: iso, mb2")),
        }
    }
}

impl Default for OutputType {
    fn default() -> Self {
        Self::Multiboot2
    }
}

impl OutputType {
    fn default_name(&self) -> &'static str {
        match self {
            Self::Iso => "atmosphere.iso",
            Self::Multiboot2 => "atmosphere.mb2",
        }
    }

    async fn prepare_output(&self, path: Option<PathBuf>) -> Result<PathBuf> {
        let path = path.unwrap_or(env::current_dir()?.join(self.default_name()));

        let dir = if path.file_name().is_none() {
            &path
        } else {
            path.parent().ok_or(anyhow!("Could not get parent directory of output path"))?
        };

        fs::create_dir_all(dir).await?;

        Ok(path)
    }
}

/// Build the OS.
#[derive(Debug, Clap)]
pub struct Opts {
    /// Type of the output.
    #[clap(short = 't', long, default_value = "mb2")]
    output_type: OutputType,

    /// Output path.
    #[clap(short = 'o', long)]
    output: Option<PathBuf>,

    /// Extra command-line arguments.
    #[clap(long = "cmdline")]
    command_line: Option<String>,
}

pub(super) async fn run(global: GlobalOpts) -> Result<()> {
    let local = unwrap_command!(global, SubCommand::Build);

    let project = Project::discover()?;

    let mut opts = BuildOptions::default();
    opts.release = global.release;
    opts.verbose = global.verbose;

    let kernel_crate = project.kernel();
    let kernel = kernel_crate.build(&opts).await?
        .expect("No binary was produced");

    let output_path = local.output_type.prepare_output(local.output).await?;

    match local.output_type {
        OutputType::Iso => {
            let cmdline = local.command_line.unwrap_or(String::new());
            let iso = BootableImage::generate(cmdline, Some(&kernel)).await?;

            fs::copy(iso.iso_path(), &output_path).await?;
        }
        OutputType::Multiboot2 => {
            fs::copy(kernel.path(), &output_path).await?;
        }
    }

    println!("{}", output_path.to_str().expect("Output path is not valid UTF-8"));

    Ok(())
}


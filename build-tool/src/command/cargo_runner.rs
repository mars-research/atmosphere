//! The Cargo runner wrapper.
//!
//! Cargo will pass us a kernel image, and we just run it.

use std::path::PathBuf;

use anyhow::anyhow;
use clap::Clap;

use crate::error::Result;
use crate::emulator::{Emulator, EmulatorExit, RunConfiguration, Bochs};
use crate::project::{Project, Binary};
use super::{SubCommand, GlobalOpts};

/// Run Atmosphere.
#[derive(Debug, Clap)]
pub struct Opts {
    /// Path to the kernel.
    kernel: PathBuf,

    /// Whether we are running benchmarks.
    #[clap(long)]
    bench: bool,
}

pub(super) async fn run(global: GlobalOpts) -> Result<()> {
    let local = unwrap_command!(global, SubCommand::CargoRunner);

    let project = Project::discover()?;

    let run_config = RunConfiguration::default();
    let kernel = Binary::new(local.kernel);

    if local.bench {
        return Err(anyhow!("Benchmarks are not supported at the moment"));
    }

    let mut emulator = Bochs::new(project.clone());
    let ret = emulator.run(&run_config, &kernel).await?;

    match ret {
        EmulatorExit::Code(code) => {
            std::process::exit(code);
        }
        EmulatorExit::Killed => {
            log::error!("The emulator was killed by a signal");
            std::process::exit(1);
        }
        _ => {}
    }

    Ok(())
}

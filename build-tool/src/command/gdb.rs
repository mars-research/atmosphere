//! Runs GDB.

use std::os::unix::process::ExitStatusExt;

use clap::Parser;
use tokio::fs;

use super::{GlobalOpts, SubCommand};
use crate::emulator::GdbConnectionInfo;
use crate::error::Result;
use crate::project::Project;

/// Runs GDB.
#[derive(Debug, Parser)]
#[clap(trailing_var_arg = true)]
pub struct Opts {
    /// Extra arguments for GDB.
    extra_args: Vec<String>,
}

pub(super) async fn run(global: GlobalOpts) -> Result<()> {
    let local = unwrap_command!(global, SubCommand::Gdb);

    let project = Project::discover()?;
    let json_path = project.gdb_info_path();

    if !json_path.exists() {
        log::error!("The GDB connection info file doesn't exist");
        log::error!("Hint: Try `atmo run --gdb` or `cargo run -- --gdb`");
        std::process::exit(1);
    }

    let json = fs::read(&json_path).await?;
    let gdb_info: GdbConnectionInfo = serde_json::from_slice(&json)?;

    let status = gdb_info.launch_gdb(local.extra_args).await?;

    if let Some(code) = status.code() {
        if code != 0 {
            std::process::exit(code);
        }
    } else if let Some(signal) = status.signal() {
        log::error!("GDB was killed by signal {}", signal);
        std::process::exit(1);
    }

    Ok(())
}

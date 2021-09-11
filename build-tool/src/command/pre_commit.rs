//! Pre-commit hook.

use clap::Clap;
// use tokio::process::Command;

use crate::error::Result;
use super::{SubCommand, GlobalOpts};

/// Run pre-commit checks.
#[derive(Debug, Clap)]
pub struct Opts {
}

pub(super) async fn run(global: GlobalOpts) -> Result<()> {
    let _local = unwrap_command!(global, SubCommand::PreCommit);
    Ok(())
}

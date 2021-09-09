//! Run the OS in QEMU.

use clap::Clap;

use crate::error::Result;
use crate::project::{BuildOptions, Project};
use crate::qemu::Qemu;
use super::GlobalOpts;

/// Run Atmosphere.
#[derive(Debug, Clap)]
pub struct Opts {
}

pub(super) async fn run(cli: GlobalOpts) -> Result<()> {
    let project = Project::discover()?;
    log::info!("Project: {:?}", project.root());

    let mut opts = BuildOptions::default();
    opts.release = cli.release;
    opts.verbose = cli.verbose;

    let kernel_crate = project.kernel();
    let kernel = kernel_crate.build(&opts).await?
        .expect("No binary was produced");

    let qemu = Qemu::new(project.clone());
    qemu.run(&kernel).await?;

    Ok(())
}

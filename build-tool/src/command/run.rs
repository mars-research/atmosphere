//! Run the OS in QEMU.

use clap::Clap;

use crate::error::Result;
use crate::project::{BuildOptions, Project};
use crate::qemu::{Qemu, QemuExit};
use super::{SubCommand, GlobalOpts};

/// Run Atmosphere.
#[derive(Debug, Clap)]
pub struct Opts {
    /// A script to run.
    #[clap(long)]
    script: Option<String>,

    /// Extra command-line arguments.
    #[clap(long = "cmdline")]
    command_line: Option<String>,

    /// Do not automatically shutdown.
    ///
    /// This will pass `-no-shutdown` to QEMU as well as
    /// tell Atmosphere not to shutdown after the script
    /// finishes.
    #[clap(long)]
    no_shutdown: bool,
}

pub(super) async fn run(global: GlobalOpts) -> Result<()> {
    let local = unwrap_command!(global, SubCommand::Run);

    let project = Project::discover()?;
    log::info!("Project: {:?}", project.root());

    let mut opts = BuildOptions::default();
    opts.release = global.release;
    opts.verbose = global.verbose;

    let kernel_crate = project.kernel();
    let kernel = kernel_crate.build(&opts).await?
        .expect("No binary was produced");

    let mut qemu = Qemu::new(project.clone());
    qemu.set_no_shutdown(local.no_shutdown);

    if let Some(script) = local.script {
        qemu.set_script(script);
    }

    if let Some(cmdline) = local.command_line {
        qemu.set_command_line(cmdline);
    }

    match qemu.run(&kernel).await? {
        QemuExit::Code(code) => {
            std::process::exit(code);
        }
        QemuExit::Killed => {
            std::process::exit(1);
        }
        _ => {}
    }

    Ok(())
}

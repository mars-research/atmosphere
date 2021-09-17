//! Run the OS in QEMU.

use clap::Clap;

use crate::error::Result;
use crate::project::{BuildOptions, Project};
use crate::emulator::{CpuModel, Emulator, EmulatorExit, RunConfiguration, Qemu, Bochs};
use super::{SubCommand, GlobalOpts};

/// Run Atmosphere.
#[derive(Debug, Clap)]
pub struct Opts {
    /// The CPU model to emulate.
    #[clap(long = "cpu")]
    cpu_model: Option<CpuModel>,

    /// A script to run.
    #[clap(long)]
    script: Option<String>,

    /// Extra command-line arguments.
    #[clap(long = "cmdline")]
    command_line: Option<String>,

    /// Whether to use Bochs.
    #[clap(long)]
    bochs: bool,

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

    let mut run_config = RunConfiguration::default();
    run_config.auto_shutdown(!local.no_shutdown);

    if let Some(cpu_model) = local.cpu_model {
        run_config.cpu_model(cpu_model);
    }

    if let Some(script) = local.script {
        run_config.script(script);
    }

    if let Some(cmdline) = local.command_line {
        run_config.command_line(cmdline);
    }

    let mut emulator: Box<dyn Emulator> = if local.bochs {
        Box::new(Bochs::new(project.clone()))
    } else {
        Box::new(Qemu::new(project.clone()))
    };
    // let mut qemu = Qemu::new(project.clone());
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

//! Run the OS in QEMU.

use std::path::PathBuf;

use clap::Parser;

use super::{GlobalOpts, SubCommand};
use crate::emulator::{Bochs, CpuModel, Emulator, EmulatorExit, GdbServer, Qemu, RunConfiguration};
use crate::error::Result;
use crate::project::{Binary, BuildOptions, Project};

/// Run Atmosphere.
#[derive(Debug, Parser)]
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

    /// Whether to enable the debugger.
    #[clap(long)]
    debugger: bool,

    /// Whether to enable the GDB server.
    #[clap(long, hidden = true)]
    gdb: bool,

    /// Whether to use QEMU.
    ///
    /// KVM on an Intel machine with nested virtualization is required.
    #[clap(long)]
    qemu: bool,

    /// Whether to emit full output from the emulator.
    #[clap(long)]
    full_output: bool,

    /// Do not automatically shutdown.
    ///
    /// This will pass `-no-shutdown` to QEMU as well as
    /// tell Atmosphere not to shutdown after the script
    /// finishes.
    #[clap(long)]
    no_shutdown: bool,

    /// (Hidden) Kernel file to execute.
    ///
    /// This is used by the Cargo runner.
    #[clap(long, hidden = true)]
    cargo_runner: Option<PathBuf>,
}

pub(super) async fn run(global: GlobalOpts) -> Result<()> {
    let local = unwrap_command!(global, SubCommand::Run);

    let project = Project::discover()?;
    log::info!("Project: {:?}", project.root());

    let mut opts = BuildOptions::default();
    opts.release = global.release;
    opts.verbose = global.verbose;

    let kernel = if let Some(prebuilt) = local.cargo_runner {
        Binary::new(prebuilt)
    } else {
        let kernel_crate = project.kernel();
        kernel_crate
            .build(&opts)
            .await?
            .expect("No binary was produced")
    };

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

    if local.full_output {
        run_config.suppress_initial_outputs(false);
    }

    if local.debugger {
        if local.qemu {
            unimplemented!();
        }

        run_config.suppress_initial_outputs(false);
        run_config.freeze_on_startup(true);
    }

    // FIXME: Make this configurable
    if local.gdb {
        if local.qemu {
            // Use Unix Domain Socket
            unimplemented!()
        } else {
            run_config.gdb_server(GdbServer::Tcp(1234));
        }

        run_config.freeze_on_startup(true);

        panic!("Not implemented yet")
    }

    let mut emulator: Box<dyn Emulator> = if local.qemu {
        Box::new(Qemu::new(project.clone()))
    } else {
        Box::new(Bochs::new(project.clone()))
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

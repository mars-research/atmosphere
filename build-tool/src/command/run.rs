//! Run the OS in QEMU.

use std::path::PathBuf;

use anyhow::Context;
use clap::Parser;
use tempfile::Builder as TempfileBuilder;
use tokio::fs;

use super::{GlobalOpts, SubCommand};
use crate::emulator::{
    Bochs, CpuModel, Emulator, EmulatorExit, GdbConnectionInfo, GdbServer, Qemu, RunConfiguration,
};
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
    #[clap(long)]
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

    let run_dir = TempfileBuilder::new().prefix("atmo-run-").tempdir()?;

    // FIXME: Make this configurable
    if local.gdb {
        let gdb_server = if local.qemu {
            // Use Unix Domain Socket
            let socket_path = run_dir.path().join("gdb.sock").to_owned();
            GdbServer::Unix(socket_path)
        } else {
            GdbServer::Tcp(1234)
        };

        run_config.gdb_server(gdb_server.clone());
        run_config.freeze_on_startup(true);

        if !local.qemu {
            unimplemented!("GDB support for Bochs not implemented yet - use QEMU with --qemu")
        }

        // Save connection info to `.gdb`
        let gdb_info = GdbConnectionInfo::new(kernel.path().to_owned(), gdb_server);
        let json_path = project.gdb_info_path();
        let json = serde_json::to_vec(&gdb_info)?;

        if json_path.exists() {
            log::warn!("GDB connection info file already exists - Overwriting");
        }

        fs::write(&json_path, json).await?;

        log::warn!("Run `atmo gdb` in another terminal. Execution will be frozen until you continue in the debugger.");
    }

    let mut emulator: Box<dyn Emulator> = if local.qemu {
        Box::new(Qemu::new(project.clone()))
    } else {
        Box::new(Bochs::new(project.clone()))
    };
    // let mut qemu = Qemu::new(project.clone());
    let ret = emulator.run(&run_config, &kernel).await?;

    if local.gdb {
        let json_path = project.gdb_info_path();
        fs::remove_file(&json_path)
            .await
            .with_context(|| "Failed to remove GDB connection info JSON")?;
    }

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

    drop(run_dir);

    Ok(())
}

//! Run the OS in QEMU.

use std::path::PathBuf;
use std::process::ExitCode;

use anyhow::Context;
use clap::Parser;
use tempfile::Builder as TempfileBuilder;
use tokio::fs;

use super::{GlobalOpts, SubCommand};
use crate::emulator::{CpuModel, Emulator, EmulatorExit, GdbServer, Qemu, RunConfiguration};
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

    /// Whether to use KVM.
    ///
    /// This only has an effect for QEMU.
    #[clap(long)]
    kvm: bool,

    /// Whether to enable the early loader.
    #[clap(long, hide = true)]
    loader: bool,

    /// Whether to enable the GDB server.
    #[clap(long)]
    gdb: bool,

    /// Whether to enable Nvme emulation
    #[clap(long)]
    nvme: bool,

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
    #[clap(long, hide = true)]
    cargo_runner: Option<PathBuf>,
}

pub(super) async fn run(global: GlobalOpts) -> Result<()> {
    let local = unwrap_command!(global, SubCommand::Run);

    let project = Project::discover()?;
    log::info!("Project: {:?}", project.root());

    let mut opts = BuildOptions::default();
    opts.release = global.release || local.cargo_runner.is_some();
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

    let loader = project
        .loader()
        .build(&opts)
        .await?
        .expect("No binary was reproduced for the early loader");

    let dom0 = project
        .dom0()
        .build(&opts)
        .await?
        .expect("No binary was reproduced for Dom0");

    let mut run_config = RunConfiguration::new(kernel, loader);
    run_config.use_virtualization(local.kvm);
    run_config.auto_shutdown(!local.no_shutdown);
    run_config.dom0(dom0);
    run_config.enable_nvme(local.nvme);

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

    let run_dir = TempfileBuilder::new().prefix("atmo-run-").tempdir()?;

    // FIXME: Make this configurable
    if local.gdb {
        let gdb_server = {
            let socket_path = run_dir.path().join("gdb.sock").to_owned();
            GdbServer::Unix(socket_path)
        };

        run_config.gdb_server(gdb_server.clone());
        run_config.freeze_on_startup(true);
    }

    // TODO: Bring Bochs back maybe?
    let mut emulator: Box<dyn Emulator> = Box::new(Qemu::new(project.clone(), run_config));

    if let Some(gdb_info) = emulator.gdb_connection_info() {
        // Save connection info to `.gdb`
        let json_path = project.gdb_info_path();
        let json = serde_json::to_vec(&gdb_info)?;

        if json_path.exists() {
            log::warn!("GDB connection info file already exists - Overwriting");
        }

        fs::write(&json_path, json).await?;

        log::warn!("Run `atmo gdb` in another terminal. Execution will be frozen until you continue in the debugger.");
    }

    let ret = emulator.run().await?;

    if local.gdb {
        let json_path = project.gdb_info_path();
        fs::remove_file(&json_path)
            .await
            .with_context(|| "Failed to remove GDB connection info JSON")?;
    }

    match ret {
        EmulatorExit::Code(code) => {
            quit::with_code(code as u8);
        }
        EmulatorExit::Killed => {
            log::error!("The emulator was killed by a signal");
            quit::with_code(ExitCode::FAILURE);
        }
        _ => {}
    }

    drop(run_dir);

    Ok(())
}

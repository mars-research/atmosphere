//! Command-line interface.

mod run;

use clap::Clap;

/// Run the CLI.
pub async fn run() -> Result<(), anyhow::Error> {
    let opts = GlobalOpts::parse();

    match &opts.cmd {
        Command::Run(_) => {
            run::run(opts).await?;
        }
    }

    /*
    let project = Project::discover().unwrap();

    let qemu = qemu::Qemu::new(project.clone());
    qemu.run().await?;

    let grub = grub::BootableImage::generate("script=vmx_test").await?;
    tokio::fs::copy(grub.iso_path(), "/tmp/grub.iso").await?;
    */

    Ok(())
}

/// Atmosphere build utility.
#[derive(Debug, Clap)]
struct GlobalOpts {
    #[clap(subcommand)]
    cmd: Command,

    /// Use verbose output.
    #[clap(short, long, global = true)]
    verbose: bool,

    /// Build in release mode.
    #[clap(long, global = true)]
    release: bool,
}

#[derive(Debug, Clap)]
enum Command {
    Run(run::Opts),
}


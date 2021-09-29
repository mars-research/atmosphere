//! Command-line interface.

macro_rules! unwrap_command {
    ($global:expr, $type:path) => {
        if let $type(local) = $global.cmd {
            local
        } else {
            panic!("Invalid command {:?}", $global.cmd)
        }
    }
}

mod run;
mod build;

use clap::{Clap, IntoApp};

/// Run the CLI.
pub async fn run() -> Result<(), anyhow::Error> {
    let opts = GlobalOpts::parse();

    match &opts.cmd {
        SubCommand::Run(_) => run::run(opts).await?,
        SubCommand::Build(_) => build::run(opts).await?,
        SubCommand::GenCompletions(local) => {
            gen_completions(&local.shell);
        }
    }

    Ok(())
}

/// Atmosphere build utility.
#[derive(Debug, Clap)]
struct GlobalOpts {
    #[clap(subcommand)]
    cmd: SubCommand,

    /// Use verbose output.
    #[clap(short, long, global = true)]
    verbose: bool,

    /// Build in release mode.
    #[clap(long, global = true)]
    release: bool,
}

#[derive(Debug, Clap)]
enum SubCommand {
    Run(run::Opts),
    Build(build::Opts),

    #[clap(setting(clap::AppSettings::Hidden))]
    GenCompletions(GenCompletions),
}

#[derive(Debug, Clap)]
struct GenCompletions {
    #[clap(index = 1)]
    shell: String,
}

macro_rules! generate_for {
    ($shell:ty) => {
        clap_generate::generate::<$shell, _>(&mut GlobalOpts::into_app(), "atmo", &mut std::io::stdout())
    }
}

fn gen_completions(shell: &str) {
    use clap_generate::generators::{Bash, Fish, Zsh};

    match shell {
        "bash" => generate_for!(Bash),
        "fish" => generate_for!(Fish),
        "zsh" => generate_for!(Zsh),
        _ => panic!("{} is not supported", shell),
    }
}

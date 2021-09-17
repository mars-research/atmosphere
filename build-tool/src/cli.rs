//! Global CLI Setup.

use clap::{App, AppSettings, Arg, ArgMatches, SubCommand};
use crate::command;

macro_rules! register_command {
    ($module:ident, $app:ident) => {
        $app = $app.subcommand(command::$module::subcommand());
    };
}

macro_rules! handle_command {
    ($module:ident, $matches:ident) => {
        if let Some(sub_matches) = $matches.subcommand_matches(stringify!($module)) {
            command::$module::run(&$matches, &sub_matches).await;
            return;
        }
    };
    ($name:expr, $module:ident, $matches:ident) => {
        if let Some(sub_matches) = $matches.subcommand_matches($name) {
            command::$module::run(&$matches, &sub_matches).await;
            return;
        }
    };
}

pub fn build_cli(include_internal: bool) -> App<'static, 'static> {
    let mut app = App::new("Ace Build Tool")
        .bin_name("ace")
        .version("0.1.0")
        .global_setting(AppSettings::ColoredHelp)
        .setting(AppSettings::ArgRequiredElseHelp);

    if include_internal {
        app = app.subcommand(SubCommand::with_name("gen-completions")
            .about("Generate shell auto-completion files (Internal)")
            .setting(AppSettings::Hidden)
            .arg(Arg::with_name("shell")
                .index(1)
                .required(true)
                .takes_value(true)));
    }

    app
}

pub async fn run() {
    let mut app = build_cli(true);
    let matches = app.clone().get_matches();

    if let Some(args) = matches.subcommand_matches("gen-completions") {
        return gen_completions(args);
    }

    app.print_long_help().unwrap();
    println!();
}

fn gen_completions(args: &ArgMatches<'_>) {
    let mut app = build_cli(false);
    let shell: clap::Shell = args.value_of("shell").unwrap()
        .parse().unwrap();

    app.gen_completions_to("ace", shell, &mut std::io::stdout());
}

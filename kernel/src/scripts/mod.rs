//! Debug scripts.
//!
//! We have a set of debug scripts to facilitate testing.
//! They can be executed with the `script=` kernel command line parameter.

mod vmx_test;
mod cap_test;

use super::boot::command_line;

macro_rules! match_script {
    ($name:expr, $func:path, $supplied:ident) => {
        if $supplied == $name {
            log::info!("Running script {}...", $name);
            $func();
            log::info!("Script {} completed.", $name);
            return;
        }
    }
}

/// Runs the specified debug script.
pub unsafe fn run_script(script: &str) {
    match_script!("vmx_test", vmx_test::run, script);
    match_script!("cap_test", cap_test::run, script);

    panic!("Script {} does not exist", script);
}

/// Runs the debug script specified in the command line.
pub unsafe fn run_script_from_command_line() {
    if let Some(script) = command_line::get_first_value("script") {
        run_script(script)
    }
}

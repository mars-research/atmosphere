//! Debug scripts.
//!
//! We have a set of debug scripts to facilitate testing.
//! They can be executed with the `script=` kernel command line parameter.

mod cap_test;
mod fail_test;
mod vmx_test;

use crate::boot::{command_line, shutdown};
use crate::error::{Error, Result};

macro_rules! match_script {
    ($name:expr, $func:path, $supplied:ident) => {
        if $supplied == $name {
            log::info!("Running script {}...", $name);
            let ret = $func();

            if let Err(e) = &ret {
                log::error!("Script {} failed with {}.", $name, e);
            } else {
                log::info!("Script {} completed.", $name);
            }

            return ret;
        }
    }
}

/// Runs the specified debug script.
pub unsafe fn run_script(script: &str) -> Result<()> {
    match_script!("cap_test", cap_test::run, script);
    match_script!("fail_test", fail_test::run, script);
    match_script!("vmx_test", vmx_test::run, script);

    log::error!("Script {} does not exist", script);
    Err(Error::NoSuchScript)
}

/// Runs the debug script specified in the command line.
pub unsafe fn run_script_from_command_line() {
    if let Some(script) = command_line::get_first_value("script") {
        let ret = run_script(script);

        if command_line::get_flag("script_shutdown") {
            shutdown(ret.is_ok());
        }
    }
}

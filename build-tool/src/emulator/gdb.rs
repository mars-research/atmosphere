//! GDB integration.
//!
//! When launching `atmo run --gdb`, the build tool writes a JSON file
//! at `.gdb` under the workspace root with information in `GdbConnectionInfo`.

use std::{collections::HashMap, path::PathBuf};

use serde::{Deserialize, Serialize};

use crate::error::Result;
use crate::project::Project;

const GDB_HELPER_PATH: &str = "build-tool/src/emulator/gdb-helper.py";

/// GDB server connection info.
#[allow(dead_code)]
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct GdbConnectionInfo {
    /// The main executable file.
    file: PathBuf,

    /// Method to connect to the GDB server.
    server: GdbServer,

    /// Paths to other binaries.
    binaries: HashMap<String, PathBuf>,
}

/// GDB server configurations.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub enum GdbServer {
    /// Listen on a Unix socket.
    Unix(PathBuf),

    /// Listen on a TCP port.
    Tcp(u16),
}

impl GdbConnectionInfo {
    pub fn new(file: PathBuf, server: GdbServer) -> Self {
        Self {
            file,
            server,
            binaries: HashMap::new(),
        }
    }

    pub fn add_binary(&mut self, name: String, path: PathBuf) {
        self.binaries.insert(name, path);
    }

    pub async fn launch_gdb(&self, pause: bool, extra_args: Vec<String>) -> Result<()> {
        let file_command = format!(
            "file {}",
            self.file
                .to_str()
                .expect("Executable path contains non-UTF-8")
        );

        let project = Project::discover()?;
        let helper_path = project.root().join(GDB_HELPER_PATH);

        let mut command = exec::Command::new("gdb");
        command
            .arg("-q")
            .args(&["-ex", &file_command])
            .args(&["-ex", &self.server.to_gdb_target_command()]);

        for (name, path) in &self.binaries {
            let var_command = format!("set $bin_{} = \"{}\"", name, path.to_str().unwrap());
            command.args(&["-ex", &var_command]);
        }

        command
            .args(&["-ex", &format!("source {}", helper_path.to_str().unwrap())])
            .args(&extra_args);

        if !pause {
            command.args(&["-ex", "c"]);
        }

        let error = command.exec();

        Err(error.into())
    }
}

impl GdbServer {
    fn to_gdb_target_command(&self) -> String {
        match self {
            Self::Unix(path) => format!(
                "target remote {}",
                path.to_str().expect("GDB socket path contains non-UTF-8")
            ),
            Self::Tcp(port) => format!("target remote :{}", port),
        }
    }
}

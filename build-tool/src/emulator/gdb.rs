//! GDB integration.
//!
//! When launching `atmo run --gdb`, the build tool writes a JSON file
//! at `.gdb` under the workspace root with information in `GdbConnectionInfo`.

use std::path::PathBuf;
use std::process::ExitStatus;

use serde::{Deserialize, Serialize};
use tokio::process::Command;

use crate::error::Result;

/// GDB server connection info.
#[allow(dead_code)]
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct GdbConnectionInfo {
    /// The main executable file.
    executable: PathBuf,

    /// Method to connect to the GDB server.
    server: GdbServer,
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
    pub fn new(executable: PathBuf, server: GdbServer) -> Self {
        Self { executable, server }
    }

    pub async fn launch_gdb(&self, extra_args: Vec<String>) -> Result<ExitStatus> {
        let file_command = format!(
            "file {}",
            self.executable
                .to_str()
                .expect("Executable path contains non-UTF-8")
        );
        let status = Command::new("gdb")
            .arg("-q")
            .args(&["-ex", &file_command])
            .args(&["-ex", &self.server.to_gdb_target_command()])
            .args(extra_args)
            .status()
            .await?;

        Ok(status)
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

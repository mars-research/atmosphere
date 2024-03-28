//! Project.
//!
//! We handle interaction with Cargo here.

use std::env;
use std::io::Cursor;
use std::path::{Path, PathBuf};
use std::process::Stdio;
use std::sync::Arc;

use anyhow::anyhow;
use byte_unit::Byte;

// TODO: Get rid of cargo dep
use cargo::core::Workspace;
use cargo::util::config::Config as CargoConfig;
use cargo::util::important_paths::find_root_manifest_for_wd;

use cargo_metadata::Message as CargoMessage;
use tokio::fs;
use tokio::process::Command;

use super::error::Result;

/// A handle to a project.
pub type ProjectHandle = Arc<Project>;

/// The Atmosphere project.
#[derive(Debug)]
pub struct Project {
    root: PathBuf,
}

impl Project {
    /// Automatically discover the Atmosphere project root.
    pub fn discover() -> Result<ProjectHandle> {
        let cwd = env::current_dir()?;
        let mut cargo_toml = find_root_manifest_for_wd(&cwd)?;

        // Ugly exception for build-tool which lives outside the workspace
        if "build-tool" == cargo_toml.parent().unwrap().file_name().unwrap() {
            cargo_toml = cargo_toml
                .parent()
                .unwrap()
                .parent()
                .unwrap()
                .join("Cargo.toml");
        }

        let cargo_config = CargoConfig::default()?;

        let workspace = Workspace::new(&cargo_toml, &cargo_config)?;
        let root = workspace.root().to_owned();

        // sanity check
        let kernel_pkg = workspace.members().find(|pkg| pkg.name() == "kernel");

        if kernel_pkg.is_none() {
            return Err(anyhow!(
                "Invalid workspace - The kernel crate (\"kernel\") doesn't exist"
            ));
        }

        Ok(Arc::new(Self { root }))
    }

    /// Returns the kernel crate.
    pub fn kernel(self: &Arc<Self>) -> Crate {
        Crate {
            name: "kernel".to_string(),
            crate_dir: self.root.join("kernel"),
            binary: Some("kernel".to_string()),
            max_stack_size: Some(Byte::from_bytes(1024 * 1024 * 16)), // 16 MiB
        }
    }

    /// Returns the early loader crate
    pub fn loader(self: &Arc<Self>) -> Crate {
        Crate {
            name: "aloader".to_string(),
            crate_dir: self.root.join("aloader"),
            binary: Some("aloader".to_string()),
            max_stack_size: Some(Byte::from_bytes(1024 * 1024 * 16)), // 16 MiB
        }
    }

    /// Returns the init/dom0 crate
    pub fn dom0(self: &Arc<Self>) -> Crate {
        Crate {
            name: "dom0".to_string(),
            crate_dir: self.root.join("dom0"),
            binary: Some("dom0".to_string()),
            max_stack_size: Some(Byte::from_bytes(1024 * 1024 * 16)), // 16 MiB
        }
    }

    /// Returns the path to the workspace root.
    pub fn root(&self) -> PathBuf {
        self.root.clone()
    }

    /// Returns the path to the GDB connection info.
    pub fn gdb_info_path(&self) -> PathBuf {
        self.root.join(".gdb").to_owned()
    }
}

/// A crate.
///
/// The build will be initiated from the crate's directory. We do
/// this to make Cargo automatically pull in crate-specific
/// `.cargo/config` so we don't need to waste time injecting
/// various configurations ourselves.
pub struct Crate {
    /// Name of the crate.
    name: String,

    /// Directory of the crate.
    crate_dir: PathBuf,

    /// Name of the binary, if this is a binary crate.
    binary: Option<String>,

    /// Maximum limit of stack sizes.
    max_stack_size: Option<Byte>,
}

impl Crate {
    /// Build the crate.
    pub async fn build(&self, options: &BuildOptions) -> Result<Option<Binary>> {
        //log::info!("Building crate {:?}", self.crate_dir);
        let mut command = Command::new("cargo");
        command
            .args(&["build"])
            .args(&["--message-format=json-render-diagnostics"])
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .current_dir(&self.crate_dir);

        if options.release {
            command.arg("--release");
        }

        let build = command.spawn()?;
        let output = build.wait_with_output().await?;

        if !output.status.success() {
            return Err(anyhow!("Compilation failed with {}", output.status));
        }

        if let Some(binary) = &self.binary {
            let reader = Cursor::new(output.stdout.as_slice());
            let messages = CargoMessage::parse_stream(reader).collect::<Result<Vec<_>, _>>()?;

            let executable = messages
                .iter()
                .find_map(|message| {
                    if let CargoMessage::CompilerArtifact(artifact) = message {
                        if artifact.target.name != self.name {
                            return None;
                        }

                        return artifact.executable.clone();
                    }

                    None
                })
                .map(|utf8| utf8.into_std_path_buf())
                .ok_or(anyhow!(
                    "Compilation did not generate binary \"{}\"",
                    binary
                ))?;

            self.check_stack_sizes(&executable).await?;

            let binary = Binary::new(executable);
            Ok(Some(binary))
        } else {
            Ok(None)
        }
    }

    async fn check_stack_sizes(&self, path: &Path) -> Result<()> {
        use stack_sizes::Function;

        if let Some(limit) = self.max_stack_size {
            let elf = fs::read(path).await?;
            let functions = stack_sizes::analyze_executable(&elf).map_err(|e| anyhow!("{}", e))?;
            let mut functions = functions.defined.values().collect::<Vec<&Function>>();

            functions.sort_by(|a, b| a.size().cmp(&b.size()).reverse());

            if let Some(top) = functions.first() {
                if top.size() as u128 > limit.get_bytes() {
                    eprintln!("Top stack sizes:");
                    for func in &functions[..10] {
                        eprintln!("{}: {:?}", func.size(), func.names());
                    }

                    return Err(anyhow!(
                        "The stack size of function {:?} is {} bytes, which is over the limit of {:?}",
                        top.names(),
                        top.size(),
                        limit,
                    ));
                }
            }
        }

        Ok(())
    }
}

/// A binary in the build output.
#[derive(Debug, Clone)]
pub struct Binary(PathBuf);

impl Binary {
    pub fn new(path: PathBuf) -> Self {
        Self(path)
    }

    pub fn path(&self) -> &Path {
        &self.0
    }
}

#[derive(Debug, Clone)]
pub struct BuildOptions {
    pub release: bool,
    pub verbose: bool,
}

impl Default for BuildOptions {
    fn default() -> Self {
        Self {
            release: false,
            verbose: false,
        }
    }
}

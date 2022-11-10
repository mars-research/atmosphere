//! Project.
//!
//! We handle interaction with Cargo here.

use std::env;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use anyhow::anyhow;
use byte_unit::Byte;
use cargo::core::compiler::CompileMode;
use cargo::core::shell::Shell as CargoShell;
use cargo::core::Workspace;
use cargo::ops::{CompileOptions, Packages};
use cargo::util::config::Config as CargoConfig;
use cargo::util::important_paths::find_root_manifest_for_wd;
use cargo::util::interning::InternedString;
use tokio::fs;
use tokio::task::block_in_place;

use super::error::Result;

/// A handle to a project.
pub type ProjectHandle = Arc<Project>;

/// The Atmosphere project.
#[derive(Debug)]
pub struct Project {
    cargo_toml: PathBuf,
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
        let kernel_pkg = workspace.members().find(|pkg| pkg.name() == "atmosphere");

        if kernel_pkg.is_none() {
            return Err(anyhow!(
                "Invalid workspace - The kernel crate (\"atmosphere\") doesn't exist"
            ));
        }

        Ok(Arc::new(Self {
            cargo_toml: root.join("Cargo.toml"),
            root,
        }))
    }

    /// Returns the kernel crate.
    pub fn kernel(self: &Arc<Self>) -> Crate {
        Crate {
            name: "atmosphere".to_string(),
            crate_dir: self.root.join("kernel"),
            project: self.clone(),
            binary: Some("atmosphere".to_string()),
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

    /// Handle to the project.
    project: ProjectHandle,

    /// Name of the binary, if this is a binary crate.
    binary: Option<String>,

    /// Maximum limit of stack sizes.
    max_stack_size: Option<Byte>,
}

impl Crate {
    /// Build the crate.
    pub async fn build(&self, options: &BuildOptions) -> Result<Option<Binary>> {
        let cfg = self.get_cargo_config(options)?;
        let ws = self.get_cargo_workspace(&cfg)?;

        let mut compile_opts = CompileOptions::new(&cfg, CompileMode::Build)?;
        compile_opts.spec = Packages::Packages(vec![self.name.clone()]);

        if options.release {
            compile_opts.build_config.requested_profile = InternedString::new("release");
        }

        let compilation = block_in_place(move || cargo::ops::compile(&ws, &compile_opts))?;

        if let Some(binary) = &self.binary {
            let unit = compilation
                .binaries
                .iter()
                .find(|b| b.path.file_name().unwrap() == binary.as_str())
                .ok_or(anyhow!(
                    "Compilation did not generate binary \"{}\"",
                    binary
                ))?;

            self.check_stack_sizes(&unit.path).await?;

            let binary = Binary::new(unit.path.clone());
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

    fn get_cargo_config(&self, options: &BuildOptions) -> Result<CargoConfig> {
        let shell = CargoShell::new();
        let home = ::home::cargo_home()?;
        let verbose = if options.verbose { 1 } else { 0 };

        let mut cfg = CargoConfig::new(shell, self.crate_dir.clone(), home);

        // This is required for the unstable options to be parsed and loaded
        cfg.configure(verbose, false, None, false, false, false, &None, &[], &[])?;

        Ok(cfg)
    }

    fn get_cargo_workspace<'a>(&self, config: &'a CargoConfig) -> Result<Workspace<'a>> {
        Workspace::new(&self.project.cargo_toml, config)
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

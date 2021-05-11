# Atmosphere

Atmosphere is a type-1 hypervisor for x86-64, written in Rust.
It's inspired by the design of [seL4](https://sel4.systems/Info/Docs/seL4-manual-latest.pdf), where memory for kernel objects is not dynamically allocated by the microkernel.

## Development Setup

An Intel x86-64 machine running Linux is required to develop Atmosphere.
We currently do not support AMD-V.

It's highly recommended that you use [Nix](https://nixos.org/download.html) to install all dependencies.
With Nix installed, enter the prepared nix-shell environment with `nix-shell`.

A more convenient way to activate the development environment is with [direnv](https://direnv.net) which automatically activates the nix-shell when you enter the project directory.
With direnv installed, run `direnv allow` under the project root to allow it to activate automatically.

If you do not want to use Nix for any reason, the list of dependencies can be found at `nix/environment.nix`.
The version of the nightly Rust toolchain can be found in `nix/nixpkgs.nix`.

### Editor/IDE

We recommend using [rust-analyzer](https://github.com/rust-analyzer/rust-analyzer) with your favorite editor or IDE.
In some setups, rust-analyzer may have trouble finding the correct Rust toolchain to use.
If this is the case, configure your editor to use `nix/rust-analyzer.sh` as the rust-analyzer executable.
For VSCode, this is the `rust-analyzer.server.path` key in `settings.json`.

## Documentation

Documentations can be built with `cargo doc`.

## Licensing

Atmosphere is available under the MIT License.

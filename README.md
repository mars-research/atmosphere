# Atmosphere

[![Build](https://github.com/mars-research/atmosphere/actions/workflows/build.yml/badge.svg)](https://github.com/mars-research/atmosphere/actions/workflows/build.yml)

Atmosphere is a Type-1 hypervisor for Intel x86-64, written in Rust.
It's inspired by the design of [seL4](https://sel4.systems/Info/Docs/seL4-manual-latest.pdf), where memory for kernel objects is not dynamically allocated by the microkernel.

## Development Setup

An Intel x86-64 machine running Linux is required to develop Atmosphere.
We currently do not support AMD-V.

[Nix](https://github.com/numtide/nix-unstable-installer) is required to install development dependencies.
With Nix installed, enter the prepared nix-shell environment with `nix-shell` or `nix develop` (Nix 2.4).

You can now build and run Atmosphere with `atmo run`.

### Direnv

A more convenient way to activate the development environment is with [direnv](https://direnv.net) which automatically activates the nix-shell when you enter the project directory.
With direnv installed, run `direnv allow` under the project root to allow it to activate automatically.

### `/dev/kvm` Access

Your user will need to be in the `kvm` or `libvirtd` group to access `/dev/kvm` directly.
Previously we made use of `sudo` to launch the QEMU process but that resulted in additional complications regarding the ownership of generated files (serial logs, trace dumps, etc.).

### Editor/IDE

We recommend using [rust-analyzer](https://github.com/rust-analyzer/rust-analyzer) with your favorite editor or IDE.
In some setups, rust-analyzer may have trouble finding the correct Rust toolchain to use.
If this is the case, configure your editor to use `nix/rust-analyzer.sh` as the rust-analyzer executable.
For VSCode, this is the `rust-analyzer.server.path` key in `settings.json`.

## Documentation

Documentations can be built by running `cargo doc` inside `kernel`.

## Licensing

Atmosphere is available under the MIT License.

# Atmosphere

Atmosphere is a proving ground for novel isolation techniques and formal verification, written in Rust.

## Development Setup

We use [Nix](https://nixos.org) to manage development dependencies.
Install Nix with the following command:

```bash
# Using https://github.com/DeterminateSystems/nix-installer
curl --proto '=https' --tlsv1.2 -sSf -L https://install.determinate.systems/nix | sh -s -- install
```

You can now build and run Atmosphere with `cd kernel && cargo run`.

## Atmo

Atmosphere builds with `atmo`, a build system that extends Cargo.
Run `atmo help` for more information.

## TODO

Remove transit state for threads @Xiangdong.

Move per CPU cache to MMU Manager @Xiangdong.

Optimize PtRegs Copying for syscall @Xiangdong.
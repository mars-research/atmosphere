# build-tool

`atmo` is a build helper tool for Atmosphere.
It's designed to *augment* the Cargo experience rather than replace it.

It's set as the `runner` executable so `cargo run` and `cargo test` will *just work*.
The `atmo` command provides Atmosphere-specific options, like running the kernel with a special command-line (`atmo run --cmdline`) and building different flavors of boot images (`atmo build -t`).

## Terminal output

By default, the tool suppresses initial outputs from the emulator (BIOS, GRUB, etc.) so the terminal isn't messed up by the control sequences they contain.

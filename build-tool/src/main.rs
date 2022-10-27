#![deny(
    asm_sub_register,
    dead_code,
    deprecated,
    missing_abi,
    rustdoc::bare_urls,
    unused_imports,
    unused_must_use,
    unused_mut,
    unused_unsafe,
    unused_variables
)]

mod command;
mod emulator;
mod error;
mod grub;
mod project;

// use std::env;

#[tokio::main]
async fn main() -> Result<(), anyhow::Error> {
    init_logging();
    command::run().await
}

fn init_logging() {
    env_logger::builder()
        .format_timestamp(None)
        .format_module_path(false)
        .init();
}

#![deny(
    asm_sub_register,
    deprecated,
    missing_abi,
    rustdoc::bare_urls,
    unused_must_use,
    unused_unsafe
)]
#![cfg_attr(
    not(debug_assertions),
    deny(dead_code, unused_imports, unused_mut, unused_variables)
)]

mod command;
mod emulator;
mod error;
mod grub;
mod project;

#[tokio::main]
#[quit::main]
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

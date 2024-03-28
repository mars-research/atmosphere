//! Debugger integration.

use core::hint::black_box;
use core::mem::MaybeUninit;

#[used]
static mut LOADED_BINARIES: [MaybeUninit<LoadedBinary>; 10] = [UNINIT_BINARY; 10];

#[used]
static mut LOADED_BINARIES_LEN: usize = 0;

const UNINIT_BINARY: MaybeUninit<LoadedBinary> = MaybeUninit::zeroed();

#[inline(never)]
fn on_binary_added() {
    black_box(());
}

#[inline(never)]
pub fn on_ready() {
    black_box(());
}

#[derive(Debug, Clone)]
#[allow(dead_code)] // Read by GDB
pub struct LoadedBinary {
    name: &'static str,
    offset: usize,
}

#[inline(never)]
pub fn add_binary(name: &'static str, offset: usize) {
    let binary = LoadedBinary { name, offset };

    unsafe {
        if LOADED_BINARIES_LEN >= LOADED_BINARIES.len() {
            panic!("Too many binaries");
        }

        LOADED_BINARIES[LOADED_BINARIES_LEN].write(binary);
        LOADED_BINARIES_LEN += 1;
    }

    on_binary_added();
}

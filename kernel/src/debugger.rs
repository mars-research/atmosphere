//! Debugger integration.

use core::hint;

#[no_mangle]
pub fn breakpoint(frames_to_rewind: usize) {
    hint::black_box(frames_to_rewind);
}

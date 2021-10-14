//! Utilities.

/// Signals BOCHS to break. This function is otherwise harmless
pub fn bochs_magic_breakpoint() {
    unsafe {
        asm!("xchg bx, bx");
    }
}

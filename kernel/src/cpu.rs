//! Per-CPU data structures.

// use super::boot::get_bsp_initial_stack;

/*
/// The bootstrap processor.
static BSP: Mutex<Cpu> = Mutex::new(Cpu {
    id: 0,
    stack: unsafe { get_bsp_initial_stack() },
});
*/

/// A CPU.
pub struct Cpu {
    /// Numeric identifier of the CPU.
    id: usize,

    /// Stack space for the initial kernel thread.
    stack: *const [u8],
}

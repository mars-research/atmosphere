pub trait TrustedBridge {
    fn set_switch_decision(decision: SwitchDecision);
}

#[derive(Debug)]
#[repr(u8)]
pub enum SwitchDecision {
    /// The kernel will return to the same thread.
    NoSwitching = 0,

    /// The kernel will switch to a clean thread.
    ///
    /// Clean means it entered the kernel through a syscall.
    SwitchToClean = 1,

    /// The kernel will switch to a clean thread.
    SwitchToPreempted = 2,
}

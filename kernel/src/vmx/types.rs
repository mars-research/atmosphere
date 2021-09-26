use core::mem;

use displaydoc::Display;
use enum_primitive_derive::Primitive;
use num_traits::cast::FromPrimitive;

pub const GUEST_CONTEXT_SIZE: usize = mem::size_of::<GuestContext>();

/// The VMCS revision.
#[repr(transparent)]
#[derive(Debug, Clone, Copy)]
pub struct VmcsRevision(u32);

impl VmcsRevision {
    pub fn new(vmcs_revision: u32) -> Self {
        Self(vmcs_revision)
    }

    pub const fn invalid() -> Self {
        Self(0)
    }
}

impl Into<u32> for VmcsRevision {
    fn into(self) -> u32 {
        self.0
    }
}

/// Guest register state.
///
/// VMX will save/restore RIP, RSP and RFLAGS for us, and we need
/// to do the rest.
///
/// FIXME: We will need to save and restore the SIMD registers
/// as well
#[repr(C)]
#[derive(Debug, Clone)]
pub struct GuestContext {
    /// The host's original RSP before the VM entry.
    pub host_rsp: u64,

    pub rax: u64,
    pub rbx: u64,
    pub rcx: u64,
    pub rdx: u64,
    pub rbp: u64,

    pub rdi: u64,
    pub rsi: u64,
    pub r8: u64,
    pub r9: u64,
    pub r10: u64,
    pub r11: u64,
    pub r12: u64,
    pub r13: u64,
    pub r14: u64,
    pub r15: u64,

    /// Whether the vCPU has been launched before or not.
    ///
    /// After restoring all the registers, we will cmp \[rsp\], 0.
    /// We use this to determine whether to VMLAUNCH or VMRESUME.
    launched: u64,
}

impl GuestContext {
    pub const fn new() -> Self {
        Self {
            host_rsp: 0,
            rax: 0,
            rbx: 0,
            rcx: 0,
            rdx: 0,
            rbp: 0,
            rdi: 0,
            rsi: 0,
            r8: 0,
            r9: 0,
            r10: 0,
            r11: 0,
            r12: 0,
            r13: 0,
            r14: 0,
            r15: 0,
            launched: 0,
        }
    }
}

/// Guest register dump for debugging.
///
/// This is more complete than [GuestContext]. Information like RSP, RIP, and
/// control registers is read from the Guest State Area.
#[derive(Debug, Clone)]
pub struct GuestRegisterDump {
    pub rax: u64,
    pub rbx: u64,
    pub rcx: u64,
    pub rdx: u64,
    pub rbp: u64,

    pub rdi: u64,
    pub rsi: u64,
    pub r8: u64,
    pub r9: u64,
    pub r10: u64,
    pub r11: u64,
    pub r12: u64,
    pub r13: u64,
    pub r14: u64,
    pub r15: u64,

    pub rsp: u64,
    pub rip: u64,

    pub cr0: u64,
    pub cr3: u64,
    pub cr4: u64,
}

/// The reason for a VM exit.
#[derive(Clone, Copy, Debug, PartialEq, Display)]
pub enum ExitReason {
    /// {0}
    Known(KnownExitReason),

    /// Unknown exit reason: {0}
    Unknown(u64),
}

impl PartialEq<KnownExitReason> for ExitReason {
    fn eq(&self, other: &KnownExitReason) -> bool {
        if let Self::Known(known) = self {
            known == other
        } else {
            false
        }
    }
}

impl ExitReason {
    pub fn new(reason: u64) -> Self {
        if let Some(known_reason) = KnownExitReason::from_u64(reason) {
            Self::Known(known_reason)
        } else {
            Self::Unknown(reason)
        }
    }
}

/// A known VM exit reason.
#[derive(Clone, Copy, Debug, PartialEq, Display, Primitive)]
#[repr(u64)]
pub enum KnownExitReason {
    /// Exception or non-maskable interrupt (NMI).
    Nmi = 0,

    /// External interrupt.
    ExternalInterrupt = 1,

    /// Triple fault.
    TripleFault = 2,

    /// INIT signal.
    InitSignal = 3,

    /// Start-up IPI (SIPI).
    StartUpIpi = 4,

    /// CPUID.
    Cpuid = 10,

    /// HLT.
    Hlt = 12,

    /// VMCALL.
    Vmcall = 18,

    /// Invalid guest state.
    InvalidGuestState = 33,

    /// EPT violation.
    EptViolation = 48,
}

/// A VM-instruction error.
#[derive(Clone, Copy, Debug, PartialEq, Display)]
pub enum VmInstructionError {
    /// {0}
    Known(KnownVmInstructionError),

    /// Unknown VM-instruction error: {0}
    Unknown(u64),
}

impl PartialEq<KnownVmInstructionError> for VmInstructionError {
    fn eq(&self, other: &KnownVmInstructionError) -> bool {
        if let Self::Known(known_error) = self {
            known_error == other
        } else {
            false
        }
    }
}

impl VmInstructionError {
    pub fn new(error: u64) -> Self {
        if let Some(known_error) = KnownVmInstructionError::from_u64(error) {
            Self::Known(known_error)
        } else {
            Self::Unknown(error)
        }
    }
}

/// A known VM-instruction error.
#[derive(Clone, Copy, Debug, PartialEq, Display, Primitive)]
#[repr(u64)]
pub enum KnownVmInstructionError {
    /// VMCALL executed in VMX root operation
    VmcallInVmxRoot = 1,

    /// VMCLEAR with invalid physical address
    VmclearWithInvalidPhysicalAddr = 2,

    /// VMCLEAR with VMXON pointer
    VmclearWithVmxonPointer = 3,

    /// VMLAUNCH with non-clear VMCS
    VmlaunchWithNonClearVmcs = 4,

    /// VMRESUME with non-launched VMCS
    VmresumeWithNonLaunchedVmcs = 5,

    /// VMRESUME after VMXOFF (VMXOFF and VMXON between VMLAUNCH and VMRESUME)
    VmresumeAfterVmxoff = 6,

    /// VM entry with invalid control field(s)
    VmEntryWithInvalidControlFields = 7,

    /// VM entry with invalid host-state field(s)
    VmEntryWithInvalidHostStateFields = 8,

    /// VMPTRLD with invalid physical address
    VmptrldWithInvalidPhysicalAddr = 9,

    /// VMPTRLD with VMXON pointer
    VmptrldWithVmxonPointer = 10,

    /// VMPTRLD with incorrect VMCS revision identifier
    VmptrldWithIncorrectVmcsRevision = 11,

    /// VMREAD/VMWRITE from/to unsupported VMCS component
    VmcsReadWriteUnsupportedComponent = 12,

    /// VMWRITE to read-only VMCS component
    VmwriteToReadOnlyComponent = 13,

    /// VMXON executed in VMX root operation
    VmxonInVmxRoot = 15,
}

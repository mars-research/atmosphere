use displaydoc::Display;
use enum_primitive_derive::Primitive;
use num_traits::cast::FromPrimitive;

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

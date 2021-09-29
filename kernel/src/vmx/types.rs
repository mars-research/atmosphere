use core::mem;
use core::fmt::{Display, Formatter, Result as FmtResult};
use core::ops::{Deref, DerefMut};

use displaydoc::Display;
use enum_primitive_derive::Primitive;
use num_traits::cast::FromPrimitive;
use x86::bits64::vmx;
use x86::msr;

use super::{VmxResult, VmxError};

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

impl From<VmcsRevision> for u32 {
    fn from(revision: VmcsRevision) -> u32 {
        revision.0
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

/// A set of constraints for bitfield values.
///
/// Intel enforces constraints on VMCS fields to ensure that
/// only configurations supported by the processor can be
/// used. If we violate a constraint, all we get is a super-
/// unhelpful `VmFailValid(7)` ("VM entry with invalid control field(s)").
/// So here we perform the check ourselves and provide useful
/// error messages.
///
/// The constraints can be retrieved from MSRs, with the
/// following layout:
///
/// - Bits 31:0  - If the bit is zero, then the corresponding bit is allowed to be zero.
/// - Bits 63:32 - If the bit is one, then the corresponding bit is allowed to be one.
#[derive(Debug, Clone, PartialEq)]
pub struct BitfieldConstraint {
    /// Name of the VMCS field, for debugging purposes.
    field_name: &'static str,

    /// Constraints for cleared bits (0).
    ///
    /// If the bit is 0, then the corresponding bit is allowed to
    /// be 0.
    /// If the bit is 1, then the corresponding bit must be 1.
    allowed_zero: u32,

    /// Constraints for set bits (1).
    ///
    /// If the bit is 1, then the corresponding bit is allowed to
    /// be 1.
    /// If the bit is 0, then the corresponding bit must be 0.
    allowed_one: u32,
}

impl BitfieldConstraint {
    /// Creates a new constraint from a 64-bit value of an MSR.
    fn new(field_name: &'static str, constraint: u64) -> VmxResult<Self> {
        let allowed_zero = constraint as u32;
        let allowed_one = (constraint >> 32) as u32;

        if (allowed_zero & !allowed_one) != 0 {
            return Err(VmxError::VmcsImpossibleConstraint { constraint });
        }

        Ok(Self {
            field_name,
            allowed_zero,
            allowed_one,
        })
    }

    /// Verifies that the supplied value meets the constraint.
    fn check(&self, value: u32) -> VmxResult<()> {
        if (!value & self.allowed_zero) != 0 || ( value & !self.allowed_one ) != 0 {
            let explain = ExplainBitfieldConstraint {
                constraint: self.clone(),
                value,
            };

            Err(VmxError::VmcsConstraintViolation {
                explain,
            })
        } else {
            Ok(())
        }
    }

    /// Returns a value with the forced bits set to 1.
    fn forced_value(&self) -> u32 {
        self.allowed_zero
    }
}

/// Object that implements Display to explain why a constraint isn't met.
#[derive(Clone, Debug, PartialEq)]
pub struct ExplainBitfieldConstraint {
    constraint: BitfieldConstraint,
    value: u32,
}

impl Display for ExplainBitfieldConstraint {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        if self.constraint.check(self.value).is_ok() {
            return Ok(());
        }

        writeln!(f, "{}", self.constraint.field_name)?;

        {
            let zero_violation = !self.value & self.constraint.allowed_zero;
            self.traverse(f, zero_violation, 1)?;
        }

        {
            let one_violation = self.value & !self.constraint.allowed_one;
            self.traverse(f, one_violation, 0)?;
        }

        Ok(())
    }
}

impl ExplainBitfieldConstraint {
    fn traverse(&self, f: &mut Formatter<'_>, mut violation: u32, must_be: u8) -> FmtResult {
        let mut offset = 0;

        while violation != 0 {
            if violation & 1 != 0 {
                writeln!(f, "Bit {} of {} must be {}",
                    offset,
                    self.constraint.field_name,
                    must_be,
                )?;
            }

            offset += 1;
            violation >>= 1;
        }

        Ok(())
    }
}

/// Low-level struct to manipulate a VMCS field according to a constraint.
pub struct CurrentVmcsField {
    /// ID of the VMCS field.
    vmcs_field: u32,

    /// The constraint.
    constraint: BitfieldConstraint,

    /// Current value.
    value: u32,
}

impl CurrentVmcsField {
    pub unsafe fn new(name: &'static str, vmcs_field: u32, constraint_msr: u32) -> VmxResult<Self> {
        let constraint = {
            let msr_value = msr::rdmsr(constraint_msr);
            BitfieldConstraint::new(name, msr_value)?
        };

        let value = constraint.forced_value();

        Ok(Self {
            constraint,
            vmcs_field,
            value,
        })
    }

    /// Applies the new value after checking that it meets the constraint.
    pub unsafe fn apply(&self) -> VmxResult<()> {
        self.constraint.check(self.value)?;
        vmx::vmwrite(self.vmcs_field, self.value as u64)?;
        Ok(())
    }
}

impl Deref for CurrentVmcsField {
    type Target = u32;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl DerefMut for CurrentVmcsField {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

#[cfg(test)]
mod tests {
    use atest::test;
    use super::*;

    fn get_full_constraint(allowed_zero: u32, allowed_one: u32) -> u64 {
        ((allowed_one as u64) << 32) | (allowed_zero as u64)
    }

    #[test]
    fn test_constraint_split() {
        let msr: u64 = 0x7f00000016;
        let constraint = BitfieldConstraint::new("Pin-Based Controls", msr)
            .expect("The constraint must be valid");
        assert_eq!(constraint.allowed_zero, 0b0010110);
        assert_eq!(constraint.allowed_one, 0b1111111);
    }

    #[test]
    fn test_impossible_constraint() {
        let constraint = get_full_constraint(
            1, // "must be 1"
            0, // "must be 0"
        );
        BitfieldConstraint::new("Impossible Constraint", constraint)
            .expect_err("This bad constraint must not pass validation");
    }

    fn get_simple_constraint() -> BitfieldConstraint {
        let constraint = get_full_constraint(
            0b0000000000011000,
            0b0000000000011111,
        );

        BitfieldConstraint::new("Test Constraint", constraint)
            .expect("The simple constraint must be valid")
    }

    #[test]
    fn test_constraint() {
        let constraint = get_simple_constraint();
        constraint.check(0b0000011111).unwrap();
        constraint.check(0b1111111111)
            .expect_err("Value must fail 1-constraint");
        constraint.check(0b0000000000)
            .expect_err("Value must fail 0-constraint");
    }

    #[test]
    fn test_explain_constraint() {
        let constraint = get_simple_constraint();
        let error = constraint.check(0b1111111111)
            .expect_err("Value must fail 1-constraint");
        log::info!("Returned error (should say that bits 5-9 must be 0): {}", error);
    }
}

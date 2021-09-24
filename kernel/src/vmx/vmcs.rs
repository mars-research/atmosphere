//! VMCS structures.

use core::fmt::{Display, Formatter, Result as FmtResult};
use core::ops::{Deref, DerefMut};

use x86::bits64::paging::PAddr;
use x86::bits64::vmx::vmwrite;
use x86::msr;

use crate::memory::get_physical;
use super::{VmxResult, VmxError};

/// A VMXON region.
///
/// We allocate a VMXON region for each logical core. The allocation
/// is done in compile-time.
///
/// The size of the VMXON region is not defined by the ISA, and is
/// read from the IA32_VMX_BASIC MSR. We make an assumption that
/// it's 4KiB and crash during the initialization process if it's
/// not true.
///
/// The data in the VMXON region is opaque and we do not interact
/// with it at all.
#[repr(align(4096))]
#[repr(C)]
pub struct Vmxon {
    /// The VMCS revision identifier.
    vmcs_revision: u32,

    /// Opaque VMXON data.
    _data: [u8; 4096 - 4],
}

impl Vmxon {
    /// Creates a new VMXON region.
    pub const fn new() -> Self {
        Self {
            vmcs_revision: 0,
            _data: [0; 4096 - 4],
        }
    }

    /// Sets the VMCS revision identifier.
    pub fn set_revision(&mut self, vmcs_revision: u32) {
        self.vmcs_revision = vmcs_revision;
    }

    /// Checks the alignment of the VMXON region.
    pub fn check_alignment(&self) -> VmxResult<()> {
        let addr = self as *const Self as usize;
        if addr % 4096 != 0 {
            Err(VmxError::VmxonBadAlignment { addr })
        } else {
            Ok(())
        }
    }

    /// Returns the physical address of the VMXON region.
    pub fn get_physical(&self) -> PAddr {
        let addr = self as *const Self as usize;
        get_physical(addr.into())
    }
}

/// A VMCS region.
///
/// We allocate a VMCS region for each vCPU. The allocation is
/// handled by the supervisory VM with the capability to re-type
/// an untyped region to VMCS. The VMCS region of the supervisory
/// VM is pre-allocated in compile time.
///
/// The size of the VMCS region is not defined by the ISA, and is
/// read from the IA32_VMX_BASIC MSR. We make an assumption that
/// it's 4KiB and crash during the initialization process if it's
/// not true.
///
/// The data in the VMCS region is opaque and we interact with it
/// using VMREAD/VMWRITE instructions.
#[repr(align(4096))]
#[repr(C)]
pub struct Vmcs {
    /// The VMCS revision identifier.
    vmcs_revision: u32,

    /// The VMX-abort indicator.
    vmx_abort: u32,

    /// Opaque VMXON data.
    _data: [u8; 4096 - 8],
}

impl Vmcs {
    /// Creates a new VMCS region.
    pub const fn new() -> Self {
        Self {
            vmcs_revision: 0,
            vmx_abort: 0,
            _data: [0; 4096 - 8],
        }
    }

    /// Sets the VMCS revision identifier.
    pub fn set_revision(&mut self, vmcs_revision: u32) {
        self.vmcs_revision = vmcs_revision;
    }

    /// Checks the alignment of the VMCS region.
    pub fn check_alignment(&self) -> VmxResult<()> {
        let addr = self as *const Self as usize;
        if addr % 4096 != 0 {
            Err(VmxError::VmcsBadAlignment { addr })
        } else {
            Ok(())
        }
    }

    /// Returns the physical address of the VMCS region.
    pub fn get_physical(&self) -> PAddr {
        let addr = self as *const Self as usize;
        get_physical(addr.into())
    }
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
#[derive(Debug, Clone)]
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
            return Err(VmxError::VmcsBadConstraint { constraint });
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
#[derive(Clone, Debug)]
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
        vmwrite(self.vmcs_field, self.value as u64)?;
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
        log::info!("Returned error: {}", error);
    }
}

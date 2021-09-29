//! VMCS structures.

use core::fmt::{Display, Formatter, Result as FmtResult};
use core::ops::{Deref, DerefMut};
use core::sync::atomic::{AtomicBool, Ordering};

use x86::bits64::paging::PAddr;
use x86::bits64::vmx;
use x86::msr;

use crate::memory::get_physical;
use super::{VmxResult, VmxError};
use super::types::{GuestContext, VmcsRevision};

/// A VMXON region.
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
    vmcs_revision: VmcsRevision,

    /// Opaque VMXON data.
    _data: [u8; 4096 - 4],
}

impl Vmxon {
    /// Creates a new VMXON region.
    pub const fn new() -> Self {
        Self {
            vmcs_revision: VmcsRevision::invalid(),
            _data: [0; 4096 - 4],
        }
    }

    /// Sets the VMCS revision identifier.
    pub fn set_revision(&mut self, vmcs_revision: VmcsRevision) {
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

/// The state of a vCPU.
#[derive(Debug, Clone, PartialEq)]
enum VCpuState {
    /// Uninitialized.
    ///
    /// The VMCS contains garbage data. It has to be initialized
    /// properly by setting the VMCS revision and calling VMCLEAR
    /// on it.
    Uninitialized,

    /// Initialized, but no guest state has been configured.
    Unconfigured,

    /// Ready to be launched or resumed.
    Ready,
}

/// A vCPU.
///
/// FIXME: We need to figure out how this plays with our VM
/// abstraction as well as SMP/parallelization.
#[repr(align(4096))]
pub struct VCpu {
    /// The VMCS region.
    pub vmcs: Vmcs,

    /// The state of the vCPU.
    state: VCpuState,

    /// Whether the vCPU is loaded.
    ///
    /// Currently this is set and unset by the VMM.
    pub loaded: AtomicBool,

    /// The guest register state.
    pub context: GuestContext,
}

impl VCpu {
    /// Creates a new vCPU.
    pub const fn new() -> Self {
        Self {
            vmcs: Vmcs::new(),
            state: VCpuState::Uninitialized,
            loaded: AtomicBool::new(false),
            context: GuestContext::new(),
        }
    }

    /// Initializes the vCPU.
    pub fn init(&mut self, vmcs_revision: VmcsRevision) -> VmxResult<()> {
        if VCpuState::Uninitialized != self.state {
            return Err(VmxError::VCpuAlreadyInitialized);
        }

        self.vmcs.check_alignment()?;
        self.vmcs.init(vmcs_revision)?;

        self.state = VCpuState::Unconfigured;

        Ok(())
    }

    /// Deinitializes the vCPU.
    ///
    /// We need to confirm that this is not currently loaded,
    /// and not part of a VM.
    pub fn deinit(&mut self) -> VmxResult<()> {
        self.check_unloaded()?;

        self.state = VCpuState::Uninitialized;
        self.context = GuestContext::new();

        Ok(())
    }

    /// Returns whether this vCPU is initialized.
    pub fn initialized(&self) -> bool {
        self.state != VCpuState::Uninitialized
    }

    /// Returns whether this vCPU is loaded.
    pub fn loaded(&self) -> bool {
        self.loaded.load(Ordering::SeqCst)
    }

    /// Returns whether this vCPU is ready.
    pub fn ready(&self) -> bool {
        self.state == VCpuState::Ready
    }

    /// Marks this vCPU as configured and ready.
    pub fn mark_ready(&mut self) -> VmxResult<()> {
        if !self.initialized() {
            return Err(VmxError::VCpuNotInitialized);
        }

        if self.state == VCpuState::Ready {
            return Err(VmxError::VCpuAlreadyConfigured);
        }

        self.state = VCpuState::Ready;

        Ok(())
    }

    /// Ensures that this vCPU is not loaded.
    fn check_unloaded(&self) -> VmxResult<()> {
        if self.loaded() {
            return Err(VmxError::VCpuInUse);
        }

        Ok(())
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
    vmcs_revision: VmcsRevision,

    /// The VMX-abort indicator.
    vmx_abort: u32,

    /// Opaque VMXON data.
    _data: [u8; 4096 - 8],
}

impl Vmcs {
    /// Creates a new VMCS region.
    const fn new() -> Self {
        Self {
            vmcs_revision: VmcsRevision::invalid(),
            vmx_abort: 0,
            _data: [0; 4096 - 8],
        }
    }

    /// Initializes the VMCS from scratch.
    fn init(&mut self, vmcs_revision: VmcsRevision) -> VmxResult<()> {
        unsafe {
            vmx::vmclear(self.get_physical().as_u64())?;
        }

        self.vmcs_revision = vmcs_revision;

        Ok(())
    }

    /// Checks the alignment of the VMCS region.
    fn check_alignment(&self) -> VmxResult<()> {
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
    use astd::cell::AtomicRefCell;
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

    #[test]
    fn test_member_alignment() {
        let vmxon = AtomicRefCell::new(Vmxon::new());
        vmxon.borrow().check_alignment().unwrap();
    }
}

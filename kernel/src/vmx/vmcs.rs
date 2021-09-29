//! VMCS structures.

use core::sync::atomic::{AtomicBool, Ordering};

use x86::bits64::paging::PAddr;
use x86::bits64::vmx;

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

#[cfg(test)]
mod tests {
    use astd::cell::AtomicRefCell;
    use atest::test;
    use super::*;

    #[test]
    fn test_member_alignment() {
        let vmxon = AtomicRefCell::new(Vmxon::new());
        vmxon.borrow().check_alignment().unwrap();
    }
}

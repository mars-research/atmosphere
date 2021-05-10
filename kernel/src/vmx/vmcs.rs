//! VMCS structures.

use x86::bits64::paging::PAddr;

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

//! Intel VT-x support.
//!
//! Intel SDM Volume 3C:
//! <https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-3c-part-3-manual.pdf>

pub mod vmcs;

use core::mem;

use bit_field::BitField;
use snafu::Snafu;
use x86::bits64::vmx::{self, vmwrite};
use x86::cpuid::CpuId;
use x86::msr;
use x86::vmx::vmcs::ro::VM_INSTRUCTION_ERROR;
/*
use x86::segmentation as x86_seg;
use x86::vmx::vmcs::host::{
    ES_SELECTOR as HOST_ES_SELECTOR,
    CS_SELECTOR as HOST_CS_SELECTOR,
    SS_SELECTOR as HOST_SS_SELECTOR,
    DS_SELECTOR as HOST_DS_SELECTOR,
    FS_SELECTOR as HOST_FS_SELECTOR,
    GS_SELECTOR as HOST_GS_SELECTOR,
    TR_SELECTOR as HOST_TR_SELECTOR,
};
*/

use astd::sync::{Mutex, RwLock};
use vmcs::{Vmcs, Vmxon};

type VmxResult<T, E = VmxError> = core::result::Result<T, E>;

/// A virtualization error.
///
/// The naming of the variants are subject to change.
#[non_exhaustive]
#[derive(Clone, Debug, Snafu)]
pub enum VmxError {
    #[snafu(display("The platform does not support VT-x."))]
    VmxUnsupported,

    #[snafu(display("The platform supports VT-x, but is disabled in BIOS."))]
    VmxDisabled,

    #[snafu(display("The VMCS region size {} is not supported.", size))]
    UnsupportedVmcsSize { size: usize },

    #[snafu(display("The VMXON region at {:#x} has bad alignment. It must be 4KiB aligned.", addr))]
    VmxonBadAlignment { addr: usize },

    #[snafu(display("The VMCS region at {:#x} has bad alignment. It must be 4KiB aligned.", addr))]
    VmcsBadAlignment { addr: usize },

    #[snafu(display("The VMM has already started."))]
    VmmAlreadyStarted,

    #[snafu(display("The VMM has not started."))]
    VmmNotStarted,

    #[snafu(display("There is no current VMCS loaded."))]
    NoCurrentVmcs,

    #[snafu(display("The VMCS pointer is not valid."))]
    VmcsPtrInvalid,

    #[snafu(display("The VMCS pointer is valid, but some other error was encountered."))]
    VmcsPtrValid,

    #[snafu(display("VM-Instruction error: {:?}.", error))]
    InstructionError { error: VmxInstructionError },
}

impl From<x86::vmx::VmFail> for VmxError {
    fn from(vmfail: x86::vmx::VmFail) -> Self {
        use x86::vmx::VmFail::*;

        match vmfail {
            VmFailValid => Self::VmcsPtrValid,
            VmFailInvalid => Self::VmcsPtrInvalid,
        }
    }
}

/// A VM-instruction error.
///
/// See Intel SDM, Volume 3C, Chapter 30.4.
#[allow(dead_code)]
#[non_exhaustive]
#[derive(Clone, Copy, Debug)]
pub enum VmxInstructionError {
    /// VMCALL executed in VMX root operation
    VmcallInVmxRoot,

    /// VMCLEAR with invalid physical address
    VmclearWithInvalidPhysicalAddr,

    /// VMCLEAR with VMXON pointer
    VmclearWithVmxonPointer,

    /// VMLAUNCH with non-clear VMCS
    VmlaunchWithNonClearVmcs,

    /// VMRESUME with non-launched VMCS
    VmresumeWithNonLaunchedVmcs,

    /// VMRESUME after VMXOFF (VMXOFF and VMXON between VMLAUNCH and VMRESUME)
    VmresumeAfterVmxoff,

    /// VM entry with invalid control field(s)
    VmEntryWithInvalidControlFields,

    /// VM entry with invalid host-state field(s)
    VmEntryWithInvalidHostStateFields,

    /// VMPTRLD with invalid physical address
    VmptrldWithInvalidPhysicalAddr,

    /// VMPTRLD with VMXON pointer
    VmptrldWithVmxonPointer,

    /// VMPTRLD with incorrect VMCS revision identifier
    VmptrldWithIncorrectVmcsRevision,

    /// VMREAD/VMWRITE from/to unsupported VMCS component
    VmcsReadWriteUnsupportedComponent,

    /// VMWRITE to read-only VMCS component
    VmwriteToReadOnlyComponent,

    /// VMXON executed in VMX root operation
    VmxonInVmxRoot,

    /// Unknown error
    Unknown(u32),
}

impl From<u32> for VmxInstructionError {
    fn from(error: u32) -> Self {
        use VmxInstructionError::*;
        match error {
            1  => VmcallInVmxRoot,
            2  => VmclearWithInvalidPhysicalAddr,
            3  => VmclearWithVmxonPointer,
            4  => VmlaunchWithNonClearVmcs,
            5  => VmresumeWithNonLaunchedVmcs,
            6  => VmresumeAfterVmxoff,
            7  => VmEntryWithInvalidControlFields,
            8  => VmEntryWithInvalidHostStateFields,
            9  => VmptrldWithInvalidPhysicalAddr,
            10 => VmptrldWithVmxonPointer,
            11 => VmptrldWithIncorrectVmcsRevision,
            12 => VmcsReadWriteUnsupportedComponent,
            13 => VmwriteToReadOnlyComponent,
            15 => VmxonInVmxRoot,
            _  => Unknown(error),
        }
    }
}

impl Into<u32> for VmxInstructionError {
    fn into(self) -> u32 {
        use VmxInstructionError::*;
        match self {
            VmcallInVmxRoot                     => 1,
            VmclearWithInvalidPhysicalAddr      => 2,
            VmclearWithVmxonPointer             => 3,
            VmlaunchWithNonClearVmcs            => 4,
            VmresumeWithNonLaunchedVmcs         => 5,
            VmresumeAfterVmxoff                 => 6,
            VmEntryWithInvalidControlFields     => 7,
            VmEntryWithInvalidHostStateFields   => 8,
            VmptrldWithInvalidPhysicalAddr      => 9,
            VmptrldWithVmxonPointer             => 10,
            VmptrldWithIncorrectVmcsRevision    => 11,
            VmcsReadWriteUnsupportedComponent   => 12,
            VmwriteToReadOnlyComponent          => 13,
            VmxonInVmxRoot                      => 15,
            Unknown(error)                      => error,
        }
    }
}

/// VT-x platform information.
#[derive(Clone, Debug)]
pub struct PlatformInfo {
    /// The VMCS revision identifier.
    vmcs_revision: u32,

    /// Size of VMXON/VMCS regions.
    ///
    /// We only support 4KiB (4096).
    vmcs_size: usize,
}

/// Returns VT-x platform information.
///
/// Returns `None` if VT-x is not available.
pub fn get_platform_info() -> Option<PlatformInfo> {
    // Check CPUID VMX bit
    let cpuid = CpuId::new();
    let feature_info = cpuid.get_feature_info()?;

    if !feature_info.has_vmx() {
        return None;
    }

    // Check VMXON/VMCS region size
    let vmx_basic = unsafe { msr::rdmsr(msr::IA32_VMX_BASIC) };
    let vmcs_revision = vmx_basic.get_bits(0..32) as u32;
    let vmcs_size = vmx_basic.get_bits(32..45) as usize;

    if vmcs_size != 4096 {
        log::warn!("Platform requires the VMXON/VMCS regions to be of size {} which we do not support.", vmcs_size);
    }

    Some(PlatformInfo {
        vmcs_revision,
        vmcs_size,
    })
}

/// A Virtual Machine Monitor (VMM).
///
/// Here we keep track of all states related to the VMM running
/// on one physical logical core.
///
/// All methods must be called on the correct CPU.
pub struct Monitor<'a> {
    /// Whether VMX operations are enabled.
    enabled: RwLock<bool>,

    /// The VMCS revision identifier.
    vmcs_revision: u32,

    /// The VMXON region.
    vmxon: &'a mut Vmxon,

    /// The current VMCS.
    current_vmcs: Mutex<Option<&'a mut Vmcs>>,
}

impl<'a> Monitor<'a> {
    /// Creates a new VMM.
    pub fn new(vmxon: &'a mut Vmxon) -> Self {
        Self {
            enabled: RwLock::new(false),
            vmcs_revision: 0,
            vmxon,
            current_vmcs: Mutex::new(None),
        }
    }

    /// Initializes the VMM and enters VMX root operation mode.
    pub unsafe fn start(&mut self) -> VmxResult<()> {
        let mut vmx_enabled = self.enabled.write();
        if *vmx_enabled {
            return Err(VmxError::VmmAlreadyStarted);
        }

        let platform_info = get_platform_info()
            .ok_or(VmxError::VmxUnsupported)?;

        self.vmcs_revision = platform_info.vmcs_revision;

        if platform_info.vmcs_size != mem::size_of::<vmcs::Vmcs>() {
            return Err(VmxError::UnsupportedVmcsSize { size: platform_info.vmcs_size });
        }

        // Check the IA32_VMX_CR{0,4}_FIXED{0,1} MSRs
        //
        // We need to set the specified bits in CR0 and CR0 prior to
        // entering VMX operation.
        //
        // The names of the MSRs are pretty confusing. Intel SDM has the following:
        //
        // > If bit X is 1 in IA32_VMX_CR0_FIXED0, then that bit of CR0 is fixed to 1
        // > in VMX operation. Similarly, if bit X is 0 in IA32_VMX_CR0_FIXED1, then that
        // > bit of CR0 is fixed to 0 in VMX operation. It is always the case that, if
        // > bit X is 1 in IA32_VMX_CR0_FIXED0, then that bit is also 1 in IA32_VMX_CR0_FIXED1;
        // > if bit X is 0 in IA32_VMX_CR0_FIXED1, then that bit is also 0 in IA32_VMX_CR0_FIXED0.
        // > Thus, each bit in CR0 is either fixed to 0 (with value 0 in both MSRs), fixed to
        // > 1 (1 in both MSRs), or flexible (0 in IA32_VMX_CR0_FIXED0 and 1 in
        // > IA32_VMX_CR0_FIXED1).
        //
        // Thus, in boolean logic, to compute the new value of a register:
        //
        // ```
        // new = (old | fixed0) & fixed1
        // ```
        let cr0_fixed0 = msr::rdmsr(msr::IA32_VMX_CR0_FIXED0) as u32;
        let cr0_fixed1 = msr::rdmsr(msr::IA32_VMX_CR0_FIXED1) as u32;
        write_cr0((read_cr0() | cr0_fixed0) & cr0_fixed1);

        let cr4_fixed0 = msr::rdmsr(msr::IA32_VMX_CR4_FIXED0) as u32;
        let cr4_fixed1 = msr::rdmsr(msr::IA32_VMX_CR4_FIXED1) as u32;
        write_cr4((read_cr4() | cr4_fixed0) & cr4_fixed1);

        // Check the IA32_FEATURE_CONTROL MSR
        //
        // We only care about the 3 least significant bits.
        let mut feature_control = msr::rdmsr(msr::IA32_FEATURE_CONTROL);
        let lock_bit = feature_control.get_bit(0);

        if !lock_bit {
            // Commonly, the BIOS sets the MSR then locks it with this bit,
            // but somehow it's not set here. Let's enable VMXON outside SMX
            // operation then lock the MSR.
            log::warn!("Lock bit in IA32_FEATURE_CONTROL is clear. Enabling VMXON outside SMX and locking...");
            feature_control.set_bit(2, true); // VMXON outside SMX operation
            feature_control.set_bit(0, true); // Lock
            msr::wrmsr(msr::IA32_FEATURE_CONTROL, feature_control);
        }

        if !feature_control.get_bit(2) {
            return Err(VmxError::VmxDisabled);
        }

        // Check VMXON alignment
        self.vmxon.check_alignment()?;

        // Enter VMX operation
        //
        // FIXME: Error reporting
        self.vmxon.set_revision(self.vmcs_revision);
        vmx::vmxon(self.vmxon.get_physical().as_u64()).unwrap();

        *vmx_enabled = true;

        Ok(())
    }

    /// Leaves VMX operation and stops the VMM.
    pub unsafe fn stop(&mut self) -> VmxResult<()> {
        let mut vmx_enabled = self.enabled.write();
        if !*vmx_enabled {
            return Err(VmxError::VmmNotStarted);
        }

        // Leave VMX operation
        //
        // FIXME: Error reporting
        vmx::vmxoff().unwrap();
        *vmx_enabled = false;

        Ok(())
    }

    /// Loads the specified VMCS and make it the current VMCS.
    pub unsafe fn load_vmcs(&mut self, vmcs: &'a mut Vmcs) -> VmxResult<()> {
        self.check_vmm_started()?;

        let mut current_vmcs = self.current_vmcs.lock();

        // Check VMCS alignment
        vmcs.check_alignment()?;

        // Load VMCS
        vmx::vmptrld(vmcs.get_physical().as_u64()).unwrap();

        *current_vmcs = Some(vmcs);

        Ok(())
    }

    /// Low-level method to initialize the currently-loaded VMCS.
    pub unsafe fn init_vmcs(&mut self) -> VmxResult<()> {
        use x86::vmx::vmcs::control::{
            PINBASED_EXEC_CONTROLS,
            PRIMARY_PROCBASED_EXEC_CONTROLS,
            EXCEPTION_BITMAP,
            VMEXIT_CONTROLS,
        };

        self.check_vmm_started()?;

        let current_vmcs = self.current_vmcs.lock();
        if current_vmcs.is_none() {
            return Err(VmxError::VmcsPtrInvalid);
        }

        // Set Pin-Based VM-Execution Controls.
        //
        // The value of the IA32_VMX_PINBASED_CTLS capability MSR specifies the allowed/supported settings.
        // This is like the CR0_FIXED MSRs we use in start(). Intel SDM Vol. 3D A.3.1 has
        // the details, but the basic idea is:
        // - Bits 31:0  - If the bit is zero, then the corresponding bit is allowed to be zero.
        // - Bits 63:32 - If the bit is one, then the corresponding bit is allowed to be one.
        //
        // See Intel SDM Vol. 3C 24.6.1 for the bitfield definition.
        {
            let pinbased_ctrl_msr = msr::rdmsr(msr::IA32_VMX_PINBASED_CTLS);
            let allowed_zero = pinbased_ctrl_msr as u32;
            let allowed_one = (pinbased_ctrl_msr >> 32) as u32;

            // FIXME: Make this configurable
            let pinbased_ctrl = allowed_zero & allowed_one;
            vmwrite(PINBASED_EXEC_CONTROLS, pinbased_ctrl as u64)?;
        }

        // Set Processor-Based VM-Execution Controls.
        //
        // Similar to above.
        // See Intel SDM Vol. 3C 24.6.2 for the bitfield definition.
        {
            let procbased_ctrl_msr = msr::rdmsr(msr::IA32_VMX_PROCBASED_CTLS);
            let allowed_zero = procbased_ctrl_msr as u32;
            let allowed_one = (procbased_ctrl_msr >> 32) as u32;

            // FIXME: Make this configurable
            let mut procbased_ctrl = allowed_zero & allowed_one;

            // Disable secondary control
            procbased_ctrl.set_bit(31, false); // "Activate secondary controls"

            vmwrite(PRIMARY_PROCBASED_EXEC_CONTROLS, procbased_ctrl as u64)?;
        }

        // Set Exception Bitmap
        //
        // A 32-bit bitfield with each bit corresponding to an exception.
        // VM exits will occur for exceptions with their bits set to 1.
        // See Intel SDM Vol. 3C 24.6.3 for more explanation.
        {
            // FIXME: Specify reasonable defaults
            vmwrite(EXCEPTION_BITMAP, 0)?;
        }

        // Set VM-Exit Control
        //
        // See Intel SDM Vol. 3C 24.7.1.
        {
            let exit_ctrl_msr = msr::rdmsr(msr::IA32_VMX_EXIT_CTLS);
            let allowed_zero = exit_ctrl_msr as u32;
            // let allowed_one = (exit_ctrl_msr >> 32) as u32;

            let mut exit_ctrl = allowed_zero;
            exit_ctrl.set_bit(9, true); // "Host address-space size" - We want the processor to be in 64-bit mode on exit

            vmwrite(VMEXIT_CONTROLS, 0)?;
        }

        // Set VM-Entry Control
        //
        // See Intel SDM Vol. 3C 24.8.1.
        {
            let entry_ctrl_msr = msr::rdmsr(msr::IA32_VMX_ENTRY_CTLS);
            let allowed_zero = entry_ctrl_msr as u32;
            // let allowed_one = (entry_ctrl_msr >> 32) as u32;

            let mut entry_ctrl = allowed_zero;
            entry_ctrl.set_bit(9, true); // "A-32e mode guest"

            vmwrite(VMEXIT_CONTROLS, 0)?;
        }

        Ok(())
    }

    /*
    /// Low-level method to launch/resume the current VMCS.
    pub unsafe fn low_level_launch(&mut self) -> VmxResult<()> {
        // Save host state into VMCS

        // The 3 least significant bits must be zero.
        let selector_mask = 0b11111000;
        vmwrite(HOST_CS_SELECTOR, (x86_seg::cs().bits() & selector_mask) as u64)?;
        vmwrite(HOST_ES_SELECTOR, (x86_seg::es().bits() & selector_mask) as u64)?;
        vmwrite(HOST_SS_SELECTOR, (x86_seg::ss().bits() & selector_mask) as u64)?;
        vmwrite(HOST_DS_SELECTOR, (x86_seg::ds().bits() & selector_mask) as u64)?;

        vmwrite(HOST_FS_SELECTOR, (x86_seg::fs().bits() & selector_mask) as u64)?;
        vmwrite(HOST_GS_SELECTOR, (x86_seg::gs().bits() & selector_mask) as u64)?;

        vmwrite(HOST_TR_SELECTOR, (x86::task::tr().bits() & selector_mask) as u64)?;
        unimplemented!()
    }
    */

    /// Returns the VMCS revision identifier.
    pub fn get_vmcs_revision(&self) -> u32 {
        self.vmcs_revision
    }

    /// Reads the VM-instruction error field of the current VMCS.
    pub fn get_vm_instruction_error(&self) -> VmxResult<Option<u32>> {
        self.check_vmm_started()?;

        {
            let current_vmcs = self.current_vmcs.lock();
            if current_vmcs.is_none() {
                return Err(VmxError::NoCurrentVmcs);
            }
        }

        let error = unsafe { vmx::vmread(VM_INSTRUCTION_ERROR).map_err::<VmxError, _>(|e| e.into())? as u32 };

        Ok(Some(error.into()))
    }

    /// Checks that the VMM has started.
    fn check_vmm_started(&self) -> VmxResult<()> {
        let vmx_enabled = self.enabled.read();
        if !*vmx_enabled {
            return Err(VmxError::VmmNotStarted);
        }

        Ok(())
    }
}


/// Reads the value of CR0.
pub unsafe fn read_cr0() -> u32 {
    let val: u32;
    asm!("mov {0:r}, cr0", out(reg) val);
    val
}

/// Writes a value into CR0.
pub unsafe fn write_cr0(val: u32) {
    asm!("mov cr0, {0:r}", in(reg) val);
}

/// Reads the value of CR4.
pub unsafe fn read_cr4() -> u32 {
    let val: u32;
    asm!("mov {0:r}, cr4", out(reg) val);
    val
}

/// Writes a value into CR4.
pub unsafe fn write_cr4(val: u32) {
    asm!("mov cr4, {0:r}", in(reg) val);
}

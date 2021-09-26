//! Intel VT-x support.
//!
//! Intel SDM Volume 3C:
//! <https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-3c-part-3-manual.pdf>
//!
//! ## Debugging VT-x Problems
//!
//! Bochs errors:
//!
//! - Descriptors: Check `bx_descriptor_t` in `cpu/descriptor.h`.

pub mod vmcs;

use core::mem;

use snafu::Snafu;
use x86::bits64::rflags::{read as read_rflags, RFlags};
use x86::bits64::vmx;
use x86::cpuid::CpuId;
use x86::msr;
// use x86::vmx::vmcs::ro::VM_INSTRUCTION_ERROR;
use x86::vmx::vmcs::control;

use astd::sync::{Mutex, RwLock};
use vmcs::{CurrentVmcsField, Vmcs, Vmxon, ExplainBitfieldConstraint};
use crate::cpu;
use crate::gdt::TaskStateSegment;

type VmxResult<T, E = VmxError> = core::result::Result<T, E>;

static GUEST_STACK: [u8; 4096] = [0u8; 4096];

macro_rules! copy_host_state {
    ($x:ident) => {
        {
            use x86::vmx::vmcs::{guest, host};
            (true, host::$x, guest::$x)
        }
    };
    ($cond:expr, $x:ident) => {
        {
            use x86::vmx::vmcs::{guest, host};
            ($cond, host::$x, guest::$x)
        }
    };
}


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

    #[snafu(display("VMCS constraint violation: {}", explain))]
    VmcsConstraintViolation { explain: ExplainBitfieldConstraint },

    #[snafu(display("VMCS bad constraint: {:#x?}", constraint))]
    VmcsBadConstraint { constraint: u64 },

    #[snafu(display("Other VMCS error: {}", error))]
    VmcsOtherError { error: &'static str },

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
#[derive(Clone, Copy, Debug, PartialEq)]
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
    use pal::msr::ia32_vmx_basic;

    // Check CPUID VMX bit
    let cpuid = CpuId::new();
    let feature_info = cpuid.get_feature_info()?;

    if !feature_info.has_vmx() {
        return None;
    }

    // Check VMXON/VMCS region size
    let msr = ia32_vmx_basic::get();
    let vmcs_revision = ia32_vmx_basic::get_revision_id_from_value(msr) as u32;
    let vmcs_size = ia32_vmx_basic::get_vmxon_vmcs_region_size_from_value(msr) as usize;

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
        {
            use pal::msr::ia32_feature_control::*;

            let mut feature_control = get();

            if lock_bit_is_disabled_in_value(feature_control) {
                // Commonly, the BIOS sets the MSR then locks it with this bit,
                // but somehow it's not set here. Let's enable VMXON outside SMX
                // operation then lock the MSR.
                log::warn!("Lock bit in IA32_FEATURE_CONTROL is clear. Enabling VMXON outside SMX and locking...");
                enable_enable_vmx_outside_smx_in_value(&mut feature_control);
                enable_lock_bit_in_value(&mut feature_control);
                set(feature_control);
            }

            if !enable_vmx_outside_smx_is_enabled() {
                return Err(VmxError::VmxDisabled);
            }
        }

        // Check VMXON alignment
        self.vmxon.check_alignment()?;

        // Enter VMX operation
        self.vmxon.set_revision(self.vmcs_revision);
        vmx::vmxon(self.vmxon.get_physical().as_u64())?;

        *vmx_enabled = true;

        Ok(())
    }

    /// Leaves VMX operation and stops the VMM.
    pub fn stop(&mut self) -> VmxResult<()> {
        let mut vmx_enabled = self.enabled.write();
        if !*vmx_enabled {
            return Err(VmxError::VmmNotStarted);
        }

        // Leave VMX operation
        unsafe {
            vmx::vmxoff()?;
        }
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

    /// Test method to initialize and launch an unconfined VM.
    pub unsafe fn demo_launch(&mut self) -> VmxResult<()> {
        self.check_vmcs_loaded()?;

        self.init_vmcs_controls()?;
        self.save_vmcs_host_state()?;
        self.init_vmcs_guest_state()?;
        self.copy_vmcs_host_state_to_guest()?;

        let stack_end = (&GUEST_STACK as *const u8).offset(4096) as u64;
        let target = demo_guest_main as *const () as u64;

        self.set_vmcs_guest_entrypoint(target, stack_end)?;

        self.launch_current(false)?;

        Ok(())
    }

    /// Initializes VMCS control fields.
    unsafe fn init_vmcs_controls(&mut self) -> VmxResult<()> {
        self.check_vmcs_loaded()?;

        // Set Pin-Based VM-Execution Controls.
        {
            use pal::msr::ia32_vmx_basic::true_based_controls_is_enabled;
            use pal::vmcs::pin_based_vm_execution_controls::*;

            let msr = if true_based_controls_is_enabled() {
                msr::IA32_VMX_TRUE_PINBASED_CTLS
            } else {
                msr::IA32_VMX_PINBASED_CTLS
            };

            let mut value = CurrentVmcsField::new(
                "Pin-Based VM-Execution Controls",
                control::PINBASED_EXEC_CONTROLS,
                msr,
            )?;

            enable_nmi_exiting_in_value(&mut value);

            value.apply()?;
        }

        // Set Processor-Based VM-Execution Controls.
        //
        // Similar to above.
        // See Intel SDM Vol. 3C 24.6.2 for the bitfield definition.
        {
            use pal::vmcs::primary_processor_based_vm_execution_controls::*;

            let mut value = CurrentVmcsField::new(
                "Primary Processor-Based VM-Execution Controls",
                control::PRIMARY_PROCBASED_EXEC_CONTROLS,
                msr::IA32_VMX_PROCBASED_CTLS,
            )?;

            disable_activate_secondary_controls_in_value(&mut value);

            value.apply()?;
        }

        // Set VM-Exit Controls.
        //
        // See Intel SDM Vol. 3C 24.7.1.
        {
            use pal::vmcs::vm_exit_controls::*;

            let mut value = CurrentVmcsField::new(
                "VM-Exit Controls",
                control::VMEXIT_CONTROLS,
                msr::IA32_VMX_EXIT_CTLS,
            )?;

            // We want the processor to be in 64-bit mode on exit
            enable_host_address_space_size_in_value(&mut value);

            // FIXME: Detect the availability of those features.
            enable_load_ia32_efer_in_value(&mut value);
            enable_load_ia32_pat_in_value(&mut value);

            value.apply()?;
        }

        // Set VM-Entry Control
        //
        // See Intel SDM Vol. 3C 24.8.1.
        {
            use pal::vmcs::vm_entry_controls::*;

            let mut value = CurrentVmcsField::new(
                "VM-Entry Controls",
                control::VMENTRY_CONTROLS,
                msr::IA32_VMX_ENTRY_CTLS,
            )?;

            enable_ia_32e_mode_guest_in_value(&mut value);

            // FIXME: Detect the availability of those features.
            enable_load_ia32_efer_in_value(&mut value);
            enable_load_ia32_pat_in_value(&mut value);

            value.apply()?;
        }

        Ok(())
    }

    /// Initializes the VMCS Guest-State Area.
    unsafe fn init_vmcs_guest_state(&self) -> VmxResult<()> {
        self.check_vmcs_loaded()?;

        // ## Register State

        // Limits
        // If G(Granularity) = 0, then we must mask out the higher bits
        let unlimited = u32::MAX as u64 & !0xfff00000;
        vmx::vmwrite(CS_LIMIT, unlimited)?;
        vmx::vmwrite(SS_LIMIT, unlimited)?;
        vmx::vmwrite(DS_LIMIT, unlimited)?;
        vmx::vmwrite(ES_LIMIT, unlimited)?;
        vmx::vmwrite(FS_LIMIT, unlimited)?;
        vmx::vmwrite(GS_LIMIT, unlimited)?;
        vmx::vmwrite(LDTR_LIMIT, unlimited)?;
        vmx::vmwrite(TR_LIMIT, mem::size_of::<TaskStateSegment>() as u64)?;

        vmx::vmwrite(GDTR_LIMIT, 0xffff)?;
        vmx::vmwrite(IDTR_LIMIT, 0xffff)?;

        // Access Rights
        // Attention: Here we disable all access. This must be initialized
        // correctly before the machine can be started.
        //
        // TODO: Implement a builder interface that can be shared between
        //       here and gdt.
        vmx::vmwrite(CS_ACCESS_RIGHTS, 0b10000000000000000)?;
        vmx::vmwrite(SS_ACCESS_RIGHTS, 0b10000000000000000)?;
        vmx::vmwrite(DS_ACCESS_RIGHTS, 0b10000000000000000)?;
        vmx::vmwrite(ES_ACCESS_RIGHTS, 0b10000000000000000)?;
        vmx::vmwrite(FS_ACCESS_RIGHTS, 0b10000000000000000)?;
        vmx::vmwrite(GS_ACCESS_RIGHTS, 0b10000000000000000)?;
        vmx::vmwrite(LDTR_ACCESS_RIGHTS, 0b10000000000000000)?;
        vmx::vmwrite(TR_ACCESS_RIGHTS, 0b10000000000000000)?;

        // ## Non-register State
        use x86::vmx::vmcs::guest::*;
        use pal::vmcs::secondary_processor_based_vm_execution_controls::{
            vmcs_shadowing_is_enabled,
            enable_pml_is_enabled,
        };

        vmx::vmwrite(ACTIVITY_STATE, 0)?;

        // Only has an effect when Virtual Interrupt Delivery is enabled
        vmx::vmwrite(INTERRUPT_STATUS, 0)?;

        // Only has an effect when VMX Preemption Timer is enabled
        vmx::vmwrite(VMX_PREEMPTION_TIMER_VALUE, 0)?;

        // TODO: Support this for performance gain in nested virtualization
        if vmcs_shadowing_is_enabled() {
            return Err(VmxError::VmcsOtherError {
                error: "VMCS Shadowing is not implemented",
            });
        } else {
            vmx::vmwrite(LINK_PTR_FULL, 0xffff_ffff_ffff_ffff)?;
        }

        // TODO: Investigate this
        if enable_pml_is_enabled() {
            return Err(VmxError::VmcsOtherError {
                error: "Page-Modification Logging is not implemented",
            });
        } else {
            // vmx::vmwrite(PML_INDEX, 0)?;
        }

        Ok(())
    }

    /// Saves the current host state to the Host-State Area.
    unsafe fn save_vmcs_host_state(&self) -> VmxResult<()> {
        // See Intel SDM, Volume 3C, Chapter 24.5.

        self.check_vmcs_loaded()?;

        use pal::vmcs::vm_exit_controls::*;
        use x86::segmentation as seg;
        use x86::controlregs as ctl;
        use x86::vmx::vmcs::host::*;

        // > Selector fields (16 bits each) for the segment registers
        // > CS, SS, DS, ES, FS, GS, and TR.
        let selector_mask = 0b11111000;
        vmx::vmwrite(CS_SELECTOR, (seg::cs().bits() & selector_mask) as u64)?;
        vmx::vmwrite(SS_SELECTOR, (seg::ss().bits() & selector_mask) as u64)?;
        vmx::vmwrite(DS_SELECTOR, (seg::ds().bits() & selector_mask) as u64)?;
        vmx::vmwrite(ES_SELECTOR, (seg::es().bits() & selector_mask) as u64)?;

        vmx::vmwrite(FS_SELECTOR, (seg::fs().bits() & selector_mask) as u64)?;
        vmx::vmwrite(GS_SELECTOR, (seg::gs().bits() & selector_mask) as u64)?;
        vmx::vmwrite(TR_SELECTOR, (x86::task::tr().bits() & selector_mask) as u64)?;

        // > Base-address fields for FS, GS, TR, GDTR, and IDTR (64 bits
        // > each; 32 bits on processors that do not support Intel 64
        // > architecture)."
        vmx::vmwrite(FS_BASE, msr::rdmsr(msr::IA32_FS_BASE))?;
        vmx::vmwrite(GS_BASE, msr::rdmsr(msr::IA32_GS_BASE))?;

        let (tr_base, gdt_base) = {
            let cpu = cpu::get_current();
            (&cpu.tss as *const _ as u64, &cpu.gdt as *const _ as u64)
        };
        vmx::vmwrite(TR_BASE, tr_base)?;
        vmx::vmwrite(GDTR_BASE, gdt_base)?;
        vmx::vmwrite(IDTR_BASE, read_idt_base())?;

        // > CR0, CR3, and CR4 (64 bits each; 32 bits on processors that
        // > do not support Intel 64 architecture).
        vmx::vmwrite(CR0, read_cr0() as u64)?;
        vmx::vmwrite(CR3, ctl::cr3())?;
        vmx::vmwrite(CR4, read_cr4() as u64)?;

        // > The following MSRs:
        // > - IA32_SYSENTER_CS (32 bits)
        // > - IA32_SYSENTER_ESP and IA32_SYSENTER_EIP
        // > - IA32_PERF_GLOBAL_CTRL
        // > - IA32_PAT
        // > - IA32_EFER

        // FIXME: Detect the availability of those features.
        vmx::vmwrite(IA32_SYSENTER_CS, msr::rdmsr(msr::IA32_SYSENTER_CS))?;
        vmx::vmwrite(IA32_SYSENTER_ESP, msr::rdmsr(msr::IA32_SYSENTER_ESP))?;
        vmx::vmwrite(IA32_SYSENTER_EIP, msr::rdmsr(msr::IA32_SYSENTER_EIP))?;

        if load_ia32_perf_global_ctrl_is_enabled() {
            vmx::vmwrite(IA32_PERF_GLOBAL_CTRL_FULL, msr::rdmsr(msr::IA32_PERF_GLOBAL_CTRL))?;
        }

        if load_ia32_efer_is_enabled() {
            vmx::vmwrite(IA32_EFER_FULL, msr::rdmsr(msr::IA32_EFER))?;
        }

        if load_ia32_pat_is_enabled() {
            vmx::vmwrite(IA32_PAT_FULL, msr::rdmsr(msr::IA32_PAT))?;
        }

        Ok(())
    }

    /// Copies values from the Host-State Area to the Guest-State Area.
    unsafe fn copy_vmcs_host_state_to_guest(&self) -> VmxResult<()> {
        use pal::vmcs::vm_entry_controls::*;
        use x86::vmx::vmcs::guest::{
            RFLAGS as GUEST_RFLAGS,

            CS_ACCESS_RIGHTS,
            SS_ACCESS_RIGHTS,
            DS_ACCESS_RIGHTS,
            ES_ACCESS_RIGHTS,
            FS_ACCESS_RIGHTS,
            GS_ACCESS_RIGHTS,
            TR_ACCESS_RIGHTS,
        };

        self.check_vmcs_loaded()?;

        // Copy required host state
        let to_copy = [
            // > Selector fields (16 bits each) for the segment registers
            // > CS, SS, DS, ES, FS, GS, and TR.
            copy_host_state!(CS_SELECTOR),
            copy_host_state!(SS_SELECTOR),
            copy_host_state!(DS_SELECTOR),
            copy_host_state!(ES_SELECTOR),

            copy_host_state!(FS_SELECTOR),
            copy_host_state!(GS_SELECTOR),

            copy_host_state!(TR_SELECTOR),

            // > Base-address fields for FS, GS, TR, GDTR, and IDTR (64 bits
            // > each; 32 bits on processors that do not support Intel 64
            // > architecture)."
            copy_host_state!(FS_BASE),
            copy_host_state!(GS_BASE),
            copy_host_state!(TR_BASE),

            copy_host_state!(GDTR_BASE),
            copy_host_state!(IDTR_BASE),

            // > CR0, CR3, and CR4 (64 bits each; 32 bits on processors that
            // > do not support Intel 64 architecture).
            copy_host_state!(CR0),
            copy_host_state!(CR3),
            copy_host_state!(CR4),

            // > The following MSRs:
            // > - IA32_SYSENTER_CS (32 bits)
            // > - IA32_SYSENTER_ESP and IA32_SYSENTER_EIP
            // > - IA32_PERF_GLOBAL_CTRL
            // > - IA32_PAT
            // > - IA32_EFER

            // FIXME: Detect the availability of those features.
            copy_host_state!(IA32_SYSENTER_CS),
            copy_host_state!(IA32_SYSENTER_ESP),
            copy_host_state!(IA32_SYSENTER_EIP),

            // Conditional on whether we load those registers
            // on VM entry
            copy_host_state!(
                load_ia32_perf_global_ctrl_is_enabled(),
                IA32_PERF_GLOBAL_CTRL_FULL
            ),
            copy_host_state!(
                load_ia32_efer_is_enabled(),
                IA32_EFER_FULL
            ),
            copy_host_state!(
                load_ia32_pat_is_enabled(),
                IA32_PAT_FULL
            ),
        ];

        for (condition, from, to) in to_copy {
            if condition {
                let val = vmx::vmread(from)?;
                vmx::vmwrite(to, val)?;
            }
        }

        let cpu = crate::cpu::get_current();

        // The zeroth bit is A (Accessed). Here we are feeding
        // the access rights directly into the segment cache, so
        // it must have been "accessed."
        let code_ar = cpu.gdt.kernel_code.access_bytes() | 1;
        let data_ar = cpu.gdt.kernel_data.access_bytes() | 1;

        // Same idea, but for TSS where the A bit is at bit 2
        let tss_ar = cpu.gdt.tss.access_bytes() | (1 << 1);

        vmx::vmwrite(CS_ACCESS_RIGHTS, code_ar as u64)?;
        vmx::vmwrite(SS_ACCESS_RIGHTS, data_ar as u64)?;
        vmx::vmwrite(DS_ACCESS_RIGHTS, data_ar as u64)?;
        vmx::vmwrite(ES_ACCESS_RIGHTS, data_ar as u64)?;
        vmx::vmwrite(FS_ACCESS_RIGHTS, data_ar as u64)?;
        vmx::vmwrite(GS_ACCESS_RIGHTS, data_ar as u64)?;
        vmx::vmwrite(TR_ACCESS_RIGHTS, tss_ar as u64)?;

        // Bit 1 in RFLAGS must be 1
        vmx::vmwrite(GUEST_RFLAGS, 0x2)?;

        Ok(())
    }

    /// Sets the Guest RIP and RSP for the currently-loaded VMCS.
    unsafe fn set_vmcs_guest_entrypoint(&mut self, rip: u64, rsp: u64) -> VmxResult<()> {
        use x86::vmx::vmcs::guest::{RIP as GUEST_RIP, RSP as GUEST_RSP};

        self.check_vmcs_loaded()?;

        vmx::vmwrite(GUEST_RIP, rip)?;
        vmx::vmwrite(GUEST_RSP, rsp)?;

        Ok(())
    }

    /// Launches or resumes the currently-loaded VMCS (low-level).
    unsafe fn launch_current(&mut self, resume: bool) -> VmxResult<()> {
        use x86::vmx::vmcs::host::{RIP as HOST_RIP, RSP as HOST_RSP};

        let failure: usize;
        asm!(
            "xor rax, rax",

            "push rbx",
            "push rbp",
            "pushfq",

            "mov rbx, {vmcs_host_rsp}",
            "vmwrite rbx, rsp",

            "lea rdx, 3f", // -> VM Exit
            "mov rbx, {vmcs_host_rip}",
            "vmwrite rbx, rdx",

            "cmp {resume:r}, 1",
            "je 1f", // -> Resume

            // Launch
            "vmlaunch",
            "jmp 2f", // -> Failure

            // Resume
            "1:",
            "vmresume",

            // Failure
            "2:",
            "mov rax, 1",

            // VM Exit
            "3:",

            "popfq",
            "pop rbp",
            "pop rbx",

            vmcs_host_rsp = const HOST_RSP,
            vmcs_host_rip = const HOST_RIP,
            resume = in(reg) resume as usize,

            lateout("rax") failure,
            lateout("rdx") _,
            lateout("rdi") _,
            lateout("rsi") _,
            lateout("r8") _,
            lateout("r9") _,
            lateout("r10") _,
            lateout("r11") _,

            lateout("r12") _,
            lateout("r13") _,
            lateout("r14") _,
            lateout("r15") _,
        );

        if failure == 1 {
            let rflags = read_rflags();

            if rflags.contains(RFlags::FLAGS_ZF) {
                return Err(VmxError::VmcsPtrValid);
            }

            if rflags.contains(RFlags::FLAGS_CF) {
                return Err(VmxError::VmcsPtrInvalid);
            }
        }

        Ok(())
    }

    /// Returns the VMCS revision identifier.
    pub fn get_vmcs_revision(&self) -> u32 {
        self.vmcs_revision
    }

    /*
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

        Ok(Some(error))
    }
    */

    /// Checks that the VMM has started.
    fn check_vmm_started(&self) -> VmxResult<()> {
        let vmx_enabled = self.enabled.read();
        if !*vmx_enabled {
            return Err(VmxError::VmmNotStarted);
        }

        Ok(())
    }

    /// Checks that a VMCS is currently loaded.
    fn check_vmcs_loaded(&self) -> VmxResult<()> {
        self.check_vmm_started()?;

        let current_vmcs = self.current_vmcs.lock();
        if current_vmcs.is_none() {
            return Err(VmxError::VmcsPtrInvalid);
        }

        Ok(())
    }
}

impl<'a> Drop for Monitor<'a> {
    fn drop(&mut self) {
        let vmx_enabled = *self.enabled.read();
        if vmx_enabled {
            self.stop().expect("Monitor::Drop(): Could not VMXOFF");
        }
    }
}

#[no_mangle]
unsafe extern "C" fn demo_guest_main() {
    log::info!("Hello from VM");

    // Cause an exit
    asm!("cpuid");
}

// FIXME: Also set RIP and RSP


/// Reads the value of CR0.
unsafe fn read_cr0() -> u32 {
    let val: u32;
    asm!("mov {0:r}, cr0", out(reg) val);
    val
}

/// Writes a value into CR0.
unsafe fn write_cr0(val: u32) {
    asm!("mov cr0, {0:r}", in(reg) val);
}

/// Reads the value of CR4.
unsafe fn read_cr4() -> u32 {
    let val: u32;
    asm!("mov {0:r}, cr4", out(reg) val);
    val
}

/// Writes a value into CR4.
unsafe fn write_cr4(val: u32) {
    asm!("mov cr4, {0:r}", in(reg) val);
}

/// Returns the IDT base address.
unsafe fn read_idt_base() -> u64 {
    use x86::segmentation::Descriptor;
    use x86::dtables::DescriptorTablePointer;

    let mut idt_pointer = DescriptorTablePointer::<Descriptor>::default();
    x86::dtables::sidt(&mut idt_pointer);

    idt_pointer.base as u64
}

#[cfg(test)]
mod tests {
    use x86::bits64::vmx;
    use x86::vmx::vmcs::control;

    use super::*;
    use atest::test;

    static mut VMXON: Vmxon = Vmxon::new();
    static mut VMCS: Vmcs = Vmcs::new();
    static GUEST_STACK: [u8; 4096] = [0u8; 4096];

    unsafe extern "C" fn guest_main() {
        asm!("cpuid");
    }

    #[test]
    fn test_simple_vm() {
        unsafe {
            let mut vmm = Monitor::new(&mut VMXON);
            vmm.start()
                .expect("Could not start VMM");

            VMCS.init(vmm.get_vmcs_revision())
                .expect("Could not initialize VMCS");

            vmm.load_vmcs(&mut VMCS)
                .expect("Could not load VMCS");

            vmm.init_vmcs_controls()
                .expect("Could not initialize VMCS Controls");

            vmm.init_vmcs_guest_state()
                .expect("Could not initialize VMCS Guest State");

            vmm.save_vmcs_host_state()
                .expect("Could not save VMCS Host State");

            vmm.copy_vmcs_host_state_to_guest()
                .expect("Could not copy VMCS Host State to Guest State");

            let stack_end = (&GUEST_STACK as *const u8).offset(4096) as u64;
            let target = guest_main as *const () as u64;

            vmm.set_vmcs_guest_entrypoint(target, stack_end)
                .expect("Failed to set guest entrypoint");

            vmm.launch_current(false)
                .expect("Failed to launch VM");
        }
    }

    #[test]
    fn test_invalid_vm() {
        unsafe {
            let mut vmm = Monitor::new(&mut VMXON);
            vmm.start()
                .expect("Could not start VMM");

            VMCS.init(vmm.get_vmcs_revision())
                .expect("Could not initialize VMCS");

            vmm.load_vmcs(&mut VMCS)
                .expect("Could not load VMCS");

            vmm.init_vmcs_controls()
                .expect("Could not initialize VMCS Controls");

            vmm.init_vmcs_guest_state()
                .expect("Could not initialize VMCS Guest State");

            vmm.save_vmcs_host_state()
                .expect("Could not save VMCS Host State");

            vmm.copy_vmcs_host_state_to_guest()
                .expect("Could not copy VMCS Host State to Guest State");

            // manually inject an invalid control value
            vmx::vmwrite(control::PINBASED_EXEC_CONTROLS, u64::MAX)
                .expect("Could not inject control value");

            let stack_end = (&GUEST_STACK as *const u8).offset(4096) as u64;
            let target = guest_main as *const () as u64;

            vmm.set_vmcs_guest_entrypoint(target, stack_end)
                .expect("Failed to set guest entrypoint");

            let launch_err = vmm.launch_current(false)
                .expect_err("VM launch must fail");

            if let VmxError::VmcsPtrValid = launch_err {
            } else {
                panic!("Launch must fail with VmxError::VmcsPtrValid");
            }
        }
    }
}

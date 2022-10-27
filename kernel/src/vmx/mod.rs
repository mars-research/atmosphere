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

#[allow(dead_code)] // used in tests
mod scheduler;
mod types;

use core::arch::asm;
use core::mem;
use core::sync::atomic::{AtomicBool, Ordering};

use displaydoc::Display;
use x86::bits64::paging::PAddr;
use x86::bits64::rflags::{read as read_rflags, RFlags};
use x86::bits64::vmx;
use x86::cpuid::CpuId;
use x86::msr;
use x86::vmx::vmcs::control;

use crate::cpu;
use crate::gdt::TaskStateSegment;
use crate::memory::get_physical;
use astd::cell::AtomicRefMut;
use astd::sync::RwLock;
use types::{
    CurrentVmcsField, ExitReason, ExplainBitfieldConstraint, GuestContext, GuestRegisterDump,
    KnownExitReason, VmInstructionError, VmcsRevision, GUEST_CONTEXT_SIZE,
};

pub type VmxResult<T, E = VmxError> = core::result::Result<T, E>;

/// An exclusive handle to a vCPU.
///
/// In Atmosphere, vCpus themselves are managed by capabilities
/// and have their addresses pinned in place in memory. They can
/// never be moved.
pub type VCpuHandle = AtomicRefMut<'static, VCpu>;

static GUEST_STACK: [u8; 4096] = [0u8; 4096];

macro_rules! copy_host_state {
    ($x:ident) => {{
        use x86::vmx::vmcs::{guest, host};
        (true, host::$x, guest::$x)
    }};
    ($cond:expr, $x:ident) => {{
        use x86::vmx::vmcs::{guest, host};
        ($cond, host::$x, guest::$x)
    }};
}

/// A virtualization error.
///
/// The naming of the variants are subject to change.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, Display)]
#[ignore_extra_doc_attributes]
pub enum VmxError {
    /// The platform does not support VT-x.
    VmxUnsupported,

    /// The platform supports VT-x, but it's disabled in BIOS.
    VmxDisabled,

    /// The VMCS region size {size} is not supported.
    UnsupportedVmcsSize { size: usize },

    /// The VMXON region at {addr:#x} has bad alignment. It must be 4KiB aligned.
    VmxonBadAlignment { addr: usize },

    /// The VMCS region at {addr:#x} has bad alignment. It must be 4KiB aligned.
    VmcsBadAlignment { addr: usize },

    /// The VMM has already started.
    VmmAlreadyStarted,

    /// The VMM has not started.
    VmmNotStarted,

    /// The vCPU hasn't been initialized.
    VCpuNotInitialized,

    /// The vCPU hasn't been configured.
    VCpuNotConfigured,

    /// The vCPU is already initialized.
    ///
    /// It has to be deinitialized before being reused.
    VCpuAlreadyInitialized,

    /// The vCPU is already configured.
    VCpuAlreadyConfigured,

    /// The vCPU is currently in use.
    VCpuInUse,

    /// The vCPU is at an invalid RIP.
    VCpuBadRip,

    /// There is no vCPU currently loaded.
    NoCurrentVCpu,

    /// The VMCS pointer is not valid.
    VmcsPtrInvalid,

    /// The VMCS pointer is valid, but some other error occurred.
    VmcsPtrValid,

    /// A VMCS control field constraint wasn't met: {explain}
    VmcsConstraintViolation { explain: ExplainBitfieldConstraint },

    /// A VMCS control field constraint is impossible: {constraint:#x?}.
    VmcsImpossibleConstraint { constraint: u64 },

    /// The VMX Preemption Timer is not supported by the system.
    PreemptionTimerUnavailable,

    /// Other error: {0}
    OtherError(&'static str),

    /// VM-instruction error: {0}
    VmInstructionError(VmInstructionError),
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

/// VT-x platform information.
#[derive(Clone, Debug)]
pub struct PlatformInfo {
    /// The VMCS revision identifier.
    vmcs_revision: VmcsRevision,

    /// Size of VMXON/VMCS regions.
    ///
    /// We only support 4KiB (4096).
    vmcs_size: usize,

    /// The rate at which the VMX Preemption Timer ticks down with respect to guest TSC.
    ///
    /// The value X here means that the preemption timer will decrease
    /// by 1 every time the guest TSC changes by X. This is converted
    /// from the value in IA32_VMX_MISC MSR which contains N as in
    /// `X = 2^N`.
    ///
    /// Take note that the guest TSC may be running at a multiplier of
    /// the host TSC.
    ///
    /// If this value is `None`, then the VMX Preemption Timer is not
    /// supported by this platform.
    preemption_timer_rate: Option<u32>,
}

impl PlatformInfo {
    pub const fn invalid() -> Self {
        Self {
            vmcs_revision: VmcsRevision::invalid(),
            vmcs_size: 0,
            preemption_timer_rate: None,
        }
    }

    /// Detects VT-x platform information.
    ///
    /// Returns `None` if VT-x is not available.
    pub fn detect() -> Option<Self> {
        use pal::msr::ia32_vmx_basic::{self, *};

        // Check CPUID VMX bit
        let cpuid = CpuId::new();
        let feature_info = cpuid.get_feature_info()?;

        if !feature_info.has_vmx() {
            return None;
        }

        // Check VMXON/VMCS region size
        let msr = unsafe { ia32_vmx_basic::get() };
        let vmcs_revision = unsafe { get_revision_id_from_value(msr) } as u32;
        let vmcs_size = unsafe { get_vmxon_vmcs_region_size_from_value(msr) } as usize;

        // Check Preemption Timer support
        let preemption_timer_rate = {
            let constraint = {
                let true_based_controls = unsafe { true_based_controls_is_enabled() };

                let msr = if true_based_controls {
                    msr::IA32_VMX_TRUE_PINBASED_CTLS
                } else {
                    msr::IA32_VMX_PINBASED_CTLS
                };

                unsafe { msr::rdmsr(msr) }
            };

            let one_constraint = constraint >> 32;
            if (one_constraint & (1 << 6)) != 0 {
                let rate = unsafe { pal::msr::ia32_vmx_misc::get_preemption_timer_decrement() };
                Some(1 << rate as u32)
            } else {
                None
            }
        };

        if vmcs_size != 4096 {
            log::warn!("Platform requires the VMXON/VMCS regions to be of size {} which we do not support.", vmcs_size);
        }

        Some(PlatformInfo {
            vmcs_revision: VmcsRevision::new(vmcs_revision),
            vmcs_size,
            preemption_timer_rate,
        })
    }
}

/// A Virtual Machine Monitor (VMM).
///
/// Here we keep track of all states related to the VMM running
/// on one physical logical core.
///
/// All methods must be called on the correct CPU.
#[repr(align(4096))]
pub struct Monitor {
    /// A dummy VMCS.
    ///
    /// This is loaded in order to unload the current VMCS.
    dummy_vmcs: Vmcs,

    /// Whether VMX operations are enabled.
    enabled: RwLock<bool>,

    /// The platform information.
    platform_info: PlatformInfo,

    /// The VMXON region.
    vmxon: &'static mut Vmxon,

    /// The current vCPU.
    current_vcpu: Option<VCpuHandle>,
}

impl Monitor {
    /// Creates a new VMM.
    pub fn new(vmxon: &'static mut Vmxon) -> Self {
        Self {
            dummy_vmcs: Vmcs::new(),
            enabled: RwLock::new(false),
            platform_info: PlatformInfo::invalid(),
            vmxon,
            current_vcpu: None,
        }
    }

    /// Initializes the VMM and enters VMX root operation mode.
    ///
    /// ## Safety
    ///
    /// This is unsafe because the control registers may be modified during
    /// the procedure.
    pub unsafe fn start(&mut self) -> VmxResult<()> {
        let mut vmx_enabled = self.enabled.write();
        if *vmx_enabled {
            return Err(VmxError::VmmAlreadyStarted);
        }

        let platform_info = PlatformInfo::detect().ok_or(VmxError::VmxUnsupported)?;

        if platform_info.vmcs_size != mem::size_of::<Vmcs>() {
            return Err(VmxError::UnsupportedVmcsSize {
                size: platform_info.vmcs_size,
            });
        }

        self.platform_info = platform_info;

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
        self.vmxon.set_revision(self.platform_info.vmcs_revision);
        vmx::vmxon(self.vmxon.get_physical().as_u64())?;

        // Initialize the dummy VMCS
        self.dummy_vmcs.init(self.platform_info.vmcs_revision)?;

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

        if let Some(current_vcpu) = self.current_vcpu.take() {
            current_vcpu.loaded.store(false, Ordering::Release);
        }

        Ok(())
    }

    /// Loads the specified vCPU and make it the current vCPU.
    ///
    /// The previously-loaded vCPU will be returned if there is one.
    pub fn load_vcpu(&mut self, vcpu: VCpuHandle) -> VmxResult<Option<VCpuHandle>> {
        #[cfg(debug_assertions)]
        self.check_vmm_started()?;

        if !vcpu.initialized() {
            return Err(VmxError::VCpuNotInitialized);
        }

        if vcpu
            .loaded
            .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            return Err(VmxError::VCpuInUse);
        }

        // Load VMCS
        unsafe {
            vmx::vmptrld(vcpu.vmcs.get_physical().as_u64())?;
        }

        if let Some(prev_vcpu) = self.current_vcpu.replace(vcpu) {
            prev_vcpu.loaded.store(false, Ordering::Release);

            Ok(Some(prev_vcpu))
        } else {
            Ok(None)
        }
    }

    /// Unloads the current vCPU.
    ///
    /// This loads a dummy VMCS to take its place.
    #[allow(dead_code)] // used in tests
    pub fn unload_vcpu(&mut self) -> VmxResult<VCpuHandle> {
        if let Some(prev_vcpu) = self.current_vcpu.take() {
            unsafe {
                vmx::vmptrld(self.dummy_vmcs.get_physical().as_u64())?;
            }

            prev_vcpu.loaded.store(false, Ordering::Release);
            Ok(prev_vcpu)
        } else {
            Err(VmxError::NoCurrentVCpu)
        }
    }

    /// Sets the preemption timer value in the currently loaded VMCS.
    ///
    /// The value returned by this function is the deviation between
    /// the supplied value and the value that is actually set. It
    /// tells you how many cycles *sooner* it will trigger than your
    /// supplied time.
    ///
    /// This is because that the VMX Preemption Timer ticks at a fixed
    /// rate that is a power of two. If you supplied a value of 10
    /// cycles and the Preemption Timer ticks down every 4 cycles,
    /// the actual applied value will be 8 cycles and 2 will be
    /// returned.
    #[allow(dead_code)] // used in tests
    pub fn set_vmcs_preemption_timer_value(&mut self, tsc: Option<u32>) -> VmxResult<u32> {
        use pal::vmcs::guest_preemption_timer_value;
        use pal::vmcs::pin_based_vm_execution_controls::*;
        use pal::vmcs::vm_exit_controls::*;

        let vcpu = self.current_vcpu.as_mut().ok_or(VmxError::NoCurrentVCpu)?;

        match tsc {
            None => {
                // Disable Timer

                unsafe {
                    disable_activate_vmx_preeemption_timer();
                    disable_save_vmxpreemption_timer_value();
                }

                Ok(0)
            }
            Some(tsc) => {
                // Enable Timer
                let rate = self
                    .platform_info
                    .preemption_timer_rate
                    .ok_or(VmxError::PreemptionTimerUnavailable)?;

                let value = tsc / rate;
                let remainder = tsc % rate;

                vcpu.preemption_timer = Some(value);

                unsafe {
                    guest_preemption_timer_value::set(value);
                    enable_activate_vmx_preeemption_timer();
                    enable_save_vmxpreemption_timer_value();
                }

                Ok(remainder)
            }
        }
    }

    /// Test method to initialize and launch an unconfined VM.
    pub unsafe fn demo_launch(&mut self) -> VmxResult<ExitReason> {
        self.check_vcpu_loaded()?;

        self.init_vmcs_controls()?;
        self.init_vmcs_guest_state()?;
        self.copy_vmcs_host_state_to_guest()?;

        let stack_end = (&GUEST_STACK as *const u8).offset(4096) as u64;
        let target = demo_guest_main as *const () as u64;

        self.set_vmcs_guest_entrypoint(target, stack_end)?;
        self.mark_vcpu_ready()?;

        self.launch_current()
    }

    /// Initializes VMCS control fields.
    unsafe fn init_vmcs_controls(&mut self) -> VmxResult<()> {
        #[cfg(debug_assertions)]
        self.check_vcpu_loaded()?;

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
            enable_hlt_exiting_in_value(&mut value);

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
    pub fn init_vmcs_guest_state(&self) -> VmxResult<()> {
        self.check_vcpu_loaded()?;

        // ## Register State

        // Limits
        // If G(Granularity) = 0, then we must mask out the higher bits
        let unlimited = u32::MAX as u64 & !0xfff00000;

        unsafe {
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
            use pal::vmcs::secondary_processor_based_vm_execution_controls::{
                enable_pml_is_enabled, vmcs_shadowing_is_enabled,
            };
            use x86::vmx::vmcs::guest::*;

            vmx::vmwrite(ACTIVITY_STATE, 0)?;

            // Only has an effect when Virtual Interrupt Delivery is enabled
            vmx::vmwrite(INTERRUPT_STATUS, 0)?;

            // Only has an effect when VMX Preemption Timer is enabled
            vmx::vmwrite(VMX_PREEMPTION_TIMER_VALUE, 0)?;

            if vmcs_shadowing_is_enabled() {
                return Err(VmxError::OtherError("VMCS Shadowing is not implemented"));
            } else {
                vmx::vmwrite(LINK_PTR_FULL, 0xffff_ffff_ffff_ffff)?;
            }

            // TODO: Investigate this
            if enable_pml_is_enabled() {
                return Err(VmxError::OtherError(
                    "Page-Modification Logging is not implemented",
                ));
            } else {
                // vmx::vmwrite(PML_INDEX, 0)?;
            }
        }

        Ok(())
    }

    /// Saves the current host state to the Host-State Area.
    unsafe fn save_vmcs_host_state(&self) -> VmxResult<()> {
        // See Intel SDM, Volume 3C, Chapter 24.5.

        #[cfg(debug_assertions)]
        self.check_vcpu_loaded()?;

        use pal::vmcs::vm_exit_controls::*;
        use x86::controlregs as ctl;
        use x86::segmentation as seg;
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
            vmx::vmwrite(
                IA32_PERF_GLOBAL_CTRL_FULL,
                msr::rdmsr(msr::IA32_PERF_GLOBAL_CTRL),
            )?;
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
    ///
    /// ## Safety
    ///
    /// This causes information leak from the host to guest.
    pub unsafe fn copy_vmcs_host_state_to_guest(&self) -> VmxResult<()> {
        use pal::vmcs::vm_entry_controls::*;
        use x86::vmx::vmcs::guest::{
            CS_ACCESS_RIGHTS, DS_ACCESS_RIGHTS, ES_ACCESS_RIGHTS, FS_ACCESS_RIGHTS,
            GS_ACCESS_RIGHTS, RFLAGS as GUEST_RFLAGS, SS_ACCESS_RIGHTS, TR_ACCESS_RIGHTS,
        };

        self.check_vcpu_loaded()?;

        self.save_vmcs_host_state()?;

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
            copy_host_state!(load_ia32_efer_is_enabled(), IA32_EFER_FULL),
            copy_host_state!(load_ia32_pat_is_enabled(), IA32_PAT_FULL),
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

        #[cfg(debug_assertions)]
        self.check_vcpu_loaded()?;

        vmx::vmwrite(GUEST_RIP, rip)?;
        vmx::vmwrite(GUEST_RSP, rsp)?;

        Ok(())
    }

    /// Moves the guest RIP to the next instruction.
    ///
    /// This can only be done after a VM exit.
    pub unsafe fn advance_vmcs_guest_rip(&mut self) -> VmxResult<()> {
        use x86::vmx::vmcs::guest::RIP as GUEST_RIP;
        use x86::vmx::vmcs::ro::VMEXIT_INSTRUCTION_LEN;

        #[cfg(debug_assertions)]
        self.check_vcpu_loaded()?;

        let rip = vmx::vmread(GUEST_RIP)?;

        if rip == 0 {
            return Err(VmxError::VCpuBadRip);
        }

        let instruction_length = vmx::vmread(VMEXIT_INSTRUCTION_LEN)?;

        if instruction_length == 0 {
            return Err(VmxError::OtherError("Instruction length is 0"));
        }

        vmx::vmwrite(GUEST_RIP, rip + instruction_length)?;

        Ok(())
    }

    /// Launches or resumes the currently-loaded VMCS (low-level).
    ///
    /// From Intel SDM:
    ///
    /// > Failure to pass checks on the VMX controls or on the host-state
    /// > area passes control to the instruction following the VMLAUNCH
    /// > or VMRESUME instruction. If these pass but checks on the
    /// > guest-state area fail, the logical processor loads state from
    /// > the host-state area of the VMCS, passing control to the instruction
    /// > referenced by the RIP field in the host-state area.
    ///
    /// Currently, we only return `Err` for the first case ("failure
    /// to pass checks on the VMX controls or on the host-state area") and
    /// return `Ok(VmExitReason::InvalidGuestState)` otherwise.
    pub fn launch_current(&mut self) -> VmxResult<ExitReason> {
        use x86::vmx::vmcs::host::{RIP as HOST_RIP, RSP as HOST_RSP};

        #[cfg(debug_assertions)]
        self.check_vcpu_ready()?;

        let guest_context = self.get_guest_context_region()?;

        unsafe {
            self.save_vmcs_host_state()?;
        }

        let failure: usize;
        unsafe {
            asm!(
                // Input: rax <- guest_context
                // Output: rax -> failure

                "push rbx",
                "push rbp",
                "pushfq",

                // Save host RSP to GuestContext
                "mov [rax], rsp",

                // ... and make the end of GuestContext
                // the host RSP to restore
                "mov rbx, rax",
                "add rbx, {guest_context_size}",
                "mov rbp, {vmcs_host_rsp}",
                "vmwrite rbp, rbx",

                // Set up VM exit RIP
                "lea rbx, 3f", // -> VM Exit
                "mov rbp, {vmcs_host_rip}",
                "vmwrite rbp, rbx",

                // Restore guest state
                "add rax, 8",
                "mov rsp, rax",
                "pop rax",
                "pop rbx",
                "pop rcx",
                "pop rdx",
                "pop rbp",
                "pop rdi",
                "pop rsi",
                "pop r8",
                "pop r9",
                "pop r10",
                "pop r11",
                "pop r12",
                "pop r13",
                "pop r14",
                "pop r15", // rsp is now at .launched

                "cmp qword ptr [rsp], 0",
                "je 1f", // -> Launch

                // Resume
                "vmresume",
                "jmp 2f",

                // Launch
                "1:",
                "mov qword ptr [rsp], 1", // set launched = 1
                "vmlaunch",
                "mov qword ptr [rsp], 0", // failed - clear to 0 again

                // Common Failure
                "2:", // rsp is now at .launched
                "add rsp, 8",
                "sub rsp, {guest_context_size}",
                "pop rsp",

                "popfq",
                "pop rbp",
                "pop rbx",

                "mov rax, 1",
                "jmp 4f", // -> End

                // VM Exit
                // Restored rsp is at the end of GuestContext
                "3:",

                // Save guest state
                "sub rsp, 8", // rsp is now at .launched
                "push r15",
                "push r14",
                "push r13",
                "push r12",
                "push r11",
                "push r10",
                "push r9",
                "push r8",
                "push rsi",
                "push rdi",
                "push rbp",
                "push rdx",
                "push rcx",
                "push rbx",
                "push rax",

                "sub rsp, 8", // rsp is at beginning of GuestContext (host_rsp)
                "pop rsp",

                "popfq",
                "pop rbp",
                "pop rbx",

                "xor rax, rax",

                // End
                "4:",

                vmcs_host_rsp = const HOST_RSP,
                vmcs_host_rip = const HOST_RIP,
                guest_context_size = const GUEST_CONTEXT_SIZE,

                inout("rax") guest_context => failure,
                lateout("rcx") _,
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
        }

        if failure == 1 {
            let rflags = read_rflags();

            if rflags.contains(RFlags::FLAGS_ZF) {
                let error = self.read_vm_fail_valid()?;
                return Err(error);
            }

            if rflags.contains(RFlags::FLAGS_CF) {
                return Err(VmxError::VmcsPtrInvalid);
            }
        }

        self.read_vm_exit_reason()
    }

    /// Returns a dump of the guest context.
    pub fn dump_guest_registers(&self) -> VmxResult<GuestRegisterDump> {
        use x86::vmx::vmcs::guest;

        let vcpu = self.current_vcpu.as_ref().ok_or(VmxError::NoCurrentVCpu)?;

        let dump = unsafe {
            GuestRegisterDump {
                rax: vcpu.context.rax,
                rbx: vcpu.context.rbx,
                rcx: vcpu.context.rcx,
                rdx: vcpu.context.rdx,
                rbp: vcpu.context.rbp,
                rdi: vcpu.context.rdi,
                rsi: vcpu.context.rsi,
                r8: vcpu.context.r8,
                r9: vcpu.context.r9,
                r10: vcpu.context.r10,
                r11: vcpu.context.r11,
                r12: vcpu.context.r12,
                r13: vcpu.context.r13,
                r14: vcpu.context.r14,
                r15: vcpu.context.r15,
                rsp: vmx::vmread(guest::RSP)?,
                rip: vmx::vmread(guest::RIP)?,
                cr0: vmx::vmread(guest::CR0)?,
                cr3: vmx::vmread(guest::CR3)?,
                cr4: vmx::vmread(guest::CR4)?,
            }
        };

        Ok(dump)
    }

    /// Returns the VMCS revision identifier.
    pub fn get_vmcs_revision(&self) -> VmcsRevision {
        self.platform_info.vmcs_revision
    }

    /// Returns an mutable reference to the current-loaded VCpu.
    pub fn get_current_vcpu(&mut self) -> Option<&mut VCpu> {
        // pub fn get_current_vcpu(&mut self) -> Option<&impl DerefMut<Target = VCpu>> {
        self.current_vcpu.as_mut().map(|r| &mut **r)
    }

    /// Reads the VM exit reason from the current VMCS.
    ///
    /// This will also reset the preemption timer if it's the reason
    /// of the VM exit.
    fn read_vm_exit_reason(&self) -> VmxResult<ExitReason> {
        use pal::vmcs::guest_preemption_timer_value;
        use x86::vmx::vmcs::ro::EXIT_REASON;

        let reason = unsafe { ExitReason::new(vmx::vmread(EXIT_REASON)?) };

        if reason == KnownExitReason::PreemptionTimerExpired {
            let vcpu = self.current_vcpu.as_ref().unwrap();
            let timer_value = vcpu
                .preemption_timer
                .expect("The preemption timer value must exist");

            unsafe {
                guest_preemption_timer_value::set(timer_value);
            }
        }

        Ok(reason)
    }

    /// Attempts to return a more specific error than VmcsPtrValid.
    fn read_vm_fail_valid(&self) -> VmxResult<VmxError> {
        if let Some(err) = self.read_vm_instruction_error()? {
            Ok(err)
        } else {
            Ok(VmxError::VmcsPtrValid)
        }
    }

    /// Reads the VM-instruction error field of the current VMCS.
    fn read_vm_instruction_error(&self) -> VmxResult<Option<VmxError>> {
        use x86::vmx::vmcs::ro::VM_INSTRUCTION_ERROR;

        let error = unsafe { vmx::vmread(VM_INSTRUCTION_ERROR) };

        // Nested errors can be confusing
        if let Err(vmfail) = &error {
            log::error!(
                "Error occurred while trying to read VM-instruction error: {:?}",
                vmfail
            );
        }

        match error? {
            0 => Ok(None),
            x => Ok(Some(VmxError::VmInstructionError(VmInstructionError::new(
                x,
            )))),
        }
    }

    /// Marks the currently-loaded vCPU as ready.
    ///
    /// ## Safety
    ///
    /// The caller must ensure all required control fields and states are
    /// set up.
    pub unsafe fn mark_vcpu_ready(&mut self) -> VmxResult<()> {
        if let Some(vcpu) = self.current_vcpu.as_mut() {
            vcpu.mark_ready()
        } else {
            Err(VmxError::NoCurrentVCpu)
        }
    }

    /// Returns the context save region for the currently-loaded VMCS.
    fn get_guest_context_region(&self) -> VmxResult<*mut GuestContext> {
        #[cfg(debug_assertions)]
        self.check_vmm_started()?;

        if let Some(vcpu) = self.current_vcpu.as_ref() {
            Ok(&vcpu.context as *const _ as *mut _)
        } else {
            Err(VmxError::NoCurrentVCpu)
        }
    }

    // sanity checks

    /// Checks that the VMM has started.
    #[allow(dead_code)] // calls are stripped out in release mode
    fn check_vmm_started(&self) -> VmxResult<()> {
        let vmx_enabled = self.enabled.read();
        if !*vmx_enabled {
            return Err(VmxError::VmmNotStarted);
        }

        Ok(())
    }

    /// Checks that a vCPU is currently loaded.
    fn check_vcpu_loaded(&self) -> VmxResult<()> {
        #[cfg(debug_assertions)]
        self.check_vmm_started()?;

        if self.current_vcpu.is_none() {
            return Err(VmxError::NoCurrentVCpu);
        }

        Ok(())
    }

    /// Checks that a vCPU is currently loaded and ready.
    #[allow(dead_code)] // calls are stripped out in release mode
    fn check_vcpu_ready(&self) -> VmxResult<()> {
        #[cfg(debug_assertions)]
        self.check_vmm_started()?;

        if let Some(vcpu) = self.current_vcpu.as_ref() {
            if vcpu.ready() {
                Ok(())
            } else {
                Err(VmxError::VCpuNotConfigured)
            }
        } else {
            Err(VmxError::NoCurrentVCpu)
        }
    }
}

impl Drop for Monitor {
    fn drop(&mut self) {
        let vmx_enabled = *self.enabled.read();
        if vmx_enabled {
            self.stop().expect("Monitor::Drop(): Could not VMXOFF");
        }
    }
}

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
#[derive(Debug)]
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
    /*
    /// Cannot be launched or resumed.
    ///
    /// The CPU may be waiting for an SIPI (Start-up IPI), for
    /// example.
    NotReady,
    */
}

/// A vCPU.
///
/// FIXME: We need to figure out how this plays with our VM
/// abstraction as well as SMP/parallelization.
#[repr(align(4096))]
#[derive(Debug)]
pub struct VCpu {
    /// The VMCS region.
    vmcs: Vmcs,

    /// The state of the vCPU.
    state: VCpuState,

    /// Whether the vCPU is loaded.
    loaded: AtomicBool,

    /// The guest register state.
    context: GuestContext,

    /// The preemption timer value.
    ///
    /// This value is dependent on the Preemption Timer Rate
    /// of the platform, so this field should only be set via
    /// [`Monitor::set_vmcs_preemption_timer_value`]
    /// which does the conversion for you.
    ///
    /// A value of `Some(0)` is guaranteed to cause an exit before any
    /// instruction is executed. However, take note that certain
    /// other exit reasons may take precendence over the preemption
    /// timer and cause an exit before the timer is checked.
    ///
    /// A value of `None` means that the Preemption Timer is disabled.
    preemption_timer: Option<u32>,
}

impl VCpu {
    /// Creates a new vCPU.
    pub const fn new() -> Self {
        Self {
            vmcs: Vmcs::new(),
            state: VCpuState::Uninitialized,
            loaded: AtomicBool::new(false),
            context: GuestContext::new(),
            preemption_timer: None,
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
    fn mark_ready(&mut self) -> VmxResult<()> {
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

#[no_mangle]
unsafe extern "C" fn demo_guest_main() {
    log::warn!("VM: Hello from VM");
    log::warn!("VM: Doing a CPUID");
    asm!("cpuid");

    log::warn!("VM: We have resumed from CPUID :D");
    log::warn!("VM: Doing a VMCALL");
    asm!("vmcall");
}

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
    use x86::dtables::DescriptorTablePointer;
    use x86::segmentation::Descriptor;

    let mut idt_pointer = DescriptorTablePointer::<Descriptor>::default();
    x86::dtables::sidt(&mut idt_pointer);

    idt_pointer.base as u64
}

#[cfg(test)]
mod tests {
    use core::ops::{Deref, DerefMut};

    use x86::bits64::vmx;
    use x86::vmx::vmcs::control;

    use super::*;
    use crate::cpu::get_current_vmm;
    use astd::cell::AtomicRefCell;
    use atest::test;
    use types::{KnownExitReason, KnownVmInstructionError};

    pub struct VmmTestSession {
        vmm: &'static mut Monitor,
        vcpu: &'static AtomicRefCell<VCpu>,
    }

    impl VmmTestSession {
        /// Creates a new test session.
        unsafe fn new(
            vmm: &'static mut Monitor,
            vcpu: &'static AtomicRefCell<VCpu>,
        ) -> VmxResult<Self> {
            vmm.start()?;

            let mut vcpu_mut = vcpu.borrow_mut();
            vcpu_mut.init(vmm.get_vmcs_revision())?;

            vmm.load_vcpu(vcpu_mut)?;

            Ok(Self { vmm, vcpu })
        }
    }

    impl Drop for VmmTestSession {
        fn drop(&mut self) {
            self.vmm.stop().unwrap();
            self.vcpu.borrow_mut().deinit().unwrap();
        }
    }

    impl Deref for VmmTestSession {
        type Target = Monitor;
        fn deref(&self) -> &Monitor {
            self.vmm
        }
    }

    impl DerefMut for VmmTestSession {
        fn deref_mut(&mut self) -> &mut Monitor {
            self.vmm
        }
    }

    static VCPU: AtomicRefCell<VCpu> = AtomicRefCell::new(VCpu::new());

    static GUEST_STACK: [u8; 4096] = [0u8; 4096];
    static EXPECTED_VALUES: [u64; 15] = [
        0x8000000000000001,
        0x8000000000000011,
        0x8000000000000101,
        0x8000000000001001,
        0x8000000000010001,
        0x8000000000100001,
        0x8000000001000001,
        0x8000000010000001,
        0x8000000100000001,
        0x8000001000000001,
        0x8000010000000001,
        0x8000100000000001,
        0x8001000000000001,
        0x8010000000000001,
        0x8100000000000001,
    ];

    macro_rules! assert_register_eq {
        ($vmm:ident, $reg:ident, $value:expr) => {
            let registers = $vmm
                .dump_guest_registers()
                .expect("Could not dump guest context");
            assert_eq!(registers.$reg, $value);
        };
    }

    unsafe extern "C" fn guest_infinite_loop() {
        loop {}
    }

    unsafe extern "C" fn guest_reg_test() {
        asm!(
            "mov rax, 0x8000000000000001",
            "mov rbx, 0x8000000000000011",
            "mov rcx, 0x8000000000000101",
            "mov rdx, 0x8000000000001001",
            "mov rbp, 0x8000000000010001",
            "mov rdi, 0x8000000000100001",
            "mov rsi, 0x8000000001000001",
            "mov  r8, 0x8000000010000001",
            "mov  r9, 0x8000000100000001",
            "mov r10, 0x8000001000000001",
            "mov r11, 0x8000010000000001",
            "mov r12, 0x8000100000000001",
            "mov r13, 0x8001000000000001",
            "mov r14, 0x8010000000000001",
            "mov r15, 0x8100000000000001",
            "vmcall", // We will set rax to &EXPECTED_VALUES
            // Verify that registers have been restored correctly
            "cmp rbx, [rax +   8]",
            "jne 2f",
            "cmp rcx, [rax +  16]",
            "jne 2f",
            "cmp rdx, [rax +  24]",
            "jne 2f",
            "cmp rbp, [rax +  32]",
            "jne 2f",
            "cmp rdi, [rax +  40]",
            "jne 2f",
            "cmp rsi, [rax +  48]",
            "jne 2f",
            "cmp  r8, [rax +  56]",
            "jne 2f",
            "cmp  r9, [rax +  64]",
            "jne 2f",
            "cmp r10, [rax +  72]",
            "jne 2f",
            "cmp r11, [rax +  80]",
            "jne 2f",
            "cmp r12, [rax +  88]",
            "jne 2f",
            "cmp r13, [rax +  96]",
            "jne 2f",
            "cmp r14, [rax + 104]",
            "jne 2f",
            "cmp r15, [rax + 112]",
            "jne 2f",
            "jmp 3f",
            // Failure
            "2:",
            "xchg bx, bx",
            "hlt",
            "jmp 2b",
            // Success
            "3:",
            "mov rax, 0xc000000000000001",
            "cpuid",
        );
    }

    /// Common code to bootstrap a simple VM.
    unsafe fn bootstrap_simple_vm() -> VmmTestSession {
        let mut vmm = VmmTestSession::new(get_current_vmm(), &VCPU).expect("Could not start VMM");

        vmm.init_vmcs_controls()
            .expect("Could not initialize VMCS Controls");

        vmm.init_vmcs_guest_state()
            .expect("Could not initialize VMCS Guest State");

        vmm.copy_vmcs_host_state_to_guest()
            .expect("Could not copy VMCS Host State to Guest State");

        let stack_end = (&GUEST_STACK as *const u8).offset(4096) as u64;
        let target = guest_reg_test as *const () as u64;

        vmm.set_vmcs_guest_entrypoint(target, stack_end)
            .expect("Could not set guest entrypoint");

        vmm.mark_vcpu_ready().expect("Could not mark vCPU as ready");

        vmm
    }

    #[test]
    fn test_simple_vm() {
        unsafe {
            let mut vmm = bootstrap_simple_vm();

            // Initial launch
            let reason = vmm.launch_current().expect("Failed to launch VM");

            assert_eq!(reason, KnownExitReason::Vmcall);
            assert_register_eq!(vmm, rax, 0x8000000000000001);
            assert_register_eq!(vmm, rbx, 0x8000000000000011);
            assert_register_eq!(vmm, rcx, 0x8000000000000101);
            assert_register_eq!(vmm, rdx, 0x8000000000001001);
            assert_register_eq!(vmm, rbp, 0x8000000000010001);
            assert_register_eq!(vmm, rdi, 0x8000000000100001);
            assert_register_eq!(vmm, rsi, 0x8000000001000001);
            assert_register_eq!(vmm, r8, 0x8000000010000001);
            assert_register_eq!(vmm, r9, 0x8000000100000001);
            assert_register_eq!(vmm, r10, 0x8000001000000001);
            assert_register_eq!(vmm, r11, 0x8000010000000001);
            assert_register_eq!(vmm, r12, 0x8000100000000001);
            assert_register_eq!(vmm, r13, 0x8001000000000001);
            assert_register_eq!(vmm, r14, 0x8010000000000001);
            assert_register_eq!(vmm, r15, 0x8100000000000001);

            // Inject RAX
            {
                let vcpu = vmm.current_vcpu.as_mut().unwrap();
                vcpu.context.rax = &EXPECTED_VALUES as *const _ as u64;
            }

            vmm.advance_vmcs_guest_rip()
                .expect("Could not advance guest RIP");

            // Resume
            log::debug!("Trying to resume...");
            let reason = vmm.launch_current().expect("Failed to resume VM");

            assert_eq!(reason, KnownExitReason::Cpuid);
            assert_register_eq!(vmm, rax, 0xc000000000000001);
        }
    }

    #[test]
    fn test_invalid_vm() {
        unsafe {
            let mut vmm = bootstrap_simple_vm();

            // manually inject an invalid control value
            vmx::vmwrite(control::PINBASED_EXEC_CONTROLS, u64::MAX)
                .expect("Could not inject control value");

            let launch_err = vmm.launch_current().expect_err("VM launch must fail");

            if let VmxError::VmInstructionError(err) = launch_err {
                assert_eq!(
                    err,
                    KnownVmInstructionError::VmEntryWithInvalidControlFields
                );
            } else {
                panic!(
                    "Launch must fail with an VM-instruction error - It failed with {}",
                    launch_err
                );
            }
        }
    }

    #[test]
    fn test_vm_preemption() {
        unsafe {
            let mut vmm = bootstrap_simple_vm();

            let stack_end = (&GUEST_STACK as *const u8).offset(4096) as u64;
            let target = guest_infinite_loop as *const () as u64;

            vmm.set_vmcs_guest_entrypoint(target, stack_end)
                .expect("Could not set guest entrypoint");

            vmm.set_vmcs_preemption_timer_value(Some(100))
                .expect("Could not set preemption timer");

            let reason = vmm.launch_current().expect("Failed to launch VM");

            assert_eq!(reason, KnownExitReason::PreemptionTimerExpired);
        }
    }

    #[test]
    fn test_unload_vcpu() {
        let mut vmm = unsafe { bootstrap_simple_vm() };
        vmm.unload_vcpu().expect("Failed to unload vCPU");

        // Ensure that it really isn't loaded
        let vmptr = unsafe { vmx::vmptrst().unwrap() };
        assert_eq!(vmptr, vmm.dummy_vmcs.get_physical().as_u64());
    }

    #[test]
    fn test_member_alignment() {
        let vmxon = AtomicRefCell::new(Vmxon::new());
        vmxon.borrow().check_alignment().unwrap();
    }
}

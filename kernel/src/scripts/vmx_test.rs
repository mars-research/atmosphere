use x86::bits64::vmx::{vmwrite, vmlaunch};
use x86::vmx::vmcs::control::{PinbasedControls, PINBASED_EXEC_CONTROLS, CR0_READ_SHADOW, CR4_READ_SHADOW};
use x86::vmx::vmcs::guest::{CR0, CR3, CR4, RIP, IA32_EFER_FULL};

use crate::vmx::vmcs::{Vmcs, Vmxon};
use crate::vmx::{self, Monitor};

static mut VMXON: Vmxon = Vmxon::new();
static mut VMCS: Vmcs = Vmcs::new();

#[naked]
unsafe extern "C" fn vm_test() {
    // this is 64-bit
    asm!(
        "mov rax, 2",
        "mov rcx, 2",
        "add rax, rcx",
        "cpuid", // cause an exit
        options(noreturn),
    );
}

pub unsafe fn run() {
    log::debug!("VT-x platform info: {:?}", vmx::get_platform_info());

    let mut vmm = Monitor::new(&mut VMXON);
    log::info!("VMM start -> {:?}", vmm.start());

    VMCS.set_revision(vmm.get_vmcs_revision());
    log::info!("Load VMCS -> {:?}", vmm.load_vmcs(&mut VMCS));

    // VM execution control fields
    //
    // All of this should be moved to Monitor or Vmcs.
    let mut pin_based_controls = PinbasedControls::empty();
    pin_based_controls.insert(PinbasedControls::EXTERNAL_INTERRUPT_EXITING);
    pin_based_controls.insert(PinbasedControls::NMI_EXITING);
    vmwrite(PINBASED_EXEC_CONTROLS, pin_based_controls.bits() as u64).unwrap();

    // What am I doing again?
    let host_cr0 = x86::controlregs::cr0();
    vmwrite(CR0, host_cr0.bits() as u64).unwrap();
    vmwrite(CR0_READ_SHADOW, host_cr0.bits() as u64).unwrap();

    let host_cr3 = x86::controlregs::cr3();
    vmwrite(CR3, host_cr3).unwrap();

    let host_cr4 = x86::controlregs::cr4();
    vmwrite(CR4, host_cr4.bits() as u64).unwrap();
    vmwrite(CR4_READ_SHADOW, host_cr4.bits() as u64).unwrap();

    let host_efer = x86::msr::rdmsr(x86::msr::IA32_EFER);
    vmwrite(IA32_EFER_FULL, host_efer).unwrap();

    let guest_rip = vm_test as *const fn() as u64;
    vmwrite(RIP, guest_rip).unwrap();

    log::info!("VM launch -> {:?}", vmlaunch());

    log::info!("VM-instruction error: {:?}", vmm.get_vm_instruction_error());

    log::info!("VMM stop -> {:?}", vmm.stop());
}

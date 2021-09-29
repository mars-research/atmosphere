use astd::cell::AtomicRefCell;
use crate::error::Result;
use crate::cpu::get_current_vmm;
use crate::vmx::{PlatformInfo, VCpu};

static VCPU: AtomicRefCell<VCpu> = AtomicRefCell::new(VCpu::new());

pub unsafe fn run() -> Result<()> {
    log::debug!("VT-x platform info: {:#?}", PlatformInfo::detect());

    let vmm = get_current_vmm();

    log::info!("VMM start -> {:?}", vmm.start());

    let mut vcpu = VCPU.borrow_mut(); // FIXME: This could panic
    vcpu.init(vmm.get_vmcs_revision())?;
    log::info!("Load VMCS -> {:?}", vmm.load_vcpu(vcpu));

    log::info!("Trying to launch...");
    log::info!("Launch -> {:?}", vmm.demo_launch()?);

    log::info!("Advance RIP -> {:?}", vmm.advance_vmcs_guest_rip()?);

    log::info!("Trying to resume...");
    log::info!("Resume -> {:?}", vmm.launch_current()?);

    log::info!("Register dump -> {:#x?}", vmm.dump_guest_registers()?);

    log::info!("VMM stop -> {:?}", vmm.stop());

    let mut vcpu = VCPU.borrow_mut(); // FIXME: This could panic
    vcpu.deinit().expect("Could not deinitialize the vCPU");

    Ok(())
}

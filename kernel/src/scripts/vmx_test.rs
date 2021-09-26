use crate::error::Result;
use crate::vmx::vmcs::{VCpu, Vmxon};
use crate::vmx::{self, Monitor};

static mut VMXON: Vmxon = Vmxon::new();
static mut VCPU: VCpu = VCpu::new();

pub unsafe fn run() -> Result<()> {
    log::debug!("VT-x platform info: {:?}", vmx::get_platform_info());

    let mut vmm = Monitor::new(&mut VMXON);
    log::info!("VMM start -> {:?}", vmm.start());

    VCPU.init(vmm.get_vmcs_revision())?;
    log::info!("Load VMCS -> {:?}", vmm.load_vcpu(&mut VCPU));

    log::info!("Trying to launch...");
    log::info!("Launch -> {:?}", vmm.demo_launch()?);

    log::info!("Advance RIP -> {:?}", vmm.advance_vmcs_guest_rip()?);

    log::info!("Trying to resume...");
    log::info!("Resume -> {:?}", vmm.launch_current()?);

    log::info!("Register dump -> {:#x?}", vmm.dump_guest_registers()?);

    log::info!("VMM stop -> {:?}", vmm.stop());

    VCPU.deinit().expect("Could not deinitialize the vCPU");

    Ok(())
}

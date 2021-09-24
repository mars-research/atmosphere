use crate::error::Result;
use crate::vmx::vmcs::{Vmcs, Vmxon};
use crate::vmx::{self, Monitor};

static mut VMXON: Vmxon = Vmxon::new();
static mut VMCS: Vmcs = Vmcs::new();

pub unsafe fn run() -> Result<()> {
    log::debug!("VT-x platform info: {:?}", vmx::get_platform_info());

    let mut vmm = Monitor::new(&mut VMXON);
    log::info!("VMM start -> {:?}", vmm.start());

    VMCS.set_revision(vmm.get_vmcs_revision());
    log::info!("Load VMCS -> {:?}", vmm.load_vmcs(&mut VMCS));

    vmm.demo_launch()?;

    log::info!("VMM stop -> {:?}", vmm.stop());

    Ok(())
}

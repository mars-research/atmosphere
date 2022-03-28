//! Scheduler.

use displaydoc::Display;

use astd::collections::deque::Deque;
use super::{ExitReason, VCpu, VCpuHandle, VmxError, VmxResult};
use crate::cpu::get_current_vmm;

/// An action to be taken by the scheduler.
#[derive(Debug)]
pub enum SchedulerAction {
    /// Abort the main loop.
    Abort,

    /// Continue executing.
    Continue,
}

/// An error occurred while pushing a vCPU to the queue.
#[derive(Debug, Display)]
pub enum PushError {
    /// The queue is full.
    QueueFull(VCpuHandle),

    /// Some other VM error occurred: {0}
    VmxError(VmxError),
}

impl From<VmxError> for PushError {
    fn from(error: VmxError) -> Self {
        Self::VmxError(error)
    }
}

/// A handler of scheduler callbacks.
pub trait SchedulerCallbacks<const N: usize>
where
    Self: Sized,
{
    /// Handles a VM exit.
    fn vm_exit(&mut self, vcpu: &mut VCpu, reason: ExitReason) -> SchedulerAction;

    /// Handles the scenario where the queue is empty.
    fn queue_empty(&mut self) -> SchedulerAction {
        SchedulerAction::Continue
    }

    // TODO: Event that all vCPUs are NotReady (do work stealing?)
}

/// A VM scheduler with a queue of N vCPUs.
#[allow(dead_code)] // used in tests
pub struct Scheduler<H: SchedulerCallbacks<N>, const N: usize> {
    /// The queue of vCPUs.
    queue: Deque<VCpuHandle, N>,

    /// Time slice for each vCPU, in cycles.
    quantum: u32,

    /// The callback handler implementing exit-handling logic.
    handler: H,
}

impl<H, const N: usize> Scheduler<H, N>
where
    H: SchedulerCallbacks<N>,
{
    /// Creates a new scheduler.
    pub fn new(handler: H, quantum: u32) -> Self {
        Self {
            queue: Deque::new(),
            quantum,
            handler,
        }
    }

    /// Adds a vCPU to the scheduler.
    ///
    /// This vCPU will be loaded immediately in order to set the
    /// preemption timer.
    ///
    /// If the queue is full, the vCPU will be refunded as an `Err`.
    pub unsafe fn push_vcpu(&mut self, vcpu: VCpuHandle) -> Result<(), PushError> {
        if self.queue.len() >= self.queue.capacity() {
            return Err(PushError::QueueFull(vcpu));
        }

        let vmm = get_current_vmm();
        let cur_vcpu = vmm.load_vcpu(vcpu)?;
        vmm.set_vmcs_preemption_timer_value(Some(self.quantum))?;

        let vcpu = if let Some(cur_vcpu) = cur_vcpu {
            vmm.load_vcpu(cur_vcpu)?.unwrap()
        } else {
            vmm.unload_vcpu()?
        };

        self.queue.push_back(vcpu).unwrap();

        Ok(())
    }

    /// Runs the main loop.
    ///
    /// This will run forever until [`SchedulerAction::Abort`] is issued
    /// by the handler.
    pub unsafe fn run_forever(&mut self) -> VmxResult<()> {
        let vmm = get_current_vmm();

        loop {
            while let Some(vcpu) = self.queue.pop_front() {
                let prev = vmm.load_vcpu(vcpu)?;

                // We assume that there will be at least one space because we popped
                // TODO: Flesh out the work stealing design
                if let Some(prev) = prev {
                    self.queue.push_back(prev).unwrap();
                }

                let exit_reason = vmm.launch_current()?;
                let vcpu = vmm.get_current_vcpu().unwrap();

                match self.handler.vm_exit(vcpu, exit_reason) {
                    SchedulerAction::Continue => {},
                    SchedulerAction::Abort => {
                        let vcpu = vmm.unload_vcpu()?;
                        self.queue.push_back(vcpu).unwrap(); // FIXME: This may not succeed!
                        return Ok(());
                    }
                }
            }

            // Queue is empty - Steal some jobs?
            if let SchedulerAction::Abort = self.handler.queue_empty() {
                return Ok(());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use core::arch::asm;

    use astd::cell::AtomicRefCell;
    use atest::test;
    use crate::vmx::KnownExitReason;
    use super::*;

    static VCPU0: AtomicRefCell<VCpu> = AtomicRefCell::new(VCpu::new());
    static VCPU1: AtomicRefCell<VCpu> = AtomicRefCell::new(VCpu::new());

    static VCPU0_STACK: [u8; 4096] = [0u8; 4096];
    static VCPU1_STACK: [u8; 4096] = [0u8; 4096];

    #[naked]
    unsafe extern "C" fn guest_main() {
        // Repeatedly rdtsc
        asm!(
            // rcx <- initial tsc
            "rdtsc",
            "shl rdx, 32",
            "or rax, rdx",
            "mov rcx, rax",

            "2:",

            // rdi <- tsc
            "rdtsc",
            "shl rdx, 32",
            "or rax, rdx",
            "mov rdi, rax",

            "jmp 2b",
            options(noreturn),
        );
    }

    unsafe fn setup_test_vms() -> (VCpuHandle, VCpuHandle) {
        let vmm = get_current_vmm();
        vmm.start().expect("Could not start VMM");

        let vcpu0 = {
            let mut vcpu0 = VCPU0.borrow_mut();
            vcpu0.init(vmm.get_vmcs_revision()).unwrap();

            vmm.load_vcpu(vcpu0).unwrap();
            vmm.init_vmcs_controls().unwrap();
            vmm.init_vmcs_guest_state().unwrap();
            vmm.copy_vmcs_host_state_to_guest().unwrap();

            let stack_end = (&VCPU0_STACK as *const u8).offset(4096) as u64;
            let target = guest_main as *const () as u64;
            vmm.set_vmcs_guest_entrypoint(target, stack_end).unwrap();

            vmm.mark_vcpu_ready().unwrap();
            vmm.unload_vcpu().unwrap()
        };

        let vcpu1 = {
            let mut vcpu1 = VCPU1.borrow_mut();
            vcpu1.init(vmm.get_vmcs_revision()).unwrap();

            vmm.load_vcpu(vcpu1).unwrap();
            vmm.init_vmcs_controls().unwrap();
            vmm.init_vmcs_guest_state().unwrap();
            vmm.copy_vmcs_host_state_to_guest().unwrap();

            let stack_end = (&VCPU1_STACK as *const u8).offset(4096) as u64;
            let target = guest_main as *const () as u64;
            vmm.set_vmcs_guest_entrypoint(target, stack_end).unwrap();

            vmm.mark_vcpu_ready().unwrap();
            vmm.unload_vcpu().unwrap()
        };

        vmm.stop().unwrap();

        (vcpu0, vcpu1)
    }

    struct Run100TimesHandler {
        counter: usize,
    }

    impl Run100TimesHandler {
        fn new() -> Self {
            Self {
                counter: 0,
            }
        }
    }

    impl SchedulerCallbacks<2> for Run100TimesHandler {
        fn vm_exit(&mut self, _vcpu: &mut VCpu, reason: ExitReason) -> SchedulerAction {
            assert_eq!(reason, KnownExitReason::PreemptionTimerExpired);

            if self.counter == 100 {
                // 100_000 cycles in total
                SchedulerAction::Abort
            } else {
                self.counter += 1;

                SchedulerAction::Continue
            }
        }
    }

    #[test]
    fn test_scheduler() {
        let (vcpu0, vcpu1) = unsafe { setup_test_vms() };

        let vmm = get_current_vmm();
        unsafe {
            vmm.start().expect("Could not start VMM");
        }

        let handler = Run100TimesHandler::new();
        let mut scheduler = Scheduler::<Run100TimesHandler, 2>::new(handler, 100);

        unsafe {
            scheduler.push_vcpu(vcpu0).unwrap();
            scheduler.push_vcpu(vcpu1).unwrap();
            scheduler.run_forever().unwrap();
        }

        // Verify that both VMs have made progress
        let cycles1 = {
            let vcpu = scheduler.queue.pop_front().unwrap();
            vmm.load_vcpu(vcpu).unwrap();
            let reg = vmm.dump_guest_registers().unwrap();

            reg.rdi - reg.rcx
        };
        let cycles2 = {
            let vcpu = scheduler.queue.pop_front().unwrap();
            vmm.load_vcpu(vcpu).unwrap();
            let reg = vmm.dump_guest_registers().unwrap();

            reg.rdi - reg.rcx
        };

        let ratio = cycles1 as f32 / cycles2 as f32;

        log::info!("Cycles #1 = {}", cycles1);
        log::info!("Cycles #2 = {}", cycles2);
        log::info!("Ratio = {}", ratio);

        if ratio < 0.9 || ratio > 1.1 {
            panic!("Cycle difference must be under 10%");
        }

        vmm.stop()
            .expect("Could not stop VMM");
    }
}

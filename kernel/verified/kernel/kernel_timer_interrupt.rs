use vstd::prelude::*;
verus! {

use crate::define::*;
use crate::trap::*;
use crate::kernel::Kernel;

impl Kernel {
    /// Handles the timer interrupt that ends a time slice on `cpu_id`.
    ///
    /// `pt_regs` is the context that the interrupt took from user mode. If the kernel switches
    /// threads, `pt_regs` holds the context of the next thread on return, and the caller loads
    /// the address space that the return value names. Scheduling is round-robin in the run queue
    /// of the container that owns the CPU; see `ProcessManager::preempt_spec`.
    ///
    /// The thread keeps the CPU (`NoSwitch`) if no other thread of the container is runnable,
    /// and also if the run queue is full, because there is no room to queue the thread.
    pub fn timer_interrupt(&mut self, cpu_id: CpuId, pt_regs: &mut Registers) -> (ret:
        SyscallReturnStruct)
        requires
            old(self).wf(),
            0 <= cpu_id < NUM_CPUS,
        ensures
            self.wf(),
            ret.switch_decision == SwitchDecision::NoSwitch ==> *self == *old(self) && *pt_regs
                == *old(pt_regs),
            ret.switch_decision != SwitchDecision::NoSwitch ==> self.get_cpu(
                cpu_id,
            ).current_thread.is_Some() && self.proc_man.preempt_spec(
                old(self).proc_man,
                cpu_id,
                self.get_cpu(cpu_id).current_thread.unwrap(),
            ),
    {
        proof {
            self.proc_man.thread_inv();
            self.proc_man.endpoint_inv();
            self.proc_man.container_inv();
            self.proc_man.cpu_inv();
        }

        let switched = self.proc_man.preempt_running_thread(cpu_id, pt_regs);
        if switched.is_none() {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Else);
        }
        let (next_thread_ptr, preempted) = switched.unwrap();
        let proc_ptr = self.proc_man.get_thread(next_thread_ptr).owning_proc;
        let pcid = self.proc_man.get_proc(proc_ptr).pcid;
        let cr3 = self.mem_man.get_cr3_by_pcid(pcid);
        if preempted {
            return SyscallReturnStruct::SwitchPreemptedNew(RetValueType::Else, cr3, pcid);
        }
        return SyscallReturnStruct::SwitchNew(RetValueType::Else, cr3, pcid);
    }
}

} // verus!

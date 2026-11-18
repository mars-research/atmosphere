use vstd::prelude::*;
verus! {

// use crate::allocator::page_allocator_spec_impl::*;
// use crate::memory_manager::spec_impl::*;
// use crate::process_manager::spec_proof::*;
// use crate::util::page_ptr_util_u::*;
use crate::define::*;
use crate::trap::*;
use crate::kernel::Kernel;

impl Kernel {
    pub fn schedule_idle_cpu(&mut self, cpu_id: CpuId, pt_regs: &mut Registers) -> (ret:
        SyscallReturnStruct)
        requires
            old(self).wf(),
            0 <= cpu_id < NUM_CPUS,
        ensures
            self.wf(),
    {
        proof {
            self.proc_man.thread_inv();
            self.proc_man.endpoint_inv();
            self.proc_man.container_inv();
            self.proc_man.cpu_inv();
        }

        let container_ptr = self.proc_man.cpu_list.get(cpu_id).owning_container;

        if self.proc_man.cpu_list.get(cpu_id).active == false {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.cpu_list.get(cpu_id).current_thread.is_some() {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_container(container_ptr).scheduler.len() == 0 {
            return SyscallReturnStruct::NoNextThreadNew(RetValueType::Error);
        }
        let ret_thread_ptr = self.proc_man.pop_scheduler_for_idle_cpu(cpu_id, pt_regs);
        // The fast restore above is enough for a thread that entered the kernel through a
        // syscall. A thread that an interrupt took off the CPU gets every register back.
        let preempted = self.proc_man.take_preempted_trap_frame(ret_thread_ptr, pt_regs);
        let proc_ptr = self.proc_man.get_thread(ret_thread_ptr).owning_proc;
        let pcid = self.proc_man.get_proc(proc_ptr).pcid;
        let cr3 = self.mem_man.get_cr3_by_pcid(pcid);
        if preempted {
            return SyscallReturnStruct::SwitchPreemptedNew(RetValueType::Else, cr3, pcid);
        }
        return SyscallReturnStruct::SwitchNew(RetValueType::Else, cr3, pcid);
    }
}

} // verus!

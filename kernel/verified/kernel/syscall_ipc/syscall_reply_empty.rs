use vstd::prelude::*;
verus! {

// use crate::array_vec::*;
// use crate::proc::*;
// use crate::page_alloc::*;
// use crate::cpu::*;
// use crate::mars_array::MarsArray;
use crate::proc::*;
use crate::pagetable::*;
use crate::cpu::*;
use crate::define::*;
use crate::trap::*;
// use crate::page_alloc::*;

use crate::kernel::*;

pub closed spec fn syscall_reply_empty_spec(old:Kernel, new:Kernel, cpu_id:CPUID) -> bool
{
    if !old.wf() || !new.wf()
    {
        false
    }
    else{
        let valid_thread = (cpu_id < NUM_CPUS &&
            old.cpu_list@[cpu_id as int].get_is_idle() == false);
        let has_caller = old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).caller.is_Some();
        let system_scheduler_has_space = old.proc_man.scheduler.len() != MAX_NUM_THREADS;

        if valid_thread && has_caller && system_scheduler_has_space
        {
            forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
            &&
            new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).caller.get_Some_0())
            &&
            new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
            &&
            new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
        }else{
            //if the syscall is not success, nothing will change, goes back to user level
            old == new
        }

    }
}

impl Kernel {
    pub fn syscall_reply_empty(&mut self, cpu_id:CPUID, pt_regs: &mut Registers) -> (ret: SyscallReturnStruct)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            syscall_reply_empty_spec(*old(self),*self, cpu_id),
    {
        let (default_pcid, default_cr3) = self.mmu_man.get_reserved_pcid_and_cr3();
        if cpu_id >= NUM_CPUS{
            return SyscallReturnStruct::new(CPU_ID_INVALID,default_pcid,default_cr3,0);
        }

        if self.cpu_list.get(cpu_id).get_is_idle() {
            return SyscallReturnStruct::new(CPU_NO_IDLE,default_pcid,default_cr3,0);
        }

        assert(self.cpu_list[cpu_id as int].get_is_idle() == false);
        let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
        assert(current_thread_ptr_op.is_Some());
        let current_thread_ptr = current_thread_ptr_op.unwrap();

        let pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
        let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);

        let caller_ptr_op = self.proc_man.get_thread_caller(current_thread_ptr);

        if caller_ptr_op.is_none() {
            return SyscallReturnStruct::new(NO_CALLER,pcid,cr3,current_thread_ptr);
        }

        if self.proc_man.scheduler.len() == MAX_NUM_THREADS {

            return SyscallReturnStruct::new(SCHEDULER_NO_SPACE,pcid,cr3,current_thread_ptr);
        }
        let caller_ptr = caller_ptr_op.unwrap();

        let new_pcid = self.proc_man.get_pcid_by_thread_ptr(caller_ptr);
        let new_cr3 = self.mmu_man.get_cr3_by_pcid(new_pcid);

        self.proc_man.weak_up_caller_and_schedule(caller_ptr, current_thread_ptr, pt_regs, Some(SUCCESS));
        self.cpu_list.set_current_thread(cpu_id,Some(caller_ptr));
        return SyscallReturnStruct::new(SUCCESS,new_pcid,new_cr3,caller_ptr);

    }
}
}

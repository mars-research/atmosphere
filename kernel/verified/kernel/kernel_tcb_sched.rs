use vstd::prelude::*;
verus! {

// use crate::array_vec::*;
// use crate::proc::*;
// use crate::page_alloc::*;
// use crate::cpu::*;
// use crate::mars_array::MarsArray;
// use crate::pagetable::*;
use crate::cpu::*;
use crate::define::*;
use crate::trap::*;
// use crate::page_alloc::*;

use crate::kernel::*;

pub closed spec fn kernel_timer_int_spec(old:Kernel,new:Kernel,cpu_id:CPUID) -> bool
{
    if !old.wf() || !new.wf()
    {
        false
    }
    else{
        //checking arguments
        let valid_thread = (cpu_id < NUM_CPUS &&
            old.cpu_list@[cpu_id as int].get_is_idle() == false);
        let scheduler_has_thread = old.proc_man.scheduler.len() != 0;

        if valid_thread && scheduler_has_thread
        {
            forall|i:CPUID|#![auto] 0 <= i < NUM_CPUS && i != cpu_id ==> new.cpu_list@[i as int] =~= old.cpu_list@[i as int]
            &&
            new.cpu_list@[cpu_id as int].get_current_thread().unwrap() =~= old.proc_man.scheduler@[0]
            &&
            new.proc_man.scheduler@ =~= old.proc_man.scheduler@.subrange(1, old.proc_man.scheduler.len() as int).push(old.cpu_list@[cpu_id as int].get_current_thread().unwrap())
            &&
            new.mmu_man =~= old.mmu_man
            &&
            new.page_alloc =~= old.page_alloc
        }else{
            //if the syscall is not success, nothing will change, goes back to user level
            old =~= new
        }
    }
}

pub closed spec fn kernel_idle_pop_sched_spec(old:Kernel,new:Kernel,cpu_id:CPUID) -> bool
{
    if !old.wf() || !new.wf()
    {
        false
    }
    else{
        //checking arguments
        let cpu_idle = (cpu_id < NUM_CPUS &&
            old.cpu_list@[cpu_id as int].get_is_idle());
        let scheduler_has_thread = old.proc_man.scheduler.len() != 0;

        if cpu_idle && scheduler_has_thread
        {
            forall|i:CPUID|#![auto] 0 <= i < NUM_CPUS && i != cpu_id ==> new.cpu_list@[i as int] =~= old.cpu_list@[i as int]
            &&
            new.cpu_list@[cpu_id as int].get_current_thread().unwrap() =~= old.proc_man.scheduler@[0]
            &&
            new.proc_man.scheduler@ =~= old.proc_man.scheduler@.subrange(1, old.proc_man.scheduler.len() as int)
            &&
            new.mmu_man =~= old.mmu_man
            &&
            new.page_alloc =~= old.page_alloc
        }else{
            //if the syscall is not success, nothing will change, goes back to user level
            old =~= new
        }
    }

}

impl Kernel {
    pub fn kernel_timer_int(&mut self, cpu_id:CPUID, pt_regs: PtRegs) -> (ret:SyscallReturnStruct)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            kernel_timer_int_spec(*old(self), *self, cpu_id),
    {
        let (default_pcid, default_cr3) = self.mmu_man.get_reserved_pcid_and_cr3();
        if cpu_id >= NUM_CPUS{
            return SyscallReturnStruct::new(CPU_ID_INVALID,default_pcid,default_cr3,pt_regs);
        }

        if self.cpu_list.get(cpu_id).get_is_idle() {
            return SyscallReturnStruct::new(CPU_NO_IDLE,default_pcid,default_cr3,pt_regs);
        }
        if self.proc_man.scheduler.len() == 0 {
            let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
            assert(current_thread_ptr_op.is_Some());
            let current_thread_ptr = current_thread_ptr_op.unwrap();
            let current_proc_ptr = self.proc_man.get_parent_proc_ptr_by_thread_ptr(current_thread_ptr);

            let pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
            let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);
            assert(self.wf());
            return SyscallReturnStruct::new(SCHEDULER_EMPTY,pcid,cr3,pt_regs);
        }
        else if self.proc_man.scheduler.len() == MAX_NUM_THREADS {
                let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
                assert(current_thread_ptr_op.is_Some());
                let current_thread_ptr = current_thread_ptr_op.unwrap();
                let current_proc_ptr = self.proc_man.get_parent_proc_ptr_by_thread_ptr(current_thread_ptr);
                let (new_thread_ptr,new_pt_regs,error_code)  = self.proc_man.pop_scheduler();
                self.proc_man.push_scheduler(current_thread_ptr, Some(SUCCESS),pt_regs);
                let old_tlb = self.cpu_list.get(cpu_id).tlb;
                let old_iotlb = self.cpu_list.get(cpu_id).iotlb;
                self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));

                let new_pcid = self.proc_man.get_pcid_by_thread_ptr(new_thread_ptr);
                let new_cr3 = self.mmu_man.get_cr3_by_pcid(new_pcid);
                assert(self.wf());
                if error_code.is_none() {
                    return SyscallReturnStruct::new(NO_ERROR_CODE,new_pcid,new_cr3,new_pt_regs);
                }else{
                    return SyscallReturnStruct::new(error_code.unwrap(),new_pcid,new_cr3,new_pt_regs);
                }
        }
        else{
            let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
            assert(current_thread_ptr_op.is_Some());
            let current_thread_ptr = current_thread_ptr_op.unwrap();
            let (new_thread_ptr,new_pt_regs,error_code)  = self.proc_man.pop_scheduler();
            self.proc_man.push_scheduler(current_thread_ptr, Some(SUCCESS),pt_regs);
            let old_tlb = self.cpu_list.get(cpu_id).tlb;
            let old_iotlb = self.cpu_list.get(cpu_id).iotlb;
            self.cpu_list.set(cpu_id, Cpu{
                current_t: Some(new_thread_ptr),
                tlb: old_tlb,
                iotlb: old_iotlb,
            });
            let new_pcid = self.proc_man.get_pcid_by_thread_ptr(new_thread_ptr);
            let new_cr3 = self.mmu_man.get_cr3_by_pcid(new_pcid);
            assert(self.wf());
            if error_code.is_none() {
                return SyscallReturnStruct::new(NO_ERROR_CODE,new_pcid,new_cr3,new_pt_regs);
            }else{
                return SyscallReturnStruct::new(error_code.unwrap(),new_pcid,new_cr3,new_pt_regs);
            }
        }
    }
    pub fn kernel_idle_pop_sched(&mut self, cpu_id:CPUID, pt_regs: PtRegs) -> (ret:SyscallReturnStruct)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            kernel_idle_pop_sched_spec(*old(self), *self, cpu_id),
    {
        let (default_pcid, default_cr3) = self.mmu_man.get_reserved_pcid_and_cr3();
        if cpu_id >= NUM_CPUS{
            return SyscallReturnStruct::new(CPU_ID_INVALID,default_pcid,default_cr3,pt_regs);
        }

        if self.cpu_list.get(cpu_id).get_is_idle() == false {
            return SyscallReturnStruct::new(CPU_NO_IDLE,default_pcid,default_cr3,pt_regs);
        }
        if self.proc_man.scheduler.len() == 0 {
            assert(self.wf());
            return SyscallReturnStruct::new(SCHEDULER_EMPTY,default_pcid,default_cr3,pt_regs);
        }

        let (new_thread_ptr,new_pt_regs,error_code)  = self.proc_man.pop_scheduler();
        assert(old(self).proc_man.get_thread(new_thread_ptr).state == SCHEDULED);
        self.cpu_list.set_current_thread(cpu_id, Some(new_thread_ptr));
        let new_pcid = self.proc_man.get_pcid_by_thread_ptr(new_thread_ptr);
        let new_cr3 = self.mmu_man.get_cr3_by_pcid(new_pcid);
        assert(self.wf());
        if error_code.is_none() {
            return SyscallReturnStruct::new(NO_ERROR_CODE,new_pcid,new_cr3,new_pt_regs);
        }else{
            return SyscallReturnStruct::new(error_code.unwrap(),new_pcid,new_cr3,new_pt_regs);
        }

    }
}

pub fn hello_world() -> (ret:usize){
    return 233;
}
}

use vstd::prelude::*;
verus! {

// use crate::array_vec::*;
// use crate::proc::*;
// use crate::page_alloc::*;
// use crate::cpu::*;
// use crate::mars_array::MarsArray;
use crate::pagetable::*;
use crate::cpu::*;
use crate::define::*;
use crate::trap::*;
// use crate::page_alloc::*;

use crate::kernel::*;

pub closed spec fn syscall_new_thread_spec(old:Kernel,new:Kernel,cpu_id:CPUID, endpoint_index: EndpointIdx, proc:Option<ProcPtr>, new_thread:Option<ThreadPtr>) -> bool
{
    if !old.wf() || !new.wf()
    {
        false
    }
    else{
        //checking arguments
        let valid_thread = (cpu_id < NUM_CPUS &&
            old.cpu_list@[cpu_id as int].get_is_idle() == false);
        let valid_endpoint = (endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS &&
            old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int] != 0 &&
            old.proc_man.get_endpoint(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int]).rf_counter != usize::MAX);
        let system_has_memory = old.page_alloc.free_pages.len() >= 1;
        let system_scheduler_has_space = old.proc_man.scheduler.len() != MAX_NUM_THREADS;
        let proc_thread_list_has_space = old.proc_man.proc_perms@[old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent]@.value.get_Some_0().owned_threads.len() < MAX_NUM_THREADS_PER_PROC;

        if valid_thread && valid_endpoint && system_has_memory && system_scheduler_has_space && proc_thread_list_has_space
        {
            (
                //if the syscall is success, a new process and a new thread of the new process will be created
                proc.is_Some()
                &&
                proc.unwrap() == old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent
                &&
                new_thread.is_Some()
                &&
                //each cpu still runs the same thread, no context switch
                new.cpu_list =~= old.cpu_list
                &&
                // kernel correctly created a new process
                new.proc_man.get_proc_ptrs() =~= old.proc_man.get_proc_ptrs()
                &&
                // kernel correctly created a new thread for that process
                new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs().insert(new_thread.unwrap())
                &&
                // the new thread is scheduled
                new.proc_man.get_thread(new_thread.unwrap()).state == SCHEDULED
                &&
                // the new thread stores the endpoint from the parent process at 1st slot
                new.proc_man.get_thread(new_thread.unwrap()).endpoint_descriptors@[0] =~= new.proc_man.get_thread(new.cpu_list[cpu_id as int].current_t.unwrap()).endpoint_descriptors@[endpoint_index as int]
                &&
                // the new proccess's pagetable is empty. There are kernel and loader mapped in this new pagetable, but they are transparent to user level
                forall|va:VAddr| #![auto] spec_va_valid(va) ==> new.mmu_man.get_pagetable_by_pcid(new.proc_man.get_proc(new.proc_man.get_thread(new_thread.unwrap()).parent).pcid).get_pagetable_mapping()[va].is_None()
                &&
                forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                &&
                forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                &&
                forall|proc_ptr:ProcPtr|#![auto] old.proc_man.get_proc_ptrs().contains(proc_ptr) ==> new.proc_man.get_proc(proc_ptr) =~= old.proc_man.get_proc(proc_ptr)
                &&
                forall|thread_ptr:ThreadPtr|#![auto] old.proc_man.get_thread_ptrs().contains(thread_ptr) ==> new.proc_man.get_thread(thread_ptr) =~= old.proc_man.get_thread(thread_ptr)
                &&
                forall|endpoint_ptr:EndpointPtr|#![auto] old.proc_man.get_endpoint_ptrs().contains(endpoint_ptr) ==> new.proc_man.get_endpoint(endpoint_ptr) =~= old.proc_man.get_endpoint(endpoint_ptr)
            )
        }else{
            //if the syscall is not success, nothing will change, goes back to user level
            old =~= new
        }
    }

}


impl Kernel {

    pub fn syscall_new_thread(&mut self, cpu_id:CPUID, pt_regs: PtRegs, endpoint_index: EndpointIdx, pt_regs_new_thread: PtRegs) -> (ret:(SyscallReturnStruct,Option<ProcPtr>,Option<ThreadPtr>))
        requires
            old(self).wf(),
        ensures
            self.wf(),
    {
        let (default_pcid, default_cr3) = self.mmu_man.get_reserved_pcid_and_cr3();
        if cpu_id >= NUM_CPUS{
            return (SyscallReturnStruct::new(CPU_ID_INVALID,default_pcid,default_cr3,pt_regs),None,None);
        }

        if self.cpu_list.get(cpu_id).get_is_idle() {
            return (SyscallReturnStruct::new(NO_RUNNING_THREAD,default_pcid,default_cr3,pt_regs),None,None);
        }
        assert(self.cpu_list[cpu_id as int].get_is_idle() == false);
        let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
        assert(current_thread_ptr_op.is_Some());
        let current_thread_ptr = current_thread_ptr_op.unwrap();
        let current_proc_ptr = self.proc_man.get_parent_proc_ptr_by_thread_ptr(current_thread_ptr);

        let pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
        let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);

        if endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS{
            return (SyscallReturnStruct::new(ENDPOINT_INDEX_INVALID,pcid,cr3,pt_regs),None,None);
        }

        let target_endpoint_ptr = self.proc_man.get_thread_endpoint_ptr_by_endpoint_idx(current_thread_ptr, endpoint_index);
        if target_endpoint_ptr == 0 {
            return (SyscallReturnStruct::new(SHARED_ENDPOINT_NOT_EXIST,pcid,cr3,pt_regs),None,None);
        }
        assert(self.proc_man.endpoint_perms@.dom().contains(target_endpoint_ptr));

        if self.proc_man.get_endpoint_rf_counter_by_endpoint_ptr(target_endpoint_ptr) == usize::MAX {
            return (SyscallReturnStruct::new(SHARED_ENDPOINT_REF_COUNT_OVERFLOW,pcid,cr3,pt_regs),None,None);
        }

        if self.page_alloc.free_pages.len() < 1 {
            return (SyscallReturnStruct::new(SYSTEM_OUT_OF_MEM,pcid,cr3,pt_regs),None,None);
        }

        if self.proc_man.scheduler.len() == MAX_NUM_THREADS{
            return (SyscallReturnStruct::new(SCHEDULER_NO_SPACE,pcid,cr3,pt_regs),None,None);
        }
        if self.mmu_man.free_pcids.len() == 0 {
            return (SyscallReturnStruct::new(NO_FREE_PCID,pcid,cr3,pt_regs),None,None);
        }

        if self.proc_man.get_proc_num_of_threads_by_proc_ptr(current_proc_ptr) >= MAX_NUM_THREADS_PER_PROC {
            return (SyscallReturnStruct::new(PROC_THREAD_LIST_FULL,pcid,cr3,pt_regs),None,None);
        }

        let (page_ptr1, page_perm1) = self.page_alloc.alloc_kernel_mem();
        let new_thread = self.proc_man.new_thread_with_endpoint_ptr(pt_regs_new_thread,page_ptr1, page_perm1,current_proc_ptr, target_endpoint_ptr);


        assert(self.wf());
        return (SyscallReturnStruct::new(SUCCESS,pcid,cr3,pt_regs),None,None);
    }

}
}

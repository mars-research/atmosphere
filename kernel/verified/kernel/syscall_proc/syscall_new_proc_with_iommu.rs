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

pub closed spec fn syscall_new_proc_with_iommu_spec(old:Kernel,new:Kernel,cpu_id:CPUID, endpoint_index: EndpointIdx, new_proc:Option<ProcPtr>, new_thread:Option<ThreadPtr>) -> bool 
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
        let proc_list_has_space = old.proc_man.proc_ptrs.len() != MAX_NUM_PROCS;
        let system_has_memory = old.page_alloc.free_pages.len() >= 5;
        let system_has_free_pcid_ioid = old.mmu_man.free_pcids.len() != 0 && old.mmu_man.free_ioids.len() != 0;
        let system_scheduler_has_space = old.proc_man.scheduler.len() != MAX_NUM_THREADS;

        if valid_thread && valid_endpoint && proc_list_has_space && system_has_memory && system_has_free_pcid_ioid && system_scheduler_has_space
        {
            (
                //if the syscall is success, a new process and a new thread of the new process will be created
                new_proc.is_Some()
                &&
                new_thread.is_Some()
                &&
                //each cpu still runs the same thread, no context switch
                new.cpu_list =~= old.cpu_list
                &&
                // kernel correctly created a new process
                new.proc_man.get_proc_ptrs() =~= old.proc_man.get_proc_ptrs().push(new_proc.unwrap())
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
            )
        }else{
            //if the syscall is not success, nothing will change, goes back to user level
            old =~= new
        }
    }
}

impl Kernel {


    pub fn syscall_new_proc_with_iommu(&mut self, cpu_id:CPUID, endpoint_index: EndpointIdx, pt_regs_new_proc: Registers) -> (ret:(SyscallReturnStruct,Option<ProcPtr>, Option<ThreadPtr>,Option<usize>))
        requires
            old(self).wf(),
        ensures
            self.wf(),
            syscall_new_proc_with_iommu_spec(*old(self), *self, cpu_id, endpoint_index, ret.1, ret.2)
    {
        let (default_pcid, default_cr3) = self.mmu_man.get_reserved_pcid_and_cr3();
        if cpu_id >= NUM_CPUS{
            return (SyscallReturnStruct::new(CPU_ID_INVALID,default_pcid,default_cr3),None,None,None);
        }else if self.cpu_list.get(cpu_id).get_is_idle() {
            return (SyscallReturnStruct::new(NO_RUNNING_THREAD,default_pcid,default_cr3),None,None,None);
        }else{
            assert(self.cpu_list[cpu_id as int].get_is_idle() == false);
            let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
            assert(current_thread_ptr_op.is_Some());
            let current_thread_ptr = current_thread_ptr_op.unwrap();

            let pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
            let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);

            if endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS{
                return (SyscallReturnStruct::new(ENDPOINT_INDEX_INVALID,pcid,cr3),None,None,None);
            }else{
                let target_endpoint_ptr = self.proc_man.get_thread_endpoint_ptr_by_endpoint_idx(current_thread_ptr, endpoint_index);
                if target_endpoint_ptr == 0 {
                    return (SyscallReturnStruct::new(SHARED_ENDPOINT_NOT_EXIST,pcid,cr3),None,None,None);
                }
                else if self.proc_man.get_endpoint_rf_counter_by_endpoint_ptr(target_endpoint_ptr) == usize::MAX {
                    return (SyscallReturnStruct::new(SHARED_ENDPOINT_REF_COUNT_OVERFLOW,pcid,cr3),None,None,None);
                }else if self.page_alloc.free_pages.len() < 5 {
                    return (SyscallReturnStruct::new(SYSTEM_OUT_OF_MEM,pcid,cr3),None,None,None);
                }else if self.proc_man.scheduler.len() == MAX_NUM_THREADS{
                    return (SyscallReturnStruct::new(SCHEDULER_NO_SPACE,pcid,cr3),None,None,None);
                }else if self.proc_man.proc_ptrs.len() == MAX_NUM_PROCS {
                    return (SyscallReturnStruct::new(PROCESS_LIST_NO_SPEC,pcid,cr3),None,None,None);
                }else if self.mmu_man.free_pcids.len() == 0 {
                    return (SyscallReturnStruct::new(NO_FREE_PCID,pcid,cr3),None,None,None);
                }else if self.mmu_man.free_ioids.len() == 0 {
                    return (SyscallReturnStruct::new(NO_FREE_IOID,pcid,cr3),None,None,None);
                }else{
                    let (page_ptr1, page_perm1) = self.page_alloc.alloc_pagetable_mem();
                    let new_pcid = self.mmu_man.new_pagetable(page_ptr1,page_perm1,Some(self.kernel_pml4_entry));
                    let (page_ptr2, page_perm2) = self.page_alloc.alloc_pagetable_mem();
                    let new_ioid = self.mmu_man.new_iommutable(page_ptr2,page_perm2);
                    let iommutable_cr3 = self.mmu_man.get_cr3_by_ioid(new_ioid);
                    let (page_ptr3, page_perm3) = self.page_alloc.alloc_kernel_mem();
                    let (page_ptr4, page_perm4) = self.page_alloc.alloc_kernel_mem();
                    let new_proc = self.proc_man.new_proc(page_ptr3, page_perm3, new_pcid, Some(new_ioid));
                    let new_thread = self.proc_man.new_thread_with_endpoint_ptr(pt_regs_new_proc,page_ptr4, page_perm4,new_proc, target_endpoint_ptr);

                    return (SyscallReturnStruct::new(SUCCESS,pcid,cr3),Some(new_proc),Some(new_thread),Some(iommutable_cr3));
                }
            }

        }
    }
}
}

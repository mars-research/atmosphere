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




impl Kernel {

    pub fn syscall_new_proc_pass_mem(&mut self, cpu_id:CPUID, endpoint_index: EndpointIdx, pt_regs_new_proc: Registers) -> (ret:(SyscallReturnStruct,Option<ProcPtr>,Option<ThreadPtr>))
        requires
            old(self).wf(),
        ensures
            // kernel is well-formed
            self.wf(),
            syscall_new_proc_spec(*old(self), *self, cpu_id, endpoint_index, ret.1, ret.2),
    {
        let (default_pcid, default_cr3) = self.mmu_man.get_reserved_pcid_and_cr3();
        if cpu_id >= NUM_CPUS{
            assert(self == old(self));
            return (SyscallReturnStruct::new(CPU_ID_INVALID,default_pcid,default_cr3,0),None,None);
        }else if self.cpu_list.get(cpu_id).get_is_idle() {
            assert(self == old(self));
            return (SyscallReturnStruct::new(NO_RUNNING_THREAD,default_pcid,default_cr3,0),None,None);
        }else{
            assert(self.cpu_list[cpu_id as int].get_is_idle() == false);
            let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
            assert(current_thread_ptr_op.is_Some());
            let current_thread_ptr = current_thread_ptr_op.unwrap();

            let pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
            let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);

            if endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS{
                assert(self == old(self));
                return (SyscallReturnStruct::new(ENDPOINT_INDEX_INVALID,pcid,cr3,current_thread_ptr),None,None);
            }else{
                let target_endpoint_ptr = self.proc_man.get_thread_endpoint_ptr_by_endpoint_idx(current_thread_ptr, endpoint_index);
                if target_endpoint_ptr == 0 {
                    assert(self == old(self));
                    return (SyscallReturnStruct::new(SHARED_ENDPOINT_NOT_EXIST,pcid,cr3,current_thread_ptr),None,None);
                }else if self.proc_man.get_endpoint_rf_counter_by_endpoint_ptr(target_endpoint_ptr) == usize::MAX {
                    assert(self == old(self));
                    return (SyscallReturnStruct::new(SHARED_ENDPOINT_REF_COUNT_OVERFLOW,pcid,cr3,current_thread_ptr),None,None);
                }else if self.page_alloc.free_pages.len() < 4 {
                    assert(self == old(self));
                    return (SyscallReturnStruct::new(SYSTEM_OUT_OF_MEM,pcid,cr3,current_thread_ptr),None,None);
                }else if self.proc_man.scheduler.len() == MAX_NUM_THREADS{
                    assert(self == old(self));
                    return (SyscallReturnStruct::new(SCHEDULER_NO_SPACE,pcid,cr3,current_thread_ptr),None,None);
                }else if self.proc_man.proc_ptrs.len() == MAX_NUM_PROCS {
                    assert(self == old(self));
                    return (SyscallReturnStruct::new(PROCESS_LIST_NO_SPEC,pcid,cr3,current_thread_ptr),None,None);
                }else if self.mmu_man.free_pcids.len() == 0 {
                    assert(self == old(self));
                    return (SyscallReturnStruct::new(NO_FREE_PCID,pcid,cr3,current_thread_ptr),None,None);
                }else{
                    let (page_ptr1, page_perm1) = self.page_alloc.alloc_pagetable_mem();
                    let new_pcid = self.mmu_man.new_pagetable(page_ptr1,page_perm1,Some(self.kernel_pml4_entry));
                    let (page_ptr2, page_perm2) = self.page_alloc.alloc_kernel_mem();
                    let (page_ptr3, page_perm3) = self.page_alloc.alloc_kernel_mem();
                    let new_proc = self.proc_man.new_proc(page_ptr2, page_perm2, new_pcid, None);
                    let new_thread = self.proc_man.new_thread_with_endpoint_ptr(pt_regs_new_proc,page_ptr3, page_perm3,new_proc, target_endpoint_ptr);
                    // assert(self.wf());
                    // self.proc_man.pass_endpoint(current_thread_ptr,endpoint_index,new_thread,0);
                    assert(self.wf());
                    return (SyscallReturnStruct::new(SUCCESS,pcid,cr3,current_thread_ptr),Some(new_proc),Some(new_thread));
                }


            }
        }
    }
}
}

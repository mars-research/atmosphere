use vstd::prelude::*;
verus!{

// use crate::array_vec::*;
use crate::proc::*;
// use crate::page_alloc::*;
// use crate::cpu::*;
// use crate::mars_array::MarsArray;
use crate::pagetable::*;
use crate::cpu::*;
use crate::define::*;
use crate::trap::*;
use crate::page_alloc::*;

use crate::kernel::*;


impl Kernel {

    pub fn kernel_push_current_thread_to_endpoint(&mut self, cpu_id:CPUID, thread_ptr: ThreadPtr, endpoint_idx: EndpointIdx, ipc_payload: IPCPayLoad, pt_regs: Registers) 
        requires
            old(self).wf(),
            0<=cpu_id<NUM_CPUS,
            old(self).cpu_list@[cpu_id as int].get_is_idle() == false,
            old(self).cpu_list@[cpu_id as int].get_current_thread().unwrap() == thread_ptr,
            0<=endpoint_idx<MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).proc_man.get_thread(thread_ptr).endpoint_descriptors@[endpoint_idx as int] != 0,
            old(self).proc_man.get_endpoint(old(self).proc_man.get_thread(thread_ptr).endpoint_descriptors@[endpoint_idx as int]).len() < MAX_NUM_THREADS_PER_ENDPOINT,
    {
        if self.proc_man.scheduler.len() == 0{
            assert(self.proc_man.get_thread(thread_ptr).endpoint_descriptors@[endpoint_idx as int] != 0);
            self.proc_man.set_thread_to_transit(thread_ptr);
            self.proc_man.push_endpoint(thread_ptr, endpoint_idx, ipc_payload);
            self.cpu_list.set_current_thread(cpu_id, None);
            assert(self.wf());
        }else{
            self.proc_man.set_thread_to_transit(thread_ptr);
            self.proc_man.push_endpoint(thread_ptr, endpoint_idx, ipc_payload);
            let new_thread_ptr = self.proc_man.pop_scheduler();
            self.cpu_list.set_current_thread(cpu_id, Some(new_thread_ptr));
            assert(self.wf());
        }

    }

    pub fn kernel_pop_endpoint(&mut self, cpu_id:CPUID, thread_ptr: ThreadPtr, endpoint_idx:EndpointIdx) -> (ret: ThreadPtr)
        requires
            old(self).wf(),
            0<=cpu_id<NUM_CPUS,
            old(self).cpu_list@[cpu_id as int].get_is_idle() == false,
            old(self).cpu_list@[cpu_id as int].get_current_thread().unwrap() == thread_ptr,
            0<=endpoint_idx<MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).proc_man.get_thread(thread_ptr).endpoint_descriptors@[endpoint_idx as int] != 0,
            old(self).proc_man.get_endpoint(old(self).proc_man.get_thread(thread_ptr).endpoint_descriptors@[endpoint_idx as int]).len() != 0,
            old(self).proc_man.scheduler.len() != MAX_NUM_THREADS,
        ensures
            self.wf(),
            self.proc_man.get_proc_ptrs() =~= old(self).proc_man.get_proc_ptrs(),
            self.proc_man.get_thread_ptrs() =~= old(self).proc_man.get_thread_ptrs(),
            self.page_alloc =~= old(self).page_alloc,
            self.mmu_man =~= old(self).mmu_man,
            self.proc_man.get_thread_ptrs().contains(ret);
    {
        let new_thread_ptr = self.proc_man.pop_endpoint(thread_ptr, endpoint_idx);
        assert(forall|thread_ptr:ThreadPtr|#![auto] thread_ptr != new_thread_ptr && self.proc_man.get_thread_ptrs().contains(thread_ptr) ==> self.proc_man.get_thread(thread_ptr).state != TRANSIT);
        assert(old(self).proc_man.get_thread(new_thread_ptr).state == BLOCKED);
        assert(forall|i:int|#![auto]0<=i<NUM_CPUS && old(self).cpu_list@[i].get_current_thread().is_Some() 
            ==> old(self).cpu_list@[i].get_current_thread().unwrap() != new_thread_ptr);
        self.proc_man.set_thread_to_running(new_thread_ptr);
        self.proc_man.push_scheduler(thread_ptr);
        self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));

        assert(
            self.proc_man.wf());
        assert(
            self.mmu_man.wf()
        );
        assert(
        
            self.page_alloc.wf()
        );
        assert(
            self.cpu_list.wf()
        );

        assert(
            self.kernel_cpu_list_wf()
        );
        assert(
            self.kernel_mem_layout_wf()
        );
        assert(self.page_alloc =~= old(self).page_alloc);
        assert(self.mmu_man =~= old(self).mmu_man);
        assert(
            self.kernel_mmu_page_alloc_pagetable_wf()
        );
        assert(
            self.kernel_mmu_page_alloc_iommutable_wf()
        );
        assert(self.kernel_proc_mmu_wf());
        assert(self.kernel_proc_no_thread_in_transit());
        assert(forall|i:int|#![auto]0<=i<NUM_CPUS
            ==> old(self).cpu_list@[i].tlb =~= self.cpu_list@[i].tlb);
        assert(forall|i:int|#![auto]0<=i<NUM_CPUS
            ==> old(self).cpu_list@[i].iotlb =~= self.cpu_list@[i].iotlb);
        assert(self.kernel_tlb_wf());
        return new_thread_ptr;
    }


    // pub fn syscall_send_wait(&mut self, cpu_id:CPUID, pt_regs: Registers, endpoint_index: EndpointIdx)
    //     requires
    //         old(self).wf(),
    // {
    //     if cpu_id >= NUM_CPUS{
    //         return SyscallReturnStruct::new(CPU_ID_INVALID,0,0,pt_regs);
    //     }

    //     if self.cpu_list.get(cpu_id).get_is_idle() {
    //         return SyscallReturnStruct::new(CPU_NO_IDLE,0,0,pt_regs);
    //     }

    //     let pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
    //     let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);
        
    //     if endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS{
    //         return (SyscallReturnStruct::new(ENDPOINT_INDEX_INVALID,pcid,cr3,pt_regs),None,None);
    //     }

    //     let target_endpoint_ptr = self.proc_man.get_thread_endpoint_ptr_by_endpoint_idx(current_thread_ptr, endpoint_index);
    //     if target_endpoint_ptr == 0 {
    //         return (SyscallReturnStruct::new(SHARED_ENDPOINT_NOT_EXIST,pcid,cr3,pt_regs),None,None);
    //     }

    //     if self.proc_man.get_endpoint_len_by_endpoint_ptr(target_endpoint_ptr) == MAX_NUM_THREADS_PER_ENDPOINT {
    //         return
    //     }
    // }

}
}
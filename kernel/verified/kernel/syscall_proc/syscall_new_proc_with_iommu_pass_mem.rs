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


    pub fn syscall_new_proc_with_iommu_pass_mem(&mut self, cpu_id:CPUID, endpoint_index: EndpointIdx, pt_regs_new_proc: Registers, va:VAddr, range: usize) -> (ret:(SyscallReturnStruct,Option<ProcPtr>, Option<ThreadPtr>,Option<usize>))
        requires
            old(self).wf(),
        ensures
            self.wf(),
    {
        let (default_pcid, default_cr3) = self.mmu_man.get_reserved_pcid_and_cr3();
        let perm_bits = READ_WRITE_EXECUTE;
        assume(spec_va_perm_bits_valid(perm_bits));
        if cpu_id >= NUM_CPUS{
            return (SyscallReturnStruct::new(CPU_ID_INVALID,default_pcid,default_cr3,0),None,None,None);
        }else if self.cpu_list.get(cpu_id).get_is_idle() {
            return (SyscallReturnStruct::new(NO_RUNNING_THREAD,default_pcid,default_cr3,0),None,None,None);
        }else{
            assert(self.cpu_list[cpu_id as int].get_is_idle() == false);
            let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
            assert(current_thread_ptr_op.is_Some());
            let current_thread_ptr = current_thread_ptr_op.unwrap();

            let pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
            let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);

            if endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS{
                return (SyscallReturnStruct::new(ENDPOINT_INDEX_INVALID,pcid,cr3,current_thread_ptr),None,None,None);
            }else{
                let target_endpoint_ptr = self.proc_man.get_thread_endpoint_ptr_by_endpoint_idx(current_thread_ptr, endpoint_index);
                if target_endpoint_ptr == 0 {
                    return (SyscallReturnStruct::new(SHARED_ENDPOINT_NOT_EXIST,pcid,cr3,current_thread_ptr),None,None,None);
                }
                else if self.proc_man.get_endpoint_rf_counter_by_endpoint_ptr(target_endpoint_ptr) == usize::MAX {
                    return (SyscallReturnStruct::new(SHARED_ENDPOINT_REF_COUNT_OVERFLOW,pcid,cr3,current_thread_ptr),None,None,None);
                }else if range >= (usize::MAX/3) - 2 {
                    return (SyscallReturnStruct::new(PAGE_PAYLOAD_INVALID,pcid,cr3,current_thread_ptr),None,None,None);
                }
                else if self.page_alloc.free_pages.len() < 5 + 3 * range{
                    return (SyscallReturnStruct::new(SYSTEM_OUT_OF_MEM,pcid,cr3,current_thread_ptr),None,None,None);
                }else if self.proc_man.scheduler.len() == MAX_NUM_THREADS{
                    return (SyscallReturnStruct::new(SCHEDULER_NO_SPACE,pcid,cr3,current_thread_ptr),None,None,None);
                }else if self.proc_man.proc_ptrs.len() == MAX_NUM_PROCS {
                    return (SyscallReturnStruct::new(PROCESS_LIST_NO_SPEC,pcid,cr3,current_thread_ptr),None,None,None);
                }else if self.mmu_man.free_pcids.len() == 0 {
                    return (SyscallReturnStruct::new(NO_FREE_PCID,pcid,cr3,current_thread_ptr),None,None,None);
                }else if self.mmu_man.free_ioids.len() == 0 {
                    return (SyscallReturnStruct::new(NO_FREE_IOID,pcid,cr3,current_thread_ptr),None,None,None);
                }else if self.kernel_page_sharing_helper_2(pcid, perm_bits, va, range) == false {
                    return (SyscallReturnStruct::new(PAGE_PAYLOAD_INVALID,pcid,cr3,current_thread_ptr),None,None,None);
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

                    self.kernel_map_pagetable_range_page_to_pagetable(pcid, new_pcid, va, va, perm_bits,range);

                    return (SyscallReturnStruct::new(SUCCESS,pcid,cr3,current_thread_ptr),Some(new_proc),Some(new_thread),Some(iommutable_cr3));
                }
            }

        }
    }
}
}

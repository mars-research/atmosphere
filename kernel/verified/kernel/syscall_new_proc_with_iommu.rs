use vstd::prelude::*;
verus! {

// use crate::allocator::page_allocator_spec_impl::*;
// use crate::memory_manager::spec_impl::*;
// use crate::process_manager::spec_proof::*;
// use crate::util::page_ptr_util_u::*;
// use crate::lemma::lemma_t::set_lemma;
use crate::lemma::lemma_u::*;

// use crate::util::page_ptr_util_u::*;
use crate::define::*;

// use crate::trap::*;
// use crate::pagetable::pagemap_util_t::*;
// use crate::pagetable::entry::*;
use crate::kernel::Kernel;
use crate::va_range::VaRange4K;
use crate::trap::Registers;

//use crate::pagetable::pagemap_util_t::*;
impl Kernel {
    pub fn syscall_new_proc_with_endpoint_iommu(
        &mut self,
        thread_ptr: ThreadPtr,
        endpoint_index: EndpointIdx,
        pt_regs: &Registers,
        va_range: VaRange4K,
    ) -> (ret: SyscallReturnStruct)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            va_range.wf(),
            va_range.len * 3 + 3 < usize::MAX,
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        ensures
    {
        proof {
            seq_push_lemma::<usize>();
        }
        let proc_ptr = self.proc_man.get_thread(thread_ptr).owning_proc;
        let pcid = self.proc_man.get_proc(proc_ptr).pcid;
        let container_ptr = self.proc_man.get_thread(thread_ptr).owning_container;

        proof {
            self.proc_man.thread_inv();
            self.proc_man.process_inv();
            assert(self.proc_man.get_proc(proc_ptr).owning_container == container_ptr);
        }

        if self.proc_man.get_proc(proc_ptr).children.len() >= PROC_CHILD_LIST_LEN {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_proc(proc_ptr).depth >= usize::MAX {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_container(container_ptr).quota.mem_4k < va_range.len * 3 + 3 {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_container(container_ptr).scheduler.len()
            >= MAX_CONTAINER_SCHEDULER_LEN {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_container(container_ptr).owned_procs.len() >= CONTAINER_PROC_LIST_LEN {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.page_alloc.free_pages_4k.len() < va_range.len * 3 + 3 {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.mem_man.free_pcids.len() < 1 {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.mem_man.free_ioids.len() < 1 {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        let endpoint_ptr_op = self.proc_man.get_endpoint_ptr_by_endpoint_idx(
            thread_ptr,
            endpoint_index,
        );
        if endpoint_ptr_op.is_none() {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        let endpoint_ptr = endpoint_ptr_op.unwrap();
        if self.proc_man.get_endpoint(endpoint_ptr).rf_counter == usize::MAX {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.check_address_space_va_range_shareable(proc_ptr, &va_range) == false {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        // let (page_ptr_1,mut page_perm_1) = self.page_alloc.alloc_page_4k();

        let (page_ptr_2, page_perm_2) = self.page_alloc.alloc_page_4k();
        let (page_ptr_3, page_perm_3) = self.page_alloc.alloc_page_4k();

        // assert(page_ptr_1 != page_ptr_2);
        // assert(page_ptr_1 != page_ptr_3);
        // assert(page_ptr_2 != page_ptr_3);
        // let (page_map_ptr, mut page_map_perm) = page_perm_to_page_map(page_ptr_1,page_perm_1);
        let new_pcid = self.mem_man.alloc_page_table(page_ptr_2);
        let new_ioid = self.mem_man.alloc_iommu_table(page_ptr_2);

        assert(self.proc_man == old(self).proc_man);
        self.proc_man.new_proc_with_endpoint_iommu(
            thread_ptr,
            endpoint_index,
            pt_regs,
            page_ptr_2,
            page_perm_2,
            page_ptr_3,
            page_perm_3,
            new_pcid,
            new_ioid,
        );

        assert(self.mem_man.wf());
        assert(self.page_alloc.wf());
        assert(self.proc_man.wf());
        assert(self.memory_wf()) by {
            assert(self.mem_man.page_closure().disjoint(self.proc_man.page_closure()));
            assert(self.mem_man.page_closure() + self.proc_man.page_closure()
                == self.page_alloc.allocated_pages_4k());
            assert(self.page_alloc.mapped_pages_2m() =~= Set::empty());
            assert(self.page_alloc.mapped_pages_1g() =~= Set::empty());
            assert(self.page_alloc.allocated_pages_2m() =~= Set::empty());
            assert(self.page_alloc.allocated_pages_1g() =~= Set::empty());
            assert(self.page_alloc.container_map_4k@.dom() =~= self.proc_man.container_dom());
        };
        assert(self.mapping_wf());
        assert(self.pcid_ioid_wf()) by {
            assert(forall|p_ptr_i: ProcPtr, p_ptr_j: ProcPtr|
                #![auto]
                self.proc_dom().contains(p_ptr_i) && self.proc_dom().contains(p_ptr_j) && p_ptr_i
                    != p_ptr_j ==> self.get_proc(p_ptr_i).pcid != self.get_proc(p_ptr_j).pcid);
            assert(forall|p_ptr_i: ProcPtr, p_ptr_j: ProcPtr|
                #![auto]
                old(self).proc_dom().contains(p_ptr_i) && old(self).proc_dom().contains(p_ptr_j)
                    && p_ptr_i != p_ptr_j && old(self).get_proc(p_ptr_i).ioid.is_Some() && old(
                    self,
                ).get_proc(p_ptr_j).ioid.is_Some() ==> old(self).get_proc(p_ptr_i).ioid.unwrap()
                    != old(self).get_proc(p_ptr_j).ioid.unwrap());
            assert(forall|p_ptr_i: ProcPtr, p_ptr_j: ProcPtr|
                #![auto]
                self.proc_dom().contains(p_ptr_i) && self.proc_dom().contains(p_ptr_j) && p_ptr_i
                    != p_ptr_j && self.get_proc(p_ptr_i).ioid.is_Some() && self.get_proc(
                    p_ptr_j,
                ).ioid.is_Some() ==> self.get_proc(p_ptr_i).ioid.unwrap() != self.get_proc(
                    p_ptr_j,
                ).ioid.unwrap());
        };
        assert(self.page_mapping_wf());

        self.range_create_and_share_mapping(proc_ptr, &va_range, page_ptr_2, &va_range);

        return SyscallReturnStruct::NoSwitchNew(
            RetValueType::SuccessPairUsize { value1: page_ptr_2, value2: page_ptr_3 },
        );
    }
}

} // verus!

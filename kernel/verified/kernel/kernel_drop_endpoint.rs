use vstd::prelude::*;
verus! {
use crate::define::*;
use crate::kernel::Kernel;
use crate::va_range::*;
use crate::process_manager::spec_util::*;
impl Kernel {
    pub fn kernel_drop_endpoint(&mut self, thread_ptr: ThreadPtr, edp_idx: EndpointIdx)
        requires
            old(self).wf(),
            0 <= edp_idx < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).thread_dom().contains(thread_ptr),
            old(self).get_thread(thread_ptr).state == ThreadState::BLOCKED
            ==>
                old(self).get_thread(thread_ptr).blocking_endpoint_index.unwrap() != edp_idx,
        ensures
            self.wf(),
            self.container_dom() == old(self).container_dom(),
            self.proc_dom() == old(self).proc_dom(),
            self.thread_dom() == old(self).thread_dom(),
            containers_tree_unchanged(old(self).proc_man, self.proc_man),
            containers_owned_proc_unchanged(old(self).proc_man, self.proc_man),
            processes_unchanged(old(self).proc_man, self.proc_man),
            threads_unchanged_except(old(self).proc_man, self.proc_man, set![thread_ptr]),
            self.get_thread(thread_ptr).endpoint_descriptors@ 
                =~= old(self).get_thread(thread_ptr).endpoint_descriptors@.update(edp_idx as int, None),
            old(self).get_thread(thread_ptr).state == self.get_thread(thread_ptr).state,
            self.get_thread(thread_ptr).blocking_endpoint_index == old(self).get_thread(thread_ptr).blocking_endpoint_index,
    {
        let page_op = self.proc_man.drop_endpoint(thread_ptr, edp_idx);

        if let Some((page_ptr, page_perm)) = page_op{
            self.page_alloc.free_page_4k(page_ptr, page_perm);
                   assert( self.mem_man.page_closure().disjoint(
            self.proc_man.page_closure(),
        ));
        assert(self.mem_man.page_closure() + self.proc_man.page_closure()
            == self.page_alloc.allocated_pages_4k());
        assert(self.page_alloc.mapped_pages_2m() =~= Set::empty());
        assert(self.page_alloc.mapped_pages_1g() =~= Set::empty());
        assert(self.page_alloc.allocated_pages_2m() =~= Set::empty());
        assert(self.page_alloc.allocated_pages_1g() =~= Set::empty());
        assert(self.page_alloc.container_map_4k@.dom() =~= self.proc_man.container_dom());
        assert(self.page_alloc.container_map_2m@.dom() =~= self.proc_man.container_dom());
        assert(self.page_alloc.container_map_1g@.dom() =~= self.proc_man.container_dom());
            assert(self.memory_wf());
            assert(self.page_mapping_wf());
            assert(self.mapping_wf());
            assert(self.pcid_ioid_wf());
        }else{
            assert(self.memory_wf());
            assert(self.page_mapping_wf());
            assert(self.mapping_wf());
            assert(self.pcid_ioid_wf());
        }
    }
}

}
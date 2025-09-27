use vstd::prelude::*;
verus! {
use crate::define::*;
use crate::kernel::Kernel;
use crate::va_range::*;
impl Kernel {
    pub fn kernel_drop_endpoint(&mut self, thread_ptr: ThreadPtr, edp_idx: EndpointIdx)
        requires
            old(self).wf(),
            0 <= edp_idx < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).thread_dom().contains(thread_ptr),
            old(self).get_thread(thread_ptr).blocking_endpoint_index.is_Some() ==>
                old(self).get_thread(thread_ptr).blocking_endpoint_index.unwrap() != edp_idx,
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
        }else{
            assert(self.memory_wf());
            assert(self.page_mapping_wf());
        }
    }
}

}
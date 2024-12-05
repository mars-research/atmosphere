use vstd::prelude::*;
verus! {
// use crate::allocator::page_allocator_spec_impl::*;
// use crate::memory_manager::spec_impl::*;
// use crate::process_manager::spec_impl::*;
// use crate::util::page_ptr_util_u::*;
// use crate::lemma::lemma_t::set_lemma;
// use crate::lemma::lemma_u::*;
use crate::util::page_ptr_util_u::*;
use crate::define::*;
// use crate::trap::*;
use crate::pagetable::pagemap_util_t::*;
// use crate::pagetable::entry::*;
use crate::kernel::Kernel;
use crate::va_range::VaRange4K;

impl Kernel{

// pub fn check_address_space_va_range_shareable(&self, target_proc_ptr:ProcPtr, va_range:&VaRange4K) -> (ret:bool)
//     requires
//         self.wf(),
//         self.proc_dom().contains(target_proc_ptr),
//         va_range.wf(),
//     ensures
//         ret == self.address_space_range_free(target_proc_ptr, *va_range),
// {
//     let target_pcid = self.proc_man.get_proc(target_proc_ptr).pcid;
//     for i in 0..va_range.len
//         invariant
//             self.mem_man.pcid_active(target_pcid),
//             target_pcid == self.get_proc(target_proc_ptr).pcid,
//             0<=i<=va_range.len,
//             self.wf(),
//             self.proc_dom().contains(target_proc_ptr),
//             va_range.wf(),
//             forall|j:int| #![auto] 0<=j<i ==> self.get_address_space(target_proc_ptr).dom().contains(va_range@[j]) == false,
//     {
//         if self.mem_man.resolve_pagetable_mapping(target_pcid, va_range.index(i)).is_some(){
//             return false;
//         }
//     }
//     return true;
// }

pub fn create_entry(&mut self, proc_ptr:ProcPtr, va:VAddr) -> (ret: (usize, PageMapPtr))
    requires
        old(self).wf(),
        old(self).proc_dom().contains(proc_ptr),
        old(self).get_container_quota(old(self).get_proc(proc_ptr).owning_container) >= 3,
        old(self).get_num_of_free_pages() >= 3,
        va_4k_valid(va),
        old(self).get_address_space(proc_ptr).dom().contains(va) == false,
    ensures
        ret.0 <= 3,
        self.wf(),
        self.proc_dom() == old(self).proc_dom(),
        self.thread_dom() == old(self).thread_dom(),
        self.endpoint_dom() == old(self).endpoint_dom(),
        self.container_dom() == old(self).container_dom(),
        self.get_num_of_free_pages() == old(self).get_num_of_free_pages() - ret.0,
        forall|p_ptr:ProcPtr|
            #![auto]
            self.proc_dom().contains(p_ptr)
            ==>
            self.get_address_space(p_ptr) =~= old(self).get_address_space(p_ptr)
            &&
            self.get_proc(p_ptr) =~= old(self).get_proc(p_ptr),
        forall|t_ptr:ThreadPtr|
            #![auto]
            self.thread_dom().contains(t_ptr)
            ==>
            self.get_thread(t_ptr) =~= old(self).get_thread(t_ptr),
        forall|c_ptr:ContainerPtr|
            #![auto]
            self.container_dom().contains(c_ptr) && c_ptr != self.get_proc(proc_ptr).owning_container
            ==>
            self.get_container(c_ptr) =~= old(self).get_container(c_ptr),
        forall|e_ptr:EndpointPtr|
            #![auto]
            self.endpoint_dom().contains(e_ptr)
            ==>
            self.get_endpoint(e_ptr) =~= old(self).get_endpoint(e_ptr),
        forall|c_ptr:ContainerPtr|
            #![auto]
            self.container_dom().contains(c_ptr) && c_ptr != self.get_proc(proc_ptr).owning_container
            ==>
            self.get_container(c_ptr) =~= old(self).get_container(c_ptr),
        forall|c_ptr:ContainerPtr|
            #![auto]
            self.container_dom().contains(c_ptr)
            ==>
            self.get_container_owned_pages(c_ptr) =~= old(self).get_container_owned_pages(c_ptr),
        self.get_container(old(self).get_proc(proc_ptr).owning_container).owned_procs =~= old(self).get_container(old(self).get_proc(proc_ptr).owning_container).owned_procs,
        self.get_container(old(self).get_proc(proc_ptr).owning_container).parent =~= old(self).get_container(old(self).get_proc(proc_ptr).owning_container).parent,
        self.get_container(old(self).get_proc(proc_ptr).owning_container).parent_rev_ptr =~= old(self).get_container(old(self).get_proc(proc_ptr).owning_container).parent_rev_ptr,
        self.get_container(old(self).get_proc(proc_ptr).owning_container).children =~= old(self).get_container(old(self).get_proc(proc_ptr).owning_container).children,
        self.get_container(old(self).get_proc(proc_ptr).owning_container).owned_endpoints =~= old(self).get_container(old(self).get_proc(proc_ptr).owning_container).owned_endpoints,
        self.get_container(old(self).get_proc(proc_ptr).owning_container).owned_threads =~= old(self).get_container(old(self).get_proc(proc_ptr).owning_container).owned_threads,
        // self.get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota =~= old(self).get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota,
        self.get_container(old(self).get_proc(proc_ptr).owning_container).mem_used =~= old(self).get_container(old(self).get_proc(proc_ptr).owning_container).mem_used,
        self.get_container(old(self).get_proc(proc_ptr).owning_container).owned_cpus =~= old(self).get_container(old(self).get_proc(proc_ptr).owning_container).owned_cpus,
        self.get_container(old(self).get_proc(proc_ptr).owning_container).scheduler =~= old(self).get_container(old(self).get_proc(proc_ptr).owning_container).scheduler,
        self.get_container(old(self).get_proc(proc_ptr).owning_container).depth =~= old(self).get_container(old(self).get_proc(proc_ptr).owning_container).depth,
        self.get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota as int =~= old(self).get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota - ret.0,
        self.get_container(old(self).get_proc(proc_ptr).owning_container).subtree_set =~= old(self).get_container(old(self).get_proc(proc_ptr).owning_container).subtree_set,
        self.mem_man.get_pagetable_by_pcid(self.get_proc(proc_ptr).pcid).unwrap().spec_resolve_mapping_l2(spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2).is_Some(),
        self.mem_man.get_pagetable_by_pcid(self.get_proc(proc_ptr).pcid).unwrap().spec_resolve_mapping_l2(spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2).unwrap().addr == ret.1,
        forall|p:PagePtr|
            #![trigger self.page_alloc.page_is_mapped(p)] 
            self.page_alloc.page_is_mapped(p) == old(self).page_alloc.page_is_mapped(p),
        forall|p:PagePtr|
            #![trigger self.page_alloc.page_is_mapped(p)] 
            self.page_alloc.page_is_mapped(p) ==>
            self.get_physical_page_reference_counter(p) == old(self).get_physical_page_reference_counter(p),
        forall|p:Pcid|
            #![trigger self.mem_man.pcid_active(p)]
            #![trigger self.mem_man.pcid_to_proc_ptr(p)]
            self.mem_man.pcid_active(p)
            ==>
            old(self).mem_man.pcid_to_proc_ptr(p) == self.mem_man.pcid_to_proc_ptr(p),
        self.page_mapping == old(self).page_mapping,
    {
        let mut ret = 0;
        let container_ptr = self.proc_man.get_proc(proc_ptr).owning_container;
        let old_quota = self.proc_man.get_container(container_ptr).mem_quota;
        let target_pcid = self.proc_man.get_proc(proc_ptr).pcid;
        proof{va_lemma();}
        let (l4i, l3i, l2i, l1i) = va2index(va);
        let mut l4_entry_op = self.mem_man.get_pagetable_l4_entry(target_pcid, l4i);
        if l4_entry_op.is_none() {
            proof{
                self.page_alloc.free_pages_are_not_mapped();
            }
            let (new_page_ptr, new_page_perm) = self.page_alloc.alloc_page_4k();
            let (page_map_ptr, page_map_perm) = page_perm_to_page_map(new_page_ptr, new_page_perm);
            self.mem_man.create_pagetable_l4_entry(target_pcid, l4i, page_map_ptr, page_map_perm);
            assert(self.wf()) by {
                assert(self.mem_man.wf());
                assert(self.page_alloc.wf());
                assert(self.proc_man.wf());
                assert(self.memory_wf()) by {
                    assert(self.mem_man.page_closure().disjoint(self.proc_man.page_closure()));
                    assert(self.mem_man.page_closure() + self.proc_man.page_closure() == self.page_alloc.allocated_pages_4k());
                    assert(self.page_alloc.mapped_pages_2m() =~= Set::empty());
                    assert(self.page_alloc.mapped_pages_1g() =~= Set::empty());
                    assert(self.page_alloc.allocated_pages_2m() =~= Set::empty());
                    assert(self.page_alloc.allocated_pages_1g() =~= Set::empty());
                    assert(self.page_alloc.container_map_4k@.dom() =~= self.proc_man.container_dom());
                };
                assert(self.mapping_wf());
                assert(self.pcid_ioid_wf());
            };
            ret = ret + 1;
            l4_entry_op = self.mem_man.get_pagetable_l4_entry(target_pcid, l4i);
        }
        assert(l4_entry_op.is_Some());
        let l4_entry = l4_entry_op.unwrap();
        let mut l3_entry_op = self.mem_man.get_pagetable_l3_entry(target_pcid, l4i, l3i, &l4_entry);
        if l3_entry_op.is_none(){
            proof{
                self.page_alloc.free_pages_are_not_mapped();
            }
            let (new_page_ptr, new_page_perm) = self.page_alloc.alloc_page_4k();
            let (page_map_ptr, page_map_perm) = page_perm_to_page_map(new_page_ptr, new_page_perm);
            self.mem_man.create_pagetable_l3_entry(target_pcid, l4i, l3i, l4_entry.addr, page_map_ptr, page_map_perm);
            assert(self.wf()) by {
                assert(self.mem_man.wf());
                assert(self.page_alloc.wf());
                assert(self.proc_man.wf());
                assert(self.memory_wf()) by {
                    assert(self.mem_man.page_closure().disjoint(self.proc_man.page_closure()));
                    assert(self.mem_man.page_closure() + self.proc_man.page_closure() == self.page_alloc.allocated_pages_4k());
                    assert(self.page_alloc.mapped_pages_2m() =~= Set::empty());
                    assert(self.page_alloc.mapped_pages_1g() =~= Set::empty());
                    assert(self.page_alloc.allocated_pages_2m() =~= Set::empty());
                    assert(self.page_alloc.allocated_pages_1g() =~= Set::empty());
                    assert(self.page_alloc.container_map_4k@.dom() =~= self.proc_man.container_dom());
                };
                assert(self.mapping_wf());
                assert(self.pcid_ioid_wf());
            };
            ret = ret + 1;
            l3_entry_op = self.mem_man.get_pagetable_l3_entry(target_pcid, l4i, l3i, &l4_entry);
        }
        let l3_entry = l3_entry_op.unwrap();
        let mut l2_entry_op = self.mem_man.get_pagetable_l2_entry(target_pcid, l4i, l3i, l2i, &l3_entry);

        if l2_entry_op.is_none(){
            proof{
                self.page_alloc.free_pages_are_not_mapped();
            }
            let (new_page_ptr, new_page_perm) = self.page_alloc.alloc_page_4k();
            let (page_map_ptr, page_map_perm) = page_perm_to_page_map(new_page_ptr, new_page_perm);
            self.mem_man.create_pagetable_l2_entry(target_pcid, l4i, l3i, l2i, l3_entry.addr, page_map_ptr, page_map_perm);
            assert(self.wf()) by {
                assert(self.mem_man.wf());
                assert(self.page_alloc.wf());
                assert(self.proc_man.wf());
                assert(self.memory_wf()) by {
                    assert(self.mem_man.page_closure().disjoint(self.proc_man.page_closure()));
                    assert(self.mem_man.page_closure() + self.proc_man.page_closure() == self.page_alloc.allocated_pages_4k());
                    assert(self.page_alloc.mapped_pages_2m() =~= Set::empty());
                    assert(self.page_alloc.mapped_pages_1g() =~= Set::empty());
                    assert(self.page_alloc.allocated_pages_2m() =~= Set::empty());
                    assert(self.page_alloc.allocated_pages_1g() =~= Set::empty());
                    assert(self.page_alloc.container_map_4k@.dom() =~= self.proc_man.container_dom());
                };  
                assert(self.mapping_wf());
                assert(self.pcid_ioid_wf());
            };
            ret = ret + 1;
            l2_entry_op = self.mem_man.get_pagetable_l2_entry(target_pcid, l4i, l3i, l2i, &l3_entry);
        }
        self.proc_man.set_container_mem_quota(container_ptr, old_quota - ret);

        assert(self.wf()) by {
            assert(self.mem_man.wf());
            assert(self.page_alloc.wf());
            assert(self.proc_man.wf());
            assert(self.memory_wf()) by {
                assert(self.mem_man.page_closure().disjoint(self.proc_man.page_closure()));
                assert(self.mem_man.page_closure() + self.proc_man.page_closure() == self.page_alloc.allocated_pages_4k());
                assert(self.page_alloc.mapped_pages_2m() =~= Set::empty());
                assert(self.page_alloc.mapped_pages_1g() =~= Set::empty());
                assert(self.page_alloc.allocated_pages_2m() =~= Set::empty());
                assert(self.page_alloc.allocated_pages_1g() =~= Set::empty());
                assert(self.page_alloc.container_map_4k@.dom() =~= self.proc_man.container_dom());
            };
            assert(self.mapping_wf());
            assert(self.pcid_ioid_wf());
        };

        (ret, l2_entry_op.unwrap().addr)
    }

pub fn get_address_space_va_range_none(&self, target_proc_ptr:ProcPtr, va_range: VaRange4K) -> (ret: bool)
    requires
        self.wf(),
        self.proc_dom().contains(target_proc_ptr),
        va_range.wf(),
    ensures
        ret == (forall|i:int| #![auto] 0<=i<va_range.len ==> self.get_address_space(target_proc_ptr).dom().contains(va_range@[i]) == false),
{
    for i in 0..va_range.len
        invariant
            0<=i<=va_range.len,
            self.wf(),
            self.proc_dom().contains(target_proc_ptr),
            va_range.wf(),
            forall|j:int| #![auto] 0<=j<i ==> self.get_address_space(target_proc_ptr).dom().contains(va_range@[j]) == false
    {
        let target_pcid = self.proc_man.get_proc(target_proc_ptr).pcid;
        if self.mem_man.resolve_pagetable_mapping(target_pcid, va_range.index(i)).is_some(){
            return false;
        }
    }
    return true;
}


}
}
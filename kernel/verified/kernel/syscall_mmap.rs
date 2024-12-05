use vstd::prelude::*;
verus! {
// use crate::allocator::page_allocator_spec_impl::*;
// use crate::memory_manager::spec_impl::*;
// use crate::process_manager::spec_impl::*;
// use crate::util::page_ptr_util_u::*;
// use crate::lemma::lemma_t::set_lemma;
// use crate::lemma::lemma_u::*;
// use crate::util::page_ptr_util_u::*;
use crate::define::*;
// use crate::trap::*;
// use crate::pagetable::pagemap_util_t::*;
// use crate::pagetable::entry::*;
use crate::kernel::Kernel;
use crate::va_range::VaRange4K;

pub open spec fn syscall_mmap_requirement(old:Kernel,  thread_ptr: ThreadPtr, va_range: VaRange4K) -> bool{
    let proc_ptr = old.proc_man.get_thread(thread_ptr).owning_proc;
    let pcid = old.proc_man.get_proc(proc_ptr).pcid;
    let container_ptr = old.proc_man.get_proc(proc_ptr).owning_container;

    if old.get_container_quota(container_ptr) < va_range.len * 4{
        false
    }else if old.address_space_range_free(proc_ptr, &va_range) == false {
        false
    }else{
        true
    }
}

pub open spec fn syscall_mmap_spec(old:Kernel, new:Kernel, thread_id: ThreadPtr, va_range: VaRange4K, ret: SyscallReturnStruct) -> bool{
    let proc_ptr = old.get_thread(thread_id).owning_proc;
    let container_ptr = old.get_thread(thread_id).owning_container;
    let mmapped_physcial_pages_seq = ret.get_return_vaule_seq_usize().unwrap();
    if  syscall_mmap_requirement(old, thread_id, va_range) == false {
        new =~= old
    }
    else{
        // things that did not change
        &&&
        old.thread_dom() =~= new.thread_dom()
        &&&
        old.proc_dom() =~= new.proc_dom()
        &&&
        old.container_dom() =~= new.container_dom()
        &&&
        old.endpoint_dom() =~= new.endpoint_dom()
        &&&
        forall|t_ptr:ThreadPtr| 
            #![trigger new.get_thread(t_ptr)]
            #![trigger old.get_thread(t_ptr)]
            old.thread_dom().contains(t_ptr)
            ==>
            new.get_thread(t_ptr) =~= old.get_thread(t_ptr)
        &&&
        forall|proc_ptr:ProcPtr| 
            #![trigger new.get_proc(proc_ptr)]
            new.proc_dom().contains(proc_ptr)
            ==>
            new.get_proc(proc_ptr) =~= old.get_proc(proc_ptr)
        &&&
        forall|c:ContainerPtr| 
            #![trigger new.get_container(c)]
            new.container_dom().contains(c) && c != container_ptr
            ==>
            old.get_container(c) =~= new.get_container(c)
        &&&
        forall|e_ptr:EndpointPtr| 
            #![trigger new.get_endpoint(e_ptr)]
            new.endpoint_dom().contains(e_ptr)
            ==> 
            old.get_endpoint(e_ptr) =~= new.get_endpoint(e_ptr)
        &&&
        forall|c:ContainerPtr| 
            #![trigger new.get_container_owned_pages(c)]
            new.container_dom().contains(c) && c != container_ptr
            ==> 
            old.get_container_owned_pages(c) =~= new.get_container_owned_pages(c)
        &&&
        forall|p_ptr:ProcPtr| 
            #![trigger new.get_address_space(p_ptr)]
            new.proc_dom().contains(p_ptr) && p_ptr != proc_ptr
            ==>
            new.get_address_space(p_ptr) =~= old.get_address_space(p_ptr)
        &&&
        forall|page_ptr:PagePtr|
            #![trigger new.get_physical_page_mapping()[page_ptr]]
            old.get_physical_page_mapping().dom().contains(page_ptr)
            ==> 
            old.get_physical_page_mapping()[page_ptr] == new.get_physical_page_mapping()[page_ptr]
        &&&
        forall|va:VAddr| 
            #![trigger new.get_address_space(proc_ptr).dom().contains(va)]
            #![trigger new.get_address_space(proc_ptr)[va]]
            va_range@.contains(va) == false
            ==>
            new.get_address_space(proc_ptr).dom().contains(va) == old.get_address_space(proc_ptr).dom().contains(va)
            &&
            new.get_address_space(proc_ptr)[va] =~= old.get_address_space(proc_ptr)[va]
        &&&
        new.get_container(container_ptr).owned_threads@ =~= old.get_container(container_ptr).owned_threads@
        &&&
        new.get_container(container_ptr).owned_procs@ =~= old.get_container(container_ptr).owned_procs@
        &&&
        new.get_container(container_ptr).owned_endpoints@ =~= old.get_container(container_ptr).owned_endpoints@
        &&&
        new.get_container(container_ptr).subtree_set =~= old.get_container(container_ptr).subtree_set
        &&&
        new.get_container(container_ptr).depth =~= old.get_container(container_ptr).depth
        //Things that changed
        &&&
        forall|page_ptr:PagePtr| 
            #![auto]
            mmapped_physcial_pages_seq.contains(page_ptr) ==> old.get_physical_page_mapping().dom().contains(page_ptr) == false
        &&&
        new.get_physical_page_mapping().dom() =~= old.get_physical_page_mapping().dom() + mmapped_physcial_pages_seq.to_set()
        &&&
        forall|i:usize| #![auto] 0<=i<va_range.len ==>
            new.get_physical_page_mapping()[mmapped_physcial_pages_seq[i as int]] == Set::empty().insert((proc_ptr, va_range@[i as int]))
        &&&
        forall|i:usize| 
            #![auto] 
            0<=i<va_range.len 
            ==> 
            new.get_address_space(proc_ptr)[va_range@[i as int]].addr == mmapped_physcial_pages_seq[i as int]
        &&&
        forall|new_va:VAddr, p_ptr:ProcPtr, va:VAddr| 
            #![trigger old.get_address_space(p_ptr), old.get_address_space(p_ptr)[va].addr, new.get_address_space(proc_ptr)[new_va].addr] 
            va_range@.contains(new_va) 
            &&
            old.proc_dom().contains(p_ptr)
            &&
            old.get_address_space(p_ptr).dom().contains(va)
            ==> 
            new.get_address_space(proc_ptr)[new_va].addr != old.get_address_space(p_ptr)[va].addr
        &&&
        forall|new_va:VAddr| 
            #![trigger new.get_address_space(proc_ptr).dom().contains(new_va)] 
            va_range@.contains(new_va) 
            ==> 
            new.get_address_space(proc_ptr).dom().contains(new_va)
        }
}

impl Kernel{

pub fn syscall_mmap(&mut self, thread_ptr: ThreadPtr, va_range: VaRange4K) ->  (ret: SyscallReturnStruct)
    requires
        old(self).total_wf(),
        old(self).thread_dom().contains(thread_ptr),
        va_range.wf(),
        va_range.len * 4 < usize::MAX,
    ensures
        syscall_mmap_requirement(*old(self), thread_ptr, va_range) == false <==> ret.is_error(),
        syscall_mmap_spec(*old(self), *self, thread_ptr, va_range, ret),
{
    let proc_ptr = self.proc_man.get_thread(thread_ptr).owning_proc;
    let pcid = self.proc_man.get_proc(proc_ptr).pcid;
    let container_ptr = self.proc_man.get_proc(proc_ptr).owning_container;

    proof{
        self.proc_man.thread_inv();
    }

    if self.proc_man.get_container(container_ptr).mem_quota < va_range.len * 4{
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }

    assert(self.page_alloc.free_pages_4k.len() >= va_range.len * 4) by {
        old(self).fold_lemma();
    }

    if self.check_address_space_va_range_free(proc_ptr, &va_range) == false {
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
    }

    let (num_page, seq_pages) = self.range_alloc_and_map(proc_ptr, &va_range);

    assert(self.container_dom().fold(0, |e:int, a:ContainerPtr| e + self.get_container(a).mem_quota) == old(self).container_dom().fold(0, |e:int, a:ContainerPtr| e + old(self).get_container(a).mem_quota) - num_page) by {
        self.fold_change_lemma(*old(self), container_ptr);
    }
    assert(self.total_wf());
    
    assert(forall|j:usize| #![auto] 0<=j<seq_pages@.len() ==> old(self).page_alloc.mapped_pages_4k().contains(seq_pages@[j as int]) == false);
    assert(forall|page_ptr:PagePtr| #![auto] seq_pages@.contains(page_ptr) ==> old(self).get_physical_page_mapping().dom().contains(page_ptr) == false);

    assert(
        forall|i:usize| 
            #![auto] 
            0<=i<va_range.len 
            ==> 
            old(self).page_alloc.page_is_mapped(self.get_address_space(proc_ptr)[va_range@[i as int]].addr) == false 
    );

    assert(
        forall|p_ptr:ProcPtr, va:VAddr| 
            #![auto] 
            old(self).proc_dom().contains(p_ptr)
            &&
            old(self).get_address_space(p_ptr).dom().contains(va)
            ==> 
            old(self).page_alloc.page_is_mapped(old(self).get_address_space(p_ptr)[va].addr) == true
    );

    assert(
        forall|i:usize, p_ptr:ProcPtr, va:VAddr| 
            #![auto] 
            0<=i<va_range.len 
            &&
            old(self).proc_dom().contains(p_ptr)
            &&
            old(self).get_address_space(p_ptr).dom().contains(va)
            ==> 
            self.get_address_space(proc_ptr)[va_range@[i as int]].addr != old(self).get_address_space(p_ptr)[va].addr
    );

    return SyscallReturnStruct::NoSwitchNew(RetValueType::SuccessSeqUsize{value: seq_pages});
}

}
}
use vstd::prelude::*;
verus! {

// use crate::allocator::page_allocator_spec_impl::*;
// use crate::memory_manager::spec_impl::*;
// use crate::process_manager::spec_proof::*;
// use crate::util::page_ptr_util_u::*;
use crate::define::*;
use crate::trap::*;
use crate::kernel::Kernel;

pub open spec fn syscall_new_endpoint_success_pre(
    old: Kernel,
    thread_id: ThreadPtr,
    endpoint_index: EndpointIdx,
) -> bool {
    let container_ptr = old.get_thread(thread_id).owning_container;

    if old.get_thread(thread_id).endpoint_descriptors@[endpoint_index as int].is_Some() {
        false
    } else if old.get_container(container_ptr).quota.mem_4k == 0 {
        false
    } else if old.get_num_of_free_pages() == 0 {
        false
    } else {
        true
    }
}

pub open spec fn syscall_new_endpoint_success_post(
    old: Kernel,
    new: Kernel,
    thread_id: ThreadPtr,
    endpoint_index: EndpointIdx,
    ret: SyscallReturnStruct,
) -> bool {
    let new_endpoint_ptr = ret.get_return_vaule_usize().unwrap();
    let container_ptr = old.get_thread(thread_id).owning_container;

    &&& syscall_new_endpoint_success_pre(old, thread_id, endpoint_index) == false ==> old === new
    &&& syscall_new_endpoint_success_pre(old, thread_id, endpoint_index) == true ==> (
    old.thread_dom() =~= new.thread_dom() && old.proc_dom() =~= new.proc_dom()
        && old.container_dom() =~= new.container_dom() && forall|t_ptr: ThreadPtr|
        #![trigger new.get_thread(t_ptr)]
        old.thread_dom().contains(t_ptr) && t_ptr != thread_id ==> new.get_thread(t_ptr)
            =~= old.get_thread(t_ptr) && forall|p_ptr: ProcPtr|
            #![trigger new.get_proc(p_ptr)]
            old.proc_dom().contains(p_ptr) ==> new.get_proc(p_ptr) =~= old.get_proc(p_ptr)
                && forall|c: ContainerPtr|
                #![trigger new.get_container(c)]
                old.container_dom().contains(c) && c != container_ptr ==> old.get_container(c)
                    =~= new.get_container(c) && forall|e_ptr: EndpointPtr|
                    #![trigger new.get_endpoint(e_ptr)]
                    old.endpoint_dom().contains(e_ptr) ==> old.get_endpoint(e_ptr)
                        =~= new.get_endpoint(e_ptr) && forall|c: ContainerPtr|
                        #![trigger new.get_container_owned_pages(c)]
                        old.container_dom().contains(c) ==> old.get_container_owned_pages(c)
                            =~= new.get_container_owned_pages(c) && forall|p_ptr: ProcPtr|
                            #![trigger new.get_address_space(p_ptr)]
                            old.proc_dom().contains(p_ptr) ==> new.get_address_space(p_ptr)
                                =~= old.get_address_space(p_ptr) && new.get_physical_page_mapping()
                                =~= old.get_physical_page_mapping()
                            // things that changed
                             && old.endpoint_dom().insert(new_endpoint_ptr) =~= new.endpoint_dom()
                                && new.get_container(container_ptr).owned_endpoints@
                                =~= old.get_container(container_ptr).owned_endpoints@.insert(
                                new_endpoint_ptr,
                            ) && new.get_container(container_ptr).quota.mem_4k == old.get_container(
                                container_ptr,
                            ).quota.mem_4k - 1 && new.get_container(container_ptr).quota.mem_2m
                                == old.get_container(container_ptr).quota.mem_2m
                                && new.get_container(container_ptr).quota.mem_1g
                                == old.get_container(container_ptr).quota.mem_1g
                                && new.get_container(container_ptr).quota.pcid == old.get_container(
                                container_ptr,
                            ).quota.pcid && new.get_container(container_ptr).quota.ioid
                                == old.get_container(container_ptr).quota.ioid && new.get_container(
                                container_ptr,
                            ).owned_threads == old.get_container(container_ptr).owned_threads
                                && new.get_container(container_ptr).scheduler == old.get_container(
                                container_ptr,
                            ).scheduler && new.get_container(container_ptr).owned_endpoints@
                                == old.get_container(container_ptr).owned_endpoints@.insert(
                                new_endpoint_ptr,
                            ) && new.get_container(container_ptr).children == old.get_container(
                                container_ptr,
                            ).children && new.get_thread(thread_id).ipc_payload =~= old.get_thread(
                                thread_id,
                            ).ipc_payload && new.get_thread(thread_id).state =~= old.get_thread(
                                thread_id,
                            ).state && new.get_thread(thread_id).endpoint_descriptors@
                                =~= old.get_thread(thread_id).endpoint_descriptors@.update(
                                endpoint_index as int,
                                Some(new_endpoint_ptr),
                            ) && new.get_endpoint(new_endpoint_ptr).queue@ =~= Seq::<
                                ThreadPtr,
                            >::empty() && new.get_endpoint(new_endpoint_ptr).queue_state
                                =~= EndpointState::SEND && new.get_endpoint(
                                new_endpoint_ptr,
                            ).rf_counter =~= 1 && new.get_endpoint(new_endpoint_ptr).owning_threads@
                                =~= Set::<(ThreadPtr, EndpointIdx)>::empty().insert(
                                (thread_id, endpoint_index),
                            ) && new.get_endpoint(new_endpoint_ptr).owning_container
                                =~= container_ptr)
}

impl Kernel {
    pub fn syscall_new_endpoint(
        &mut self,
        thread_ptr: ThreadPtr,
        endpoint_index: EndpointIdx,
    ) -> (ret: SyscallReturnStruct)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        ensures
            syscall_new_endpoint_success_post(*old(self), *self, thread_ptr, endpoint_index, ret),
    {
        proof {
            self.proc_man.thread_inv();
            self.proc_man.endpoint_inv();
            self.proc_man.container_inv();
        }

        let container_ptr = self.proc_man.get_thread(thread_ptr).owning_container;

        if self.proc_man.get_thread(thread_ptr).endpoint_descriptors.get(endpoint_index).is_some() {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_container(container_ptr).quota.mem_4k == 0 {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.page_alloc.free_pages_4k.len() <= 0 {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        let (page_ptr_1, mut page_perm_1) = self.page_alloc.alloc_page_4k();
        self.proc_man.new_endpoint(thread_ptr, endpoint_index, page_ptr_1, page_perm_1);

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
        assert(self.pcid_ioid_wf());
        assert(self.page_mapping_wf());
        return SyscallReturnStruct::NoSwitchNew(RetValueType::SuccessUsize { value: page_ptr_1 });
    }
}

} // verus!

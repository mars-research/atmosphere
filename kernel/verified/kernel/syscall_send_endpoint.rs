use vstd::prelude::*;
verus! {

// use crate::allocator::page_allocator_spec_impl::*;
// use crate::memory_manager::spec_impl::*;
// use crate::process_manager::spec_proof::*;
// use crate::util::page_ptr_util_u::*;
// use crate::lemma::lemma_t::set_lemma;
// use crate::lemma::lemma_u::*;
// use crate::util::page_ptr_util_u::*;
use crate::define::*;

// use crate::trap::*;
// use crate::pagetable::pagemap_util_t::*;
// use crate::pagetable::entry::*;
use crate::kernel::Kernel;

// use crate::va_range::VaRange4K;
// use crate::trap::Registers;
// use crate::pagetable::pagemap_util_t::*;
use crate::process_manager::thread::IPCPayLoad;

pub open spec fn syscall_send_endpoint_spec(
    old: Kernel,
    new: Kernel,
    sender_thread_ptr: ThreadPtr,
    blocking_endpoint_index: EndpointIdx,
    sender_endpoint_payload: EndpointIdx,
    ret: SyscallReturnStruct,
) -> bool {
    let blocking_endpoint_ptr = old.get_endpoint_ptr_by_endpoint_idx(
        sender_thread_ptr,
        blocking_endpoint_index,
    ).unwrap();
    let sender_container_ptr = old.get_thread(sender_thread_ptr).owning_container;
    let sender_endpoint_ptr_op = old.get_thread(
        sender_thread_ptr,
    ).endpoint_descriptors@[sender_endpoint_payload as int];
    let sender_endpoint_ptr = old.get_thread(
        sender_thread_ptr,
    ).endpoint_descriptors@[sender_endpoint_payload as int].unwrap();
    let receiver_thread_ptr = old.get_endpoint(blocking_endpoint_ptr).queue@[0];
    let receiver_container_ptr = old.get_thread(receiver_thread_ptr).owning_container;
    let receiver_endpoint_payload_op = old.get_thread(
        receiver_thread_ptr,
    ).ipc_payload.get_payload_as_endpoint();
    let receiver_endpoint_payload = old.get_thread(
        receiver_thread_ptr,
    ).ipc_payload.get_payload_as_endpoint().unwrap();

    if old.get_endpoint_exists(sender_thread_ptr, blocking_endpoint_index) == false {
        old =~= new
    } else if old.get_endpoint_exists(sender_thread_ptr, blocking_endpoint_index)
        && old.sender_queue_full(sender_thread_ptr, blocking_endpoint_index) {
        old =~= new
    } else if old.get_endpoint_exists(sender_thread_ptr, blocking_endpoint_index)
        && old.no_receiver(sender_thread_ptr, blocking_endpoint_index) {
        // basically nothing changed
        old.thread_dom() =~= new.thread_dom() && old.proc_dom() =~= new.proc_dom()
            && old.container_dom() =~= new.container_dom() && old.endpoint_dom()
            =~= new.endpoint_dom() && forall|t_ptr: ThreadPtr|
            #![trigger new.get_thread(t_ptr)]
            old.thread_dom().contains(t_ptr) && t_ptr != sender_thread_ptr ==> new.get_thread(t_ptr)
                =~= old.get_thread(t_ptr) && forall|proc_ptr: ProcPtr|
                #![trigger new.get_proc(proc_ptr)]
                new.proc_dom().contains(proc_ptr) ==> new.get_proc(proc_ptr) =~= old.get_proc(
                    proc_ptr,
                ) && forall|c: ContainerPtr|
                    #![trigger new.get_container_owned_pages(c)]
                    new.container_dom().contains(c) && c != sender_container_ptr
                        ==> old.get_container(c) =~= new.get_container(c) && forall|
                        e_ptr: EndpointPtr,
                    |
                        #![trigger new.get_endpoint(e_ptr)]
                        new.endpoint_dom().contains(e_ptr) && e_ptr != blocking_endpoint_ptr
                            ==> old.get_endpoint(e_ptr) =~= new.get_endpoint(e_ptr) && forall|
                            c: ContainerPtr,
                        |
                            #![trigger new.get_container_owned_pages(c)]
                            new.container_dom().contains(c) ==> old.get_container_owned_pages(c)
                                =~= new.get_container_owned_pages(c) && forall|p_ptr: ProcPtr|
                                #![trigger new.get_address_space(p_ptr)]
                                new.proc_dom().contains(p_ptr) ==> new.get_address_space(p_ptr)
                                    =~= old.get_address_space(p_ptr) && forall|page_ptr: PagePtr|
                                    #![trigger new.get_physical_page_mapping()[page_ptr]]
                                    old.get_physical_page_mapping().dom().contains(page_ptr)
                                        ==> old.get_physical_page_mapping()[page_ptr]
                                        == new.get_physical_page_mapping()[page_ptr]
                                    // Things changed
                                     && new.get_thread(sender_thread_ptr).endpoint_descriptors@
                                        =~= old.get_thread(sender_thread_ptr).endpoint_descriptors@
                                        && new.get_endpoint(blocking_endpoint_ptr).queue@
                                        =~= old.get_endpoint(blocking_endpoint_ptr).queue@.push(
                                        sender_thread_ptr,
                                    ) && new.get_endpoint(blocking_endpoint_ptr).owning_threads@
                                        =~= old.get_endpoint(blocking_endpoint_ptr).owning_threads@
                                        && new.get_thread(
                                        sender_thread_ptr,
                                    ).ipc_payload.get_payload_as_endpoint() == Some(
                                        sender_endpoint_payload,
                                    ) && new.get_endpoint(blocking_endpoint_ptr).queue_state
                                        =~= old.get_endpoint(blocking_endpoint_ptr).queue_state
    } else if old.get_endpoint_exists(sender_thread_ptr, blocking_endpoint_index)
        && old.receiver_queue_empty(sender_thread_ptr, blocking_endpoint_index) {
        // basically nothing changed
        old.thread_dom() =~= new.thread_dom() && old.proc_dom() =~= new.proc_dom()
            && old.container_dom() =~= new.container_dom() && old.endpoint_dom()
            =~= new.endpoint_dom() && forall|t_ptr: ThreadPtr|
            #![trigger new.get_thread(t_ptr)]
            old.thread_dom().contains(t_ptr) && t_ptr != sender_thread_ptr ==> new.get_thread(t_ptr)
                =~= old.get_thread(t_ptr) && forall|proc_ptr: ProcPtr|
                #![trigger new.get_proc(proc_ptr)]
                new.proc_dom().contains(proc_ptr) ==> new.get_proc(proc_ptr) =~= old.get_proc(
                    proc_ptr,
                ) && forall|c: ContainerPtr|
                    #![trigger new.get_container_owned_pages(c)]
                    new.container_dom().contains(c) && c != sender_container_ptr
                        ==> old.get_container(c) =~= new.get_container(c) && forall|
                        e_ptr: EndpointPtr,
                    |
                        #![trigger new.get_endpoint(e_ptr)]
                        new.endpoint_dom().contains(e_ptr) && e_ptr != blocking_endpoint_ptr
                            ==> old.get_endpoint(e_ptr) =~= new.get_endpoint(e_ptr) && forall|
                            c: ContainerPtr,
                        |
                            #![trigger new.get_container_owned_pages(c)]
                            new.container_dom().contains(c) ==> old.get_container_owned_pages(c)
                                =~= new.get_container_owned_pages(c) && forall|p_ptr: ProcPtr|
                                #![trigger new.get_address_space(p_ptr)]
                                new.proc_dom().contains(p_ptr) ==> new.get_address_space(p_ptr)
                                    =~= old.get_address_space(p_ptr) && forall|page_ptr: PagePtr|
                                    #![trigger new.get_physical_page_mapping()[page_ptr]]
                                    old.get_physical_page_mapping().dom().contains(page_ptr)
                                        ==> old.get_physical_page_mapping()[page_ptr]
                                        == new.get_physical_page_mapping()[page_ptr]
                                    // Things changed
                                     && new.get_thread(sender_thread_ptr).endpoint_descriptors@
                                        =~= old.get_thread(sender_thread_ptr).endpoint_descriptors@
                                        && new.get_endpoint(blocking_endpoint_ptr).queue@
                                        =~= old.get_endpoint(blocking_endpoint_ptr).queue@.push(
                                        sender_thread_ptr,
                                    ) && new.get_endpoint(blocking_endpoint_ptr).owning_threads@
                                        =~= old.get_endpoint(blocking_endpoint_ptr).owning_threads@
                                        && new.get_thread(
                                        sender_thread_ptr,
                                    ).ipc_payload.get_payload_as_endpoint() == Some(
                                        sender_endpoint_payload,
                                    ) && new.get_endpoint(blocking_endpoint_ptr).queue_state
                                        =~= EndpointState::SEND
    } else if receiver_endpoint_payload_op.is_None() {
        old =~= new
    } else if sender_endpoint_ptr_op.is_None() {
        old =~= new
    } else if old.get_endpoint(sender_endpoint_ptr).rf_counter == usize::MAX {
        old =~= new
    } else if receiver_endpoint_payload >= MAX_NUM_ENDPOINT_DESCRIPTORS {
        old =~= new
    } else if old.get_thread(
        receiver_thread_ptr,
    ).endpoint_descriptors@[receiver_endpoint_payload as int].is_Some() {
        old =~= new
    } else if old.get_is_scheduler_full(receiver_container_ptr) {
        old =~= new
    } else {
        old.thread_dom() =~= new.thread_dom() && old.proc_dom() =~= new.proc_dom()
            && old.container_dom() =~= new.container_dom() && old.endpoint_dom()
            =~= new.endpoint_dom() && forall|t_ptr: ThreadPtr|
            #![trigger new.get_thread(t_ptr)]
            old.thread_dom().contains(t_ptr) && t_ptr != receiver_thread_ptr ==> new.get_thread(
                t_ptr,
            ) =~= old.get_thread(t_ptr) && forall|proc_ptr: ProcPtr|
                #![trigger new.get_proc(proc_ptr)]
                new.proc_dom().contains(proc_ptr) ==> new.get_proc(proc_ptr) =~= old.get_proc(
                    proc_ptr,
                ) && forall|c: ContainerPtr|
                    #![trigger new.get_container_owned_pages(c)]
                    new.container_dom().contains(c) && c != receiver_container_ptr
                        ==> old.get_container(c) =~= new.get_container(c) && forall|
                        e_ptr: EndpointPtr,
                    |
                        #![trigger new.get_endpoint(e_ptr)]
                        new.endpoint_dom().contains(e_ptr) && e_ptr != blocking_endpoint_ptr
                            && e_ptr != sender_endpoint_ptr ==> old.get_endpoint(e_ptr)
                            =~= new.get_endpoint(e_ptr) && forall|c: ContainerPtr|
                            #![trigger new.get_container_owned_pages(c)]
                            new.container_dom().contains(c) ==> old.get_container_owned_pages(c)
                                =~= new.get_container_owned_pages(c) && forall|p_ptr: ProcPtr|
                                #![trigger new.get_address_space(p_ptr)]
                                new.proc_dom().contains(p_ptr) ==> new.get_address_space(p_ptr)
                                    =~= old.get_address_space(p_ptr) && forall|page_ptr: PagePtr|
                                    #![trigger new.get_physical_page_mapping()[page_ptr]]
                                    old.get_physical_page_mapping().dom().contains(page_ptr)
                                        ==> old.get_physical_page_mapping()[page_ptr]
                                        == new.get_physical_page_mapping()[page_ptr]
                                    // Things changed
                                     && new.get_thread(sender_thread_ptr).endpoint_descriptors@
                                        =~= old.get_thread(sender_thread_ptr).endpoint_descriptors@
                                        && new.get_thread(receiver_thread_ptr).endpoint_descriptors@
                                        =~= old.get_thread(
                                        receiver_thread_ptr,
                                    ).endpoint_descriptors@.update(
                                        receiver_endpoint_payload as int,
                                        Some(sender_endpoint_ptr),
                                    ) && new.get_endpoint(blocking_endpoint_ptr).queue@
                                        =~= old.get_endpoint(blocking_endpoint_ptr).queue@.skip(1)
                                        && (blocking_endpoint_ptr != sender_endpoint_ptr
                                        ==> new.get_endpoint(blocking_endpoint_ptr).owning_threads@
                                        =~= old.get_endpoint(blocking_endpoint_ptr).owning_threads@)
                                        && new.get_endpoint(blocking_endpoint_ptr).queue_state
                                        =~= old.get_endpoint(blocking_endpoint_ptr).queue_state && (
                                    blocking_endpoint_ptr != sender_endpoint_ptr
                                        ==> new.get_endpoint(sender_endpoint_ptr).queue
                                        =~= old.get_endpoint(sender_endpoint_ptr).queue)
                                        && new.get_endpoint(sender_endpoint_ptr).owning_threads@
                                        =~= old.get_endpoint(
                                        sender_endpoint_ptr,
                                    ).owning_threads@.insert(
                                        (receiver_thread_ptr, receiver_endpoint_payload),
                                    ) && new.get_endpoint(sender_endpoint_ptr).queue_state
                                        =~= old.get_endpoint(sender_endpoint_ptr).queue_state
    }
}

impl Kernel {
    ///
    /// pass payload only below are satisified
    /// &&& endpoint must be well formed
    /// &&& sender payload must be well formed
    /// &&& receiver payload must be well formed
    /// &&& endpoint state is correct with respect to send.
    ///
    /// endpoint state
    /// | queue state | queue len | action |
    /// | send        | >= 0      | block  |
    /// | receive     | == 0      | block + changed queue state |
    /// | receive     | > 0       | success |
    ///
    pub fn syscall_send_endpoint(
        &mut self,
        sender_thread_ptr: ThreadPtr,
        blocking_endpoint_index: EndpointIdx,
        sender_endpoint_payload: EndpointIdx,
    ) -> (ret: SyscallReturnStruct)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(sender_thread_ptr),
            0 <= blocking_endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(sender_thread_ptr).state == ThreadState::RUNNING,
            0 <= sender_endpoint_payload < MAX_NUM_ENDPOINT_DESCRIPTORS,
        ensures
            syscall_send_endpoint_spec(
                *old(self),
                *self,
                sender_thread_ptr,
                blocking_endpoint_index,
                sender_endpoint_payload,
                ret,
            ),
            self.wf(),
    {
        proof {
            self.proc_man.thread_inv();
            self.proc_man.endpoint_inv();
        }
        let sender_container_ptr = self.proc_man.get_thread(sender_thread_ptr).owning_container;
        let blocking_endpoint_ptr_op = self.proc_man.get_thread(sender_thread_ptr).endpoint_descriptors.get(blocking_endpoint_index);
        let payload_endpoint_ptr_op = self.proc_man.get_thread(sender_thread_ptr).endpoint_descriptors.get(sender_endpoint_payload);

        if blocking_endpoint_ptr_op.is_none() {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        let blocking_endpoint_ptr = blocking_endpoint_ptr_op.unwrap();
        if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_send()
            && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len()
            < MAX_NUM_THREADS_PER_ENDPOINT {
            // Block
            self.proc_man.block_running_thread(
                sender_thread_ptr,
                blocking_endpoint_index,
                IPCPayLoad::Endpoint { endpoint_index: sender_endpoint_payload },
            );
            assert(self.wf());
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_send()
            && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len()
            >= MAX_NUM_THREADS_PER_ENDPOINT {
            // return error
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_receive()
            && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len() == 0 {
            // change queue state and Block
            self.proc_man.block_running_thread_and_change_queue_state(
                sender_thread_ptr,
                blocking_endpoint_index,
                IPCPayLoad::Endpoint { endpoint_index: sender_endpoint_payload },
                EndpointState::SEND,
            );
            assert(self.wf());
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        assert(self.receiver_exist(sender_thread_ptr, blocking_endpoint_index));

        let receiver_thread_ptr = self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.get_head();
        let receiver_container_ptr = self.proc_man.get_thread(receiver_thread_ptr).owning_container;
        let receiver_endpoint_payload_op = self.proc_man.get_thread(receiver_thread_ptr).ipc_payload.get_payload_as_endpoint();

        if receiver_endpoint_payload_op.is_none() {
            // receiver not receiving endpoint
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        let receiver_endpoint_payload = receiver_endpoint_payload_op.unwrap();

        if payload_endpoint_ptr_op.is_none() {
            // passing nothing
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        let payload_endpoint_ptr = payload_endpoint_ptr_op.unwrap();
        if self.proc_man.get_endpoint(payload_endpoint_ptr).rf_counter == usize::MAX {
            // src endpoint cannot be shared anymore (impossible)
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if receiver_endpoint_payload >= MAX_NUM_ENDPOINT_DESCRIPTORS || self.proc_man.get_thread(
            receiver_thread_ptr,
        ).endpoint_descriptors.get(receiver_endpoint_payload).is_some() {
            // payload is broken or receiver has no space
            //@Xiangdong schedule the reciever
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_container(receiver_container_ptr).scheduler.len()
            >= MAX_CONTAINER_SCHEDULER_LEN {
            // cannot schedule the receiver
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        
        let payload_endpoint_container_ptr = self.proc_man.get_endpoint(payload_endpoint_ptr).owning_container;

        if self.proc_man.container_check_is_ancestor(payload_endpoint_container_ptr, receiver_container_ptr) == false 
            && payload_endpoint_container_ptr != receiver_container_ptr {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }

        self.proc_man.schedule_blocked_thread(blocking_endpoint_ptr);
        assert(forall|t_ptr: ThreadPtr|
            #![trigger old(self).get_thread(t_ptr)]
            old(self).thread_dom().contains(t_ptr) ==> old(self).get_thread(
                t_ptr,
            ).endpoint_descriptors =~= self.get_thread(t_ptr).endpoint_descriptors);
        assert(forall|e_ptr: EndpointPtr|
            #![trigger self.get_endpoint(e_ptr)]
            self.endpoint_dom().contains(e_ptr) ==> old(self).get_endpoint(e_ptr).queue_state
                =~= self.get_endpoint(e_ptr).queue_state);
        assert(blocking_endpoint_ptr != payload_endpoint_ptr ==> self.get_endpoint(
            payload_endpoint_ptr,
        ).queue =~= old(self).get_endpoint(payload_endpoint_ptr).queue);

        self.proc_man.pass_endpoint(
            sender_thread_ptr,
            sender_endpoint_payload,
            receiver_thread_ptr,
            receiver_endpoint_payload,
        );

        assert(old(self).get_thread(
            sender_thread_ptr,
        ).endpoint_descriptors@[sender_endpoint_payload as int].unwrap() == payload_endpoint_ptr);
        assert(self.get_thread(
            sender_thread_ptr,
        ).endpoint_descriptors@[sender_endpoint_payload as int].unwrap() == payload_endpoint_ptr);
        assert(self.get_endpoint(payload_endpoint_ptr).queue_state == old(self).get_endpoint(
            payload_endpoint_ptr,
        ).queue_state);
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Else);
    }
}

} // verus!

use vstd::prelude::*;
verus! {

use crate::define::*;
use crate::kernel::Kernel;
use crate::process_manager::thread::IPCPayLoad;

// Block thread functional correctness
pub open spec fn is_thread_blocked(
    old: Kernel,
    new: Kernel,
    thread_ptr: ThreadPtr,
    endpoint: EndpointIdx,
    payload: EndpointIdx,
) -> bool {
    let endpoint_ptr = old.get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint).unwrap();
    let container_ptr = old.get_thread(thread_ptr).owning_container;

    // verify kernel are unchanged
    old.thread_dom() =~= new.thread_dom() && old.proc_dom() =~= new.proc_dom()
        && old.container_dom() =~= new.container_dom() && old.endpoint_dom() =~= new.endpoint_dom()
        && forall|t_ptr: ThreadPtr|
        #![trigger new.get_thread(t_ptr)]
        old.thread_dom().contains(t_ptr) && t_ptr != thread_ptr ==> new.get_thread(t_ptr)
            =~= old.get_thread(t_ptr) && forall|proc_ptr: ProcPtr|
            #![trigger new.get_proc(proc_ptr)]
            new.proc_dom().contains(proc_ptr) ==> new.get_proc(proc_ptr) =~= old.get_proc(proc_ptr)
                && forall|c: ContainerPtr|
                #![trigger new.get_container_owned_pages(c)]
                new.container_dom().contains(c) && c != container_ptr ==> old.get_container(c)
                    =~= new.get_container(c) && forall|e_ptr: EndpointPtr|
                    #![trigger new.get_endpoint(e_ptr)]
                    new.endpoint_dom().contains(e_ptr) && e_ptr != endpoint_ptr
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
                                    == new.get_physical_page_mapping()[page_ptr] && new.get_thread(
                                    thread_ptr,
                                ).endpoint_descriptors@ =~= old.get_thread(
                                    thread_ptr,
                                ).endpoint_descriptors@ && new.get_endpoint(
                                    endpoint_ptr,
                                ).owning_threads@ =~= old.get_endpoint(endpoint_ptr).owning_threads@
                                    &&   // Things changed
                                new.get_endpoint(endpoint_ptr).queue@ =~= old.get_endpoint(
                                    endpoint_ptr,
                                ).queue@.push(
                                    thread_ptr,
                                )  // thread should have been saved onto the queue
                                 && new.get_thread(thread_ptr).ipc_payload.get_payload_as_endpoint()
                                    == Some(
                                    payload,
                                )  // payload should be saved on ipc_payload on thread

}

pub open spec fn is_pass_endpoint_completed(
    old: Kernel,
    new: Kernel,
    src_thread_ptr: ThreadPtr,
    dst_thread_ptr: ThreadPtr,
    shared_endpoint: EndpointPtr,
    from: EndpointIdx,
    to: EndpointIdx,
) -> bool {
    let src_payload_endpoint_ptr = old.get_endpoint_ptr_by_endpoint_idx(
        src_thread_ptr,
        from,
    ).unwrap();
    let dst_container_ptr = old.get_thread(dst_thread_ptr).owning_container;
    let src_container_ptr = old.get_thread(src_thread_ptr).owning_container;
    old.thread_dom() =~= new.thread_dom() && old.proc_dom() =~= new.proc_dom()
        && old.container_dom() =~= new.container_dom() && old.endpoint_dom() =~= new.endpoint_dom()
        && forall|t_ptr: ThreadPtr|
        #![trigger new.get_thread(t_ptr)]
        old.thread_dom().contains(t_ptr) && t_ptr != dst_thread_ptr && t_ptr != src_thread_ptr
            ==> new.get_thread(t_ptr) =~= old.get_thread(t_ptr) && forall|proc_ptr: ProcPtr|
            #![trigger new.get_proc(proc_ptr)]
            new.proc_dom().contains(proc_ptr) ==> new.get_proc(proc_ptr) =~= old.get_proc(proc_ptr)
                && forall|c: ContainerPtr|
                #![trigger new.get_container_owned_pages(c)]
                new.container_dom().contains(c) && c != dst_container_ptr && c != src_container_ptr
                    ==> old.get_container(c) =~= new.get_container(c) && forall|e_ptr: EndpointPtr|
                    #![trigger new.get_endpoint(e_ptr)]
                    new.endpoint_dom().contains(e_ptr) && e_ptr != shared_endpoint && e_ptr
                        != src_payload_endpoint_ptr ==> old.get_endpoint(e_ptr)
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
                                    &&
                                // dst thread received endpoint from src thread
                                new.get_thread(dst_thread_ptr).endpoint_descriptors@
                                    =~= old.get_thread(dst_thread_ptr).endpoint_descriptors@.update(
                                    to as int,
                                    Some(src_payload_endpoint_ptr),
                                )
                                    &&   // shared endpoint queue (send queue) should have one less blocked threads.
                                new.get_endpoint(shared_endpoint).queue@ =~= old.get_endpoint(
                                    shared_endpoint,
                                ).queue@.skip(1)
                                    &&   // dst thread should now a owner of payload (endpoint)
                                new.get_endpoint(src_payload_endpoint_ptr).owning_threads@
                                    =~= old.get_endpoint(
                                    src_payload_endpoint_ptr,
                                ).owning_threads@.insert((dst_thread_ptr, to))
}

pub open spec fn syscall_receive_endpoint_fail(
    old: Kernel,
    new: Kernel,
    receiver_thread_ptr: ThreadPtr,
    blocking_endpoint_index: EndpointIdx,
    receiver_endpoint_payload: EndpointIdx,
) -> bool {
    let blocking_endpoint_ptr = old.get_endpoint_ptr_by_endpoint_idx(
        receiver_thread_ptr,
        blocking_endpoint_index,
    ).unwrap();

    if old.get_endpoint_exists(receiver_thread_ptr, blocking_endpoint_index) && old.no_sender(
        receiver_thread_ptr,
        blocking_endpoint_index,
    ) {
        &&& is_thread_blocked(
            old,
            new,
            receiver_thread_ptr,
            blocking_endpoint_index,
            receiver_endpoint_payload,
        )
        &&& new.get_endpoint(blocking_endpoint_ptr).queue_state =~= old.get_endpoint(
            blocking_endpoint_ptr,
        ).queue_state
    }  // queue state should have changed to receive
     else if old.get_endpoint_exists(receiver_thread_ptr, blocking_endpoint_index)
        && old.sender_queue_empty(receiver_thread_ptr, blocking_endpoint_index) {
        &&& is_thread_blocked(
            old,
            new,
            receiver_thread_ptr,
            blocking_endpoint_index,
            receiver_endpoint_payload,
        )
        &&& new.get_endpoint(blocking_endpoint_ptr).queue_state =~= EndpointState::RECEIVE
    } else {
        old =~= new
    }
}

pub open spec fn syscall_receive_endpoint_success(
    old: Kernel,
    new: Kernel,
    receiver_thread_ptr: ThreadPtr,
    blocking_endpoint_index: EndpointIdx,
    receiver_endpoint_payload: EndpointIdx,
) -> bool {
    let blocking_endpoint_ptr = old.get_endpoint_ptr_by_endpoint_idx(
        receiver_thread_ptr,
        blocking_endpoint_index,
    ).unwrap();
    let sender_thread_ptr = old.get_endpoint(blocking_endpoint_ptr).queue@[0];
    let sender_endpoint_payload = old.get_thread(
        sender_thread_ptr,
    ).ipc_payload.get_payload_as_endpoint().unwrap();
    is_pass_endpoint_completed(
        old,
        new,
        sender_thread_ptr,
        receiver_thread_ptr,
        blocking_endpoint_ptr,
        sender_endpoint_payload,
        receiver_endpoint_payload,
    )
}

pub open spec fn syscall_receive_endpoint_spec(
    old: Kernel,
    new: Kernel,
    receiver_thread_ptr: ThreadPtr,
    blocking_endpoint_index: EndpointIdx,
    receiver_endpoint_payload: EndpointIdx,
    ret: SyscallReturnStruct,
) -> bool {
    if ret.is_error() {
        syscall_receive_endpoint_fail(
            old,
            new,
            receiver_thread_ptr,
            blocking_endpoint_index,
            receiver_endpoint_payload,
        )
    } else {
        syscall_receive_endpoint_success(
            old,
            new,
            receiver_thread_ptr,
            blocking_endpoint_index,
            receiver_endpoint_payload,
        )
    }
}

impl Kernel {
    ///
    /// endpoint state
    /// | queue state | queue len | action  |
    /// | send        | > 0       | success |
    /// | send        | == 0      | block + changed queue state |
    /// | receive     | >= 0      | block |
    ///
    /// suceed only if
    ///     queue state == send && queue len > 0
    ///
    pub fn syscall_receive_endpoint(
        &mut self,
        receiver_thread_ptr: ThreadPtr,
        blocking_endpoint_index: EndpointIdx,
        receiver_endpoint_payload: EndpointIdx,
    ) -> (ret: SyscallReturnStruct)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(receiver_thread_ptr),
            0 <= blocking_endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(receiver_thread_ptr).state == ThreadState::RUNNING,
            0 <= receiver_endpoint_payload < MAX_NUM_ENDPOINT_DESCRIPTORS,
        ensures
    // syscall_receiver_endpoint_spec(*old(self), *self, receiver_thread_ptr, blocking_endpoint_index, receiver_endpoint_payload, ret),

            !ret.is_error() ==> syscall_receive_endpoint_success(
                *old(self),
                *self,
                receiver_thread_ptr,
                blocking_endpoint_index,
                receiver_endpoint_payload,
            ),
            ret.is_error() ==> syscall_receive_endpoint_fail(
                *old(self),
                *self,
                receiver_thread_ptr,
                blocking_endpoint_index,
                receiver_endpoint_payload,
            ),
            self.wf(),
    {
        proof {
            self.proc_man.thread_inv();
            self.proc_man.endpoint_inv();
        }

        // Check shared endpoint
        let blocking_endpoint_ptr_op = self.proc_man.get_thread(receiver_thread_ptr).endpoint_descriptors.get(blocking_endpoint_index);

        if blocking_endpoint_ptr_op.is_none() {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }

        let blocking_endpoint_ptr = blocking_endpoint_ptr_op.unwrap();
        if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_receive()
            && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len()
            < MAX_NUM_THREADS_PER_ENDPOINT {
            // Block
            self.proc_man.block_running_thread(
                receiver_thread_ptr,
                blocking_endpoint_index,
                IPCPayLoad::Endpoint { endpoint_index: receiver_endpoint_payload },
            );
            assert(self.wf());
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_receive()
            && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len()
            >= MAX_NUM_THREADS_PER_ENDPOINT {
            // return error
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_send()
            && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len() == 0 {
            // change queue state and Block
            self.proc_man.block_running_thread_and_change_queue_state(
                receiver_thread_ptr,
                blocking_endpoint_index,
                IPCPayLoad::Endpoint { endpoint_index: receiver_endpoint_payload },
                EndpointState::RECEIVE,
            );
            assert(self.wf());
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        // Make sure we can access sender from shared endpoint

        assert(self.sender_exist(receiver_thread_ptr, blocking_endpoint_index));

        // checking sender thread payload well formed
        let sender_thread_ptr = self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.get_head();
        let sender_container_ptr = self.proc_man.get_thread(sender_thread_ptr).owning_container;
        let sender_endpoint_payload_op = self.proc_man.get_thread(sender_thread_ptr,).ipc_payload.get_payload_as_endpoint();
        // sender payload ill formed
        if sender_endpoint_payload_op.is_none() {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        let sender_endpoint_payload = sender_endpoint_payload_op.unwrap();

        // sender payload is ill formed
        if sender_endpoint_payload >= MAX_NUM_ENDPOINT_DESCRIPTORS {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }  //assert(blocking_endpoint_ptr != sender_endpoint_ptr ==> self.get_endpoint(sender_endpoint_ptr).queue =~= old(self).get_endpoint(sender_endpoint_ptr).queue);

        let payload_endpoint_ptr_op = self.proc_man.get_thread(sender_thread_ptr).endpoint_descriptors.get(sender_endpoint_payload);
        if payload_endpoint_ptr_op.is_none() {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        let payload_endpoint_ptr = payload_endpoint_ptr_op.unwrap();
        // sender payload has max owner
        if self.proc_man.get_endpoint(payload_endpoint_ptr).rf_counter == usize::MAX {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        // Now check receiver payload

        let receiver_endpoint_dsecriptor_ptr_op = self.proc_man.get_thread(
            receiver_thread_ptr,
        ).endpoint_descriptors.get(receiver_endpoint_payload);
        let receiver_container_ptr = self.proc_man.get_thread(receiver_thread_ptr).owning_container;

        // payload idx slot should be empty.
        if receiver_endpoint_dsecriptor_ptr_op.is_some() {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        // cannot schedule the sender

        if self.proc_man.get_container(sender_container_ptr).scheduler.len()
            >= MAX_CONTAINER_SCHEDULER_LEN {
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

        self.proc_man.pass_endpoint(
            sender_thread_ptr,
            sender_endpoint_payload,
            receiver_thread_ptr,
            receiver_endpoint_payload,
        );

        return SyscallReturnStruct::NoSwitchNew(RetValueType::Else);
    }
}

} // verus!

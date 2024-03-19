use super::*;

use vstd::prelude::*;
verus! {
use vstd::ptr::*;
use crate::mars_staticlinkedlist::*;

use crate::define::*;
use crate::trap::*;


pub struct Endpoint{
    pub queue: MarsStaticLinkedList<MAX_NUM_THREADS_PER_ENDPOINT>,
    pub rf_counter: usize,
    pub queue_state: EndpointState,

    pub owning_threads: Ghost<Set<ThreadPtr>>,
}

impl Endpoint{
    pub open spec fn spec_len(&self) -> usize{
        self.queue.len()
    }

    #[verifier(when_used_as_spec(spec_len))]
    pub fn len(&self) -> (ret: usize)
        requires
            self.queue.wf(),
        ensures
            ret == self.spec_len(),
    {
        self.queue.len()
    }
}

impl ProcessManager{

        pub fn proc_man_set_endpoint_queue_state_by_endpoint_ptr(&mut self, endpoint_ptr: EndpointPtr, endpoint_queue_state: EndpointState)
            requires
                old(self).wf(),
                old(self).get_endpoint_ptrs().contains(endpoint_ptr),
            ensures
                self.wf(),
                self.get_proc_ptrs() =~= old(self).get_proc_ptrs(),
                self.get_thread_ptrs() =~= old(self).get_thread_ptrs(),
                self.get_endpoint_ptrs() =~= old(self).get_endpoint_ptrs(),
                self.pcid_closure =~= old(self).pcid_closure,
                self.ioid_closure =~= old(self).ioid_closure,
                self.scheduler =~= old(self).scheduler,
                forall|_thread_ptr:ThreadPtr| #![auto] self.thread_perms@.dom().contains(_thread_ptr) ==> self.thread_perms@[_thread_ptr]@.value.get_Some_0() =~= old(self).thread_perms@[_thread_ptr]@.value.get_Some_0(),
                forall|_thread_ptr:ThreadPtr| #![auto] self.thread_perms@.dom().contains(_thread_ptr) ==> self.thread_perms@[_thread_ptr]@.value.get_Some_0().state =~= old(self).thread_perms@[_thread_ptr]@.value.get_Some_0().state,
        {
            let mut endpoint_perm =
            Tracked((self.endpoint_perms.borrow_mut()).tracked_remove(endpoint_ptr));
            assert(self.endpoint_perms@.dom().contains(endpoint_ptr) == false);
            endpoint_set_queue_state(PPtr::<Endpoint>::from_usize(endpoint_ptr), &mut endpoint_perm, endpoint_queue_state);
            proof{
                assert(self.endpoint_perms@.dom().contains(endpoint_ptr) == false);
                (self.endpoint_perms.borrow_mut())
                    .tracked_insert(endpoint_ptr, endpoint_perm.get());
            }

            assert(self.wf());
        }

        pub fn remove_thread_endpoint_descriptors(&mut self, thread_ptr:ThreadPtr) -> (ret: Ghost<Set<PagePtr>>)
        requires
            old(self).wf(),
            old(self).get_thread_ptrs().contains(thread_ptr),
            old(self).get_thread(thread_ptr).state == TRANSIT,
        ensures
            self.wf(),
            self.get_thread_ptrs().contains(thread_ptr),
            ret@.finite(),
            ret@.disjoint(self.get_proc_man_page_closure()),
            ret@ + self.get_proc_man_page_closure() =~= old(self).get_proc_man_page_closure(),
            ret@.subset_of(old(self).get_proc_man_page_closure()),
            forall|i:int| #![auto] 0<=i< MAX_NUM_ENDPOINT_DESCRIPTORS ==> self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_descriptors@[i] == 0,
            self.proc_ptrs@ =~= old(self).proc_ptrs@,
            self.proc_perms@ =~= old(self).proc_perms@,
            self.thread_ptrs@ =~= old(self).thread_ptrs@,
            self.scheduler =~= old(self).scheduler,
            self.thread_perms@.dom() =~= old(self).thread_perms@.dom(),
            self.thread_perms@[thread_ptr].view().value.get_Some_0().parent =~= old(self).thread_perms@[thread_ptr].view().value.get_Some_0().parent,
            self.proc_perms =~= old(self).proc_perms,
            forall|_thread_ptr:ThreadPtr| #![auto] self.thread_perms@.dom().contains(_thread_ptr) && _thread_ptr != thread_ptr ==> self.thread_perms@[_thread_ptr]@ =~= old(self).thread_perms@[_thread_ptr]@,
            self.thread_perms@[thread_ptr].view().value.get_Some_0().parent == old(self).thread_perms@[thread_ptr].view().value.get_Some_0().parent,
            self.thread_perms@[thread_ptr].view().value.get_Some_0().state == old(self).thread_perms@[thread_ptr].view().value.get_Some_0().state,
            self.thread_perms@[thread_ptr].view().value.get_Some_0().parent_rf == old(self).thread_perms@[thread_ptr].view().value.get_Some_0().parent_rf,
            self.thread_perms@[thread_ptr].view().value.get_Some_0().scheduler_rf == old(self).thread_perms@[thread_ptr].view().value.get_Some_0().scheduler_rf,
            self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_ptr == old(self).thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_ptr,
            self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_rf == old(self).thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_rf,
            forall|_thread_ptr:ThreadPtr| #![auto] self.thread_perms@.dom().contains(_thread_ptr) ==> self.thread_perms@[_thread_ptr]@.value.get_Some_0().state =~= old(self).thread_perms@[_thread_ptr]@.value.get_Some_0().state,
    {
        let mut loop_i = 0;
        let mut ret = Ghost(Set::<PagePtr>::empty());
        while loop_i != MAX_NUM_ENDPOINT_DESCRIPTORS
            invariant
                0 <= loop_i <= MAX_NUM_ENDPOINT_DESCRIPTORS,
                self.wf(),
                self.thread_perms@.dom().contains(thread_ptr),
                forall|i:int| #![auto] 0<=i< loop_i ==> self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_descriptors@[i] == 0,
                self.get_thread(thread_ptr).state == TRANSIT,
                self.get_proc_man_page_closure().finite(),
                old(self).get_proc_man_page_closure().finite(),
                ret@.finite(),
                ret@.disjoint(self.get_proc_man_page_closure()),
                ret@ + self.get_proc_man_page_closure() =~= old(self).get_proc_man_page_closure(),
                self.get_proc_man_page_closure().subset_of(old(self).get_proc_man_page_closure()),
                ret@.subset_of(old(self).get_proc_man_page_closure()),
                self.proc_ptrs@ =~= old(self).proc_ptrs@,
                self.proc_perms@ =~= old(self).proc_perms@,
                self.thread_ptrs@ =~= old(self).thread_ptrs@,
                self.scheduler =~= old(self).scheduler,
                self.thread_perms@.dom() =~= old(self).thread_perms@.dom(),
                self.proc_perms =~= old(self).proc_perms,
                forall|_thread_ptr:ThreadPtr| #![auto] self.thread_perms@.dom().contains(_thread_ptr) && _thread_ptr != thread_ptr ==> self.thread_perms@[_thread_ptr]@ =~= old(self).thread_perms@[_thread_ptr]@,
                self.thread_perms@[thread_ptr].view().value.get_Some_0().parent == old(self).thread_perms@[thread_ptr].view().value.get_Some_0().parent,
                self.thread_perms@[thread_ptr].view().value.get_Some_0().state == old(self).thread_perms@[thread_ptr].view().value.get_Some_0().state,
                self.thread_perms@[thread_ptr].view().value.get_Some_0().parent_rf == old(self).thread_perms@[thread_ptr].view().value.get_Some_0().parent_rf,
                self.thread_perms@[thread_ptr].view().value.get_Some_0().scheduler_rf == old(self).thread_perms@[thread_ptr].view().value.get_Some_0().scheduler_rf,
                self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_ptr == old(self).thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_ptr,
                self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_rf == old(self).thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_rf,
                forall|_thread_ptr:ThreadPtr| #![auto] self.thread_perms@.dom().contains(_thread_ptr) ==> self.thread_perms@[_thread_ptr]@.value.get_Some_0().state =~= old(self).thread_perms@[_thread_ptr]@.value.get_Some_0().state,
            ensures
                loop_i == MAX_NUM_ENDPOINT_DESCRIPTORS,
                self.wf(),
                self.thread_perms@.dom().contains(thread_ptr),
                forall|i:int| #![auto] 0<=i< MAX_NUM_ENDPOINT_DESCRIPTORS ==> self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_descriptors@[i] == 0,
                self.get_thread(thread_ptr).state == TRANSIT,
                self.get_proc_man_page_closure().subset_of(old(self).get_proc_man_page_closure()),
                self.get_proc_man_page_closure().finite(),
                old(self).get_proc_man_page_closure().finite(),
                ret@.finite(),
                ret@.disjoint(self.get_proc_man_page_closure()),
                ret@ + self.get_proc_man_page_closure() =~= old(self).get_proc_man_page_closure(),
                self.get_proc_man_page_closure().subset_of(old(self).get_proc_man_page_closure()),
                ret@.subset_of(old(self).get_proc_man_page_closure()),
                self.proc_ptrs@ =~= old(self).proc_ptrs@,
                self.proc_perms@ =~= old(self).proc_perms@,
                self.thread_ptrs@ =~= old(self).thread_ptrs@,
                self.scheduler =~= old(self).scheduler,
                self.thread_perms@.dom() =~= old(self).thread_perms@.dom(),
                self.proc_perms =~= old(self).proc_perms,
                forall|_thread_ptr:ThreadPtr| #![auto] self.thread_perms@.dom().contains(_thread_ptr) && _thread_ptr != thread_ptr ==> self.thread_perms@[_thread_ptr]@ =~= old(self).thread_perms@[_thread_ptr]@,
                self.thread_perms@[thread_ptr].view().value.get_Some_0().parent == old(self).thread_perms@[thread_ptr].view().value.get_Some_0().parent,
                self.thread_perms@[thread_ptr].view().value.get_Some_0().state == old(self).thread_perms@[thread_ptr].view().value.get_Some_0().state,
                self.thread_perms@[thread_ptr].view().value.get_Some_0().parent_rf == old(self).thread_perms@[thread_ptr].view().value.get_Some_0().parent_rf,
                self.thread_perms@[thread_ptr].view().value.get_Some_0().scheduler_rf == old(self).thread_perms@[thread_ptr].view().value.get_Some_0().scheduler_rf,
                self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_ptr == old(self).thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_ptr,
                self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_rf == old(self).thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_rf,
                forall|_thread_ptr:ThreadPtr| #![auto] self.thread_perms@.dom().contains(_thread_ptr) ==> self.thread_perms@[_thread_ptr]@.value.get_Some_0().state =~= old(self).thread_perms@[_thread_ptr]@.value.get_Some_0().state,
            {
            assert(self.thread_perms@.dom().contains(thread_ptr));
            let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
            let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));
            assert(thread.endpoint_descriptors.wf());

            let endpoint_ptr = *thread.endpoint_descriptors.get(loop_i);
            if endpoint_ptr == 0{

            }
            else{
                let mut thread_perm =
                    Tracked((self.thread_perms.borrow_mut()).tracked_remove(thread_ptr));
                assert(self.thread_perms@.dom().contains(thread_ptr) == false);
                thread_set_endpoint_descriptors(&PPtr::<Thread>::from_usize(thread_ptr), &mut thread_perm, loop_i, 0);
                proof{
                    assert(self.thread_perms@.dom().contains(thread_ptr) == false);
                    (self.thread_perms.borrow_mut())
                        .tracked_insert(thread_ptr, thread_perm.get());
                }
                assert(self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().owning_threads@.contains(thread_ptr));
                let mut endpoint_perm =
                    Tracked((self.endpoint_perms.borrow_mut()).tracked_remove(endpoint_ptr));
                assert(self.endpoint_perms@.dom().contains(endpoint_ptr) == false);
                endpoint_remove_owning_thread(PPtr::<Endpoint>::from_usize(endpoint_ptr), &mut endpoint_perm, thread_ptr);
                assert(endpoint_perm@@.value.get_Some_0().owning_threads@.len() == endpoint_perm@@.value.get_Some_0().rf_counter);
                proof{
                    assert(self.endpoint_perms@.dom().contains(endpoint_ptr) == false);
                    (self.endpoint_perms.borrow_mut())
                        .tracked_insert(endpoint_ptr, endpoint_perm.get());
                }


                assert(self.wf_threads());
                assert(self.wf_procs());
                assert(self.wf_scheduler());
                assert(self.wf_mem_closure());
                assert(self.wf_pcid_closure());

                let tracked endpoint_perm = self.endpoint_perms.borrow().tracked_borrow(endpoint_ptr);
                let endpoint : &Endpoint = PPtr::<Endpoint>::from_usize(endpoint_ptr).borrow(Tracked(endpoint_perm));

                if endpoint.rf_counter == 0 {
                    assert(self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().owning_threads@ =~= Set::empty());
                    assert(forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr)
                        ==> self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().owning_threads@.contains(thread_ptr) == false);
                    assert(forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr)
                        ==> (forall|i:int| #![auto] 0<=i<MAX_NUM_ENDPOINT_DESCRIPTORS ==> self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_descriptors@[i] != endpoint_ptr
                    ));

                    proof{
                        assert(ret@.disjoint(self.get_proc_man_page_closure()));
                        let old_closure = self.get_proc_man_page_closure();
                        assert(self.get_proc_man_page_closure().contains(endpoint_ptr) == true);
                        assert(ret@.contains(endpoint_ptr) == false);
                        (self.endpoint_perms.borrow_mut()).tracked_remove(endpoint_ptr);
                        self.endpoint_ptrs@ =  self.endpoint_ptrs@.remove(endpoint_ptr);
                        assert(old_closure.remove(endpoint_ptr) =~= self.get_proc_man_page_closure());
                        ret@ = ret@.insert(endpoint_ptr);
                        assert(ret@.disjoint(self.get_proc_man_page_closure()));
                    }

                }

                assert(self.wf_endpoints());
            }
            loop_i = loop_i + 1;
        }
        assert(ret@.finite());
        assert(ret@.disjoint(self.get_proc_man_page_closure()));
        assert(ret@ + self.get_proc_man_page_closure() =~= old(self).get_proc_man_page_closure());

        assert(self.wf_endpoints());
        assert(self.wf());
        return ret;
    }

    //pop endpoint.
    pub fn pop_endpoint_to_running(&mut self, thread_ptr: ThreadPtr, endpoint_index: EndpointIdx) -> (ret: (ThreadPtr, PtRegs))
        requires
            old(self).wf(),
            old(self).get_thread_ptrs().contains(thread_ptr),
            0<=endpoint_index<MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int] != 0,
            //old(self).get_thread(thread_ptr).state == TRANSIT,
            old(self).get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int]).len() != 0,
        ensures
            self.wf(),
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) == old(self).get_thread_ptrs().contains(_thread_ptr),
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != ret.0 ==> self.get_thread(_thread_ptr) =~= old(self).get_thread(_thread_ptr),
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != ret.0 ==> self.get_thread(_thread_ptr).state =~= old(self).get_thread(_thread_ptr).state,
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) ==> self.get_thread(_thread_ptr).ipc_payload =~= old(self).get_thread(_thread_ptr).ipc_payload,
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) ==> self.get_thread(_thread_ptr).endpoint_descriptors =~= old(self).get_thread(_thread_ptr).endpoint_descriptors,
            forall|_endpoint_ptr:EndpointPtr| #![auto] self.get_endpoint_ptrs().contains(_endpoint_ptr) ==> self.get_endpoint(_endpoint_ptr).rf_counter =~= old(self).get_endpoint(_endpoint_ptr).rf_counter,
            self.proc_ptrs =~= old(self).proc_ptrs,
            self.proc_perms =~= old(self).proc_perms,
            self.thread_ptrs =~= old(self).thread_ptrs,
            //self.thread_perms=@ =~= old(self).thread_perms@,
            self.scheduler =~= old(self).scheduler,
            self.endpoint_ptrs =~= old(self).endpoint_ptrs,
            //self.endpoint_perms =~= old(self).endpoint_perms,
            self.pcid_closure =~= old(self).pcid_closure,
            self.ioid_closure =~= old(self).ioid_closure,
            self.get_thread_ptrs().contains(ret.0),
            // self.get_thread(ret).parent =~= old(self).get_thread(ret).parent,
            // //self.get_thread(ret).state =~= old(self).get_thread(ret).state,
            // self.get_thread(ret).parent_rf =~= old(self).get_thread(ret).parent_rf,
            // self.get_thread(ret).scheduler_rf =~= old(self).get_thread(ret).scheduler_rf,
            // //self.get_thread(ret).endpoint_ptr =~= old(self).get_thread(ret).endpoint_ptr,
            // //self.get_thread(ret).endpoint_rf =~= old(self).get_thread(ret).endpoint_rf,
            // self.get_thread(ret).endpoint_descriptors =~= old(self).get_thread(ret).endpoint_descriptors,
            // self.get_thread(ret).ipc_payload =~= old(self).get_thread(ret).ipc_payload,
            // self.get_thread(ret).error_code =~= old(self).get_thread(ret).error_code,
            old(self).get_thread(ret.0).state == BLOCKED,
            self.get_thread(ret.0).state == RUNNING,
            old(self).get_endpoint(self.get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int]).queue@[0] == ret.0,
    {
        assert(self.thread_perms@.dom().contains(thread_ptr));
        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
        let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));
        assert(thread.endpoint_descriptors.wf());
        let endpoint_ptr = *thread.endpoint_descriptors.get(endpoint_index);
        assert(self.get_endpoint_ptrs().contains(endpoint_ptr));

        let mut endpoint_perm =
        Tracked((self.endpoint_perms.borrow_mut()).tracked_remove(endpoint_ptr));
        assert(self.endpoint_perms@.dom().contains(endpoint_ptr) == false);
        let ret = endpoint_pop_thread(PPtr::<Endpoint>::from_usize(endpoint_ptr), &mut endpoint_perm);
        proof{
            assert(self.endpoint_perms@.dom().contains(endpoint_ptr) == false);
            (self.endpoint_perms.borrow_mut())
                .tracked_insert(endpoint_ptr, endpoint_perm.get());
        }

        assert(self.thread_perms@.dom().contains(ret));

        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(ret);
        assert(thread_perm@.pptr == ret);
        let thread : &Thread = PPtr::<Thread>::from_usize(ret).borrow(Tracked(thread_perm));
        assert(thread.trap_frame.is_Some());
        let ret_pt_regs = thread.trap_frame.unwrap();

        let mut ret_thread_perm =
            Tracked((self.thread_perms.borrow_mut()).tracked_remove(ret));
        assert(self.thread_perms@.dom().contains(ret) == false);
        assert(ret_thread_perm@@.pptr == ret);
        assert(ret_thread_perm@@.value.get_Some_0().state == BLOCKED);
        thread_set_endpoint_rf(&PPtr::<Thread>::from_usize(ret), &mut ret_thread_perm, None);
        thread_set_endpoint_ptr(&PPtr::<Thread>::from_usize(ret), &mut ret_thread_perm, None);
        thread_set_trap_frame(&PPtr::<Thread>::from_usize(ret), &mut ret_thread_perm, None);
        thread_set_state(&PPtr::<Thread>::from_usize(ret), &mut ret_thread_perm, RUNNING);
        proof{
            assert(self.thread_perms@.dom().contains(ret) == false);
            (self.thread_perms.borrow_mut())
                .tracked_insert(ret, ret_thread_perm.get());
        }

        assert(forall|thread_ptr: ThreadPtr| #![auto] self.get_thread_ptrs().contains(thread_ptr) ==>
            (self.get_thread(thread_ptr).state != RUNNING <==> self.get_thread(thread_ptr).trap_frame.is_Some())
        );
        assert(forall|thread_ptr: ThreadPtr| #![auto] self.get_thread_ptrs().contains(thread_ptr) ==>
            (self.get_thread(thread_ptr).error_code.is_Some() ==> self.get_thread(thread_ptr).state == SCHEDULED)
        );
        assert(self.wf_threads());
        assert(self.wf_procs());
        assert(self.wf_scheduler());
        assert(self.wf_mem_closure());
        assert(self.wf_pcid_closure());
        assert(self.wf());

        return (ret,ret_pt_regs);
    }

    pub fn push_endpoint_and_set_state(&mut self, thread_ptr: ThreadPtr, endpoint_index: EndpointIdx, endpoint_payload: IPCPayLoad, pt_regs: PtRegs, endpoint_queue_state: EndpointState)
        requires
            old(self).wf(),
            old(self).get_thread_ptrs().contains(thread_ptr),
            0<=endpoint_index<MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int] != 0,
            old(self).get_thread(thread_ptr).state == RUNNING,
            old(self).get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int]).len() < MAX_NUM_THREADS_PER_ENDPOINT,
        ensures
            self.wf(),
            self.get_thread_ptrs()=~= old(self).get_thread_ptrs(),
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != thread_ptr ==> self.get_thread(_thread_ptr) =~= old(self).get_thread(_thread_ptr),
            self.proc_ptrs =~= old(self).proc_ptrs,
            self.proc_perms =~= old(self).proc_perms,
            self.thread_ptrs =~= old(self).thread_ptrs,
            //self.thread_perms=@ =~= old(self).thread_perms@,
            self.scheduler =~= old(self).scheduler,
            self.endpoint_ptrs =~= old(self).endpoint_ptrs,
            //self.endpoint_perms =~= old(self).endpoint_perms,
            self.pcid_closure =~= old(self).pcid_closure,
            self.ioid_closure =~= old(self).ioid_closure,
            self.get_thread(thread_ptr).parent =~= old(self).get_thread(thread_ptr).parent,
            self.get_thread(thread_ptr).parent_rf =~= old(self).get_thread(thread_ptr).parent_rf,
            self.get_thread(thread_ptr).scheduler_rf =~= old(self).get_thread(thread_ptr).scheduler_rf,
            self.get_thread(thread_ptr).endpoint_descriptors =~= old(self).get_thread(thread_ptr).endpoint_descriptors,
            self.get_thread(thread_ptr).ipc_payload =~= endpoint_payload,
            self.get_thread(thread_ptr).endpoint_ptr == Some(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int]),
            self.get_thread(thread_ptr).state == BLOCKED,
    {
        assert(self.thread_perms@.dom().contains(thread_ptr));
        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
        let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));
        assert(thread.endpoint_descriptors.wf());
        let endpoint_ptr = *thread.endpoint_descriptors.get(endpoint_index);
        assert(self.get_endpoint_ptrs().contains(endpoint_ptr));

        let mut endpoint_perm =
        Tracked((self.endpoint_perms.borrow_mut()).tracked_remove(endpoint_ptr));
        assert(self.endpoint_perms@.dom().contains(endpoint_ptr) == false);
        let endpoint_rf = endpoint_push_thread(PPtr::<Endpoint>::from_usize(endpoint_ptr), &mut endpoint_perm, thread_ptr);
        endpoint_set_queue_state(PPtr::<Endpoint>::from_usize(endpoint_ptr), &mut endpoint_perm, endpoint_queue_state);
        proof{
            assert(self.endpoint_perms@.dom().contains(endpoint_ptr) == false);
            (self.endpoint_perms.borrow_mut())
                .tracked_insert(endpoint_ptr, endpoint_perm.get());
        }

        let mut thread_perm =
            Tracked((self.thread_perms.borrow_mut()).tracked_remove(thread_ptr));
        assert(self.thread_perms@.dom().contains(thread_ptr) == false);
        assert(thread_perm@@.pptr == thread_ptr);
        thread_set_endpoint_rf(&PPtr::<Thread>::from_usize(thread_ptr), &mut thread_perm, Some(endpoint_rf));
        thread_set_endpoint_ptr(&PPtr::<Thread>::from_usize(thread_ptr), &mut thread_perm, Some(endpoint_ptr));
        thread_set_state(&PPtr::<Thread>::from_usize(thread_ptr), &mut thread_perm, BLOCKED);
        thread_set_ipc_payload(&PPtr::<Thread>::from_usize(thread_ptr), &mut thread_perm, endpoint_payload);
        thread_set_trap_frame(&PPtr::<Thread>::from_usize(thread_ptr), &mut thread_perm, Some(pt_regs));
        proof{
            assert(self.thread_perms@.dom().contains(thread_ptr) == false);
            (self.thread_perms.borrow_mut())
                .tracked_insert(thread_ptr, thread_perm.get());
        }

        assert(self.wf_threads());
        assert(self.wf_procs());
        assert(self.wf_scheduler());
        assert(self.wf_mem_closure());
        assert(self.wf_pcid_closure());
        assert(self.wf_endpoints());
        assert(self.wf());
    }

    pub fn push_endpoint(&mut self, thread_ptr: ThreadPtr, endpoint_index: EndpointIdx, endpoint_payload: IPCPayLoad, pt_regs:PtRegs)
        requires
            old(self).wf(),
            old(self).get_thread_ptrs().contains(thread_ptr),
            0<=endpoint_index<MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int] != 0,
            old(self).get_thread(thread_ptr).state == RUNNING,
            old(self).get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int]).len() < MAX_NUM_THREADS_PER_ENDPOINT,
        ensures
            self.wf(),
            self.get_thread_ptrs()=~= old(self).get_thread_ptrs(),
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != thread_ptr ==> self.get_thread(_thread_ptr) =~= old(self).get_thread(_thread_ptr),
            self.proc_ptrs =~= old(self).proc_ptrs,
            self.proc_perms =~= old(self).proc_perms,
            self.thread_ptrs =~= old(self).thread_ptrs,
            //self.thread_perms=@ =~= old(self).thread_perms@,
            self.scheduler =~= old(self).scheduler,
            self.endpoint_ptrs =~= old(self).endpoint_ptrs,
            //self.endpoint_perms =~= old(self).endpoint_perms,
            self.pcid_closure =~= old(self).pcid_closure,
            self.ioid_closure =~= old(self).ioid_closure,
            self.get_thread(thread_ptr).parent =~= old(self).get_thread(thread_ptr).parent,
            self.get_thread(thread_ptr).parent_rf =~= old(self).get_thread(thread_ptr).parent_rf,
            self.get_thread(thread_ptr).scheduler_rf =~= old(self).get_thread(thread_ptr).scheduler_rf,
            self.get_thread(thread_ptr).endpoint_descriptors =~= old(self).get_thread(thread_ptr).endpoint_descriptors,
            self.get_thread(thread_ptr).ipc_payload =~= endpoint_payload,
            self.get_thread(thread_ptr).endpoint_ptr == Some(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int]),
            self.get_thread(thread_ptr).state == BLOCKED,
    {
        assert(self.thread_perms@.dom().contains(thread_ptr));
        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
        let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));
        assert(thread.endpoint_descriptors.wf());
        let endpoint_ptr = *thread.endpoint_descriptors.get(endpoint_index);
        assert(self.get_endpoint_ptrs().contains(endpoint_ptr));

        let mut endpoint_perm =
        Tracked((self.endpoint_perms.borrow_mut()).tracked_remove(endpoint_ptr));
        assert(self.endpoint_perms@.dom().contains(endpoint_ptr) == false);
        let endpoint_rf = endpoint_push_thread(PPtr::<Endpoint>::from_usize(endpoint_ptr), &mut endpoint_perm, thread_ptr);
        proof{
            assert(self.endpoint_perms@.dom().contains(endpoint_ptr) == false);
            (self.endpoint_perms.borrow_mut())
                .tracked_insert(endpoint_ptr, endpoint_perm.get());
        }

        let mut thread_perm =
            Tracked((self.thread_perms.borrow_mut()).tracked_remove(thread_ptr));
        assert(self.thread_perms@.dom().contains(thread_ptr) == false);
        assert(thread_perm@@.pptr == thread_ptr);
        thread_set_endpoint_rf(&PPtr::<Thread>::from_usize(thread_ptr), &mut thread_perm, Some(endpoint_rf));
        thread_set_endpoint_ptr(&PPtr::<Thread>::from_usize(thread_ptr), &mut thread_perm, Some(endpoint_ptr));
        thread_set_state(&PPtr::<Thread>::from_usize(thread_ptr), &mut thread_perm, BLOCKED);
        thread_set_ipc_payload(&PPtr::<Thread>::from_usize(thread_ptr), &mut thread_perm, endpoint_payload);
        thread_set_trap_frame(&PPtr::<Thread>::from_usize(thread_ptr), &mut thread_perm, Some(pt_regs));
        proof{
            assert(self.thread_perms@.dom().contains(thread_ptr) == false);
            (self.thread_perms.borrow_mut())
                .tracked_insert(thread_ptr, thread_perm.get());
        }

        assert(self.wf_threads());
        assert(self.wf_procs());
        assert(self.wf_scheduler());
        assert(self.wf_mem_closure());
        assert(self.wf_pcid_closure());
        assert(self.wf_endpoints());
        assert(self.wf());
    }

    pub fn check_receiver_endpoint_descriptors(&self, receiver_ptr: ThreadPtr, target_endpoint_ptr: EndpointPtr) -> (ret:bool)
        requires
            self.wf(),
            self.get_thread_ptrs().contains(receiver_ptr),
        ensures
            ret == (
                forall|i:int| #![auto] 0 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS ==> self.get_thread(receiver_ptr).endpoint_descriptors@[i as int] != target_endpoint_ptr
            )
        {
            let mut i = 0;
            while i != MAX_NUM_ENDPOINT_DESCRIPTORS
                invariant
                    self.wf(),
                    self.get_thread_ptrs().contains(receiver_ptr),
                    0<=i<=MAX_NUM_ENDPOINT_DESCRIPTORS,
                    forall|j:int| #![auto] 0 <= j < i ==> self.get_thread(receiver_ptr).endpoint_descriptors@[j as int] != target_endpoint_ptr,
                ensures
                    i==MAX_NUM_ENDPOINT_DESCRIPTORS,
                    forall|j:int| #![auto] 0 <= j < i ==> self.get_thread(receiver_ptr).endpoint_descriptors@[j as int] != target_endpoint_ptr,
            {
                if self.get_thread_endpoint_ptr_by_endpoint_idx(receiver_ptr, i) == target_endpoint_ptr
                {
                    return false;
                }
                i = i + 1;
            }
            return true;
        }

    pub fn pass_endpoint(&mut self, sender_ptr: ThreadPtr, sender_endpoint_index: EndpointIdx, receiver_ptr: ThreadPtr, receiver_endpoint_index: EndpointIdx,)
        requires
            old(self).wf(),
            old(self).get_thread_ptrs().contains(sender_ptr),
            old(self).get_thread_ptrs().contains(receiver_ptr),
            0<=sender_endpoint_index<MAX_NUM_ENDPOINT_DESCRIPTORS,
            0<=receiver_endpoint_index<MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(sender_ptr).endpoint_descriptors@[sender_endpoint_index as int] != 0,
            old(self).get_thread(receiver_ptr).endpoint_descriptors@[receiver_endpoint_index as int] == 0,
            forall|i:int| #![auto] 0 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS ==> old(self).get_thread(receiver_ptr).endpoint_descriptors@[i as int] != old(self).get_thread(sender_ptr).endpoint_descriptors@[sender_endpoint_index as int],
            old(self).get_endpoint(old(self).get_thread(sender_ptr).endpoint_descriptors@[sender_endpoint_index as int]).rf_counter != usize::MAX,
        ensures
            self.wf(),
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) == old(self).get_thread_ptrs().contains(_thread_ptr),
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) ==> old(self).get_proc(old(self).get_thread(_thread_ptr).parent).pcid == self.get_proc(self.get_thread(_thread_ptr).parent).pcid,
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != receiver_ptr ==> self.get_thread(_thread_ptr) =~= old(self).get_thread(_thread_ptr),
            forall|_endpoint_ptr:EndpointPtr| #![auto] self.get_endpoint_ptrs().contains(_endpoint_ptr) == old(self).get_endpoint_ptrs().contains(_endpoint_ptr),
            forall|_endpoint_ptr:EndpointPtr| #![auto] self.get_endpoint_ptrs().contains(_endpoint_ptr) && _endpoint_ptr != old(self).get_thread(sender_ptr).endpoint_descriptors@[sender_endpoint_index as int] ==>
                self.get_endpoint(_endpoint_ptr) =~= old(self).get_endpoint(_endpoint_ptr),
            self.get_proc_ptrs() =~= old(self).get_proc_ptrs(),
            self.get_thread_ptrs() =~= old(self).get_thread_ptrs(),
            self.get_pcid_closure() =~= old(self).get_pcid_closure(),
            self.get_ioid_closure() =~= old(self).get_ioid_closure(),
            self.get_proc_man_page_closure() =~= old(self).get_proc_man_page_closure(),
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) ==>  self.get_thread(_thread_ptr).state == old(self).get_thread(_thread_ptr).state,
            //self.thread_perms=@ =~= old(self).thread_perms@,
            self.scheduler =~= old(self).scheduler,
            self.endpoint_ptrs =~= old(self).endpoint_ptrs,
            //self.endpoint_perms =~= old(self).endpoint_perms,
            self.get_thread(receiver_ptr).parent =~= old(self).get_thread(receiver_ptr).parent,
            self.get_thread(receiver_ptr).state =~= old(self).get_thread(receiver_ptr).state,
            self.get_thread(receiver_ptr).parent_rf =~= old(self).get_thread(receiver_ptr).parent_rf,
            self.get_thread(receiver_ptr).scheduler_rf =~= old(self).get_thread(receiver_ptr).scheduler_rf,
            self.get_thread(receiver_ptr).endpoint_ptr =~= old(self).get_thread(receiver_ptr).endpoint_ptr,
            self.get_thread(receiver_ptr).endpoint_rf =~= old(self).get_thread(receiver_ptr).endpoint_rf,
            self.get_thread(receiver_ptr).endpoint_descriptors@ =~= old(self).get_thread(receiver_ptr).endpoint_descriptors@.update(receiver_endpoint_index as int, old(self).get_thread(sender_ptr).endpoint_descriptors@[sender_endpoint_index as int]),
            self.get_thread(receiver_ptr).ipc_payload =~= old(self).get_thread(receiver_ptr).ipc_payload,
            self.get_thread(receiver_ptr).error_code =~= old(self).get_thread(receiver_ptr).error_code,
            self.get_endpoint(self.get_thread(sender_ptr).endpoint_descriptors@[sender_endpoint_index as int]).queue =~= old(self).get_endpoint(self.get_thread(sender_ptr).endpoint_descriptors@[sender_endpoint_index as int]).queue,
            self.get_endpoint(self.get_thread(sender_ptr).endpoint_descriptors@[sender_endpoint_index as int]).rf_counter as int =~= old(self).get_endpoint(self.get_thread(sender_ptr).endpoint_descriptors@[sender_endpoint_index as int]).rf_counter + 1,
            self.get_endpoint(self.get_thread(sender_ptr).endpoint_descriptors@[sender_endpoint_index as int]).queue_state =~= old(self).get_endpoint(self.get_thread(sender_ptr).endpoint_descriptors@[sender_endpoint_index as int]).queue_state,
            self.get_endpoint(self.get_thread(sender_ptr).endpoint_descriptors@[sender_endpoint_index as int]).owning_threads@ =~= old(self).get_endpoint(self.get_thread(sender_ptr).endpoint_descriptors@[sender_endpoint_index as int]).owning_threads@.insert(receiver_ptr),
    {
        assert(self.thread_perms@.dom().contains(sender_ptr));
        let tracked sender_thread_perm = self.thread_perms.borrow().tracked_borrow(sender_ptr);
        let sender_thread : &Thread = PPtr::<Thread>::from_usize(sender_ptr).borrow(Tracked(sender_thread_perm));
        assert(sender_thread.endpoint_descriptors.wf());
        let endpoint_ptr = *sender_thread.endpoint_descriptors.get(sender_endpoint_index);

        assert(self.get_endpoint_ptrs().contains(endpoint_ptr));

        let mut endpoint_perm =
        Tracked((self.endpoint_perms.borrow_mut()).tracked_remove(endpoint_ptr));
        assert(self.endpoint_perms@.dom().contains(endpoint_ptr) == false);
        endpoint_add_owning_thread(PPtr::<Endpoint>::from_usize(endpoint_ptr), &mut endpoint_perm, receiver_ptr);
        proof{
            assert(self.endpoint_perms@.dom().contains(endpoint_ptr) == false);
            (self.endpoint_perms.borrow_mut())
                .tracked_insert(endpoint_ptr, endpoint_perm.get());
        }

        let mut receiver_thread_perm =
            Tracked((self.thread_perms.borrow_mut()).tracked_remove(receiver_ptr));
        assert(self.thread_perms@.dom().contains(receiver_ptr) == false);
        assert(receiver_thread_perm@@.pptr == receiver_ptr);
        thread_set_endpoint_descriptors(&PPtr::<Thread>::from_usize(receiver_ptr), &mut receiver_thread_perm, receiver_endpoint_index, endpoint_ptr);
        assert(receiver_thread_perm@@.value.get_Some_0().endpoint_descriptors@[receiver_endpoint_index as int] == endpoint_ptr);
        assert(receiver_thread_perm@@.value.get_Some_0().endpoint_descriptors@.contains(endpoint_ptr));
        proof{
            assert(self.thread_perms@.dom().contains(receiver_ptr) == false);
            (self.thread_perms.borrow_mut())
                .tracked_insert(receiver_ptr, receiver_thread_perm.get());
        }

        assert(self.wf());
    }

    pub fn new_endpoint(&mut self, page_ptr: PagePtr, page_perm: Tracked<PagePerm>, parent_ptr:ThreadPtr, endpoint_index:EndpointIdx)
        requires
            old(self).wf(),
            old(self).get_thread_ptrs().contains(parent_ptr),
            old(self).get_proc_man_page_closure().contains(page_ptr) == false,
            page_ptr != 0,
            0<=endpoint_index<MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(parent_ptr).endpoint_descriptors@[endpoint_index as int] == 0,
            page_perm@@.pptr == page_ptr,
            page_perm@@.value.is_Some(),
        ensures
            self.wf(),
            self.get_proc_man_page_closure() =~= old(self).get_proc_man_page_closure().insert(page_ptr),
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) ==> self.get_thread(_thread_ptr).state =~= old(self).get_thread(_thread_ptr).state,
            self.proc_ptrs =~= old(self).proc_ptrs,
            self.proc_perms =~= old(self).proc_perms,
            self.thread_ptrs =~= old(self).thread_ptrs,
            //self.thread_perms=@ =~= old(self).thread_perms@,
            self.scheduler =~= old(self).scheduler,
            self.endpoint_ptrs@ =~= old(self).endpoint_ptrs@.insert(page_ptr),
            //self.endpoint_perms =~= old(self).endpoint_perms,
            self.pcid_closure =~= old(self).pcid_closure,
            self.ioid_closure =~= old(self).ioid_closure,
            self.get_endpoint_ptrs().len() == old(self).get_endpoint_ptrs().len() + 1,
            self.get_thread(parent_ptr).endpoint_descriptors@[endpoint_index as int] != 0,
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != parent_ptr ==> self.get_thread(_thread_ptr) =~= old(self).get_thread(_thread_ptr),
            forall|_proc_ptr:ProcPtr| #![auto] self.get_proc_ptrs().contains(_proc_ptr) ==> self.get_proc(_proc_ptr) =~= old(self).get_proc(_proc_ptr),
            forall|_endpoint_ptr:EndpointPtr| #![auto] old(self).endpoint_ptrs@.contains(_endpoint_ptr) ==> self.get_endpoint(_endpoint_ptr) =~= old(self).get_endpoint(_endpoint_ptr),
    {
        let (endpoint_pptr,mut endpoint_perm) = page_to_endpoint((PPtr::<[u8; PAGE_SZ]>::from_usize(page_ptr),page_perm));
        let endpoint_ptr = endpoint_pptr.to_usize();
        endpoint_add_owning_thread(endpoint_pptr, &mut endpoint_perm, parent_ptr);
        proof {
            (self.endpoint_perms.borrow_mut()).tracked_insert(endpoint_ptr,endpoint_perm.get());
            self.endpoint_ptrs@ = self.endpoint_ptrs@.insert(endpoint_ptr);
        }
        let mut thread_perm =
            Tracked((self.thread_perms.borrow_mut()).tracked_remove(parent_ptr));
        thread_set_endpoint_descriptors(&PPtr::<Thread>::from_usize(parent_ptr),  &mut thread_perm, endpoint_index, endpoint_ptr);
        proof {
            (self.thread_perms.borrow_mut()).tracked_insert(parent_ptr,thread_perm.get());
        }

        assert(self.wf_threads());
        assert(self.wf_procs());
        assert(self.wf_scheduler());
        assert(self.wf_mem_closure());
        assert(self.wf_pcid_closure());
        assert(self.wf_endpoints());
        assert(self.wf_ipc());
        assert(self.wf_ioid_closure());
    }
}
}

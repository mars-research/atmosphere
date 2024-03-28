use super::*;

use vstd::prelude::*;
verus! {

use crate::mars_staticlinkedlist::*;
// use crate::pagetable::*;
use crate::mars_array::*;
use crate::define::*;
use crate::trap::*;

use vstd::ptr::*;

// use crate::proc::*;


pub struct Thread{
    pub parent: ProcPtr,
    pub state: ThreadState,

    // pub parent_rf: NodeRef<ThreadPtr>,
    // pub scheduler_rf: Option<NodeRef<ThreadPtr>>,
    // pub endpoint_rf: Option<NodeRef<ThreadPtr>>,

    pub parent_rf: Index,
    pub scheduler_rf: Option<Index>,

    pub endpoint_ptr: Option<EndpointPtr>,
    pub endpoint_rf: Option<Index>,

    pub endpoint_descriptors: MarsArray<EndpointPtr,MAX_NUM_ENDPOINT_DESCRIPTORS>,
    pub ipc_payload: IPCPayLoad,

    pub error_code: Option<ErrorCodeType>, //this will only be set when it comes out of endpoint and goes to scheduler.

    pub callee: Option<ThreadPtr>,
    pub caller: Option<ThreadPtr>,

    pub trap_frame: RegistersOption,
}

impl Thread {
    pub open spec fn get_proc_man_page_closure(&self) -> Set<PagePtr>
    {
        Set::empty()
    }
}
#[derive(Clone, Copy, Debug)]
pub struct IPCPayLoad{
    pub calling: bool,
    pub message: Option<(VAddr,usize)>,
    pub page_payload: Option<(VAddr, usize)>,
    pub endpoint_payload: Option<EndpointIdx>,
    pub pci_payload: Option<(u8,u8,u8)>,
}
impl IPCPayLoad {
    pub fn new_to_none() -> (ret:Self)
        ensures
            ret.calling == false,
            ret.message.is_None(),
            ret.page_payload.is_None(),
            ret.endpoint_payload.is_None(),
            ret.pci_payload.is_None(),
    {
        Self{
            calling: false,
            message: None,
            page_payload: None,
            endpoint_payload: None,
            pci_payload: None,
        }
    }
}
impl ProcessManager {

    pub fn weak_up_caller_change_queue_state_and_receive(&mut self, caller:ThreadPtr, callee:ThreadPtr, callee_pt_regs: &mut Registers, callee_ipc_payload: IPCPayLoad, endpoint_index:EndpointIdx) -> (ret: Registers)
        requires
            old(self).wf(),
            old(self).get_thread_ptrs().contains(caller),
            old(self).get_thread_ptrs().contains(callee),
            old(self).get_thread(callee).state == RUNNING,
            old(self).get_thread(callee).caller == Some(caller),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(callee).endpoint_descriptors@[endpoint_index as int] != 0,
            old(self).get_endpoint(old(self).get_thread(callee).endpoint_descriptors@[endpoint_index as int]).len() == 0,
            old(self).get_endpoint(old(self).get_thread(callee).endpoint_descriptors@[endpoint_index as int]).queue_state == SEND,
        ensures
            self.wf(),
            self.get_proc_ptrs() =~= old(self).get_proc_ptrs(),
            self.get_thread_ptrs() =~= old(self).get_thread_ptrs(),
            self.get_endpoint_ptrs() =~= old(self).get_endpoint_ptrs(),
            self.pcid_closure =~= old(self).pcid_closure,
            self.ioid_closure =~= old(self).ioid_closure,
            // forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) ==> self.get_thread(_thread_ptr).endpoint_descriptors =~= old(self).get_thread(_thread_ptr).endpoint_descriptors,
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != caller && _thread_ptr != callee ==> self.get_thread(_thread_ptr).state =~= old(self).get_thread(_thread_ptr).state,
            self.get_thread(caller).state == RUNNING,
            self.get_thread(callee).state == BLOCKED,

    {
        assert(self.get_thread(caller).callee =~= Some(callee));
        assert(self.get_thread(caller).state =~= CALLING);

        let caller_pt_regs = self.get_pt_regs_by_thread_ptr(caller);

        let caller_pptr = PPtr::<Thread>::from_usize(caller);
        let mut caller_perm =
            Tracked((self.thread_perms.borrow_mut()).tracked_remove(caller));
        thread_set_state(&caller_pptr, &mut caller_perm, RUNNING);
        thread_set_callee(&caller_pptr, &mut caller_perm, None);
        thread_empty_trap_frame(&caller_pptr, &mut caller_perm);
        thread_set_error_code(&caller_pptr, &mut caller_perm, None);
        proof{
            assert(self.thread_perms@.dom().contains(caller) == false);
            (self.thread_perms.borrow_mut())
                .tracked_insert(caller, caller_perm.get());
        }

        assert(self.thread_perms@.dom().contains(callee));
        let tracked callee_perm = self.thread_perms.borrow().tracked_borrow(callee);
        let callee_thread : &Thread = PPtr::<Thread>::from_usize(callee).borrow(Tracked(callee_perm));
        assert(callee_thread.endpoint_descriptors.wf());
        let endpoint_ptr = *callee_thread.endpoint_descriptors.get(endpoint_index);
        assert(self.get_endpoint_ptrs().contains(endpoint_ptr));

        let mut endpoint_perm =
        Tracked((self.endpoint_perms.borrow_mut()).tracked_remove(endpoint_ptr));
        assert(self.endpoint_perms@.dom().contains(endpoint_ptr) == false);
        endpoint_set_queue_state(PPtr::<Endpoint>::from_usize(endpoint_ptr), &mut endpoint_perm, RECEIVE);
        let endpoint_rf = endpoint_push_thread(PPtr::<Endpoint>::from_usize(endpoint_ptr), &mut endpoint_perm, callee);
        proof{
            assert(self.endpoint_perms@.dom().contains(endpoint_ptr) == false);
            (self.endpoint_perms.borrow_mut())
                .tracked_insert(endpoint_ptr, endpoint_perm.get());
        }

        let mut callee_perm =
            Tracked((self.thread_perms.borrow_mut()).tracked_remove(callee));
        assert(self.thread_perms@.dom().contains(callee) == false);
        assert(callee_perm@@.pptr == callee);
        thread_set_endpoint_rf(&PPtr::<Thread>::from_usize(callee), &mut callee_perm, Some(endpoint_rf));
        thread_set_endpoint_ptr(&PPtr::<Thread>::from_usize(callee), &mut callee_perm, Some(endpoint_ptr));
        thread_set_state(&PPtr::<Thread>::from_usize(callee), &mut callee_perm, BLOCKED);
        thread_set_caller(&PPtr::<Thread>::from_usize(callee), &mut callee_perm, None);
        thread_set_ipc_payload(&PPtr::<Thread>::from_usize(callee), &mut callee_perm, callee_ipc_payload);
        thread_set_trap_frame(&PPtr::<Thread>::from_usize(callee), &mut callee_perm, callee_pt_regs);
        thread_set_error_code(&PPtr::<Thread>::from_usize(callee), &mut callee_perm, None);
        proof{
            assert(self.thread_perms@.dom().contains(callee) == false);
            (self.thread_perms.borrow_mut())
                .tracked_insert(callee, callee_perm.get());
        }

        *callee_pt_regs = caller_pt_regs.unwrap();
        // let callee_pptr = PPtr::<Thread>::from_usize(callee);
        // let mut callee_perm =
        //     Tracked((self.thread_perms.borrow_mut()).tracked_remove(callee));
        // thread_set_state(&callee_pptr, &mut callee_perm, BLOCKED);
        // thread_set_caller(&callee_pptr, &mut callee_perm, None);
        // thread_set_trap_frame(&callee_pptr, &mut callee_perm, callee_pt_regs);
        // thread_set_error_code(&callee_pptr, &mut callee_perm, None);
        // proof{
        //     assert(self.thread_perms@.dom().contains(callee) == false);
        //     (self.thread_perms.borrow_mut())
        //         .tracked_insert(callee, callee_perm.get());
        // }

        // assert(self.wf_threads());
        // assert(self.wf_procs());
        // assert(self.wf_scheduler());
        // assert(self.wf_mem_closure());
        // assert(self.wf_pcid_closure());
        // assert(self.wf_endpoints());
        // assert(self.wf_ipc());
        // assert(self.wf_ioid_closure());

        assert(self.wf());
        return caller_pt_regs.unwrap();
    }

    pub fn weak_up_caller_and_receive(&mut self, caller:ThreadPtr, callee:ThreadPtr, callee_pt_regs: &mut Registers, callee_ipc_payload: IPCPayLoad, endpoint_index:EndpointIdx) -> (ret: Registers)
        requires
            old(self).wf(),
            old(self).get_thread_ptrs().contains(caller),
            old(self).get_thread_ptrs().contains(callee),
            old(self).get_thread(callee).state == RUNNING,
            old(self).get_thread(callee).caller == Some(caller),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(callee).endpoint_descriptors@[endpoint_index as int] != 0,
            old(self).get_endpoint(old(self).get_thread(callee).endpoint_descriptors@[endpoint_index as int]).len() != MAX_NUM_THREADS_PER_ENDPOINT,
            old(self).get_endpoint(old(self).get_thread(callee).endpoint_descriptors@[endpoint_index as int]).queue_state == RECEIVE,
        ensures
            self.wf(),
            self.get_proc_ptrs() =~= old(self).get_proc_ptrs(),
            self.get_thread_ptrs() =~= old(self).get_thread_ptrs(),
            self.get_endpoint_ptrs() =~= old(self).get_endpoint_ptrs(),
            self.pcid_closure =~= old(self).pcid_closure,
            self.ioid_closure =~= old(self).ioid_closure,
            // forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) ==> self.get_thread(_thread_ptr).endpoint_descriptors =~= old(self).get_thread(_thread_ptr).endpoint_descriptors,
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != caller && _thread_ptr != callee ==> self.get_thread(_thread_ptr).state =~= old(self).get_thread(_thread_ptr).state,
            self.get_thread(caller).state == RUNNING,
            self.get_thread(callee).state == BLOCKED,

    {
        assert(self.get_thread(caller).callee =~= Some(callee));
        assert(self.get_thread(caller).state =~= CALLING);

        let caller_pt_regs = self.get_pt_regs_by_thread_ptr(caller);

        let caller_pptr = PPtr::<Thread>::from_usize(caller);
        let mut caller_perm =
            Tracked((self.thread_perms.borrow_mut()).tracked_remove(caller));
        thread_set_state(&caller_pptr, &mut caller_perm, RUNNING);
        thread_set_callee(&caller_pptr, &mut caller_perm, None);
        thread_empty_trap_frame(&caller_pptr, &mut caller_perm);
        thread_set_error_code(&caller_pptr, &mut caller_perm, None);
        proof{
            assert(self.thread_perms@.dom().contains(caller) == false);
            (self.thread_perms.borrow_mut())
                .tracked_insert(caller, caller_perm.get());
        }

        assert(self.thread_perms@.dom().contains(callee));
        let tracked callee_perm = self.thread_perms.borrow().tracked_borrow(callee);
        let callee_thread : &Thread = PPtr::<Thread>::from_usize(callee).borrow(Tracked(callee_perm));
        assert(callee_thread.endpoint_descriptors.wf());
        let endpoint_ptr = *callee_thread.endpoint_descriptors.get(endpoint_index);
        assert(self.get_endpoint_ptrs().contains(endpoint_ptr));

        let mut endpoint_perm =
        Tracked((self.endpoint_perms.borrow_mut()).tracked_remove(endpoint_ptr));
        assert(self.endpoint_perms@.dom().contains(endpoint_ptr) == false);
        let endpoint_rf = endpoint_push_thread(PPtr::<Endpoint>::from_usize(endpoint_ptr), &mut endpoint_perm, callee);
        proof{
            assert(self.endpoint_perms@.dom().contains(endpoint_ptr) == false);
            (self.endpoint_perms.borrow_mut())
                .tracked_insert(endpoint_ptr, endpoint_perm.get());
        }

        let mut callee_perm =
            Tracked((self.thread_perms.borrow_mut()).tracked_remove(callee));
        assert(self.thread_perms@.dom().contains(callee) == false);
        assert(callee_perm@@.pptr == callee);
        thread_set_endpoint_rf(&PPtr::<Thread>::from_usize(callee), &mut callee_perm, Some(endpoint_rf));
        thread_set_endpoint_ptr(&PPtr::<Thread>::from_usize(callee), &mut callee_perm, Some(endpoint_ptr));
        thread_set_state(&PPtr::<Thread>::from_usize(callee), &mut callee_perm, BLOCKED);
        thread_set_caller(&PPtr::<Thread>::from_usize(callee), &mut callee_perm, None);
        thread_set_ipc_payload(&PPtr::<Thread>::from_usize(callee), &mut callee_perm, callee_ipc_payload);
        thread_set_trap_frame(&PPtr::<Thread>::from_usize(callee), &mut callee_perm, callee_pt_regs);
        thread_set_error_code(&PPtr::<Thread>::from_usize(callee), &mut callee_perm, None);
        proof{
            assert(self.thread_perms@.dom().contains(callee) == false);
            (self.thread_perms.borrow_mut())
                .tracked_insert(callee, callee_perm.get());
        }
        *callee_pt_regs = caller_pt_regs.unwrap();
        // let callee_pptr = PPtr::<Thread>::from_usize(callee);
        // let mut callee_perm =
        //     Tracked((self.thread_perms.borrow_mut()).tracked_remove(callee));
        // thread_set_state(&callee_pptr, &mut callee_perm, BLOCKED);
        // thread_set_caller(&callee_pptr, &mut callee_perm, None);
        // thread_set_trap_frame(&callee_pptr, &mut callee_perm, callee_pt_regs);
        // thread_set_error_code(&callee_pptr, &mut callee_perm, None);
        // proof{
        //     assert(self.thread_perms@.dom().contains(callee) == false);
        //     (self.thread_perms.borrow_mut())
        //         .tracked_insert(callee, callee_perm.get());
        // }

        // assert(self.wf_threads());
        // assert(self.wf_procs());
        // assert(self.wf_scheduler());
        // assert(self.wf_mem_closure());
        // assert(self.wf_pcid_closure());
        // assert(self.wf_endpoints());
        // assert(self.wf_ipc());
        // assert(self.wf_ioid_closure());

        assert(self.wf());
        return caller_pt_regs.unwrap();
    }

    pub fn weak_up_caller_and_schedule(&mut self, caller:ThreadPtr, callee:ThreadPtr, callee_pt_regs: &mut Registers, callee_error_code: Option<ErrorCodeType>)
        requires
            old(self).wf(),
            old(self).get_thread_ptrs().contains(caller),
            old(self).get_thread_ptrs().contains(callee),
            old(self).get_thread(callee).state == RUNNING,
            old(self).get_thread(callee).caller == Some(caller),
            old(self).scheduler.len() != MAX_NUM_THREADS,
        ensures
            self.wf(),
            self.get_proc_ptrs() =~= old(self).get_proc_ptrs(),
            self.get_thread_ptrs() =~= old(self).get_thread_ptrs(),
            self.get_endpoint_ptrs() =~= old(self).get_endpoint_ptrs(),
            self.pcid_closure =~= old(self).pcid_closure,
            self.ioid_closure =~= old(self).ioid_closure,
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) ==> self.get_thread(_thread_ptr).endpoint_descriptors =~= old(self).get_thread(_thread_ptr).endpoint_descriptors,
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != caller && _thread_ptr != callee ==> self.get_thread(_thread_ptr).state =~= old(self).get_thread(_thread_ptr).state,
            self.get_thread(caller).state == RUNNING,
            self.get_thread(callee).state == SCHEDULED,

    {
        assert(self.get_thread(caller).callee =~= Some(callee));
        assert(self.get_thread(caller).state =~= CALLING);

        let caller_pt_regs = self.get_pt_regs_by_thread_ptr(caller);

        let caller_pptr = PPtr::<Thread>::from_usize(caller);
        let mut caller_perm =
            Tracked((self.thread_perms.borrow_mut()).tracked_remove(caller));
        thread_set_state(&caller_pptr, &mut caller_perm, RUNNING);
        thread_set_callee(&caller_pptr, &mut caller_perm, None);
        thread_empty_trap_frame(&caller_pptr, &mut caller_perm);
        thread_set_error_code(&caller_pptr, &mut caller_perm, None);
        proof{
            assert(self.thread_perms@.dom().contains(caller) == false);
            (self.thread_perms.borrow_mut())
                .tracked_insert(caller, caller_perm.get());
        }

        let callee_pptr = PPtr::<Thread>::from_usize(callee);
        let mut callee_perm =
            Tracked((self.thread_perms.borrow_mut()).tracked_remove(callee));
        thread_set_caller(&callee_pptr, &mut callee_perm, None);
        thread_empty_trap_frame(&callee_pptr, &mut callee_perm);
        thread_set_error_code(&callee_pptr, &mut callee_perm, None);
        proof{
            assert(self.thread_perms@.dom().contains(callee) == false);
            (self.thread_perms.borrow_mut())
                .tracked_insert(callee, callee_perm.get());
        }

        self.push_scheduler(callee,callee_error_code,callee_pt_regs);
        assert(self.wf());
        *callee_pt_regs = caller_pt_regs.unwrap();

    }

    pub fn set_thread_caller(&mut self, caller:ThreadPtr, callee:ThreadPtr, caller_trap_frame: &Registers)
        requires
            old(self).wf(),
            old(self).get_thread_ptrs().contains(caller),
            old(self).get_thread_ptrs().contains(callee),
            old(self).get_thread(caller).state == RUNNING,
            old(self).get_thread(callee).state == RUNNING,
            old(self).get_thread(callee).caller.is_None(),
        ensures
            self.wf(),
            self.get_proc_ptrs() =~= old(self).get_proc_ptrs(),
            self.get_thread_ptrs() =~= old(self).get_thread_ptrs(),
            self.get_endpoint_ptrs() =~= old(self).get_endpoint_ptrs(),
            self.scheduler =~= old(self).scheduler,
            self.pcid_closure =~= old(self).pcid_closure,
            self.ioid_closure =~= old(self).ioid_closure,
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) ==> self.get_thread(_thread_ptr).endpoint_descriptors =~= old(self).get_thread(_thread_ptr).endpoint_descriptors,
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != caller ==> self.get_thread(_thread_ptr).state =~= old(self).get_thread(_thread_ptr).state,
            self.get_thread(caller).state == CALLING,
    {
        let caller_pptr = PPtr::<Thread>::from_usize(caller);
        let mut caller_perm =
            Tracked((self.thread_perms.borrow_mut()).tracked_remove(caller));
        thread_set_state(&caller_pptr, &mut caller_perm, CALLING);
        thread_set_callee(&caller_pptr, &mut caller_perm, Some(callee));
        thread_set_trap_frame(&caller_pptr, &mut caller_perm, caller_trap_frame);
        proof{
            assert(self.thread_perms@.dom().contains(caller) == false);
            (self.thread_perms.borrow_mut())
                .tracked_insert(caller, caller_perm.get());
        }

        let callee_pptr = PPtr::<Thread>::from_usize(callee);
        let mut callee_perm =
            Tracked((self.thread_perms.borrow_mut()).tracked_remove(callee));
        thread_set_caller(&callee_pptr, &mut callee_perm, Some(caller));
        proof{
            assert(self.thread_perms@.dom().contains(callee) == false);
            (self.thread_perms.borrow_mut())
                .tracked_insert(callee, callee_perm.get());
        }
        assert(self.wf());
    }

    // pub fn set_thread_to_transit(&mut self, thread_ptr:ThreadPtr)
    //     requires
    //         old(self).wf(),
    //         old(self).get_thread_ptrs().contains(thread_ptr),
    //         old(self).get_thread(thread_ptr).state != BLOCKED,
    //         old(self).get_thread(thread_ptr).state != SCHEDULED,
    //         old(self).get_thread(thread_ptr).state != CALLING,
    //     ensures
    //         self.wf(),
    //         forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) == old(self).get_thread_ptrs().contains(_thread_ptr),
    //         forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != thread_ptr ==> self.get_thread(_thread_ptr) =~= old(self).get_thread(_thread_ptr),
    //         self.proc_ptrs =~= old(self).proc_ptrs,
    //         self.proc_perms =~= old(self).proc_perms,
    //         self.thread_ptrs =~= old(self).thread_ptrs,
    //         //self.thread_perms=@ =~= old(self).thread_perms@,
    //         self.scheduler =~= old(self).scheduler,
    //         self.endpoint_ptrs =~= old(self).endpoint_ptrs,
    //         self.endpoint_perms =~= old(self).endpoint_perms,
    //         self.pcid_closure =~= old(self).pcid_closure,
    //         self.ioid_closure =~= old(self).ioid_closure,
    //         self.get_thread(thread_ptr).parent =~= old(self).get_thread(thread_ptr).parent,
    //         //self.get_thread(thread_ptr).state =~= old(self).get_thread(thread_ptr).state,
    //         self.get_thread(thread_ptr).parent_rf =~= old(self).get_thread(thread_ptr).parent_rf,
    //         self.get_thread(thread_ptr).scheduler_rf =~= old(self).get_thread(thread_ptr).scheduler_rf,
    //         self.get_thread(thread_ptr).endpoint_ptr =~= old(self).get_thread(thread_ptr).endpoint_ptr,
    //         self.get_thread(thread_ptr).endpoint_rf =~= old(self).get_thread(thread_ptr).endpoint_rf,
    //         self.get_thread(thread_ptr).endpoint_descriptors =~= old(self).get_thread(thread_ptr).endpoint_descriptors,
    //         self.get_thread(thread_ptr).ipc_payload =~= old(self).get_thread(thread_ptr).ipc_payload,
    //         self.get_thread(thread_ptr).error_code =~= old(self).get_thread(thread_ptr).error_code,
    //         self.get_thread(thread_ptr).state == TRANSIT,
    // {
    //     let thread_pptr = PPtr::<Thread>::from_usize(thread_ptr);
    //     let mut thread_perm =
    //         Tracked((self.thread_perms.borrow_mut()).tracked_remove(thread_ptr));
    //     thread_set_state(&thread_pptr, &mut thread_perm, TRANSIT);
    //     proof{
    //         assert(self.thread_perms@.dom().contains(thread_ptr) == false);
    //         (self.thread_perms.borrow_mut())
    //             .tracked_insert(thread_ptr, thread_perm.get());
    //     }
    //     assert(forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr)
    //         ==>  self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().queue@.contains(thread_ptr) == false);
    //     assert(self.wf_threads());
    //     assert(self.wf_procs());
    //     assert(self.wf_scheduler());
    //     assert(self.wf_mem_closure());
    //     assert(self.wf_pcid_closure());
    // }

//     pub fn set_thread_to_running(&mut self, thread_ptr:ThreadPtr)
//     requires
//         old(self).wf(),
//         old(self).get_thread_ptrs().contains(thread_ptr),
//         old(self).get_thread(thread_ptr).state == TRANSIT,
//         //old(self).scheduler@.contains(thread_ptr) == false,
//     ensures
//         self.wf(),
//         forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) == old(self).get_thread_ptrs().contains(_thread_ptr),
//         forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != thread_ptr ==> self.get_thread(_thread_ptr) =~= old(self).get_thread(_thread_ptr),
//         forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != thread_ptr ==> self.get_thread(_thread_ptr).state =~= old(self).get_thread(_thread_ptr).state,
//         self.proc_ptrs =~= old(self).proc_ptrs,
//         self.proc_perms =~= old(self).proc_perms,
//         self.thread_ptrs =~= old(self).thread_ptrs,
//         //self.thread_perms=@ =~= old(self).thread_perms@,
//         self.scheduler =~= old(self).scheduler,
//         self.endpoint_ptrs =~= old(self).endpoint_ptrs,
//         self.endpoint_perms =~= old(self).endpoint_perms,
//         self.pcid_closure =~= old(self).pcid_closure,
//         self.ioid_closure =~= old(self).ioid_closure,
//         self.get_thread(thread_ptr).parent =~= old(self).get_thread(thread_ptr).parent,
//         //self.get_thread(thread_ptr).state =~= old(self).get_thread(thread_ptr).state,
//         self.get_thread(thread_ptr).parent_rf =~= old(self).get_thread(thread_ptr).parent_rf,
//         self.get_thread(thread_ptr).scheduler_rf =~= old(self).get_thread(thread_ptr).scheduler_rf,
//         self.get_thread(thread_ptr).endpoint_ptr =~= old(self).get_thread(thread_ptr).endpoint_ptr,
//         self.get_thread(thread_ptr).endpoint_rf =~= old(self).get_thread(thread_ptr).endpoint_rf,
//         self.get_thread(thread_ptr).endpoint_descriptors =~= old(self).get_thread(thread_ptr).endpoint_descriptors,
//         self.get_thread(thread_ptr).ipc_payload =~= old(self).get_thread(thread_ptr).ipc_payload,
//         self.get_thread(thread_ptr).error_code =~= old(self).get_thread(thread_ptr).error_code,
//         self.get_thread(thread_ptr).state == RUNNING,
// {
//     assert(self.scheduler@.contains(thread_ptr) == false);
//     let thread_pptr = PPtr::<Thread>::from_usize(thread_ptr);
//     let mut thread_perm =
//         Tracked((self.thread_perms.borrow_mut()).tracked_remove(thread_ptr));
//     thread_set_state(&thread_pptr, &mut thread_perm, RUNNING);
//     proof{
//         assert(self.thread_perms@.dom().contains(thread_ptr) == false);
//         (self.thread_perms.borrow_mut())
//             .tracked_insert(thread_ptr, thread_perm.get());
//     }
//     assert(forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr)
//         ==>  self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().queue@.contains(thread_ptr) == false);
//     assert(self.wf_threads());
//     assert(self.wf_procs());
//     assert(self.wf_scheduler());
//     assert(self.wf_mem_closure());
//     assert(self.wf_pcid_closure());
// }

// pub fn set_thread_error_code(&mut self, thread_ptr:ThreadPtr, error_code:Option<ErrorCodeType>)
//     requires
//         old(self).wf(),
//         old(self).get_thread_ptrs().contains(thread_ptr),
//     ensures
//         self.wf(),
//         forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) == old(self).get_thread_ptrs().contains(_thread_ptr),
//         forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != thread_ptr ==> self.get_thread(_thread_ptr) =~= old(self).get_thread(_thread_ptr),
//         self.proc_ptrs =~= old(self).proc_ptrs,
//         self.proc_perms =~= old(self).proc_perms,
//         self.thread_ptrs =~= old(self).thread_ptrs,
//         //self.thread_perms=@ =~= old(self).thread_perms@,
//         self.scheduler =~= old(self).scheduler,
//         self.endpoint_ptrs =~= old(self).endpoint_ptrs,
//         self.endpoint_perms =~= old(self).endpoint_perms,
//         self.pcid_closure =~= old(self).pcid_closure,
//         self.get_thread(thread_ptr).parent =~= old(self).get_thread(thread_ptr).parent,
//         self.get_thread(thread_ptr).state =~= old(self).get_thread(thread_ptr).state,
//         self.get_thread(thread_ptr).parent_rf =~= old(self).get_thread(thread_ptr).parent_rf,
//         self.get_thread(thread_ptr).scheduler_rf =~= old(self).get_thread(thread_ptr).scheduler_rf,
//         self.get_thread(thread_ptr).endpoint_ptr =~= old(self).get_thread(thread_ptr).endpoint_ptr,
//         self.get_thread(thread_ptr).endpoint_rf =~= old(self).get_thread(thread_ptr).endpoint_rf,
//         self.get_thread(thread_ptr).endpoint_descriptors =~= old(self).get_thread(thread_ptr).endpoint_descriptors,
//         self.get_thread(thread_ptr).ipc_payload =~= old(self).get_thread(thread_ptr).ipc_payload,
//         //self.get_thread(thread_ptr).error_code =~= old(self).get_thread(thread_ptr).error_code,
//         self.get_thread(thread_ptr).error_code =~= error_code,
// {
//     let thread_pptr = PPtr::<Thread>::from_usize(thread_ptr);
//     let mut thread_perm =
//         Tracked((self.thread_perms.borrow_mut()).tracked_remove(thread_ptr));
//     thread_set_error_code(&thread_pptr, &mut thread_perm, error_code);
//     proof{
//         assert(self.thread_perms@.dom().contains(thread_ptr) == false);
//         (self.thread_perms.borrow_mut())
//             .tracked_insert(thread_ptr, thread_perm.get());
//     }
//     assert(self.wf_threads());
//     assert(self.wf_procs());
//     assert(self.wf_scheduler());
//     assert(self.wf_mem_closure());
//     assert(self.wf_pcid_closure());
// }

    pub fn new_thread_with_endpoint_ptr(&mut self, pt_regs:Registers, page_ptr: PagePtr, page_perm: Tracked<PagePerm>, parent_ptr:ProcPtr, endpoint_ptr:EndpointPtr) -> (ret: ThreadPtr)
    requires
        old(self).wf(),
        old(self).get_proc_ptrs().contains(parent_ptr),
        page_perm@@.pptr == page_ptr,
        page_perm@@.value.is_Some(),
        old(self).get_proc_man_page_closure().contains(page_ptr) == false,
        old(self).scheduler.len() < MAX_NUM_THREADS,
        old(self).proc_perms@[parent_ptr]@.value.get_Some_0().owned_threads.len()<MAX_NUM_THREADS_PER_PROC,
        old(self).get_endpoint_ptrs().contains(endpoint_ptr),
        old(self).get_endpoint(endpoint_ptr).rf_counter != usize::MAX,
    ensures
        page_ptr == ret,
        self.wf(),
        self.scheduler@ =~= old(self).scheduler@.push(ret),
        self.get_proc_ptrs() =~= old(self).get_proc_ptrs(),
        self.get_thread(ret).state == SCHEDULED,
        self.get_thread(ret).endpoint_descriptors@[0] == endpoint_ptr,
        self.get_thread_ptrs() =~= old(self).get_thread_ptrs().insert(ret),
        self.get_proc_man_page_closure() =~= old(self).get_proc_man_page_closure().insert(ret),
        forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != ret ==> self.get_thread(_thread_ptr) =~= old(self).get_thread(_thread_ptr),
        forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != ret ==> self.get_thread(_thread_ptr).state =~= old(self).get_thread(_thread_ptr).state,
        forall|_endpoint_ptr:EndpointPtr|#![auto] _endpoint_ptr != endpoint_ptr && self.get_endpoint_ptrs().contains(_endpoint_ptr) ==> self.get_endpoint(_endpoint_ptr) =~= old(self).get_endpoint(_endpoint_ptr),
        self.get_ioid_closure() =~= old(self).get_ioid_closure(),
        self.get_pcid_closure() =~= old(self).get_pcid_closure(),
        forall|endpoint_index:EndpointIdx|#![auto] 1<=endpoint_index<MAX_NUM_ENDPOINT_DESCRIPTORS ==> self.get_thread(ret).endpoint_descriptors[endpoint_index as int] == 0,
        self.get_proc(self.get_thread(ret).parent).pcid == old(self).get_proc(parent_ptr).pcid,

        forall|proc_ptr:ProcPtr|#![auto] old(self).get_proc_ptrs().contains(proc_ptr) && proc_ptr != parent_ptr ==> self.get_proc(proc_ptr) =~= old(self).get_proc(proc_ptr),
        forall|thread_ptr:ThreadPtr|#![auto] old(self).get_thread_ptrs().contains(thread_ptr) ==> self.get_thread(thread_ptr) =~= old(self).get_thread(thread_ptr),
        forall|_endpoint_ptr:EndpointPtr|#![auto] old(self).get_endpoint_ptrs().contains(_endpoint_ptr) && _endpoint_ptr != endpoint_ptr ==> self.get_endpoint(_endpoint_ptr) =~= old(self).get_endpoint(_endpoint_ptr),
    {

    assert(self.thread_ptrs@.contains(page_ptr) == false);
    assert(forall|_proc_ptr: usize| #![auto] self.proc_perms@.dom().contains(_proc_ptr) ==> self.proc_perms@[_proc_ptr]@.value.get_Some_0().owned_threads@.contains(page_ptr) == false);

    let (thread_pptr,mut thread_perm) = page_to_thread((PPtr::<[u8; PAGE_SZ]>::from_usize(page_ptr),page_perm));
    thread_set_state(&thread_pptr, &mut thread_perm, SCHEDULED);
    let scheduler_rf = self.scheduler.push(page_ptr);
    thread_set_scheduler_rf(&thread_pptr, &mut thread_perm, Some(scheduler_rf));
    thread_set_parent(&thread_pptr, &mut thread_perm,parent_ptr);

    assert(self.proc_perms@.dom().contains(parent_ptr));
    let mut proc_perm =
        Tracked((self.proc_perms.borrow_mut()).tracked_remove(parent_ptr));

    let parent_rf = proc_push_thread(PPtr::<Process>::from_usize(parent_ptr), &mut proc_perm, page_ptr);
    assert(self.proc_perms@.dom().contains(parent_ptr) == false);
    proof{
        (self.proc_perms.borrow_mut())
            .tracked_insert(parent_ptr, proc_perm.get());
    }
    thread_set_parent_rf(&thread_pptr, &mut thread_perm,parent_rf);
    thread_set_trap_frame(&thread_pptr, &mut thread_perm,&pt_regs);
    thread_set_error_code(&thread_pptr, &mut thread_perm,Some(NEW_THREAD));
    thread_set_endpoint_descriptors(&thread_pptr, &mut thread_perm,0,endpoint_ptr);
    assert(self.thread_perms@.dom().contains(parent_ptr) == false);
    proof{
        (self.thread_perms.borrow_mut())
            .tracked_insert(page_ptr, thread_perm.get());
    }
    proof{
        self.thread_ptrs@ = self.thread_ptrs@.insert(page_ptr);
    }
    assert(forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr)
        ==>  self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().queue@.contains(page_ptr) == false);


    let mut endpoint_perm =
    Tracked((self.endpoint_perms.borrow_mut()).tracked_remove(endpoint_ptr));
    assert(self.endpoint_perms@.dom().contains(endpoint_ptr) == false);
    endpoint_add_owning_thread(PPtr::<Endpoint>::from_usize(endpoint_ptr), &mut endpoint_perm, page_ptr);
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
    assert(self.wf_endpoints());
    assert(self.wf_ipc());

    assert(self.wf());
    return page_ptr;
    }

    pub fn new_thread(&mut self, pt_regs:Registers, page_ptr: PagePtr, page_perm: Tracked<PagePerm>, parent_ptr:ProcPtr) -> (ret: ThreadPtr)
        requires
            old(self).wf(),
            old(self).get_proc_ptrs().contains(parent_ptr),
            page_perm@@.pptr == page_ptr,
            page_perm@@.value.is_Some(),
            old(self).get_proc_man_page_closure().contains(page_ptr) == false,
            old(self).scheduler.len() < MAX_NUM_THREADS,
            old(self).proc_perms@[parent_ptr]@.value.get_Some_0().owned_threads.len()<MAX_NUM_THREADS_PER_PROC,
        ensures
            page_ptr == ret,
            self.wf(),
            self.scheduler@ =~= old(self).scheduler@.push(ret),
            self.get_proc_ptrs() =~= old(self).get_proc_ptrs(),
            self.get_thread(ret).state == SCHEDULED,
            self.get_thread_ptrs() =~= old(self).get_thread_ptrs().insert(ret),
            self.get_proc_man_page_closure() =~= old(self).get_proc_man_page_closure().insert(ret),
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != ret ==> self.get_thread(_thread_ptr) =~= old(self).get_thread(_thread_ptr),
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != ret ==> self.get_thread(_thread_ptr).state =~= old(self).get_thread(_thread_ptr).state,
            forall|endpoint_ptr:EndpointPtr|#![auto] self.get_endpoint_ptrs().contains(endpoint_ptr) ==> self.get_endpoint(endpoint_ptr) =~= old(self).get_endpoint(endpoint_ptr),
            self.get_ioid_closure() =~= old(self).get_ioid_closure(),
            self.get_pcid_closure() =~= old(self).get_pcid_closure(),
            forall|endpoint_index:EndpointIdx|#![auto] 0<=endpoint_index<MAX_NUM_ENDPOINT_DESCRIPTORS ==> self.get_thread(ret).endpoint_descriptors[endpoint_index as int] == 0,
            self.get_proc(self.get_thread(ret).parent).pcid == old(self).get_proc(parent_ptr).pcid,
    {
        assert(self.thread_ptrs@.contains(page_ptr) == false);
        assert(forall|_proc_ptr: usize| #![auto] self.proc_perms@.dom().contains(_proc_ptr) ==> self.proc_perms@[_proc_ptr]@.value.get_Some_0().owned_threads@.contains(page_ptr) == false);

        let (thread_pptr,mut thread_perm) = page_to_thread((PPtr::<[u8; PAGE_SZ]>::from_usize(page_ptr),page_perm));
        thread_set_state(&thread_pptr, &mut thread_perm, SCHEDULED);
        let scheduler_rf = self.scheduler.push(page_ptr);
        thread_set_scheduler_rf(&thread_pptr, &mut thread_perm, Some(scheduler_rf));
        thread_set_parent(&thread_pptr, &mut thread_perm,parent_ptr);

        assert(self.proc_perms@.dom().contains(parent_ptr));
        let mut proc_perm =
            Tracked((self.proc_perms.borrow_mut()).tracked_remove(parent_ptr));

        let parent_rf = proc_push_thread(PPtr::<Process>::from_usize(parent_ptr), &mut proc_perm, page_ptr);
        assert(self.proc_perms@.dom().contains(parent_ptr) == false);
        proof{
            (self.proc_perms.borrow_mut())
                .tracked_insert(parent_ptr, proc_perm.get());
        }
        thread_set_parent_rf(&thread_pptr, &mut thread_perm,parent_rf);
        thread_set_trap_frame(&thread_pptr, &mut thread_perm,&pt_regs);
        thread_set_error_code(&thread_pptr, &mut thread_perm,None);
        assert(self.thread_perms@.dom().contains(parent_ptr) == false);
        proof{
            (self.thread_perms.borrow_mut())
                .tracked_insert(page_ptr, thread_perm.get());
        }
        proof{
            self.thread_ptrs@ = self.thread_ptrs@.insert(page_ptr);
        }
        assert(forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr)
            ==>  self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().queue@.contains(page_ptr) == false);


        assert(self.wf_threads());
        assert(self.wf_procs());
        assert(self.wf_scheduler());
        assert(self.wf_mem_closure());
        assert(self.wf_pcid_closure());
        assert(self.wf_endpoints());
        assert(self.wf_ipc());

        assert(self.wf());
        return page_ptr;
    }

    pub fn free_thread_from_endpoint(&mut self, thread_ptr:ThreadPtr)
        requires
            old(self).wf(),
            old(self).get_thread_ptrs().contains(thread_ptr),
            old(self).get_thread(thread_ptr).state == BLOCKED,
    {
        assert(self.thread_perms@.dom().contains(thread_ptr));
        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
        let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));
        let parent_ptr = thread.parent;
        assert(self.get_proc_ptrs().contains(parent_ptr));
        assert(self.proc_perms@.dom().contains(parent_ptr));
        assert(self.get_proc(parent_ptr).owned_threads.wf());
        assert(self.get_proc(parent_ptr).owned_threads@.contains(thread_ptr));

        assert(thread.endpoint_rf.is_Some());
        assert(thread.endpoint_ptr.is_Some());

        let endpoint_ptr = thread.endpoint_ptr.unwrap();
        let endpoint_rf = thread.endpoint_rf.unwrap();

        assert(thread.endpoint_descriptors@.contains(endpoint_ptr));
        assert(self.endpoint_perms@.dom().contains(endpoint_ptr));
        assert(self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().rf_counter != 0);
        let mut endpoint_perm =
            Tracked((self.endpoint_perms.borrow_mut()).tracked_remove(endpoint_ptr));
        assert(endpoint_perm@@.value.get_Some_0().queue@.contains(thread_ptr));
        endpoint_remove_thread(PPtr::<Endpoint>::from_usize(endpoint_ptr), &mut endpoint_perm, endpoint_rf);
        assert(self.endpoint_perms@.dom().contains(endpoint_ptr) == false);
        proof{
            (self.endpoint_perms.borrow_mut())
                .tracked_insert(endpoint_ptr, endpoint_perm.get());
        }


        let tracked endpoint_perm = self.endpoint_perms.borrow().tracked_borrow(endpoint_ptr);
        let endpoint : &Endpoint = PPtr::<Endpoint>::from_usize(endpoint_ptr).borrow(Tracked(endpoint_perm));

        let mut thread_perm =
            Tracked((self.thread_perms.borrow_mut()).tracked_remove(thread_ptr));
        assert(self.thread_perms@.dom().contains(thread_ptr) == false);
        thread_set_state(&PPtr::<Thread>::from_usize(thread_ptr), &mut thread_perm, TRANSIT);
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

    pub fn wake_up_to_caller(&mut self, thread_ptr: ThreadPtr)
        requires
            old(self).wf(),
            old(self).get_thread_ptrs().contains(thread_ptr),
            old(self).get_thread(thread_ptr).caller.is_Some(),
            old(self).get_thread(thread_ptr).state == TRANSIT,
    {
        assert(self.get_thread_ptrs().contains(self.get_thread(thread_ptr).caller.get_Some_0()));
        assert(self.get_thread(self.get_thread(thread_ptr).caller.get_Some_0()).state == CALLING);
        assert(self.get_thread(self.get_thread(thread_ptr).caller.get_Some_0()).callee.get_Some_0() == thread_ptr);

        let callee_thread_ptr = thread_ptr;

        let tracked callee_thread_perm = self.thread_perms.borrow().tracked_borrow(callee_thread_ptr);
        let callee_thread : &Thread = PPtr::<Thread>::from_usize(callee_thread_ptr).borrow(Tracked(callee_thread_perm));
        let caller_thread_ptr = callee_thread.caller.unwrap();

        let mut callee_thread_perm: Tracked<PointsTo<Thread>>=
            Tracked((self.thread_perms.borrow_mut()).tracked_remove(callee_thread_ptr));

        thread_set_caller(&PPtr::<Thread>::from_usize(callee_thread_ptr), &mut callee_thread_perm, None);
        proof{
            (self.thread_perms.borrow_mut())
                .tracked_insert(callee_thread_ptr, callee_thread_perm.get());
        }

        let mut caller_thread_perm: Tracked<PointsTo<Thread>>=
            Tracked((self.thread_perms.borrow_mut()).tracked_remove(caller_thread_ptr));

        thread_set_callee(&PPtr::<Thread>::from_usize(caller_thread_ptr), &mut caller_thread_perm, None);
        thread_set_state(&PPtr::<Thread>::from_usize(caller_thread_ptr), &mut caller_thread_perm, TRANSIT);
        proof{
            (self.thread_perms.borrow_mut())
                .tracked_insert(caller_thread_ptr, caller_thread_perm.get());
        }

        assert(self.wf_ipc());

        assert(self.wf());
    }

    pub fn remove_process_threads(&mut self, proc_ptr:ProcPtr) -> (ret: Ghost<Set<PagePtr>>)
    requires
        old(self).wf(),
        old(self).get_proc_ptrs().contains(proc_ptr),
        forall|i:int| #![auto] 0<=i< old(self).get_proc(proc_ptr).owned_threads.len() ==> old(self).thread_perms@[old(self).get_proc(proc_ptr).owned_threads@[i]]@.value.get_Some_0().state == TRANSIT,
        forall|i:int| #![auto] 0<=i< old(self).get_proc(proc_ptr).owned_threads.len() ==> old(self).thread_perms@[old(self).get_proc(proc_ptr).owned_threads@[i]]@.value.get_Some_0().callee.is_None(),
        forall|i:int| #![auto] 0<=i< old(self).get_proc(proc_ptr).owned_threads.len() ==> old(self).thread_perms@[old(self).get_proc(proc_ptr).owned_threads@[i]]@.value.get_Some_0().caller.is_None(),
    ensures
        ret@ + self.get_proc_man_page_closure() =~= old(self).get_proc_man_page_closure(),
        self.wf(),
    {
        let mut ret = Ghost(Set::<PagePtr>::empty());

        let original_len = self.get_proc_owned_thread_len(proc_ptr);

        let mut loop_i = 0;
        assert(self.proc_perms@.dom().contains(proc_ptr));
        assert(self.proc_perms@[proc_ptr]@.value.get_Some_0().owned_threads.wf());

        while loop_i != original_len
            invariant
                self.wf(),
                old(self).get_proc_ptrs().contains(proc_ptr),
                self.get_proc_ptrs().contains(proc_ptr),
                original_len == old(self).get_proc(proc_ptr).owned_threads.len(),
                self.get_proc(proc_ptr).owned_threads.len() == original_len - loop_i,
                0<=loop_i<=original_len,
                self.get_proc(proc_ptr).owned_threads.wf(),
                old(self).get_proc(proc_ptr).owned_threads.wf(),
                self.get_proc(proc_ptr).owned_threads@ =~= old(self).get_proc(proc_ptr).owned_threads@.subrange(loop_i as int, original_len as int),
                forall|i:int| #![auto] 0<=i< self.get_proc(proc_ptr).owned_threads.len() ==> self.thread_perms@[self.get_proc(proc_ptr).owned_threads@[i]]@.value.get_Some_0().state == TRANSIT,
                forall|i:int| #![auto] 0<=i< self.get_proc(proc_ptr).owned_threads.len() ==> self.thread_perms@[self.get_proc(proc_ptr).owned_threads@[i]]@.value.get_Some_0().callee.is_None(),
                forall|i:int| #![auto] 0<=i< self.get_proc(proc_ptr).owned_threads.len() ==> self.thread_perms@[self.get_proc(proc_ptr).owned_threads@[i]]@.value.get_Some_0().caller.is_None(),
                self.get_proc_man_page_closure().finite(),
                old(self).get_proc_man_page_closure().finite(),
                ret@.finite(),
                ret@.disjoint(self.get_proc_man_page_closure()),
                ret@ + self.get_proc_man_page_closure() =~= old(self).get_proc_man_page_closure(),
                self.get_proc_man_page_closure().subset_of(old(self).get_proc_man_page_closure()),
            ensures
                self.wf(),
                old(self).get_proc_ptrs().contains(proc_ptr),
                self.get_proc_ptrs().contains(proc_ptr),
                original_len == old(self).get_proc(proc_ptr).owned_threads.len(),
                loop_i==original_len,
                self.get_proc(proc_ptr).owned_threads.len() == 0,
                self.get_proc(proc_ptr).owned_threads.wf(),
                old(self).get_proc(proc_ptr).owned_threads.wf(),
                self.get_proc(proc_ptr).owned_threads@ =~= Seq::empty(),
                self.get_proc_man_page_closure().finite(),
                old(self).get_proc_man_page_closure().finite(),
                ret@.finite(),
                ret@.disjoint(self.get_proc_man_page_closure()),
                ret@ + self.get_proc_man_page_closure() =~= old(self).get_proc_man_page_closure(),
                self.get_proc_man_page_closure().subset_of(old(self).get_proc_man_page_closure()),

        {
            let thread_ptr = self.get_proc_owned_thread_head(proc_ptr);
            assert(self.get_thread_ptrs().contains(thread_ptr));
            let differential = self.remove_thread_endpoint_descriptors(thread_ptr);
            ret = Ghost(ret@.union(differential@));

            assert(self.proc_perms@.dom().contains(proc_ptr));

            let mut proc_perm =
                Tracked((self.proc_perms.borrow_mut()).tracked_remove(proc_ptr));
            let thread_ptr = proc_pop_thread(PPtr::<Process>::from_usize(proc_ptr), &mut proc_perm);
            assert(proc_perm@@.value.get_Some_0().owned_threads@.contains(thread_ptr) == false);
            assert(self.proc_perms@.dom().contains(proc_ptr) == false);
            proof{
                (self.proc_perms.borrow_mut())
                    .tracked_insert(proc_ptr, proc_perm.get());
            }
            assert(self.get_proc(proc_ptr).owned_threads@ =~= old(self).get_proc(proc_ptr).owned_threads@.subrange((loop_i as int) + 1, original_len as int));

            let mut thread_perm: Tracked<PointsTo<Thread>>=
                Tracked((self.thread_perms.borrow_mut()).tracked_remove(thread_ptr));
            assert(self.thread_perms@.dom().contains(thread_ptr) == false);
            proof{
                self.thread_ptrs@ = self.thread_ptrs@.remove(thread_ptr);
                ret@ = ret@.insert(thread_ptr);
            }
            assert(self.wf());
            loop_i = loop_i + 1;
        }

        return ret;
    }
}

}

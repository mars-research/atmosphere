// use core::mem::MaybeUninit;

use vstd::prelude::*;
verus! {
use vstd::ptr::*;

use super::*;

use crate::mars_array::*;
use crate::mars_staticlinkedlist::*;

// use crate::trap::*;

// use crate::setters::*;
use crate::define::*;
use crate::trap::PtRegs;


pub struct Process{
    // pub owned_threads: LinkedList<ThreadPtr>,
    // pub pl_rf: NodeRef<ProcPtr>,
    pub pl_rf: Index,
    pub pcid: Pcid,
    pub ioid: Option<IOid>,
    pub owned_threads: MarsStaticLinkedList<MAX_NUM_THREADS_PER_PROC>,
}

impl Process {
    pub open spec fn page_closure(&self) -> Set<PagePtr>
    {
        Set::empty()
    }

    pub open spec fn get_pcid(&self) -> Pcid {
        self.pcid
    }

    pub open spec fn get_ioid(&self) -> Option<IOid> {
        self.ioid
    }
}

pub struct ProcessManager{
    // pub proc_ptrs: LinkedList<ProcPtr>,
    pub proc_ptrs: MarsStaticLinkedList<MAX_NUM_PROCS>,
    pub proc_perms: Tracked<Map<ProcPtr, PointsTo<Process>>>,

    pub thread_ptrs: Ghost<Set<ThreadPtr>>,
    pub thread_perms: Tracked<Map<ThreadPtr, PointsTo<Thread>>>,

    //pub scheduler: Scheduler,
    pub scheduler: MarsStaticLinkedList<MAX_NUM_THREADS>,
    pub endpoint_ptrs: Ghost<Set<EndpointPtr>>,
    pub endpoint_perms: Tracked<Map<EndpointPtr, PointsTo<Endpoint>>>,

    pub pcid_closure : Ghost<Set<Pcid>>,
    pub ioid_closure : Ghost<Set<IOid>>,
}

#[verifier(inline)]
pub open spec fn endpoint_descriptors_unique(endpoint_descriptors:MarsArray<EndpointPtr,MAX_NUM_ENDPOINT_DESCRIPTORS>) -> bool
{
    (forall|i:int,j:int| #![auto] i != j && 0<=i<MAX_NUM_ENDPOINT_DESCRIPTORS && 0<=j<MAX_NUM_ENDPOINT_DESCRIPTORS
        ==> endpoint_descriptors@[i] == 0 ||
            endpoint_descriptors@[j] == 0 ||
            endpoint_descriptors@[i] != endpoint_descriptors@[j]
        )
}

impl ProcessManager {

    #[verifier(external_body)]
    pub fn new() -> (ret: ProcessManager)
        ensures
            ret.proc_ptrs.arr_seq@.len() == MAX_NUM_PROCS,
            ret.proc_perms@ =~= Map::empty(),
            ret.thread_ptrs@ =~= Set::empty(),
            ret.thread_perms@ =~= Map::empty(),
            ret.scheduler.arr_seq@.len() == MAX_NUM_THREADS,
            ret.scheduler@ =~= Seq::empty(),
            ret.endpoint_ptrs@ =~= Set::empty(),
            ret.endpoint_perms@ =~= Map::empty(),
            ret.pcid_closure@ =~= Set::empty(),
            ret.ioid_closure@ =~= Set::empty(),
    {
        let ret = Self {
            proc_ptrs: MarsStaticLinkedList::<MAX_NUM_PROCS>::new(),
            proc_perms: Tracked(Map::tracked_empty()),

            thread_ptrs: Ghost(Set::empty()),
            thread_perms: Tracked(Map::tracked_empty()),

            scheduler: MarsStaticLinkedList::<MAX_NUM_THREADS>::new(),
            endpoint_ptrs: Ghost(Set::empty()),
            endpoint_perms: Tracked(Map::tracked_empty()),

            pcid_closure : Ghost(Set::empty()),
            ioid_closure : Ghost(Set::empty()),
        };

        ret
    }

    pub fn proc_man_init(&mut self)
        requires
            old(self).proc_ptrs.arr_seq@.len() == MAX_NUM_PROCS,
            old(self).proc_perms@ =~= Map::empty(),
            old(self).thread_ptrs@ =~= Set::empty(),
            old(self).thread_perms@ =~= Map::empty(),
            old(self).scheduler.arr_seq@.len() == MAX_NUM_THREADS,
            old(self).scheduler@ =~= Seq::empty(),
            old(self).endpoint_ptrs@ =~= Set::empty(),
            old(self).endpoint_perms@ =~= Map::empty(),
            old(self).pcid_closure@ =~= Set::empty(),
            old(self).ioid_closure@ =~= Set::empty(),
        ensures
            self.wf(),
            self.proc_ptrs.arr_seq@.len() == MAX_NUM_PROCS,
            self.proc_ptrs@ =~= Seq::empty(),
            self.proc_perms@ =~= Map::empty(),
            self.thread_ptrs@ =~= Set::empty(),
            self.thread_perms@ =~= Map::empty(),
            self.scheduler.arr_seq@.len() == MAX_NUM_THREADS,
            self.scheduler@ =~= Seq::empty(),
            self.scheduler.len() =~= 0,
            self.endpoint_ptrs@ =~= Set::empty(),
            self.endpoint_perms@ =~= Map::empty(),
            self.pcid_closure@ =~= Set::empty(),
            self.ioid_closure@ =~= Set::empty(),
            forall|thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(thread_ptr) ==> self.get_thread(thread_ptr).state != TRANSIT,
        {
            self.proc_ptrs.init();
            self.scheduler.init();
        }

    #[verifier(inline)]
    pub open spec fn get_proc_ptrs(&self) -> Seq<ProcPtr>
    {
        self.proc_ptrs@
    }

    #[verifier(inline)]
    pub open spec fn get_proc(&self, proc_ptr: ProcPtr) -> Process
        recommends
            self.get_proc_ptrs().contains(proc_ptr),
    {
        self.proc_perms@[proc_ptr]@.value.get_Some_0()
    }

    pub fn get_thread_endpoint_ptr_by_endpoint_idx(&self, thread_ptr: ThreadPtr, endpoint_index:EndpointIdx) -> (ret :EndpointPtr)
        requires
            self.wf(),
            self.get_thread_ptrs().contains(thread_ptr),
            0<=endpoint_index<MAX_NUM_ENDPOINT_DESCRIPTORS,
        ensures
            ret =~= self.get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int]

    {
        assert(self.thread_perms@.dom().contains(thread_ptr));
        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
        let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));
        let ret = thread.endpoint_descriptors.get(endpoint_index);
        return *ret;
    }

    // pub open spec fn spec_get_pcid_by_thread_ptr(&self, thread_ptr:ThreadPtr) -> Pcid
    //     recommends
    //         self.wf(),
    //         self.get_thread_ptrs().contains(thread_ptr),
    // {
    //     self.get_proc(self.get_thread(thread_ptr).parent).pcid
    // }

    // #[verifier(when_used_as_spec(spec_get_pcid_by_thread_ptr))]

    pub fn get_pt_regs_by_thread_ptr(&self, thread_ptr:ThreadPtr) -> (ret: Option<PtRegs>)
        requires
            self.wf(),
            self.get_thread_ptrs().contains(thread_ptr),
        ensures
            ret =~= self.get_thread(thread_ptr).trap_frame,
            // ret =~= self.get_pcid_by_thread_ptr(thread_ptr),
        {
            let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
            let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));
            let trap_frame = thread.trap_frame;
            return trap_frame;
        }
    pub fn get_pcid_by_thread_ptr(&self, thread_ptr:ThreadPtr) -> (ret: Pcid)
        requires
            self.wf(),
            self.get_thread_ptrs().contains(thread_ptr),
        ensures
            ret =~= self.get_proc(self.get_thread(thread_ptr).parent).pcid,
            self.get_pcid_closure().contains(ret),
            0<=ret<PCID_MAX,
            // ret =~= self.get_pcid_by_thread_ptr(thread_ptr),
    {
        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
        let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));
        let proc_ptr = thread.parent;
        assert(self.proc_perms@.dom().contains(proc_ptr));
        let tracked proc_perm = self.proc_perms.borrow().tracked_borrow(proc_ptr);
        let proc : &Process = PPtr::<Process>::from_usize(proc_ptr).borrow(Tracked(proc_perm));
        let ret = proc.pcid;
        return ret;
    }

    pub fn get_ioid_by_thread_ptr(&self, thread_ptr:ThreadPtr) -> (ret: Option<IOid>)
        requires
            self.wf(),
            self.get_thread_ptrs().contains(thread_ptr),
        ensures
            ret =~= self.get_proc(self.get_thread(thread_ptr).parent).ioid,
            ret.is_Some() ==> self.get_ioid_closure().contains(ret.unwrap()),
            ret.is_Some() ==> 0<=ret.unwrap()<IOID_MAX,
            // ret =~= self.get_pcid_by_thread_ptr(thread_ptr),
    {
        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
        let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));
        let proc_ptr = thread.parent;
        assert(self.proc_perms@.dom().contains(proc_ptr));
        let tracked proc_perm = self.proc_perms.borrow().tracked_borrow(proc_ptr);
        let proc : &Process = PPtr::<Process>::from_usize(proc_ptr).borrow(Tracked(proc_perm));
        let ret = proc.ioid;
        return ret;
    }

    // pub open spec fn spec_get_parent_proc_ptr_by_thread_ptr(&self, thread_ptr:ThreadPtr) -> ProcPtr
    //     recommends
    //         self.wf(),
    //         self.get_thread_ptrs().contains(thread_ptr),
    // {
    //     self.get_thread(thread_ptr).parent
    // }

    // #[verifier(when_used_as_spec(spec_get_parent_proc_ptr_by_thread_ptr))]
    pub fn get_parent_proc_ptr_by_thread_ptr(&self, thread_ptr:ThreadPtr) -> (ret: ProcPtr)
        requires
            self.wf(),
            self.get_thread_ptrs().contains(thread_ptr),
        ensures
            ret =~= self.get_thread(thread_ptr).parent,
            self.get_proc_ptrs().contains(ret),
            // ret =~= self.get_parent_proc_ptr_by_thread_ptr(thread_ptr),
    {
        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
        let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));
        let proc_ptr = thread.parent;
        return proc_ptr;
    }

    pub fn get_error_code_by_thread_ptr(&self, thread_ptr:ThreadPtr) -> (ret: Option<ErrorCodeType>)
        requires
            self.wf(),
            self.get_thread_ptrs().contains(thread_ptr),
        ensures
            ret =~= self.get_thread(thread_ptr).error_code,
        {
        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
        let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));
        let error_code = thread.error_code;
        return error_code;
        }
    pub fn get_ipc_payload_by_thread_ptr(&self, thread_ptr:ThreadPtr) -> (ret: IPCPayLoad)
        requires
            self.wf(),
            self.get_thread_ptrs().contains(thread_ptr),
        ensures
            ret =~= self.get_thread(thread_ptr).ipc_payload,
        {
        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
        let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));
        let ipc_payload = thread.ipc_payload;
        return ipc_payload;
        }
    // pub open spec fn spec_get_proc_num_of_threads_by_proc_ptr(&self, proc_ptr:ProcPtr) -> usize
    //     recommends
    //         self.wf(),
    //         self.get_proc_ptrs().contains(proc_ptr),
    // {
    //     self.get_proc(proc_ptr).owned_threads.len()
    // }

    // #[verifier(when_used_as_spec(spec_get_proc_num_of_threads_by_proc_ptr))]
    pub fn get_proc_num_of_threads_by_proc_ptr(&self, proc_ptr:ProcPtr) -> (ret: usize)
        requires
            self.wf(),
            self.get_proc_ptrs().contains(proc_ptr),
        ensures
            ret =~= self.get_proc(proc_ptr).owned_threads.len(),
            ret =~= self.proc_perms@[proc_ptr]@.value.get_Some_0().owned_threads.len(),
            // ret =~= self.get_proc_num_of_threads_by_proc_ptr(proc_ptr),
    {
        assert(self.get_proc_ptrs().contains(proc_ptr));
        assert(self.proc_perms@.dom().contains(proc_ptr));
        let tracked proc_perm = self.proc_perms.borrow().tracked_borrow(proc_ptr);
        let proc : &Process = PPtr::<Process>::from_usize(proc_ptr).borrow(Tracked(proc_perm));
        return proc.owned_threads.len();
    }

    pub fn get_head_of_owned_thread_by_proc_ptr(&self, proc_ptr:ProcPtr) -> (ret: ThreadPtr)
        requires
            self.wf(),
            self.get_proc_ptrs().contains(proc_ptr),
            self.get_proc(proc_ptr).owned_threads.len() != 0,
        ensures
            ret =~= self.get_proc(proc_ptr).owned_threads@[0],
    {
        assert(self.get_proc_ptrs().contains(proc_ptr));
        assert(self.proc_perms@.dom().contains(proc_ptr));
        let tracked proc_perm = self.proc_perms.borrow().tracked_borrow(proc_ptr);
        let proc : &Process = PPtr::<Process>::from_usize(proc_ptr).borrow(Tracked(proc_perm));
        return proc.owned_threads.get_head();
    }

    pub fn get_head_of_endpoint_by_endpoint_ptr(&self, endpoint_ptr:EndpointPtr) -> (ret: ThreadPtr)
        requires
            self.wf(),
            self.get_endpoint_ptrs().contains(endpoint_ptr),
            self.get_endpoint(endpoint_ptr).queue.len() != 0,
        ensures
            ret =~= self.get_endpoint(endpoint_ptr).queue@[0],
    {
        assert(self.endpoint_perms@.dom().contains(endpoint_ptr));
        let tracked endpoint_perm = self.endpoint_perms.borrow().tracked_borrow(endpoint_ptr);
        let endpoint : &Endpoint = PPtr::<Endpoint>::from_usize(endpoint_ptr).borrow(Tracked(endpoint_perm));
        let ret = endpoint.queue.get_head();
        return ret;
    }

    pub fn get_endpoint_rf_counter_by_endpoint_ptr(&self, endpoint_ptr:EndpointPtr) -> (ret :usize)
        requires
            self.wf(),
            self.get_endpoint_ptrs().contains(endpoint_ptr),
        ensures
            ret =~= self.get_endpoint(endpoint_ptr).rf_counter,
    {
        assert(self.endpoint_perms@.dom().contains(endpoint_ptr));
        let tracked endpoint_perm = self.endpoint_perms.borrow().tracked_borrow(endpoint_ptr);
        let endpoint : &Endpoint = PPtr::<Endpoint>::from_usize(endpoint_ptr).borrow(Tracked(endpoint_perm));
        let ret = endpoint.rf_counter;
        return ret;
    }

    pub fn get_endpoint_state_by_endpoint_ptr(&self, endpoint_ptr:EndpointPtr) -> (ret :EndpointState)
        requires
            self.wf(),
            self.get_endpoint_ptrs().contains(endpoint_ptr),
        ensures
            ret =~= self.get_endpoint(endpoint_ptr).queue_state,
    {
        assert(self.endpoint_perms@.dom().contains(endpoint_ptr));
        let tracked endpoint_perm = self.endpoint_perms.borrow().tracked_borrow(endpoint_ptr);
        let endpoint : &Endpoint = PPtr::<Endpoint>::from_usize(endpoint_ptr).borrow(Tracked(endpoint_perm));
        let ret = endpoint.queue_state;
        return ret;
    }

    pub fn get_endpoint_len_by_endpoint_ptr(&self, endpoint_ptr:EndpointPtr) -> (ret :usize)
        requires
            self.wf(),
            self.get_endpoint_ptrs().contains(endpoint_ptr),
        ensures
            ret =~= self.get_endpoint(endpoint_ptr).len(),
    {
        assert(self.endpoint_perms@.dom().contains(endpoint_ptr));
        let tracked endpoint_perm = self.endpoint_perms.borrow().tracked_borrow(endpoint_ptr);
        let endpoint : &Endpoint = PPtr::<Endpoint>::from_usize(endpoint_ptr).borrow(Tracked(endpoint_perm));
        let ret = endpoint.queue.len();
        return ret;
    }

    #[verifier(inline)]
    pub open spec fn get_thread(&self, thread_ptr: ThreadPtr) -> Thread
        recommends
            self.get_thread_ptrs().contains(thread_ptr),
    {
        self.thread_perms@[thread_ptr]@.value.get_Some_0()
    }


    pub fn get_proc_ptrs_len(&self) ->(ret: usize)
    requires
        self.wf(),
    ensures
        ret == self.proc_ptrs.len(),
    {
        self.proc_ptrs.len()
    }

    pub fn get_proc_owned_thread_len(&self, proc_ptr: ProcPtr) -> (ret: usize)
        requires
            self.get_proc_ptrs().contains(proc_ptr),
            self.wf(),
        ensures
            ret == self.get_proc(proc_ptr).owned_threads.len(),
    {
        assert(self.proc_perms@.dom().contains(proc_ptr));
        let tracked proc_perm = self.proc_perms.borrow().tracked_borrow(proc_ptr);
        let proc : &Process = PPtr::<Process>::from_usize(proc_ptr).borrow(Tracked(proc_perm));
        return proc.owned_threads.len();
    }

    pub fn get_proc_owned_thread_head(&self, proc_ptr: ProcPtr) -> (ret: ThreadPtr)
        requires
            self.get_proc_ptrs().contains(proc_ptr),
            self.wf(),
            self.get_proc(proc_ptr).owned_threads.len() != 0,
        ensures
            ret == self.get_proc(proc_ptr).owned_threads@[0],
            self.get_thread_ptrs().contains(ret),
    {
        assert(self.proc_perms@.dom().contains(proc_ptr));
        let tracked proc_perm = self.proc_perms.borrow().tracked_borrow(proc_ptr);
        let proc : &Process = PPtr::<Process>::from_usize(proc_ptr).borrow(Tracked(proc_perm));
        let ret = proc.owned_threads.get_head();

        assert(self.get_proc(proc_ptr).owned_threads@.contains(ret));

        return ret;
    }

    pub fn get_thread_endpoint_descriptor(&self, thread_ptr:ThreadPtr, endpoint_index: EndpointIdx) -> (ret: EndpointPtr)
    requires
        self.wf(),
        self.get_thread_ptrs().contains(thread_ptr),
        0<= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
    ensures
        ret == self.get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int],
        ret != 0 ==> self.get_endpoint_ptrs().contains(ret),
    {
        assert(self.thread_perms@.dom().contains(thread_ptr));
        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
        let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));
        assert(thread.endpoint_descriptors.wf());
        let endpoint_ptr = *thread.endpoint_descriptors.get(endpoint_index);

        assert(endpoint_ptr != 0 ==> self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_descriptors@[endpoint_index as int] != 0);

        return endpoint_ptr;
    }

    pub fn get_thread_caller(&self, thread_ptr:ThreadPtr) -> (ret:Option<ThreadPtr>)
    requires
        self.wf(),
        self.get_thread_ptrs().contains(thread_ptr),
    ensures
        ret =~= self.get_thread(thread_ptr).caller,
    {
        assert(self.thread_perms@.dom().contains(thread_ptr));
        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
        let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));

        return thread.caller;
    }

    pub fn get_thread_if_is_calling(&self, thread_ptr:ThreadPtr) -> (ret: bool)
    requires
        self.wf(),
        self.get_thread_ptrs().contains(thread_ptr),
    ensures
        ret =~= self.get_thread(thread_ptr).ipc_payload.calling,
    {
        assert(self.thread_perms@.dom().contains(thread_ptr));
        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
        let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));

        return thread.ipc_payload.calling;
    }

    pub fn get_thread_message_payload(&self, thread_ptr:ThreadPtr) -> (ret: Option<(VAddr,usize)>)
    requires
        self.wf(),
        self.get_thread_ptrs().contains(thread_ptr),
    ensures
        ret =~= self.get_thread(thread_ptr).ipc_payload.message,
    {
        assert(self.thread_perms@.dom().contains(thread_ptr));
        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
        let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));

        return thread.ipc_payload.message;
    }

    pub fn get_thread_page_payload(&self, thread_ptr:ThreadPtr) -> (ret: Option<(VAddr,usize)>)
    requires
        self.wf(),
        self.get_thread_ptrs().contains(thread_ptr),
    ensures
        ret =~= self.get_thread(thread_ptr).ipc_payload.page_payload,
    {
        assert(self.thread_perms@.dom().contains(thread_ptr));
        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
        let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));

        return thread.ipc_payload.page_payload;
    }

    pub fn get_thread_endpoint_payload(&self, thread_ptr:ThreadPtr) -> (ret: Option<EndpointIdx>)
    requires
        self.wf(),
        self.get_thread_ptrs().contains(thread_ptr),
    ensures
        ret =~= self.get_thread(thread_ptr).ipc_payload.endpoint_payload,
    {
        assert(self.thread_perms@.dom().contains(thread_ptr));
        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
        let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));

        return thread.ipc_payload.endpoint_payload;
    }

    pub fn get_endpoint_rf_counter(&self, endpoint_ptr: EndpointPtr) -> (ret: usize)
    requires
        self.wf(),
        self.get_endpoint_ptrs().contains(endpoint_ptr),
    ensures
        ret == self.get_endpoint(endpoint_ptr).rf_counter,
    {
        assert(self.endpoint_perms@.dom().contains(endpoint_ptr));
        let tracked endpoint_perm = self.endpoint_perms.borrow().tracked_borrow(endpoint_ptr);
        let endpoint : &Endpoint = PPtr::<Endpoint>::from_usize(endpoint_ptr).borrow(Tracked(endpoint_perm));
        return endpoint.rf_counter;
    }

    pub fn get_endpoint_len(&self, endpoint_ptr: EndpointPtr) -> (ret: usize)
    requires
        self.wf(),
        self.get_endpoint_ptrs().contains(endpoint_ptr),
    ensures
        ret == self.get_endpoint(endpoint_ptr).queue.len(),
    {
        assert(self.endpoint_perms@.dom().contains(endpoint_ptr));
        let tracked endpoint_perm = self.endpoint_perms.borrow().tracked_borrow(endpoint_ptr);
        let endpoint : &Endpoint = PPtr::<Endpoint>::from_usize(endpoint_ptr).borrow(Tracked(endpoint_perm));
        return endpoint.queue.len();
    }


    pub fn check_thread_capable_for_new_endpoint(&self, thread_ptr:ThreadPtr, endpoint_index:EndpointIdx, endpoint_ptr: EndpointPtr) -> (ret: bool)
    requires
        self.wf(),
        self.get_thread_ptrs().contains(thread_ptr),
        0<=endpoint_index<MAX_NUM_ENDPOINT_DESCRIPTORS,
    ensures
        ret == true ==> (forall|j:int| #![auto] 0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==>
                self.get_thread(thread_ptr).endpoint_descriptors@[j as int] != endpoint_ptr),
        ret == true ==> self.get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int] == 0,

    {
        assert(self.thread_perms@.dom().contains(thread_ptr));
        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
        let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));

        let current_endpoint_at_index = self.get_thread_endpoint_descriptor(thread_ptr, endpoint_index);
        if current_endpoint_at_index != 0 {
            return false;
        }
        assert(self.get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int] == 0);

        let mut i = 0;
        let mut ret = true;
        while i != MAX_NUM_ENDPOINT_DESCRIPTORS
            invariant
                self.wf(),
                self.get_thread_ptrs().contains(thread_ptr),
                0<= i <= MAX_NUM_ENDPOINT_DESCRIPTORS,
                ret == true ==>
                    (forall|j:int| #![auto] 0 <= j < i ==>
                        self.get_thread(thread_ptr).endpoint_descriptors@[j as int] != endpoint_ptr),
                self.get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int] == 0
            ensures
                self.wf(),
                self.get_thread_ptrs().contains(thread_ptr),
                i == MAX_NUM_ENDPOINT_DESCRIPTORS,
                ret == true ==>
                    (forall|j:int| #![auto] 0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==>
                        self.get_thread(thread_ptr).endpoint_descriptors@[j as int] != endpoint_ptr),
                self.get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int] == 0,
        {
            let tmp = self.get_thread_endpoint_descriptor(thread_ptr, i);

            if tmp == endpoint_ptr {
                ret = false;
            }
            i = i + 1;
        }

        return ret;
    }


    pub fn get_endpoint_queue_state(&self, endpoint_ptr: EndpointPtr) -> (ret: bool)
    requires
        self.wf(),
        self.get_endpoint_ptrs().contains(endpoint_ptr),
    ensures
        ret == self.get_endpoint(endpoint_ptr).queue_state,
    {
        assert(self.endpoint_perms@.dom().contains(endpoint_ptr));
        let tracked endpoint_perm = self.endpoint_perms.borrow().tracked_borrow(endpoint_ptr);
        let endpoint : &Endpoint = PPtr::<Endpoint>::from_usize(endpoint_ptr).borrow(Tracked(endpoint_perm));
        return endpoint.queue_state;
    }

    pub fn get_endpoint_queue_head(&self, endpoint_ptr: EndpointPtr) -> (ret: ThreadPtr)
    requires
        self.wf(),
        self.get_endpoint_ptrs().contains(endpoint_ptr),
        self.get_endpoint(endpoint_ptr).queue.len() > 0,
    ensures
        ret == self.get_endpoint(endpoint_ptr).queue@[0],
        self.get_thread_ptrs().contains(ret),
        self.get_thread(ret).state == BLOCKED,
    {
        assert(self.endpoint_perms@.dom().contains(endpoint_ptr));
        let tracked endpoint_perm = self.endpoint_perms.borrow().tracked_borrow(endpoint_ptr);
        let endpoint : &Endpoint = PPtr::<Endpoint>::from_usize(endpoint_ptr).borrow(Tracked(endpoint_perm));
        let ret = endpoint.queue.get_head();

        assert(self.get_endpoint(endpoint_ptr).queue@[0] == ret);
        assert(self.get_endpoint(endpoint_ptr).queue@.contains(ret));
        assert(self.get_thread(ret).state == BLOCKED);
        return ret;
    }

    #[verifier(inline)]
    pub open spec fn get_thread_ptrs(&self) -> Set<ThreadPtr>
    {
        self.thread_ptrs@
    }

    #[verifier(inline)]
    pub open spec fn get_endpoint_ptrs(&self) -> Set<EndpointPtr>
    {
        self.endpoint_ptrs@
    }

    #[verifier(inline)]
    pub open spec fn get_endpoint(&self, endpoint_ptr:EndpointPtr) -> Endpoint
        recommends
            self.get_endpoint_ptrs().contains(endpoint_ptr)
    {
        self.endpoint_perms@[endpoint_ptr].view().value.get_Some_0()
    }
    ///spec helper for processes
    ///specs:
    ///Process list (PL) contains no duplicate process pointers
    ///PM contains and only contains process perms of its process pointers
    ///Each process contains no duplicate thread pointers
    ///Each process's threads are disjoint
    ///Each process owns a valid reverse pointer to free it from PL
    pub open spec fn wf_procs(&self) -> bool{
        (self.proc_ptrs.wf())
        &&
        (self.proc_ptrs.unique())
        &&
        (self.proc_ptrs@.to_set() =~= self.proc_perms@.dom())
        &&
        (forall|proc_ptr: ProcPtr| #![auto] self.proc_perms@.dom().contains(proc_ptr) ==>  self.proc_perms@[proc_ptr].view().value.is_Some())
        &&
        (forall|proc_ptr: ProcPtr| #![auto] self.proc_perms@.dom().contains(proc_ptr) ==>  self.proc_perms@[proc_ptr].view().pptr == proc_ptr)
        &&
        (forall|proc_ptr: ProcPtr| #![auto] self.proc_perms@.dom().contains(proc_ptr) ==>  self.proc_perms@[proc_ptr].view().value.get_Some_0().owned_threads.wf())
        &&
        (forall|proc_ptr: ProcPtr| #![auto] self.proc_perms@.dom().contains(proc_ptr) ==>  self.proc_perms@[proc_ptr].view().value.get_Some_0().owned_threads.unique())
        &&
        (forall|proc_ptr_i: ProcPtr, proc_ptr_j: ProcPtr| #![auto] proc_ptr_i != proc_ptr_j && self.proc_perms@.dom().contains(proc_ptr_i) && self.proc_perms@.dom().contains(proc_ptr_j) ==>
            self.proc_perms@[proc_ptr_i].view().value.get_Some_0().owned_threads@.to_set().disjoint(self.proc_perms@[proc_ptr_j].view().value.get_Some_0().owned_threads@.to_set()))
        &&
        (forall|proc_ptr: ProcPtr| #![auto] self.proc_perms@.dom().contains(proc_ptr) ==>  self.proc_ptrs.node_ref_valid(self.proc_perms@[proc_ptr].view().value.get_Some_0().pl_rf))
        &&
        (forall|proc_ptr: ProcPtr| #![auto] self.proc_perms@.dom().contains(proc_ptr) ==>  self.proc_ptrs.node_ref_resolve(self.proc_perms@[proc_ptr].view().value.get_Some_0().pl_rf) == proc_ptr)
    }

    ///spec helper for threads
    ///specs:
    ///PM contains and only contains thread perms of threads owned by some processes
    ///Each thread has a parent which owns this thread in its owned_threads list
    ///Each process owns a valid reverse pointer to free it from its parent process's owned_threads list
    ///Each process owns a valid reverse pointer to free it from the scheduler
    ///Each process owns a valid reverse pointer to free it from the endpoints
    pub open spec fn wf_threads(&self) -> bool{
        (self.get_thread_ptrs().finite())
        &&
        (self.get_thread_ptrs() =~= self.thread_perms@.dom())
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) ==>  self.thread_perms@[thread_ptr].view().value.is_Some())
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) ==>  self.thread_perms@[thread_ptr].view().pptr == thread_ptr)
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) ==>  0 <= self.thread_perms@[thread_ptr].view().value.get_Some_0().state <= TRANSIT)
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) ==>  self.proc_ptrs@.contains(self.thread_perms@[thread_ptr].view().value.get_Some_0().parent))
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) ==>  self.proc_perms@[self.get_thread(thread_ptr).parent].view().value.get_Some_0().owned_threads@.contains(thread_ptr))
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) ==>
            self.proc_perms@[self.get_thread(thread_ptr).parent].view().value.get_Some_0().owned_threads.node_ref_valid(self.thread_perms@[thread_ptr].view().value.get_Some_0().parent_rf))
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) ==>
            self.proc_perms@[self.get_thread(thread_ptr).parent].view().value.get_Some_0().owned_threads.node_ref_resolve(self.thread_perms@[thread_ptr].view().value.get_Some_0().parent_rf) == thread_ptr)
        &&
        (forall|proc_ptr: usize, i:int| #![auto] self.proc_perms@.dom().contains(proc_ptr) && 0<=i<self.proc_perms@[proc_ptr]@.value.get_Some_0().owned_threads.len()
            ==>  self.thread_perms@.dom().contains(self.proc_perms@[proc_ptr]@.value.get_Some_0().owned_threads@[i]))
        &&
        (forall|proc_ptr: usize, i:int| #![auto] self.proc_perms@.dom().contains(proc_ptr) && 0<=i<self.proc_perms@[proc_ptr]@.value.get_Some_0().owned_threads.len()
            ==>  self.thread_perms@[self.proc_perms@[proc_ptr]@.value.get_Some_0().owned_threads@[i]]@.value.get_Some_0().parent == proc_ptr)
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.get_thread_ptrs().contains(thread_ptr) ==>
            (self.get_thread(thread_ptr).state != RUNNING <==> self.get_thread(thread_ptr).trap_frame.is_Some())
        )
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.get_thread_ptrs().contains(thread_ptr) ==>
            (self.get_thread(thread_ptr).error_code.is_Some() ==> self.get_thread(thread_ptr).state == SCHEDULED)
        )
    }

    pub open spec fn wf_scheduler(&self) -> bool{
        (self.scheduler.wf())
        &&
        (self.scheduler.unique())
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.scheduler@.contains(thread_ptr) ==>  self.thread_perms@.dom().contains(thread_ptr))
        // &&
        // (forall|thread_ptr: ThreadPtr| #![auto] self.scheduler@.contains(thread_ptr) ==>  self.get_thread_ptrs().contains(thread_ptr))
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.scheduler@.contains(thread_ptr) ==>  self.thread_perms@[thread_ptr].view().value.get_Some_0().state == SCHEDULED)
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state == SCHEDULED
            ==> self.scheduler@.contains(thread_ptr))
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.scheduler@.contains(thread_ptr) ==>  self.thread_perms@[thread_ptr].view().value.get_Some_0().scheduler_rf.is_Some())
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.scheduler@.contains(thread_ptr) ==>  self.scheduler.node_ref_valid(self.thread_perms@[thread_ptr].view().value.get_Some_0().scheduler_rf.unwrap()))
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.scheduler@.contains(thread_ptr) ==>  self.scheduler.node_ref_resolve(self.thread_perms@[thread_ptr].view().value.get_Some_0().scheduler_rf.unwrap()) == thread_ptr )
    }

    pub open spec fn wf_endpoints(&self) -> bool{
        (self.endpoint_ptrs@.finite())
        &&
        (self.endpoint_ptrs@ =~= self.endpoint_perms@.dom())
        &&
        (self.endpoint_perms@.dom().contains(0) == false)
        &&
        (forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) ==>  self.endpoint_perms@[endpoint_ptr].view().value.is_Some())
        &&
        (forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) ==>  self.endpoint_perms@[endpoint_ptr].view().pptr == endpoint_ptr)
        &&
        (forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) ==>  self.endpoint_perms@[endpoint_ptr].view().value.get_Some_0().queue.wf())
        &&
        (forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) ==>  self.endpoint_perms@[endpoint_ptr].view().value.get_Some_0().queue.unique())
        &&
        (forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) ==>  self.endpoint_perms@[endpoint_ptr].view().value.get_Some_0().owning_threads@.finite())
        &&
        (forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr)
            ==> self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().owning_threads@.len() == self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().rf_counter)
        &&
        (forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr)
            ==> self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().rf_counter != 0)
        &&
        (forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr)
            ==> (forall|thread_ptr: ThreadPtr| #![auto] self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().owning_threads@.contains(thread_ptr)
                ==> self.thread_perms@.dom().contains(thread_ptr))
        )
        &&
        (forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr)
            ==> (forall|thread_ptr: ThreadPtr| #![auto] self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().owning_threads@.contains(thread_ptr)
                ==> self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_descriptors@.contains(endpoint_ptr))
        )
        &&
        (forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr)
            ==>  (forall|thread_ptr:ThreadPtr| #![auto] self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().queue@.contains(thread_ptr)
                ==> ( self.thread_perms@.dom().contains(thread_ptr)
                )
        ))
        &&
        (forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr)
            ==>  (forall|thread_ptr:ThreadPtr| #![auto] self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().queue@.contains(thread_ptr)
                ==> (
                    self.thread_perms@[thread_ptr]@.value.get_Some_0().state == BLOCKED
                )
        ))
        &&
        (forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr)
            ==>  (forall|thread_ptr:ThreadPtr| #![auto] self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().queue@.contains(thread_ptr)
                ==> (
                    self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_ptr.unwrap() == endpoint_ptr
                )
        ))
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr)
            ==> self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_descriptors.wf())
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr)
            ==> endpoint_descriptors_unique(self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_descriptors)
            )
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr)
            ==> (forall|i:int| #![auto] 0<=i<MAX_NUM_ENDPOINT_DESCRIPTORS && self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_descriptors@[i] != 0
                ==> self.endpoint_perms@.dom().contains(self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_descriptors@[i])
            ))
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr)
            ==> (forall|i:int| #![auto] 0<=i<MAX_NUM_ENDPOINT_DESCRIPTORS && self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_descriptors@[i] != 0
                ==> self.endpoint_perms@[self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_descriptors@[i]]@.value.get_Some_0().owning_threads@.contains(thread_ptr)
            ))
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state == BLOCKED
            ==> self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_ptr.is_Some())
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state == BLOCKED
            ==> self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_ptr.unwrap() != 0)
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state == BLOCKED
            ==>  self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_descriptors@.contains(self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_ptr.unwrap()))
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state == BLOCKED
            ==> self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_rf.is_Some())
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state == BLOCKED
            ==>  self.endpoint_perms@[self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_ptr.unwrap()]@.value.get_Some_0().queue@.contains(thread_ptr))
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state == BLOCKED
            ==>  self.endpoint_perms@[self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_ptr.unwrap()]@.value.get_Some_0().queue.node_ref_valid(self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_rf.unwrap())
        )
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state == BLOCKED
            ==>  self.endpoint_perms@[self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_ptr.unwrap()]@.value.get_Some_0().queue.node_ref_resolve(self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_rf.unwrap()) == thread_ptr
        )
    }

    pub open spec fn wf_ipc(&self) -> bool{
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state != CALLING ==>
            self.thread_perms@[thread_ptr].view().value.get_Some_0().callee.is_None())
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state == CALLING ==>
            (self.thread_perms@[thread_ptr].view().value.get_Some_0().callee.is_Some() && self.thread_perms@.dom().contains(self.thread_perms@[thread_ptr].view().value.get_Some_0().callee.unwrap())
            )
        )
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().caller.is_Some() ==>
            self.thread_perms@.dom().contains(self.thread_perms@[thread_ptr].view().value.get_Some_0().caller.unwrap()))
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().caller.is_Some() ==>
            self.thread_perms@[self.thread_perms@[thread_ptr].view().value.get_Some_0().caller.unwrap()].view().value.get_Some_0().callee.is_Some()
            && self.thread_perms@[self.thread_perms@[thread_ptr].view().value.get_Some_0().caller.unwrap()].view().value.get_Some_0().callee.unwrap() == thread_ptr)
        &&
        (forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().callee.is_Some() ==>
            self.thread_perms@[self.thread_perms@[thread_ptr].view().value.get_Some_0().callee.unwrap()].view().value.get_Some_0().caller.is_Some()
            && self.thread_perms@[self.thread_perms@[thread_ptr].view().value.get_Some_0().callee.unwrap()].view().value.get_Some_0().caller.unwrap() == thread_ptr)



    }

    #[verifier(inline)]
    pub open spec fn get_proc_man_page_closure(&self) -> Set<PagePtr>
    {
        // self.local_page_closure()
        // +
        self.proc_ptrs@.to_set()
        +
        self.get_thread_ptrs()
        +
        self.endpoint_ptrs@
        // self.proc_ptrs@.fold_left(Set::<PagePtr>::empty(), |acc: Set::<PagePtr>, e: ProcPtr| -> Set::<PagePtr> {
        //         acc + self.proc_perms@[e]@.value.get_Some_0().page_closure()
        // })
        // +
        // self.get_thread_ptrs().fold(Set::<PagePtr>::empty(), |acc: Set::<PagePtr>, e: ThreadPtr| -> Set::<PagePtr> {
        //         acc + self.thread_perms@[e]@.value.get_Some_0().page_closure()
        // })
        // + ... fold page closures of other PM components
    }

    #[verifier(inline)]
    pub open spec fn get_pcid_closure(&self) -> Set<Pcid>
    {
        self.pcid_closure@
    }

    #[verifier(inline)]
    pub open spec fn get_ioid_closure(&self) -> Set<IOid>
    {
        self.ioid_closure@
    }

    ///Memory spec helper
    ///specs:
    ///For two different Processes, their page closures are disjoint.
    ///For any process, its data closure is disjoint with any page closure of the system.
    pub open spec fn wf_mem_closure(&self) -> bool{
        (self.proc_ptrs@.to_set().disjoint(self.get_thread_ptrs()))
        &&
        (self.proc_ptrs@.to_set().disjoint(self.endpoint_ptrs@))
        &&
        (self.get_thread_ptrs().disjoint(self.endpoint_ptrs@))
        // (
        //     forall|proc_ptr_i: ProcPtr,proc_ptr_j: ProcPtr| #![auto] proc_ptr_i != proc_ptr_j && self.proc_perms@.dom().contains(proc_ptr_i) && self.proc_perms@.dom().contains(proc_ptr_j)
        //         ==>  self.proc_perms@[proc_ptr_i].view().value.get_Some_0().page_closure@.disjoint(self.proc_perms@[proc_ptr_j].view().value.get_Some_0().page_closure@)
        // )
        // &&
        // (
        //     forall|proc_ptr_i: ProcPtr,proc_ptr_j: ProcPtr| #![auto] self.proc_perms@.dom().contains(proc_ptr_i) && self.proc_perms@.dom().contains(proc_ptr_j)
        //         ==>  self.proc_perms@[proc_ptr_i].view().value.get_Some_0().data_page_closure@.disjoint(self.proc_perms@[proc_ptr_j].view().value.get_Some_0().page_closure@)
        // )

    }

    pub open spec fn wf_pcid_closure(&self) -> bool{
        (
            self.get_pcid_closure().finite()
        )&&
        (
            forall|proc_ptr_i: ProcPtr| #![auto] self.proc_perms@.dom().contains(proc_ptr_i)
                ==>  0<=self.proc_perms@[proc_ptr_i].view().value.get_Some_0().get_pcid()<PCID_MAX
        )
        &&
        (
            forall|proc_ptr_i: ProcPtr,proc_ptr_j: ProcPtr| #![auto] proc_ptr_i != proc_ptr_j && self.proc_perms@.dom().contains(proc_ptr_i) && self.proc_perms@.dom().contains(proc_ptr_j)
                ==>  self.proc_perms@[proc_ptr_i].view().value.get_Some_0().get_pcid() != self.proc_perms@[proc_ptr_j].view().value.get_Some_0().get_pcid()
        )
        &&
        (
            forall|proc_ptr: ProcPtr| #![auto] self.proc_perms@.dom().contains(proc_ptr)
                ==>  self.get_pcid_closure().contains(self.proc_perms@[proc_ptr].view().value.get_Some_0().get_pcid())
        )
        &&
        (
            self.proc_ptrs@.len() == self.get_pcid_closure().len()
        )
    }

    pub open spec fn wf_ioid_closure(&self) -> bool{
        (
            self.get_ioid_closure().finite()
        )&&
        (
            forall|proc_ptr_i: ProcPtr| #![auto] self.proc_perms@.dom().contains(proc_ptr_i) && self.proc_perms@[proc_ptr_i].view().value.get_Some_0().get_ioid().is_Some()
                ==>  0<=self.proc_perms@[proc_ptr_i].view().value.get_Some_0().get_ioid().unwrap()<IOID_MAX
        )
        &&
        (
            forall|proc_ptr_i: ProcPtr,proc_ptr_j: ProcPtr| #![auto] proc_ptr_i != proc_ptr_j && self.proc_perms@.dom().contains(proc_ptr_i) && self.proc_perms@.dom().contains(proc_ptr_j)
                && self.proc_perms@[proc_ptr_i].view().value.get_Some_0().get_ioid().is_Some() && self.proc_perms@[proc_ptr_j].view().value.get_Some_0().get_ioid().is_Some()
                ==>  self.proc_perms@[proc_ptr_i].view().value.get_Some_0().get_ioid().unwrap() != self.proc_perms@[proc_ptr_j].view().value.get_Some_0().get_ioid().unwrap()
        )
        &&
        (
            forall|proc_ptr: ProcPtr| #![auto] self.proc_perms@.dom().contains(proc_ptr )&& self.proc_perms@[proc_ptr].view().value.get_Some_0().get_ioid().is_Some()
                ==>  self.get_ioid_closure().contains(self.proc_perms@[proc_ptr].view().value.get_Some_0().get_ioid().unwrap())
        )
    }

    pub open spec fn wf(&self) -> bool{
        self.wf_threads()
        &&
        self.wf_procs()
        &&
        self.wf_scheduler()
        &&
        self.wf_mem_closure()
        &&
        self.wf_pcid_closure()
        &&
        self.wf_endpoints()
        &&
        self.wf_ipc()
        &&
        self.wf_ioid_closure()
    }

    pub proof fn wf_ipc_derive_1(&self, thread_ptr:ThreadPtr)
        requires
            self.wf_ipc(),
            self.thread_ptrs@.contains(thread_ptr),
            self.get_thread(thread_ptr).callee.is_None(),
            self.get_thread(thread_ptr).caller.is_None(),
        ensures
            forall|_thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(_thread_ptr) && self.thread_perms@[_thread_ptr].view().value.get_Some_0().caller.is_Some() ==>
                self.thread_perms@[_thread_ptr].view().value.get_Some_0().caller.unwrap() != thread_ptr,

    {

    }
}
}

use vstd::prelude::*;
verus! {

use crate::define::*;
use crate::slinkedlist::spec_impl_u::*;
use crate::array_set::*;
use crate::quota::*;

pub struct Container {
    pub parent: Option<ContainerPtr>,
    pub parent_rev_ptr: Option<SLLIndex>,
    pub children: StaticLinkedList<ContainerPtr, CONTAINER_CHILD_LIST_LEN>,
    pub depth: usize,
    pub uppertree_seq: Ghost<Seq<ContainerPtr>>,
    pub subtree_set: Ghost<Set<ContainerPtr>>,
    pub root_process: Option<ProcPtr>,
    pub owned_procs: StaticLinkedList<ProcPtr, CONTAINER_PROC_LIST_LEN>,
    /// Right now we don't yet have linkedlist with unlimited length, 
    /// so we cannot kill an endpoint and release all the blocked threads.
    /// We we can do now to enable unconditional kill() is to add an invariant to
    /// ensure that each endpoint can ONLY be referenced by threads in the subtree of the container.
    /// So when we kill all the threads, all the endpoints are killed too. 
    pub owned_endpoints: Ghost<Set<EndpointPtr>>,
    pub owned_threads: Ghost<Set<ThreadPtr>>,
    // pub mem_quota: usize,
    // pub mem_quota_2m: usize,
    // pub mem_quota_1g: usize,
    // pub mem_used: usize,
    // pub mem_used_2m: usize,
    // pub mem_used_1g: usize,
    pub quota: Quota,
    pub owned_cpus: ArraySet<NUM_CPUS>,
    pub scheduler: StaticLinkedList<ThreadPtr, MAX_CONTAINER_SCHEDULER_LEN>,
    pub can_have_children: bool,
}

} // verus!

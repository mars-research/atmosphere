use vstd::prelude::*;
verus! {

use crate::define::*;
use vstd::simple_pptr::PointsTo;
use crate::trap::*;
use crate::array::Array;
use crate::process_manager::endpoint::*;
use crate::process_manager::process::*;
use crate::process_manager::container::*;
use crate::process_manager::thread::*;
use crate::process_manager::cpu::*;
use vstd::simple_pptr::PPtr;
use crate::process_manager::thread_util_t::*;
use crate::process_manager::proc_util_t::*;
use crate::process_manager::container_util_t::*;
use crate::process_manager::endpoint_util_t::*;
use crate::lemma::lemma_u::*;
use crate::lemma::lemma_t::*;
use crate::array_set::ArraySet;
use core::mem::MaybeUninit;
use crate::trap::Registers;
use crate::process_manager::container_tree::*;
use crate::process_manager::process_tree::*;
use crate::quota::*;

// use crate::process_manager::container_tree_spec_impl::*;
pub struct ProcessManager {
    pub root_container: ContainerPtr,
    pub container_perms: Tracked<Map<ContainerPtr, PointsTo<Container>>>,
    pub process_perms: Tracked<Map<ProcPtr, PointsTo<Process>>>,
    pub thread_perms: Tracked<Map<ThreadPtr, PointsTo<Thread>>>,
    pub endpoint_perms: Tracked<Map<EndpointPtr, PointsTo<Endpoint>>>,
    pub cpu_list: Array<Cpu, NUM_CPUS>,
}

//utils
impl ProcessManager {
    pub proof fn page_closure_inv(&self)
        requires
            self.wf(),
        ensures
            self.container_dom() + self.proc_dom() + self.thread_dom() + self.endpoint_dom()
                =~= self.page_closure(),
    {
    }

    pub open spec fn page_closure(&self) -> Set<PagePtr> {
        self.container_perms@.dom() + self.process_perms@.dom() + self.thread_perms@.dom()
            + self.endpoint_perms@.dom()
    }

    #[verifier(inline)]
    pub open spec fn container_dom(&self) -> Set<ContainerPtr> {
        self.container_perms@.dom()
    }

    #[verifier(inline)]
    pub open spec fn proc_dom(&self) -> Set<ProcPtr> {
        self.process_perms@.dom()
    }

    #[verifier(inline)]
    pub open spec fn thread_dom(&self) -> Set<ThreadPtr> {
        self.thread_perms@.dom()
    }

    #[verifier(inline)]
    pub open spec fn endpoint_dom(&self) -> Set<EndpointPtr> {
        self.endpoint_perms@.dom()
    }

    #[verifier(inline)]
    pub open spec fn spec_get_container(&self, c_ptr: ContainerPtr) -> &Container {
        &self.container_perms@[c_ptr].value()
    }

    #[verifier(when_used_as_spec(spec_get_container))]
    pub fn get_container(&self, container_ptr: ContainerPtr) -> (ret: &Container)
        requires
            self.container_perms_wf(),
            self.container_dom().contains(container_ptr),
        ensures
            self.get_container(container_ptr) == ret,
    {
        let tracked container_perm = self.container_perms.borrow().tracked_borrow(container_ptr);
        let container: &Container = PPtr::<Container>::from_usize(container_ptr).borrow(
            Tracked(container_perm),
        );
        container
    }

    #[verifier(inline)]
    pub open spec fn spec_get_proc(&self, proc_ptr: ProcPtr) -> &Process
        recommends
            self.proc_perms_wf(),
            self.proc_dom().contains(proc_ptr),
    {
        &self.process_perms@[proc_ptr].value()
    }

    #[verifier(when_used_as_spec(spec_get_proc))]
    pub fn get_proc(&self, proc_ptr: ProcPtr) -> (ret: &Process)
        requires
            self.proc_perms_wf(),
            self.process_fields_wf(),
            self.proc_dom().contains(proc_ptr),
        ensures
            ret =~= self.get_proc(proc_ptr),
            ret.owned_threads.wf(),
            self.wf() ==> self.container_dom().contains(ret.owning_container),
    {
        let tracked proc_perm = self.process_perms.borrow().tracked_borrow(proc_ptr);
        let proc: &Process = PPtr::<Process>::from_usize(proc_ptr).borrow(Tracked(proc_perm));
        proc
    }

    pub open spec fn spec_get_proc_by_thread_ptr(&self, thread_ptr: ThreadPtr) -> &Process
        recommends
            self.wf(),
            self.thread_perms@.dom().contains(thread_ptr),
    {
        &self.process_perms@[self.get_thread(thread_ptr).owning_proc].value()
    }

    #[verifier(when_used_as_spec(spec_get_proc_by_thread_ptr))]
    pub fn get_proc_by_thread_ptr(&self, thread_ptr: ThreadPtr) -> (ret: &Process)
        requires
            self.wf(),
            self.thread_perms@.dom().contains(thread_ptr),
        ensures
            ret =~= self.spec_get_proc_by_thread_ptr(thread_ptr),
    {
        let proc_ptr = self.get_thread(thread_ptr).owning_proc;
        let tracked proc_perm = self.process_perms.borrow().tracked_borrow(proc_ptr);
        let proc: &Process = PPtr::<Process>::from_usize(proc_ptr).borrow(Tracked(proc_perm));
        proc
    }

    #[verifier(inline)]
    pub open spec fn spec_get_thread(&self, thread_ptr: ThreadPtr) -> &Thread
        recommends
            self.threads_perms_wf(),
            self.thread_dom().contains(thread_ptr),
    {
        &self.thread_perms@[thread_ptr].value()
    }

    #[verifier(when_used_as_spec(spec_get_thread))]
    pub fn get_thread(&self, thread_ptr: ThreadPtr) -> (ret: &Thread)
        requires
            self.wf(),
            self.thread_dom().contains(thread_ptr),
        ensures
            ret == self.get_thread(thread_ptr),
            self.proc_dom().contains(ret.owning_proc),
            self.container_dom().contains(ret.owning_container),
            self.get_container(ret.owning_container).scheduler.wf(),
            self.get_container(ret.owning_container).owned_procs.wf(),
            self.get_container(ret.owning_container).children.wf(),
    {
        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
        let thread: &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));
        thread
    }

    #[verifier(inline)]
    pub open spec fn spec_get_cpu(&self, cpu_id: CpuId) -> &Cpu
        recommends
            self.wf(),
            0 <= cpu_id < NUM_CPUS,
    {
        &self.cpu_list@[cpu_id as int]
    }

    #[verifier(when_used_as_spec(spec_get_cpu))]
    pub fn get_cpu(&self, cpu_id: CpuId) -> (ret: &Cpu)
        requires
            self.wf(),
            0 <= cpu_id < NUM_CPUS,
        ensures
            ret == self.get_cpu(cpu_id),
    {
        self.cpu_list.get(cpu_id)
    }

    pub open spec fn spec_get_is_cpu_running(&self, cpu_i: CpuId) -> bool
        recommends
            self.wf(),
            0 <= cpu_i < NUM_CPUS,
    {
        self.cpu_list@[cpu_i as int].current_thread.is_Some()
    }

    #[verifier(when_used_as_spec(spec_get_is_cpu_running))]
    pub fn get_is_cpu_running(&self, cpu_i: CpuId) -> (ret: bool)
        requires
            self.wf(),
            0 <= cpu_i < NUM_CPUS,
        ensures
            ret == self.get_is_cpu_running(cpu_i),
    {
        self.cpu_list.get(cpu_i).current_thread.is_some()
    }

    // pub open spec fn spec_get_container(&self, container_ptr:ContainerPtr) -> &Container
    //     recommends
    //         self.wf(),
    //         self.container_dom().contains(container_ptr),
    // {
    //     self.get_container(container_ptr)
    // }
    // #[verifier(when_used_as_spec(spec_get_container))]
    // pub fn get_container(&self, container_ptr:ContainerPtr) -> (ret:&Container)
    //     requires
    //         self.wf(),
    //         self.container_dom().contains(container_ptr),
    //     ensures
    //         self.get_container(container_ptr) == ret,
    // {
    //     self.get_container(container_ptr)
    // }
    pub open spec fn spec_get_container_by_proc_ptr(&self, proc_ptr: ProcPtr) -> &Container
        recommends
            self.wf(),
            self.proc_dom().contains(proc_ptr),
    {
        self.get_container(self.get_proc(proc_ptr).owning_container)
    }

    #[verifier(when_used_as_spec(spec_get_container_by_proc_ptr))]
    pub fn get_container_by_proc_ptr(&self, proc_ptr: ProcPtr) -> (ret: &Container)
        requires
            self.wf(),
            self.proc_dom().contains(proc_ptr),
        ensures
            self.get_container_by_proc_ptr(proc_ptr) == ret,
            self.container_dom().contains(self.get_proc(proc_ptr).owning_container),
            self.get_container(self.get_proc(proc_ptr).owning_container) == ret,
            ret.scheduler.wf(),
    {
        let container_ptr = self.get_proc(proc_ptr).owning_container;
        let container = self.get_container(container_ptr);
        container
    }

    pub open spec fn spec_get_container_by_thread_ptr(&self, thread_ptr: ThreadPtr) -> &Container
        recommends
            self.wf(),
            self.thread_perms@.dom().contains(thread_ptr),
    {
        self.get_container(self.get_proc_by_thread_ptr(thread_ptr).owning_container)
    }

    #[verifier(when_used_as_spec(spec_get_container_by_thread_ptr))]
    pub fn get_container_by_thread_ptr(&self, thread_ptr: ThreadPtr) -> (ret: &Container)
        requires
            self.wf(),
            self.thread_perms@.dom().contains(thread_ptr),
        ensures
            self.get_container_by_thread_ptr(thread_ptr) == ret,
    {
        let container_ptr = self.get_proc_by_thread_ptr(thread_ptr).owning_container;
        let container = self.get_container(container_ptr);
        container
    }

    #[verifier(inline)]
    pub open spec fn spec_get_endpoint(&self, endpoint_ptr: EndpointPtr) -> &Endpoint
        recommends
            self.wf(),
            self.endpoint_perms@.dom().contains(endpoint_ptr),
    {
        &self.endpoint_perms@[endpoint_ptr].value()
    }

    #[verifier(when_used_as_spec(spec_get_endpoint))]
    pub fn get_endpoint(&self, endpoint_ptr: EndpointPtr) -> (ret: &Endpoint)
        requires
            self.wf(),
            self.endpoint_dom().contains(endpoint_ptr),
        ensures
            ret == self.get_endpoint(endpoint_ptr),
            ret.queue.wf(),
    {
        let tracked endpoint_perm = self.endpoint_perms.borrow().tracked_borrow(endpoint_ptr);
        let endpoint: &Endpoint = PPtr::<Endpoint>::from_usize(endpoint_ptr).borrow(
            Tracked(endpoint_perm),
        );
        endpoint
    }

    pub open spec fn spec_get_thread_ptr_by_cpu_id(&self, cpu_id: CpuId) -> (ret: Option<ThreadPtr>)
        recommends
            self.wf(),
            0 <= cpu_id < NUM_CPUS,
    {
        self.cpu_list@[cpu_id as int].current_thread
    }

    #[verifier(when_used_as_spec(spec_get_thread_ptr_by_cpu_id))]
    pub fn get_thread_ptr_by_cpu_id(&self, cpu_id: CpuId) -> (ret: Option<ThreadPtr>)
        requires
            self.wf(),
            0 <= cpu_id < NUM_CPUS,
        ensures
            ret == self.get_thread_ptr_by_cpu_id(cpu_id),
            self.get_is_cpu_running(cpu_id) == ret.is_Some(),
            ret.is_Some() ==> self.get_cpu(cpu_id).current_thread.is_Some()
                && self.thread_dom().contains(ret.unwrap()),
            self.get_thread_ptr_by_cpu_id(cpu_id) == ret,
            self.get_cpu(cpu_id).current_thread == ret,
    {
        self.cpu_list.get(cpu_id).current_thread
    }

    pub open spec fn spec_get_owning_proc_by_thread_ptr(&self, t_ptr: ThreadPtr) -> (ret: ProcPtr)
        recommends
            self.wf(),
            self.thread_dom().contains(t_ptr),
    {
        self.get_thread(t_ptr).owning_proc
    }

    #[verifier(when_used_as_spec(spec_get_owning_proc_by_thread_ptr))]
    pub fn get_owning_proc_by_thread_ptr(&self, t_ptr: ThreadPtr) -> (ret: ProcPtr)
        requires
            self.wf(),
            self.thread_dom().contains(t_ptr),
        ensures
            ret == self.get_owning_proc_by_thread_ptr(t_ptr),
            self.proc_dom().contains(ret),
            self.get_thread(t_ptr).owning_proc == ret,
    {
        self.get_thread(t_ptr).owning_proc
    }

    pub fn get_proc_ptr_by_cpu_id(&self, cpu_id: CpuId) -> (ret: Option<ProcPtr>)
        requires
            self.wf(),
            0 <= cpu_id < NUM_CPUS,
        ensures
            self.get_is_cpu_running(cpu_id) <==> ret.is_Some(),
            ret.is_Some() ==> self.get_is_cpu_running(cpu_id)
                && self.cpu_list@[cpu_id as int].current_thread.is_Some() && self.get_thread(
                self.cpu_list@[cpu_id as int].current_thread.unwrap(),
            ).owning_proc == ret.unwrap() && self.proc_dom().contains(ret.unwrap()),
            ret.is_None() ==> self.get_is_cpu_running(cpu_id) == false
                && self.cpu_list@[cpu_id as int].current_thread.is_None(),
    {
        let thread_ptr_op = self.cpu_list.get(cpu_id).current_thread;
        if thread_ptr_op.is_some() {
            return Some(self.get_thread(thread_ptr_op.unwrap()).owning_proc);
        } else {
            return None;
        }
    }

    pub open spec fn spec_get_endpoint_ptr_by_endpoint_idx(
        &self,
        thread_ptr: ThreadPtr,
        endpoint_index: EndpointIdx,
    ) -> Option<EndpointPtr>
        recommends
            self.wf(),
            self.thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
    {
        self.get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int]
    }

    #[verifier(when_used_as_spec(spec_get_endpoint_ptr_by_endpoint_idx))]
    pub fn get_endpoint_ptr_by_endpoint_idx(
        &self,
        thread_ptr: ThreadPtr,
        endpoint_index: EndpointIdx,
    ) -> (ret: Option<EndpointPtr>)
        requires
            self.wf(),
            self.thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        ensures
            ret == self.get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index),
            ret.is_Some() ==> self.endpoint_dom().contains(ret.unwrap()),
    {
        *self.get_thread(thread_ptr).endpoint_descriptors.get(endpoint_index)
    }

    pub open spec fn spec_get_endpoint_by_endpoint_idx(
        &self,
        thread_ptr: ThreadPtr,
        endpoint_index: EndpointIdx,
    ) -> Option<&Endpoint>
        recommends
            self.wf(),
            self.thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
    {
        if self.get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].is_None() {
            None
        } else {
            Some(
                &self.get_endpoint(
                    self.get_thread(
                        thread_ptr,
                    ).endpoint_descriptors@[endpoint_index as int].unwrap(),
                ),
            )
        }
    }

    #[verifier(when_used_as_spec(spec_get_endpoint_by_endpoint_idx))]
    pub fn get_endpoint_by_endpoint_idx(
        &self,
        thread_ptr: ThreadPtr,
        endpoint_index: EndpointIdx,
    ) -> (ret: Option<&Endpoint>)
        requires
            self.wf(),
            self.thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        ensures
            ret == self.get_endpoint_by_endpoint_idx(thread_ptr, endpoint_index),
    {
        if self.get_thread(thread_ptr).endpoint_descriptors.get(endpoint_index).is_none() {
            None
        } else {
            Some(
                &self.get_endpoint(
                    self.get_thread(thread_ptr).endpoint_descriptors.get(endpoint_index).unwrap(),
                ),
            )
        }
    }
    // pub open spec fn spec_get_thread_owns_endpoint(&self, thread_ptr:ThreadPtr, endpoint_ptr:EndpointPtr) -> bool{
    //     exists|i:int|
    //         #![trigger self.thread_perms@[thread_ptr].value().endpoint_descriptors@[i]]
    //         0 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS
    //         &&
    //         self.thread_perms@[thread_ptr].value().endpoint_descriptors@[i].is_Some() && self.thread_perms@[thread_ptr].value().endpoint_descriptors@[i].unwrap() == endpoint_ptr
    // }
    // pub fn get_thread_owns_endpoint(&self, thread_ptr:ThreadPtr, endpoint_ptr:EndpointPtr) -> (ret:bool)
    //     requires
    //         self.wf(),
    //         self.thread_dom().contains(thread_ptr),
    //     ensures
    //         ret == self.spec_get_thread_owns_endpoint(thread_ptr, endpoint_ptr),
    // {
    //     for index in 0..MAX_NUM_ENDPOINT_DESCRIPTORS
    //         invariant
    //             self.wf(),
    //             self.thread_dom().contains(thread_ptr),
    //             forall|i:int| #![trigger self.get_thread(thread_ptr).endpoint_descriptors@[i]] 0 <= i < index ==> self.get_thread(thread_ptr).endpoint_descriptors@[i].is_None() || self.get_thread(thread_ptr).endpoint_descriptors@[i].unwrap() != endpoint_ptr
    //     {
    //         if self.get_thread(thread_ptr).endpoint_descriptors.get(index).is_some(){
    //             if self.get_thread(thread_ptr).endpoint_descriptors.get(index).unwrap() == endpoint_ptr{
    //                 return true
    //             }
    //         }
    //     }
    //     return false
    // }

}

// //specs
impl ProcessManager {
    pub open spec fn container_perms_wf(&self) -> bool {
        &&& container_perms_wf(self.container_perms@)
    }

    pub open spec fn container_tree_wf(&self) -> bool {
        &&& container_tree_wf(self.root_container, self.container_perms@)
    }

    pub open spec fn proc_perms_wf(&self) -> bool {
        &&& proc_perms_wf(self.process_perms@)
    }

    #[verifier(inline)]
    pub open spec fn process_tree_wf(&self, container_ptr: ContainerPtr) -> bool
        recommends
            self.container_dom().contains(container_ptr),
            self.container_perms_wf(),
            self.get_container(container_ptr).root_process.is_Some(),
    {
        proc_tree_wf(
            self.get_container(container_ptr).root_process.unwrap(),
            self.get_container(container_ptr).owned_procs@.to_set(),
            self.process_perms@,
        )
    }

    pub open spec fn process_trees_wf(&self) -> bool
        recommends
            self.container_perms_wf(),
    {
        &&& forall|c_ptr: ContainerPtr|
            #![trigger self.process_tree_wf(c_ptr)]
            self.container_dom().contains(c_ptr) && self.get_container(c_ptr).root_process.is_Some()
                ==> self.process_tree_wf(c_ptr)
        &&& forall|c_ptr: ContainerPtr|
            #![trigger self.get_container(c_ptr).root_process, self.get_container(c_ptr).owned_procs]
            self.container_dom().contains(c_ptr) && self.get_container(c_ptr).root_process.is_None()
                ==> self.get_container(c_ptr).owned_procs@.len() == 0
    }

    pub open spec fn cpus_wf(&self) -> bool {
        &&& 
        self.cpu_list.wf()
        &&&
        forall|cpu_i:CpuId|
            // #![trigger self.cpu_list@[cpu_i as int]]
            #![trigger self.cpu_list@[cpu_i as int].active]
            #![trigger self.cpu_list@[cpu_i as int].current_thread]
            0 <= cpu_i < NUM_CPUS 
            && self.cpu_list@[cpu_i as int].active == false 
            ==> 
            self.cpu_list@[cpu_i as int].current_thread.is_None()

    }

    pub open spec fn container_cpu_wf(&self) -> bool {
        &&& forall|cpu_i: CpuId|
            #![trigger self.cpu_list@[cpu_i as int]]
            0 <= cpu_i < NUM_CPUS 
            ==> 
            self.container_dom().contains(self.cpu_list@[cpu_i as int].owning_container) 
            && 
            self.get_container(self.cpu_list@[cpu_i as int].owning_container).owned_cpus@.contains(cpu_i)
        &&&
        forall|c_ptr: ContainerPtr, cpu_i: CpuId|
            #![trigger self.get_container(c_ptr).owned_cpus@.contains(cpu_i)]
            #![trigger self.get_container(c_ptr).owned_cpus, self.cpu_list[cpu_i as int].owning_container]
            self.container_dom().contains(c_ptr) && self.get_container(c_ptr).owned_cpus@.contains(cpu_i)
            ==>
            0 <= cpu_i < NUM_CPUS
            &&
            self.cpu_list[cpu_i as int].owning_container == c_ptr 
    }

    pub open spec fn threads_cpu_wf(&self) -> bool {
        &&& forall|t_ptr: ThreadPtr|
            #![trigger self.thread_perms@[t_ptr].value().state]
            #![trigger self.thread_perms@[t_ptr].value().running_cpu]
            self.thread_perms@.dom().contains(t_ptr) 
            ==> (
                self.thread_perms@[t_ptr].value().running_cpu.is_Some()
                <==> 
                self.thread_perms@[t_ptr].value().state == ThreadState::RUNNING
            )
        &&& forall|t_ptr: ThreadPtr|
            #![trigger self.thread_perms@[t_ptr].value().running_cpu]
            self.thread_perms@.dom().contains(t_ptr)
                && self.thread_perms@[t_ptr].value().running_cpu.is_Some() 
                ==> 
                0 <= self.thread_perms@[t_ptr].value().running_cpu.unwrap() < NUM_CPUS
                && self.cpu_list@[self.thread_perms@[t_ptr].value().running_cpu.unwrap() as int].current_thread.is_Some()
                && self.cpu_list@[self.thread_perms@[t_ptr].value().running_cpu.unwrap() as int].current_thread.unwrap()
                    == t_ptr
                && self.cpu_list@[self.thread_perms@[t_ptr].value().running_cpu.unwrap() as int].owning_container
                    == self.thread_perms@[t_ptr].value().owning_container
        &&& forall|cpu_i: CpuId|
            #![trigger self.cpu_list@[cpu_i as int].current_thread]
            0 <= cpu_i < NUM_CPUS && self.cpu_list@[cpu_i as int].current_thread.is_Some()
                ==> 
                self.thread_perms@.dom().contains(self.cpu_list@[cpu_i as int].current_thread.unwrap())
                && self.thread_perms@[self.cpu_list@[cpu_i as int].current_thread.unwrap()].value().running_cpu.is_Some()
                && self.thread_perms@[self.cpu_list@[cpu_i as int].current_thread.unwrap()].value().running_cpu.unwrap() == cpu_i 
                && self.cpu_list@[cpu_i as int].owning_container
                == self.thread_perms@[self.cpu_list@[cpu_i as int].current_thread.unwrap()].value().owning_container
    }

    pub open spec fn memory_disjoint(&self) -> bool {
        &&& self.container_dom().disjoint(self.process_perms@.dom())
        &&& self.container_dom().disjoint(self.thread_perms@.dom())
        &&& self.container_dom().disjoint(self.endpoint_perms@.dom())
        &&& self.process_perms@.dom().disjoint(self.thread_perms@.dom())
        &&& self.process_perms@.dom().disjoint(self.endpoint_perms@.dom())
        &&& self.thread_perms@.dom().disjoint(self.endpoint_perms@.dom())
    }

    pub open spec fn container_fields_wf(&self) -> bool {
        &&& forall|c_ptr: ContainerPtr|
            // #![trigger self.container_dom().contains(c_ptr)]
        // #![trigger self.container_dom().contains(c_ptr), self.get_container(c_ptr).owned_cpus]
        // #![trigger self.container_dom().contains(c_ptr), self.get_container(c_ptr).scheduler]
        // #![trigger self.container_dom().contains(c_ptr), self.get_container(c_ptr).owned_procs]
        // #![trigger self.container_dom().contains(c_ptr), self.get_container(c_ptr).owned_endpoints]
        // #![trigger self.get_container(c_ptr)]
        // #![trigger self.container_dom().contains(c_ptr)]
        #![trigger self.get_container(c_ptr).owned_cpus.wf()]
        #![trigger self.get_container(c_ptr).scheduler.wf()]
        #![trigger self.get_container(c_ptr).owned_procs.wf()]
        // #![trigger self.get_container(c_ptr).owned_endpoints.wf()]
        #![trigger self.get_container(c_ptr).scheduler.unique()]
        #![trigger self.get_container(c_ptr).owned_procs.unique()]
        // #![trigger self.get_container(c_ptr).owned_endpoints.unique()]

            self.container_dom().contains(c_ptr) 
            ==> 
            self.get_container(c_ptr).owned_cpus.wf()
                && self.get_container(c_ptr).scheduler.wf() 
                && self.get_container(c_ptr).scheduler.unique()
                && self.get_container(c_ptr).owned_procs.wf()
                && self.get_container(c_ptr).owned_procs.unique()
    }

    pub open spec fn process_fields_wf(&self) -> bool {
        &&& forall|p_ptr: ProcPtr|
            #![trigger self.get_proc(p_ptr).owned_threads.wf()]
            #![trigger self.get_proc(p_ptr).owned_threads.unique()]
            self.proc_dom().contains(p_ptr)
            ==> self.get_proc(p_ptr).owned_threads.wf()
                && self.get_proc(p_ptr).owned_threads.unique()
    }

    pub open spec fn processes_container_wf(&self) -> bool {
        &&& forall|c_ptr: ContainerPtr|
            #![trigger self.get_container(c_ptr).owned_procs]
            self.container_dom().contains(c_ptr) 
            ==> 
            self.get_container(c_ptr).owned_procs@.to_set().subset_of(self.process_perms@.dom())
        &&& forall|c_ptr: ContainerPtr, child_p_ptr: ProcPtr|
         // #![trigger self.container_dom().contains(c_ptr), self.process_perms@[child_p_ptr].value().owning_container]

            #![trigger self.get_container(c_ptr).owned_procs@.contains(child_p_ptr)]
            self.container_dom().contains(c_ptr) && self.get_container(c_ptr).owned_procs@.contains(child_p_ptr) 
            ==> 
            self.process_perms@[child_p_ptr].value().owning_container == c_ptr
        &&& forall|p_ptr: ProcPtr|
            #![trigger self.process_perms@[p_ptr].value().owning_container]
        // #![trigger self.get_container(self.process_perms@[p_ptr].value().owning_container).owned_procs]
            self.process_perms@.dom().contains(p_ptr) 
            ==> 
            self.container_dom().contains(self.process_perms@[p_ptr].value().owning_container) 
            && self.get_container(self.process_perms@[p_ptr].value().owning_container).owned_procs@.contains(p_ptr) 
            && self.get_container(self.process_perms@[p_ptr].value().owning_container).owned_procs.get_node_ref(p_ptr) 
                == self.process_perms@[p_ptr].value().rev_ptr
    }

    pub open spec fn threads_process_wf(&self) -> bool {
        &&& forall|p_ptr: ProcPtr, child_t_ptr: ThreadPtr|
            #![trigger self.process_perms@.dom().contains(p_ptr), self.thread_perms@[child_t_ptr].value().owning_proc]
            #![trigger self.process_perms@[p_ptr].value().owned_threads@.contains(child_t_ptr)]
            self.process_perms@.dom().contains(p_ptr)
                && self.process_perms@[p_ptr].value().owned_threads@.contains(child_t_ptr)
            ==> self.thread_perms@.dom().contains(child_t_ptr)
                && self.thread_perms@[child_t_ptr].value().owning_proc == p_ptr
        &&& forall|t_ptr: ThreadPtr|
            #![trigger self.thread_perms@[t_ptr].value().owning_proc]
            #![trigger self.process_perms@[self.thread_perms@[t_ptr].value().owning_proc].value().owned_threads]
            self.thread_perms@.dom().contains(t_ptr) 
            ==> 
            self.container_dom().contains(self.thread_perms@[t_ptr].value().owning_container) 
            && self.process_perms@.dom().contains(self.thread_perms@[t_ptr].value().owning_proc)
            && self.process_perms@[self.thread_perms@[t_ptr].value().owning_proc].value().owned_threads@.contains(t_ptr)
            && self.process_perms@[self.thread_perms@[t_ptr].value().owning_proc].value().owned_threads.get_node_ref(t_ptr)
                == self.thread_perms@[t_ptr].value().proc_rev_ptr
            && self.process_perms@[self.thread_perms@[t_ptr].value().owning_proc].value().owning_container
                == self.thread_perms@[t_ptr].value().owning_container
    }

    pub open spec fn threads_perms_wf(&self) -> bool {
        &&& forall|t_ptr: ThreadPtr|
         // #![trigger self.thread_perms@[t_ptr].is_init()]
        // #![trigger self.thread_perms@[t_ptr].addr()]
        // #![trigger self.thread_perms@[t_ptr].value().endpoint_descriptors.wf()]
        // #![trigger self.thread_perms@[t_ptr].value().ipc_payload]

            #![trigger self.thread_perms@.dom().contains(t_ptr)]
            self.thread_perms@.dom().contains(t_ptr) ==> 
                self.thread_perms@[t_ptr].is_init()
                && self.thread_perms@[t_ptr].addr() == t_ptr
                && self.thread_perms@[t_ptr].value().endpoint_descriptors.wf() 
                && (self.thread_perms@[t_ptr].value().ipc_payload.get_payload_as_va_range().is_Some()
                    ==> self.thread_perms@[t_ptr].value().ipc_payload.get_payload_as_va_range().unwrap().wf())
    }

    pub open spec fn threads_container_wf(&self) -> bool {
        &&& forall|c_ptr: ContainerPtr|
         // #![trigger self.container_dom().contains(c_ptr)]

            #![trigger self.get_container(c_ptr).owned_threads]
            self.container_dom().contains(c_ptr) 
            ==> 
            self.get_container(c_ptr).owned_threads@.subset_of(self.thread_perms@.dom())
        &&& forall|c_ptr: ContainerPtr, t_ptr: ThreadPtr|
            #![trigger  self.get_container(c_ptr).owned_threads, self.get_thread(t_ptr)]
            self.container_dom().contains(c_ptr) && self.get_container(c_ptr).owned_threads@.contains(t_ptr) 
            ==> 
            self.get_thread(t_ptr).owning_container == c_ptr
        &&& forall|t_ptr: ThreadPtr|
            #![trigger self.container_dom().contains(self.thread_perms@[t_ptr].value().owning_container)]
            self.thread_perms@.dom().contains(t_ptr) 
            ==> 
            self.container_dom().contains(self.thread_perms@[t_ptr].value().owning_container) 
            && self.get_container(self.thread_perms@[t_ptr].value().owning_container).owned_threads@.contains(t_ptr)
    }

    pub open spec fn endpoint_perms_wf(&self) -> bool {
        &&& forall|e_ptr: EndpointPtr|
            #![trigger self.endpoint_perms@.dom().contains(e_ptr) ]
            self.endpoint_perms@.dom().contains(e_ptr) ==> 
                self.endpoint_perms@[e_ptr].is_init()
                && self.endpoint_perms@[e_ptr].addr() == e_ptr
                && self.endpoint_perms@[e_ptr].value().queue.wf()
                && self.endpoint_perms@[e_ptr].value().queue.unique()
                && self.endpoint_perms@[e_ptr].value().owning_threads@.finite()
                && self.endpoint_perms@[e_ptr].value().rf_counter
                == self.endpoint_perms@[e_ptr].value().owning_threads@.len()
        // &&
        // self.endpoint_perms@[e_ptr].value().owning_threads@.subset_of(self.thread_perms@.dom())

    }

    pub open spec fn threads_endpoint_descriptors_wf(&self) -> bool {
        &&& forall|t_ptr: ThreadPtr, e_idx: EndpointIdx|
            #![trigger self.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int]]
            self.thread_perms@.dom().contains(t_ptr) 
            && 0 <= e_idx < MAX_NUM_ENDPOINT_DESCRIPTORS
            && self.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int].is_Some()
            ==> 
            self.endpoint_perms@.dom().contains(self.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int].unwrap())
            && self.endpoint_perms@[self.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int].unwrap()].value().owning_threads@.contains((t_ptr, e_idx))
        &&& forall|e_ptr: EndpointPtr, t_ptr: ThreadPtr, e_idx: EndpointIdx|
            #![trigger self.endpoint_perms@[e_ptr].value().owning_threads@.contains((t_ptr, e_idx))]
            self.endpoint_perms@.dom().contains(e_ptr)
                && self.endpoint_perms@[e_ptr].value().owning_threads@.contains((t_ptr, e_idx))
                ==> 0 <= e_idx < MAX_NUM_ENDPOINT_DESCRIPTORS && self.thread_perms@.dom().contains(
                t_ptr,
            ) && self.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int].is_Some()
                && self.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int].unwrap()
                == e_ptr
    }

        pub open spec fn endpoints_queue_wf(&self) -> bool {
        &&& forall|t_ptr: ThreadPtr|
            #![trigger self.thread_perms@[t_ptr].value().state]
            #![trigger self.thread_perms@[t_ptr].value().blocking_endpoint_ptr]
            #![trigger self.thread_perms@[t_ptr].value().endpoint_rev_ptr]
            self.thread_perms@.dom().contains(t_ptr) && self.thread_perms@[t_ptr].value().state
                == ThreadState::BLOCKED
                ==> self.thread_perms@[t_ptr].value().blocking_endpoint_ptr.is_Some()
                && self.thread_perms@[t_ptr].value().blocking_endpoint_index.is_Some() && 0
                <= self.thread_perms@[t_ptr].value().blocking_endpoint_index.unwrap()
                < MAX_NUM_ENDPOINT_DESCRIPTORS
                && self.thread_perms@[t_ptr].value().endpoint_descriptors@[self.thread_perms@[t_ptr].value().blocking_endpoint_index.unwrap() as int]
                == Some(self.thread_perms@[t_ptr].value().blocking_endpoint_ptr.unwrap())
                && self.thread_perms@[t_ptr].value().endpoint_rev_ptr.is_Some()
                && self.endpoint_perms@.dom().contains(
                self.thread_perms@[t_ptr].value().blocking_endpoint_ptr.unwrap(),
            )
                && self.endpoint_perms@[self.thread_perms@[t_ptr].value().blocking_endpoint_ptr.unwrap()].value().queue@.contains(
            t_ptr)
                && self.endpoint_perms@[self.thread_perms@[t_ptr].value().blocking_endpoint_ptr.unwrap()].value().queue.get_node_ref(t_ptr) 
                == self.thread_perms@[t_ptr].value().endpoint_rev_ptr.unwrap()
        &&& forall|e_ptr: EndpointPtr, t_ptr: ThreadPtr|
            #![trigger self.endpoint_perms@[e_ptr].value().queue@.contains(t_ptr), ]
            self.endpoint_perms@.dom().contains(e_ptr) && self.endpoint_perms@[e_ptr].value().queue@.contains(t_ptr)
                ==> 
                self.thread_perms@.dom().contains(t_ptr)
                && self.thread_perms@[t_ptr].value().blocking_endpoint_ptr
                == Some(e_ptr)
                && self.thread_perms@[t_ptr].value().state
                == ThreadState::BLOCKED
    }

    pub open spec fn endpoints_container_wf(&self) -> bool {
        &&& forall|c_ptr: ContainerPtr, child_e_ptr: EndpointPtr|
            #![trigger self.get_container(c_ptr).owned_endpoints@.contains(child_e_ptr)]
            self.container_dom().contains(c_ptr) && self.get_container(
                c_ptr,
            ).owned_endpoints@.contains(child_e_ptr) ==> self.endpoint_perms@.dom().contains(
                child_e_ptr,
            ) && self.endpoint_perms@[child_e_ptr].value().owning_container == c_ptr
        &&& forall|e_ptr: EndpointPtr|
            #![trigger self.endpoint_perms@[e_ptr].value().owning_container]
            self.endpoint_perms@.dom().contains(e_ptr) ==> self.container_dom().contains(
                self.endpoint_perms@[e_ptr].value().owning_container,
            ) && self.get_container(
                self.endpoint_perms@[e_ptr].value().owning_container,
            ).owned_endpoints@.contains(e_ptr) 
    }

    pub open spec fn endpoints_within_subtree(&self) -> bool{
        &&&
        forall|e_ptr:EndpointPtr, t_ptr:ThreadPtr, edp_idx:EndpointIdx|
            #![trigger self.endpoint_perms@[e_ptr].value().owning_threads@.contains((t_ptr, edp_idx))]
            self.endpoint_perms@.dom().contains(e_ptr) && self.endpoint_perms@[e_ptr].value().owning_threads@.contains((t_ptr, edp_idx)) 
            ==> 
            (
                self.thread_perms@[t_ptr].value().owning_container == self.endpoint_perms@[e_ptr].value().owning_container
                ||
                self.container_perms@[self.endpoint_perms@[e_ptr].value().owning_container].value().subtree_set@.contains(self.thread_perms@[t_ptr].value().owning_container)
            )
    }

    pub open spec fn schedulers_wf(&self) -> bool {
        &&& forall|t_ptr: ThreadPtr|
         // #![trigger self.thread_perms@[t_ptr].value().state]

            #![trigger self.thread_perms@[t_ptr].value().scheduler_rev_ptr]
            self.thread_perms@.dom().contains(t_ptr)
            && self.thread_perms@[t_ptr].value().state == ThreadState::SCHEDULED 
            ==> 
            self.get_container(self.thread_perms@[t_ptr].value().owning_container).scheduler@.contains(t_ptr)
            && self.thread_perms@[t_ptr].value().scheduler_rev_ptr.is_Some()
            && self.get_container(self.thread_perms@[t_ptr].value().owning_container).scheduler.get_node_ref(t_ptr) 
                == self.thread_perms@[t_ptr].value().scheduler_rev_ptr.unwrap()
        &&& forall|c_ptr: ContainerPtr, t_ptr: ThreadPtr|
            #![trigger self.get_container(c_ptr).scheduler@.contains(t_ptr)]
            #![trigger self.container_dom().contains(c_ptr), self.thread_perms@[t_ptr].value().owning_container]
            #![trigger self.container_dom().contains(c_ptr), self.thread_perms@[t_ptr].value().state]
            self.container_dom().contains(c_ptr) 
            && self.get_container(c_ptr).scheduler@.contains(t_ptr) 
            ==> 
            self.thread_perms@.dom().contains(t_ptr)
            && self.thread_perms@[t_ptr].value().owning_container == c_ptr
            && self.thread_perms@[t_ptr].value().state == ThreadState::SCHEDULED
    }

    pub open spec fn pcid_ioid_wf(&self) -> bool {
        &&& forall|p_ptr_i: ProcPtr, p_ptr_j: ProcPtr|
            // #![trigger self.process_perms@.dom().contains(p_ptr_i), self.process_perms@.dom().contains(p_ptr_j), self.process_perms@[p_ptr_i].value().pcid, self.process_perms@[p_ptr_j].value().pcid]
             #![trigger self.process_perms@[p_ptr_i].value().pcid, self.process_perms@[p_ptr_j].value().pcid]
            self.process_perms@.dom().contains(p_ptr_i) 
            && self.process_perms@.dom().contains(p_ptr_j) 
            && p_ptr_i != p_ptr_j 
            ==> self.process_perms@[p_ptr_i].value().pcid != self.process_perms@[p_ptr_j].value().pcid
        &&& forall|p_ptr_i: ProcPtr, p_ptr_j: ProcPtr|
            // #![trigger self.process_perms@.dom().contains(p_ptr_i), self.process_perms@.dom().contains(p_ptr_j), self.process_perms@[p_ptr_i].value().ioid, self.process_perms@[p_ptr_j].value().ioid]
            #![trigger self.process_perms@[p_ptr_i].value().ioid, self.process_perms@[p_ptr_j].value().ioid]
            self.process_perms@.dom().contains(p_ptr_i) 
            && self.process_perms@.dom().contains(p_ptr_j) 
            && p_ptr_i != p_ptr_j 
            && self.process_perms@[p_ptr_i].value().ioid.is_Some()
            && self.process_perms@[p_ptr_j].value().ioid.is_Some()
            ==> 
            self.process_perms@[p_ptr_i].value().ioid.unwrap() != self.process_perms@[p_ptr_j].value().ioid.unwrap()
    }

    pub closed spec fn internal_wf(&self) -> bool {
        &&& self.cpus_wf()
        &&& self.container_cpu_wf()
        &&& self.memory_disjoint()
        &&& self.processes_container_wf()
        &&& self.threads_process_wf()
        &&& self.threads_endpoint_descriptors_wf()
        &&& self.endpoints_queue_wf()
        &&& self.endpoints_container_wf()
        &&& self.schedulers_wf()
        &&& self.pcid_ioid_wf()
        &&& self.threads_cpu_wf()
        &&& self.threads_container_wf()
        &&& self.container_tree_wf()
        &&& self.process_trees_wf()
        &&& self.endpoints_within_subtree()
    }

    pub broadcast proof fn reveal_wf_to_cpus_wf(&self) 
        ensures
            #[trigger] self.internal_wf() ==> self.cpus_wf()
    {}

    pub broadcast proof fn reveal_wf_to_container_cpu_wf(&self) 
        ensures
            #[trigger] self.internal_wf() ==> self.container_cpu_wf()
    {}

    pub broadcast proof fn reveal_wf_to_memory_disjoint(&self) 
        ensures
            #[trigger] self.internal_wf() ==> self.memory_disjoint()
    {}

    pub broadcast proof fn reveal_wf_to_processes_container_wf(&self) 
        ensures
            #[trigger] self.internal_wf() ==> self.processes_container_wf()
    {}

    pub broadcast proof fn reveal_wf_to_threads_process_wf(&self) 
        ensures
            #[trigger] self.internal_wf() ==> self.threads_process_wf()
    {}

    pub broadcast proof fn reveal_wf_to_threads_endpoint_descriptors_wf(&self) 
        ensures
            #[trigger] self.internal_wf() ==> self.threads_endpoint_descriptors_wf()
    {}

    pub broadcast proof fn reveal_wf_to_endpoints_queue_wf(&self) 
        ensures
            #[trigger] self.internal_wf() ==> self.endpoints_queue_wf()
    {}

    pub broadcast proof fn reveal_wf_to_endpoints_container_wf(&self) 
        ensures
            #[trigger] self.internal_wf() ==> self.endpoints_container_wf()
    {}

    pub broadcast proof fn reveal_wf_to_schedulers_wf(&self) 
        ensures
            #[trigger] self.internal_wf() ==> self.schedulers_wf()
    {}

    pub broadcast proof fn reveal_wf_to_pcid_ioid_wf(&self) 
        ensures
            #[trigger] self.internal_wf() ==> self.pcid_ioid_wf()
    {}

    pub broadcast proof fn reveal_wf_to_threads_cpu_wf(&self) 
        ensures
            #[trigger] self.internal_wf() ==> self.threads_cpu_wf()
    {}

    pub broadcast proof fn reveal_wf_to_threads_container_wf(&self) 
        ensures
            #[trigger] self.internal_wf() ==> self.threads_container_wf()
    {}

    pub broadcast proof fn reveal_wf_to_container_tree_wf(&self) 
        ensures
            #[trigger] self.internal_wf() ==> self.container_tree_wf()
    {}

    pub broadcast proof fn reveal_wf_to_process_trees_wf(&self) 
        ensures
            #[trigger] self.internal_wf() ==> self.process_trees_wf()
    {}

    pub broadcast proof fn reveal_wf_to_endpoints_within_subtree(&self) 
        ensures
            #[trigger] self.internal_wf() ==> self.endpoints_within_subtree()
    {}

    pub broadcast proof fn reveal_specs_to_wf(&self)
        ensures
            #[trigger] self.internal_wf() <== {
                &&& self.cpus_wf()
                &&& self.container_cpu_wf()
                &&& self.memory_disjoint()
                &&& self.processes_container_wf()
                &&& self.threads_process_wf()
                &&& self.threads_endpoint_descriptors_wf()
                &&& self.endpoints_queue_wf()
                &&& self.endpoints_container_wf()
                &&& self.schedulers_wf()
                &&& self.pcid_ioid_wf()
                &&& self.threads_cpu_wf()
                &&& self.threads_container_wf()
                &&& self.container_tree_wf()
                &&& self.process_trees_wf()        
                &&& self.endpoints_within_subtree()
            },
    {}

    pub broadcast proof fn reveal_process_manager_wf(&self)
        ensures
            #[trigger] self.internal_wf() <==> {
                &&& self.cpus_wf()
                &&& self.container_cpu_wf()
                &&& self.memory_disjoint()
                &&& self.processes_container_wf()
                &&& self.threads_process_wf()
                &&& self.threads_endpoint_descriptors_wf()
                &&& self.endpoints_queue_wf()
                &&& self.endpoints_container_wf()
                &&& self.schedulers_wf()
                &&& self.pcid_ioid_wf()
                &&& self.threads_cpu_wf()
                &&& self.threads_container_wf()
                &&& self.container_tree_wf()
                &&& self.process_trees_wf()        
                &&& self.endpoints_within_subtree()
            },
    {}

    pub open spec fn wf(&self) -> bool {
        &&& self.container_perms_wf()
        &&& self.proc_perms_wf()
        &&& self.threads_perms_wf()
        &&& self.endpoint_perms_wf()
        &&& self.container_fields_wf()
        &&& self.process_fields_wf()
        &&& self.internal_wf()
    }
}

//proofs
impl ProcessManager {
    pub proof fn container_thread_inv_1(&self)
        requires
            self.wf(),
        ensures
            forall|c_ptr: ContainerPtr, t_ptr: ThreadPtr|
                #![auto]
                self.container_dom().contains(c_ptr) && self.thread_dom().contains(t_ptr)
                    && self.get_container(c_ptr).owned_threads@.contains(t_ptr) == false
                    ==> self.get_thread(t_ptr).owning_container != c_ptr,
    {
    }

    pub proof fn proc_thread_inv_1(&self)
        requires
            self.wf(),
        ensures
            forall|p_ptr: ProcPtr, t_ptr: ThreadPtr|
                #![auto]
                self.proc_dom().contains(p_ptr) && self.thread_dom().contains(t_ptr)
                    && self.get_proc(p_ptr).owned_threads@.contains(t_ptr) == false
                    ==> self.get_thread(t_ptr).owning_proc != p_ptr,
    {
    }

    pub proof fn thread_inv(&self)
        requires
            self.wf(),
        ensures
            forall|t_ptr: ThreadPtr|
                #![trigger self.thread_dom().contains(t_ptr)]
                #![trigger self.get_thread(t_ptr).owning_container]
                #![trigger self.get_thread(t_ptr).owning_proc]
                self.thread_dom().contains(t_ptr) ==> self.container_dom().contains(
                    self.get_thread(t_ptr).owning_container,
                ) && self.get_container(
                    self.get_thread(t_ptr).owning_container,
                ).owned_threads@.contains(t_ptr) && self.get_container(
                    self.get_thread(t_ptr).owning_container,
                ).owned_procs@.contains(self.get_thread(t_ptr).owning_proc)
                    && self.proc_dom().contains(self.get_thread(t_ptr).owning_proc)
                    && self.get_thread(t_ptr).endpoint_descriptors.wf() && (self.get_thread(
                    t_ptr,
                ).ipc_payload.get_payload_as_va_range().is_Some() ==> self.get_thread(
                    t_ptr,
                ).ipc_payload.get_payload_as_va_range().unwrap().wf()) && (forall|i: int|
                    #![auto]
                    0 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS && self.get_thread(
                        t_ptr,
                    ).endpoint_descriptors@[i].is_Some() ==> self.endpoint_dom().contains(
                        self.get_thread(t_ptr).endpoint_descriptors@[i].unwrap(),
                    )) && self.get_proc(self.get_thread(t_ptr).owning_proc).owning_container
                    == self.get_thread(t_ptr).owning_container && (self.get_thread(t_ptr).state
                    == ThreadState::BLOCKED ==> self.get_thread(
                    t_ptr,
                ).blocking_endpoint_ptr.is_Some() && self.endpoint_dom().contains(
                    self.get_thread(t_ptr).blocking_endpoint_ptr.unwrap(),
                )),
    {
    }

    pub proof fn process_inv(&self)
        requires
            self.wf(),
        ensures
            forall|p_ptr: ProcPtr|
                #![trigger self.proc_dom().contains(p_ptr)]
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) ==> self.container_dom().contains(
                    self.get_proc(p_ptr).owning_container,
                ) && self.get_proc(p_ptr).children.wf(),
    {
    }

    pub proof fn container_subtree_inv(&self)
        requires
            self.wf(),
        ensures
            forall|c_ptr: ContainerPtr|
                #![trigger self.container_dom().contains(c_ptr)]
                #![trigger self.get_container(c_ptr)]
                self.container_dom().contains(c_ptr) ==> self.get_container(
                    c_ptr,
                ).subtree_set@.subset_of(self.container_dom()) && self.get_container(
                    c_ptr,
                ).subtree_set@.contains(c_ptr) == false,
    {
        container_subtree_inv(self.root_container, self.container_perms@)
    }

    pub proof fn container_inv(&self)
        requires
            self.wf(),
        ensures
            forall|c_ptr: ContainerPtr|
                #![trigger self.container_dom().contains(c_ptr)]
                #![trigger self.get_container(c_ptr).owned_cpus.wf()]
                #![trigger self.get_container(c_ptr).scheduler.wf()]
                self.container_dom().contains(c_ptr) ==> self.get_container(c_ptr).owned_cpus.wf()
                    && self.get_container(c_ptr).scheduler.wf(),
            forall|c_ptr: ContainerPtr, p_ptr: ProcPtr|
                #![auto]
                self.container_dom().contains(c_ptr) && self.get_container(
                    c_ptr,
                ).owned_procs@.contains(p_ptr) ==> self.proc_dom().contains(p_ptr),
            forall|c_ptr: ContainerPtr, t_ptr: ThreadPtr|
                #![auto]
                self.container_dom().contains(c_ptr) && self.get_container(
                    c_ptr,
                ).owned_threads@.contains(t_ptr) ==> self.thread_dom().contains(t_ptr),
            forall|c_ptr_i: ContainerPtr, c_ptr_j: ContainerPtr, t_ptr: ThreadPtr|
                #![auto]
                c_ptr_i != c_ptr_j && self.container_dom().contains(c_ptr_i)
                    && self.container_dom().contains(c_ptr_j) && self.get_container(
                    c_ptr_i,
                ).owned_threads@.contains(t_ptr) ==> self.get_container(
                    c_ptr_j,
                ).owned_threads@.contains(t_ptr) == false,
    {
    }

    pub proof fn endpoint_inv(&self)
        requires
            self.wf(),
        ensures
            forall|e_ptr: EndpointPtr|
                #![trigger self.endpoint_dom().contains(e_ptr)]
                #![trigger self.get_endpoint(e_ptr).queue.wf()]
                self.endpoint_dom().contains(e_ptr) ==> self.get_endpoint(e_ptr).queue.wf(),
            forall|e_ptr: EndpointPtr, i: int|
                #![trigger self.get_endpoint(e_ptr).queue@[i]]
                self.endpoint_dom().contains(e_ptr) && 0 <= i < self.get_endpoint(e_ptr).queue.len()
                    ==> self.thread_dom().contains(self.get_endpoint(e_ptr).queue@[i])
                    && self.get_thread(self.get_endpoint(e_ptr).queue@[i]).state
                    == ThreadState::BLOCKED,
    {
        assert(
            forall|e_ptr: EndpointPtr, i: int|
                #![trigger self.get_endpoint(e_ptr).queue@[i]]
                self.endpoint_dom().contains(e_ptr) && 0 <= i < self.get_endpoint(e_ptr).queue.len()
                ==> 
                self.get_endpoint(e_ptr).queue@.contains(self.get_endpoint(e_ptr).queue@[i])
        );
    }

    pub proof fn container_owned_procs_disjoint_inv(&self)
        requires
            self.wf(),
        ensures
            forall|c_ptr_i: ContainerPtr, c_ptr_j: ContainerPtr|
                #![trigger  self.get_container(c_ptr_i).owned_procs, self.get_container(c_ptr_j).owned_procs]
                self.container_dom().contains(c_ptr_i) && self.container_dom().contains(c_ptr_j)
                    && c_ptr_i != c_ptr_j ==> self.get_container(c_ptr_i).owned_procs@.disjoint(
                    self.get_container(c_ptr_j).owned_procs@,
                ),
    {
        assert(forall|c_ptr_i: ContainerPtr, i: int, c_ptr_j: ContainerPtr, j: int|
            #![auto]
            self.container_dom().contains(c_ptr_i) && self.container_dom().contains(c_ptr_j)
                && c_ptr_i != c_ptr_j && 0 <= i < self.get_container(c_ptr_i).owned_procs@.len()
                && 0 <= j < self.get_container(c_ptr_j).owned_procs@.len() ==> self.get_container(
                c_ptr_i,
            ).owned_procs@.contains(self.get_container(c_ptr_i).owned_procs@[i])
                && self.get_container(c_ptr_j).owned_procs@.contains(
                self.get_container(c_ptr_j).owned_procs@[j],
            ) && self.get_proc(self.get_container(c_ptr_i).owned_procs@[i]).owning_container
                == c_ptr_i && self.get_proc(
                self.get_container(c_ptr_j).owned_procs@[j],
            ).owning_container == c_ptr_j);
    }

    pub proof fn container_owned_threads_disjoint_inv(&self)
        requires
            self.wf(),
        ensures
            forall|c_ptr_i: ContainerPtr, c_ptr_j: ContainerPtr|
                #![trigger  self.get_container(c_ptr_i), self.get_container(c_ptr_j)]
                self.container_dom().contains(c_ptr_i) && self.container_dom().contains(c_ptr_j)
                    && c_ptr_i != c_ptr_j ==> self.get_container(c_ptr_i).owned_threads@.disjoint(
                    self.get_container(c_ptr_j).owned_threads@,
                ),
    {
    }

    pub proof fn proc_owned_threads_disjoint_inv(&self)
        requires
            self.wf(),
        ensures
            forall|p_ptr_i: ProcPtr, p_ptr_j: ProcPtr|
                #![trigger  self.get_proc(p_ptr_i).owned_threads, self.get_proc(p_ptr_j).owned_threads]
                self.proc_dom().contains(p_ptr_i) && self.proc_dom().contains(p_ptr_j)
                    && p_ptr_i != p_ptr_j ==> self.get_proc(p_ptr_i).owned_threads@.disjoint(
                    self.get_proc(p_ptr_j).owned_threads@,
                ),
    {
        admit();
    }

    pub proof fn container_subtree_disjoint_inv(&self)
        requires
            self.wf(),
        ensures
            forall|c_ptr_i: ContainerPtr, c_ptr_j: ContainerPtr|
                #![trigger  self.get_container(c_ptr_i), self.get_container(c_ptr_j)]
                #![trigger  self.get_container(c_ptr_i).subtree_set@.insert(c_ptr_i), self.get_container(c_ptr_j).subtree_set@.insert(c_ptr_j)]
                self.container_dom().contains(c_ptr_i) && self.container_dom().contains(c_ptr_j)
                    && c_ptr_i != c_ptr_j && self.get_container(c_ptr_i).depth
                    == self.get_container(c_ptr_j).depth ==> self.get_container(
                    c_ptr_i,
                ).subtree_set@.disjoint(self.get_container(c_ptr_j).subtree_set@)
                    && self.get_container(c_ptr_i).subtree_set@.contains(c_ptr_j) == false
                    && self.get_container(c_ptr_j).subtree_set@.contains(c_ptr_i) == false
                    && self.get_container(c_ptr_i).subtree_set@.insert(c_ptr_i).disjoint(
                    self.get_container(c_ptr_j).subtree_set@.insert(c_ptr_j),
                ),
    {
        container_subtree_disjoint_inv(self.root_container, self.container_perms@);
    }

    pub proof fn cpu_inv(&self)
        requires
            self.wf(),
        ensures
            self.cpu_list.wf(),
            forall|cpu_i: CpuId|
                #![auto]
                0 <= cpu_i < NUM_CPUS ==> self.container_dom().contains(
                    self.cpu_list@[cpu_i as int].owning_container,
                ) && (self.cpu_list@[cpu_i as int].current_thread.is_Some()
                    ==> self.thread_dom().contains(
                    self.cpu_list@[cpu_i as int].current_thread.unwrap(),
                )),
    {
    }

    pub proof fn pcid_unique(&self, proc_ptr: ProcPtr)
        requires
            self.wf(),
            self.proc_dom().contains(proc_ptr),
        ensures
            forall|p_ptr: ProcPtr|
                #![auto]
                self.proc_dom().contains(p_ptr) && proc_ptr != p_ptr ==> self.get_proc(p_ptr).pcid
                    != self.get_proc(proc_ptr).pcid,
    {
    }

    pub proof fn ioid_unique(&self, proc_ptr: ProcPtr)
        requires
            self.wf(),
            self.proc_dom().contains(proc_ptr),
            self.get_proc(proc_ptr).ioid.is_Some(),
        ensures
            forall|p_ptr: ProcPtr|
                #![auto]
                self.proc_dom().contains(p_ptr) && proc_ptr != p_ptr && self.get_proc(
                    p_ptr,
                ).ioid.is_Some() ==> self.get_proc(p_ptr).ioid.unwrap() != self.get_proc(
                    proc_ptr,
                ).ioid.unwrap(),
    {
    }

    pub proof fn wf_imply_proc_to_unique_pcid(&self)
        requires
            self.wf(),
        ensures
            forall|p_ptr_i: ProcPtr, p_ptr_j: ProcPtr|
                #![trigger self.get_proc(p_ptr_i).pcid, self.get_proc(p_ptr_j).pcid]
                self.proc_dom().contains(p_ptr_i) && self.proc_dom().contains(p_ptr_j) && p_ptr_i
                    != p_ptr_j ==> self.get_proc(p_ptr_i).pcid != self.get_proc(p_ptr_j).pcid,
    {
    }

    pub proof fn wf_imply_container_no_proc_to_no_thread(&self, container_ptr:ContainerPtr)
        requires
            self.wf(),
            self.container_dom().contains(container_ptr),
            self.get_container(container_ptr).owned_procs@ == Seq::<ProcPtr>::empty(),
        ensures
            self.get_container(container_ptr).owned_threads@ == Set::<ThreadPtr>::empty(),
    {
        assert(
            forall|t_ptr:ThreadPtr|
                #![auto]
                self.get_container(container_ptr).owned_threads@.contains(t_ptr)
                ==>
                self.get_container(container_ptr).owned_procs@.contains(self.get_thread(t_ptr).owning_proc)
        );
        assert(
            !(
                exists|t_ptr:ThreadPtr|
                    self.get_container(container_ptr).owned_threads@.contains(t_ptr)
            )
        );
        assume(self.get_container(container_ptr).owned_threads@ == Set::<ThreadPtr>::empty());
    }

    // pub proof fn wf_imply_container_proc_disjoint(&self)
    //     requires
    //         self.wf(),
    //     ensures
    //         forall|c_ptr_i:ContainerPtr, c_ptr_j: ContainerPtr|
    //             self.container_dom().contains(c_ptr_i) && self.container_dom().contains(c_ptr_j) && c_ptr_i != c_ptr_j
    //             ==>
    //             self.container_perms@[c_ptr_i].value().children@.to_set().disjoint(self.container_perms@[c_ptr_j].value().children@.to_set()),
    //         forall|c_ptr_i:ContainerPtr, c_ptr_j: ContainerPtr|
    //             self.container_dom().contains(c_ptr_i) && self.container_dom().contains(c_ptr_j) && c_ptr_i != c_ptr_j
    //             ==>
    //             self.container_perms@[c_ptr_i].value().owned_procs@.to_set().disjoint(self.container_perms@[c_ptr_j].value().owned_procs@.to_set()),
    //         forall|c_ptr_i:ContainerPtr, c_ptr_j: ContainerPtr|
    //             self.container_dom().contains(c_ptr_i) && self.container_dom().contains(c_ptr_j) && c_ptr_i != c_ptr_j
    //             ==>
    //             self.container_perms@[c_ptr_i].value().owned_endpoints@.to_set().disjoint(self.container_perms@[c_ptr_j].value().owned_endpoints@.to_set()),
    //         forall|p_ptr_i:ProcPtr, p_ptr_j: ProcPtr|
    //             self.process_perms@.dom().contains(p_ptr_i) && self.process_perms@.dom().contains(p_ptr_j) && p_ptr_i != p_ptr_j
    //             ==>
    //             self.process_perms@[p_ptr_i].value().owned_threads@.to_set().disjoint(self.process_perms@[p_ptr_j].value().owned_threads@.to_set()),
    // {
    //     // assert(false);
    // }
    pub proof fn wf_imply_container_owned_proc_disjoint(&self)
        requires
            self.wf(),
        ensures
            forall|c_ptr_i: ContainerPtr, c_ptr_j: ContainerPtr, p_ptr: ProcPtr|
                #![auto]
                self.container_dom().contains(c_ptr_i) && self.container_dom().contains(c_ptr_j)
                    && c_ptr_i != c_ptr_j && self.get_container(c_ptr_i).owned_procs@.contains(
                    p_ptr,
                ) ==> self.get_container(c_ptr_j).owned_procs@.contains(p_ptr) == false,
    {
        // assert(false);
    }

    pub proof fn proc_tree_root_inv(&self, proc_ptr:ProcPtr)
        requires
            self.wf(),
            self.proc_dom().contains(proc_ptr),
        ensures
            self.get_proc(proc_ptr).depth == 0
                ==>
            self.get_container(self.get_proc(proc_ptr).owning_container).root_process.unwrap() == proc_ptr,
    {
        assert(self.container_dom().contains(self.get_proc(proc_ptr).owning_container));
        proc_tree_wf_imply_root_depth(
            self.get_container(self.get_proc(proc_ptr).owning_container).root_process.unwrap(),
            self.get_container(self.get_proc(proc_ptr).owning_container).owned_procs@.to_set(),
            self.process_perms@,
        );
        assert(self.get_container(self.get_proc(proc_ptr).owning_container).owned_procs@.to_set().contains(proc_ptr));
    }
}

} // verus!

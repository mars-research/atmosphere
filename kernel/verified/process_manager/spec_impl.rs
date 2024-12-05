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
    use crate::process_manager::container_tree_spec_impl::ContainerTree;

pub struct ProcessManager{
    pub container_tree:ContainerTree,

    pub process_perms: Tracked<Map<ProcPtr, PointsTo<Process>>>,
    pub thread_perms: Tracked<Map<ThreadPtr, PointsTo<Thread>>>,
    pub endpoint_perms: Tracked<Map<EndpointPtr, PointsTo<Endpoint>>>,

    pub cpu_list: Array<Cpu, NUM_CPUS>,
}

//utils
impl ProcessManager{
    pub proof fn page_closure_inv(&self)
        requires
            self.wf(),
        ensures
            self.container_dom() + self.proc_dom() + self.thread_dom() + self.endpoint_dom() =~= self.page_closure()
        {}
    
    pub closed spec fn page_closure(&self) -> Set<PagePtr>
    {
        self.container_tree.container_dom() + self.process_perms@.dom() + self.thread_perms@.dom() + self.endpoint_perms@.dom()
    }

    pub closed spec fn proc_dom(&self) -> Set<ProcPtr>
    {
        self.process_perms@.dom()
    }

    pub closed spec fn container_dom(&self) -> Set<ContainerPtr>
    {
        self.container_tree.container_dom()
    }

    pub closed spec fn thread_dom(&self) -> Set<ThreadPtr>
    {
        self.thread_perms@.dom()
    }

    pub closed spec fn endpoint_dom(&self) -> Set<EndpointPtr>
    {
        self.endpoint_perms@.dom()
    }

    pub closed spec fn spec_get_proc(&self, proc_ptr:ProcPtr) -> &Process
        recommends
            self.wf(),
            self.proc_dom().contains(proc_ptr),
    {
        &self.process_perms@[proc_ptr].value()
    }

    #[verifier(when_used_as_spec(spec_get_proc))]
    pub fn get_proc(&self, proc_ptr:ProcPtr) ->(ret:&Process)
        requires
            self.wf(),
            self.proc_dom().contains(proc_ptr),
        ensures
            ret =~= self.get_proc(proc_ptr),
            ret.owned_threads.wf(),
            self.container_dom().contains(ret.owning_container)
    {
        let tracked proc_perm = self.process_perms.borrow().tracked_borrow(proc_ptr);
        let proc : &Process = PPtr::<Process>::from_usize(proc_ptr).borrow(Tracked(proc_perm));
        proc
    }

    pub closed spec fn spec_get_proc_by_thread_ptr(&self, thread_ptr:ThreadPtr) -> &Process
        recommends
            self.wf(),
            self.thread_perms@.dom().contains(thread_ptr),
    {
        &self.process_perms@[self.get_thread(thread_ptr).owning_proc].value()
    }

    #[verifier(when_used_as_spec(spec_get_proc_by_thread_ptr))]
    pub fn get_proc_by_thread_ptr(&self, thread_ptr:ThreadPtr) ->(ret:&Process)
        requires
            self.wf(),
            self.thread_perms@.dom().contains(thread_ptr),
        ensures
            ret =~= self.spec_get_proc_by_thread_ptr(thread_ptr),
    {
        let proc_ptr = self.get_thread(thread_ptr).owning_proc;
        let tracked proc_perm = self.process_perms.borrow().tracked_borrow(proc_ptr);
        let proc : &Process = PPtr::<Process>::from_usize(proc_ptr).borrow(Tracked(proc_perm));
        proc
    }

    pub closed spec fn spec_get_thread(&self, thread_ptr:ThreadPtr) -> &Thread
        recommends
            self.wf(),
            self.thread_dom().contains(thread_ptr),
    {
        &self.thread_perms@[thread_ptr].value()
    }

    #[verifier(when_used_as_spec(spec_get_thread))]
    pub fn get_thread(&self, thread_ptr:ThreadPtr) -> (ret:&Thread)
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
        proof{
            self.container_tree.container_tree_inv();
        }
        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
        let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));
        thread
    }

    pub closed spec fn spec_get_cpu(&self, cpu_id:CpuId) -> &Cpu
        recommends
            self.wf(),
            0 <= cpu_id < NUM_CPUS,
    {
        &self.cpu_list@[cpu_id as int]
    }

    #[verifier(when_used_as_spec(spec_get_cpu))]
    pub fn get_cpu(&self, cpu_id:CpuId) -> (ret: &Cpu)
        requires
            self.wf(),
            0 <= cpu_id < NUM_CPUS,
        ensures
            ret == self.get_cpu(cpu_id),
    {
        self.cpu_list.get(cpu_id)
    }

    pub closed spec fn spec_get_is_cpu_running(&self, cpu_i:CpuId) -> bool
        recommends
            self.wf(),
            0 <= cpu_i < NUM_CPUS,
    {
        self.cpu_list@[cpu_i as int].current_thread.is_Some()
    }

    #[verifier(when_used_as_spec(spec_get_is_cpu_running))]
    pub fn get_is_cpu_running(&self, cpu_i:CpuId) -> (ret :bool)
        requires
            self.wf(),
            0 <= cpu_i < NUM_CPUS,
        ensures
            ret == self.get_is_cpu_running(cpu_i),
    {
        self.cpu_list.get(cpu_i).current_thread.is_some()
    }


    pub closed spec fn spec_get_container(&self, container_ptr:ContainerPtr) -> &Container
        recommends
            self.wf(),
            self.container_dom().contains(container_ptr),
    {
        self.container_tree.get_container(container_ptr)
    }

    #[verifier(when_used_as_spec(spec_get_container))]
    pub fn get_container(&self, container_ptr:ContainerPtr) -> (ret:&Container)
        requires
            self.wf(),
            self.container_dom().contains(container_ptr),
        ensures
            self.get_container(container_ptr) == ret,
    {
        self.container_tree.get_container(container_ptr)
    }

    pub closed spec fn spec_get_container_by_proc_ptr(&self, proc_ptr:ProcPtr) -> &Container
        recommends
            self.wf(),
            self.proc_dom().contains(proc_ptr),
    {
        self.container_tree.get_container(self.get_proc(proc_ptr).owning_container)
    }

    #[verifier(when_used_as_spec(spec_get_container_by_proc_ptr))]
    pub fn get_container_by_proc_ptr(&self, proc_ptr:ProcPtr) -> (ret:&Container)
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
        let container = self.container_tree.get_container(container_ptr);
        container
    }

    pub closed spec fn spec_get_container_by_thread_ptr(&self, thread_ptr:ThreadPtr) -> &Container
        recommends
            self.wf(),
            self.thread_perms@.dom().contains(thread_ptr),
    {
        self.container_tree.get_container(self.get_proc_by_thread_ptr(thread_ptr).owning_container)
    }

    #[verifier(when_used_as_spec(spec_get_container_by_thread_ptr))]
    pub fn get_container_by_thread_ptr(&self, thread_ptr:ThreadPtr) -> (ret:&Container)
        requires
            self.wf(),
            self.thread_perms@.dom().contains(thread_ptr),
        ensures
            self.get_container_by_thread_ptr(thread_ptr) == ret,
    {
        let container_ptr = self.get_proc_by_thread_ptr(thread_ptr).owning_container;
        let container = self.container_tree.get_container(container_ptr);
        container
    }

    pub closed spec fn spec_get_endpoint(&self, endpoint_ptr:EndpointPtr) -> &Endpoint
        recommends
            self.wf(),
            self.endpoint_perms@.dom().contains(endpoint_ptr),
    {
        &self.endpoint_perms@[endpoint_ptr].value()
    }

    #[verifier(when_used_as_spec(spec_get_endpoint))]
    pub fn get_endpoint(&self, endpoint_ptr:EndpointPtr) -> (ret:&Endpoint)
        requires
            self.wf(),
            self.endpoint_dom().contains(endpoint_ptr),
        ensures
            ret == self.get_endpoint(endpoint_ptr),
            ret.queue.wf(),
    {
        let tracked endpoint_perm = self.endpoint_perms.borrow().tracked_borrow(endpoint_ptr);
        let endpoint : &Endpoint = PPtr::<Endpoint>::from_usize(endpoint_ptr).borrow(Tracked(endpoint_perm));
        endpoint
    }

    pub closed spec fn spec_get_thread_ptr_by_cpu_id(&self, cpu_id:CpuId) -> (ret: Option<ThreadPtr>)
        recommends
            self.wf(),
            0 <= cpu_id < NUM_CPUS,
    {
        self.cpu_list@[cpu_id as int].current_thread
    }

    #[verifier(when_used_as_spec(spec_get_thread_ptr_by_cpu_id))]
    pub fn get_thread_ptr_by_cpu_id(&self, cpu_id:CpuId) -> (ret: Option<ThreadPtr>)
        requires
            self.wf(),
            0 <= cpu_id < NUM_CPUS,
        ensures
            ret == self.get_thread_ptr_by_cpu_id(cpu_id),
            self.get_is_cpu_running(cpu_id) == ret.is_Some(),
            ret.is_Some() ==> 
                self.get_cpu(cpu_id).current_thread.is_Some()
                &&
                self.thread_dom().contains(ret.unwrap()),
            self.get_thread_ptr_by_cpu_id(cpu_id) == ret,
            self.get_cpu(cpu_id).current_thread == ret,
    {
        self.cpu_list.get(cpu_id).current_thread
    }

    pub closed spec fn spec_get_owning_proc_by_thread_ptr(&self, t_ptr:ThreadPtr) -> (ret: ProcPtr)
        recommends
            self.wf(),
            self.thread_dom().contains(t_ptr),
    {
        self.get_thread(t_ptr).owning_proc
    }

    #[verifier(when_used_as_spec(spec_get_owning_proc_by_thread_ptr))]
    pub fn get_owning_proc_by_thread_ptr(&self, t_ptr:ThreadPtr) -> (ret: ProcPtr)
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

    pub fn get_proc_ptr_by_cpu_id(&self, cpu_id:CpuId) -> (ret: Option<ProcPtr>)
        requires
            self.wf(),
            0 <= cpu_id < NUM_CPUS,
        ensures
            self.get_is_cpu_running(cpu_id) <==> ret.is_Some(),
            ret.is_Some()
                ==> 
                self.get_is_cpu_running(cpu_id)
                &&
                self.cpu_list@[cpu_id as int].current_thread.is_Some()
                &&
                self.get_thread(self.cpu_list@[cpu_id as int].current_thread.unwrap()).owning_proc == ret.unwrap()
                &&
                self.proc_dom().contains(ret.unwrap()),
            ret.is_None()
                ==> 
                self.get_is_cpu_running(cpu_id) == false
                &&
                self.cpu_list@[cpu_id as int].current_thread.is_None()
             
    {
        let thread_ptr_op = self.cpu_list.get(cpu_id).current_thread;
        if thread_ptr_op.is_some(){
            return Some(self.get_thread(thread_ptr_op.unwrap()).owning_proc);
        }else{
            return None;
        }
    }

    pub open spec fn spec_get_endpoint_ptr_by_endpoint_idx(&self, thread_ptr:ThreadPtr, endpoint_index:EndpointIdx) -> Option<EndpointPtr>
        recommends
            self.wf(),
            self.thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
    {
        self.get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int]
    }

    #[verifier(when_used_as_spec(spec_get_endpoint_ptr_by_endpoint_idx))]
    pub fn get_endpoint_ptr_by_endpoint_idx(&self, thread_ptr:ThreadPtr, endpoint_index:EndpointIdx) -> (ret: Option<EndpointPtr>)
        requires
            self.wf(),
            self.thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        ensures
            ret == self.get_endpoint_ptr_by_endpoint_idx(thread_ptr,endpoint_index),
            ret.is_Some() ==> self.endpoint_dom().contains(ret.unwrap()),
    {
        *self.get_thread(thread_ptr).endpoint_descriptors.get(endpoint_index)
    }

    pub closed spec fn spec_get_endpoint_by_endpoint_idx(&self, thread_ptr:ThreadPtr, endpoint_index:EndpointIdx) -> Option<&Endpoint>
        recommends
            self.wf(),
            self.thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
    {
        if self.get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].is_None(){
            None
        }else{
            Some(&self.get_endpoint(self.get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()))
        }
    }

    #[verifier(when_used_as_spec(spec_get_endpoint_by_endpoint_idx))]
    pub fn get_endpoint_by_endpoint_idx(&self, thread_ptr:ThreadPtr, endpoint_index:EndpointIdx) -> (ret: Option<&Endpoint>)
        requires
            self.wf(),
            self.thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        ensures
            ret == self.get_endpoint_by_endpoint_idx(thread_ptr,endpoint_index),
    {
        if self.get_thread(thread_ptr).endpoint_descriptors.get(endpoint_index).is_none(){
            None
        }else{
            Some(&self.get_endpoint(self.get_thread(thread_ptr).endpoint_descriptors.get(endpoint_index).unwrap()))
        } 
    }

    pub closed spec fn spec_get_thread_owns_endpoint(&self, thread_ptr:ThreadPtr, endpoint_ptr:EndpointPtr) -> bool{
        exists|i:int| 
            #![trigger self.thread_perms@[thread_ptr].value().endpoint_descriptors@[i]]
            0 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS 
            &&
            self.thread_perms@[thread_ptr].value().endpoint_descriptors@[i].is_Some() && self.thread_perms@[thread_ptr].value().endpoint_descriptors@[i].unwrap() == endpoint_ptr
    }

    pub fn get_thread_owns_endpoint(&self, thread_ptr:ThreadPtr, endpoint_ptr:EndpointPtr) -> (ret:bool)
        requires
            self.wf(),
            self.thread_dom().contains(thread_ptr),
        ensures
            ret == self.spec_get_thread_owns_endpoint(thread_ptr, endpoint_ptr),
    {
        for index in 0..MAX_NUM_ENDPOINT_DESCRIPTORS
            invariant
                self.wf(),
                self.thread_dom().contains(thread_ptr),
                forall|i:int| #![trigger self.get_thread(thread_ptr).endpoint_descriptors@[i]] 0 <= i < index ==> self.get_thread(thread_ptr).endpoint_descriptors@[i].is_None() || self.get_thread(thread_ptr).endpoint_descriptors@[i].unwrap() != endpoint_ptr
        {
            if self.get_thread(thread_ptr).endpoint_descriptors.get(index).is_some(){
                if self.get_thread(thread_ptr).endpoint_descriptors.get(index).unwrap() == endpoint_ptr{
                    return true
                }
            }
        }
        return false
    }
}

//specs
impl ProcessManager{
    pub closed spec fn cpus_wf(&self) -> bool{
        &&&
        self.cpu_list.wf()
        // &&&
        // forall|cpu_i:CpuId| 
        //     #![trigger self.cpu_list@[cpu_i as int].active]
        //     #![trigger self.cpu_list@[cpu_i as int].current_thread]
        //     self.cpu_list@[cpu_i as int].active == false ==> self.cpu_list@[cpu_i as int].current_thread.is_None()
    }
    pub closed spec fn container_cpu_wf(&self) -> bool{
        &&&
        forall|cpu_i:CpuId|
            #![trigger self.cpu_list@[cpu_i as int]]
            0 <= cpu_i < NUM_CPUS 
            ==> 
            self.container_tree.container_dom().contains(self.cpu_list@[cpu_i as int].owning_container)
        &&&
        forall|cpu_i:CpuId|
            #![trigger self.cpu_list@[cpu_i as int]]
            0 <= cpu_i < NUM_CPUS 
            ==> 
            self.container_tree.get_container(self.cpu_list@[cpu_i as int].owning_container).owned_cpus@.contains(cpu_i)
        &&&
        forall|cpu_i:CpuId|
            #![trigger self.cpu_list@[cpu_i as int]]
            0 <= cpu_i < NUM_CPUS 
            ==> 
            self.cpu_list@[cpu_i as int].active == false ==> self.cpu_list@[cpu_i as int].current_thread.is_None()
    }

    pub closed spec fn threads_cpu_wf(&self) -> bool {
        &&&
        forall|t_ptr:ThreadPtr|
            #![trigger self.thread_perms@[t_ptr].value().state]
            #![trigger self.thread_perms@[t_ptr].value().running_cpu]
            self.thread_perms@.dom().contains(t_ptr) 
            ==>
            (self.thread_perms@[t_ptr].value().running_cpu.is_Some() 
            <==> self.thread_perms@[t_ptr].value().state == ThreadState::RUNNING)
        &&&
        forall|t_ptr:ThreadPtr|
            #![trigger self.thread_perms@[t_ptr].value().running_cpu]
            self.thread_perms@.dom().contains(t_ptr) && self.thread_perms@[t_ptr].value().running_cpu.is_Some() 
            ==>
            0 <= self.thread_perms@[t_ptr].value().running_cpu.unwrap() < NUM_CPUS
            &&
            self.cpu_list@[self.thread_perms@[t_ptr].value().running_cpu.unwrap() as int].current_thread.is_Some()
            &&
            self.cpu_list@[self.thread_perms@[t_ptr].value().running_cpu.unwrap() as int].current_thread.unwrap() == t_ptr
            &&
            self.cpu_list@[self.thread_perms@[t_ptr].value().running_cpu.unwrap() as int].owning_container ==
                self.thread_perms@[t_ptr].value().owning_container
        &&&        
        forall|cpu_i:CpuId|
            #![trigger self.cpu_list@[cpu_i as int].current_thread]
            0 <= cpu_i < NUM_CPUS && self.cpu_list@[cpu_i as int].current_thread.is_Some()
            ==> 
            self.thread_perms@.dom().contains(self.cpu_list@[cpu_i as int].current_thread.unwrap())
            &&
            self.thread_perms@[self.cpu_list@[cpu_i as int].current_thread.unwrap()].value().running_cpu.is_Some()
            &&
            self.thread_perms@[self.cpu_list@[cpu_i as int].current_thread.unwrap()].value().running_cpu.unwrap() == cpu_i
            &&
            self.cpu_list@[cpu_i as int].owning_container ==
                self.thread_perms@[self.cpu_list@[cpu_i as int].current_thread.unwrap()].value().owning_container
    }

    pub closed spec fn memory_disjoint(&self) -> bool{
        &&&
        self.container_tree.container_dom().disjoint(self.process_perms@.dom())
        &&&
        self.container_tree.container_dom().disjoint(self.thread_perms@.dom())
        &&&
        self.container_tree.container_dom().disjoint(self.endpoint_perms@.dom())
        &&&
        self.process_perms@.dom().disjoint(self.thread_perms@.dom())
        &&&
        self.process_perms@.dom().disjoint(self.endpoint_perms@.dom())
        &&&
        self.thread_perms@.dom().disjoint(self.endpoint_perms@.dom())
    }

    pub closed spec fn container_perms_wf(&self) -> bool{
        &&&
        forall|c_ptr:ContainerPtr| 
        #![trigger self.container_tree.container_dom().contains(c_ptr)]
            self.container_tree.container_dom().contains(c_ptr)
            ==> 
            self.container_tree.get_container(c_ptr).owned_cpus.wf()
            &&
            self.container_tree.get_container(c_ptr).scheduler.wf() 
            &&
            self.container_tree.get_container(c_ptr).scheduler.unique() 
            &&
            self.container_tree.get_container(c_ptr).owned_procs.wf()
            &&
            self.container_tree.get_container(c_ptr).owned_procs.unique()
            &&
            self.container_tree.get_container(c_ptr).owned_endpoints.wf()
            &&
            self.container_tree.get_container(c_ptr).owned_endpoints.unique()
    }

    pub closed spec fn processes_container_wf(&self) -> bool{
        // &&&
        // forall|c_ptr:ContainerPtr| 
        //     #![trigger self.container_tree.get_container(c_ptr).owned_procs]
        //     self.container_tree.container_dom().contains(c_ptr)
        //     ==>
        //     self.container_tree.get_container(c_ptr).owned_procs@.to_set().subset_of(self.process_perms@.dom())
        &&&
        forall|c_ptr:ContainerPtr, child_p_ptr:ProcPtr| 
            #![trigger self.container_tree.get_container(c_ptr).owned_procs@.contains(child_p_ptr)]
            self.container_tree.container_dom().contains(c_ptr) && self.container_tree.get_container(c_ptr).owned_procs@.contains(child_p_ptr)
            ==> self.process_perms@.dom().contains(child_p_ptr)
                &&
                self.process_perms@[child_p_ptr].value().owning_container == c_ptr
        &&&
        forall|p_ptr:ProcPtr| 
            #![trigger self.process_perms@[p_ptr].value().owning_container]
            self.process_perms@.dom().contains(p_ptr)
            ==>
            self.container_tree.container_dom().contains(self.process_perms@[p_ptr].value().owning_container)
            &&
            self.container_tree.get_container(self.process_perms@[p_ptr].value().owning_container).owned_procs@.to_set().contains(p_ptr)
            &&
            self.container_tree.get_container(self.process_perms@[p_ptr].value().owning_container).owned_procs.node_ref_valid(self.process_perms@[p_ptr].value().rev_ptr)
            &&
            self.container_tree.get_container(self.process_perms@[p_ptr].value().owning_container).owned_procs.node_ref_resolve(self.process_perms@[p_ptr].value().rev_ptr) == p_ptr
        }
    
    pub closed spec fn processes_wf(&self) -> bool{
        &&&
        forall|p_ptr:ProcPtr| 
            #![trigger self.process_perms@.dom().contains(p_ptr)]
            self.process_perms@.dom().contains(p_ptr)
            ==>
            self.process_perms@[p_ptr].is_init()
            &&            
            self.process_perms@[p_ptr].addr() == p_ptr
    }

    pub closed spec fn threads_process_wf(&self) -> bool{
        &&&
        forall|p_ptr:ProcPtr| 
            #![trigger self.process_perms@.dom().contains(p_ptr)]
            self.process_perms@.dom().contains(p_ptr)
            ==>
            self.process_perms@[p_ptr].value().owned_threads.wf()
            &&
            self.process_perms@[p_ptr].value().owned_threads.unique()
        &&&
        forall|p_ptr:ProcPtr, child_t_ptr:ThreadPtr| 
            #![trigger self.process_perms@.dom().contains(p_ptr), self.thread_perms@[child_t_ptr].value().owning_proc]
            #![trigger self.process_perms@[p_ptr].value().owned_threads@.contains(child_t_ptr)]
            self.process_perms@.dom().contains(p_ptr) && self.process_perms@[p_ptr].value().owned_threads@.contains(child_t_ptr)
            ==> self.thread_perms@.dom().contains(child_t_ptr)
                &&
                self.thread_perms@[child_t_ptr].value().owning_proc == p_ptr
        &&&
        forall|t_ptr:ThreadPtr| 
            #![trigger self.thread_perms@[t_ptr].value().owning_container]
            #![trigger self.thread_perms@[t_ptr].value().owning_proc]
            self.thread_perms@.dom().contains(t_ptr)
            ==>
            self.container_tree.container_dom().contains(self.thread_perms@[t_ptr].value().owning_container)
            &&
            self.process_perms@.dom().contains(self.thread_perms@[t_ptr].value().owning_proc)
            &&
            self.process_perms@[self.thread_perms@[t_ptr].value().owning_proc].value().owned_threads@.contains(t_ptr)
            &&
            self.process_perms@[self.thread_perms@[t_ptr].value().owning_proc].value().owned_threads.node_ref_valid(self.thread_perms@[t_ptr].value().proc_rev_ptr)
            &&
            self.process_perms@[self.thread_perms@[t_ptr].value().owning_proc].value().owned_threads.node_ref_resolve(self.thread_perms@[t_ptr].value().proc_rev_ptr) == t_ptr
            &&
            self.process_perms@[self.thread_perms@[t_ptr].value().owning_proc].value().owning_container == self.thread_perms@[t_ptr].value().owning_container
    }
    pub closed spec fn threads_perms_wf(&self) -> bool{
        &&&
        forall|t_ptr:ThreadPtr|
        #![trigger self.thread_perms@.dom().contains(t_ptr) ]
        self.thread_perms@.dom().contains(t_ptr) 
        ==>
        self.thread_perms@[t_ptr].is_init()
        &&
        self.thread_perms@[t_ptr].addr() == t_ptr
        &&
        self.thread_perms@[t_ptr].value().endpoint_descriptors.wf()
        &&
        (self.thread_perms@[t_ptr].value().ipc_payload.get_payload_as_va_range().is_Some() ==> self.thread_perms@[t_ptr].value().ipc_payload.get_payload_as_va_range().unwrap().wf())
    }

    pub closed spec fn threads_container_wf(&self) -> bool{
        &&&
        forall|c_ptr:ContainerPtr| 
        // #![trigger self.container_tree.container_dom().contains(c_ptr)]
        #![trigger self.container_tree.get_container(c_ptr).owned_threads]
            self.container_tree.container_dom().contains(c_ptr)
            ==>
            self.container_tree.get_container(c_ptr).owned_threads@.subset_of(self.thread_perms@.dom())
        &&&
        forall|c_ptr:ContainerPtr, t_ptr:ThreadPtr| 
            #![trigger self.container_tree.get_container(c_ptr).owned_threads@.contains(t_ptr)]
            self.container_tree.container_dom().contains(c_ptr) 
            &&
            self.container_tree.get_container(c_ptr).owned_threads@.contains(t_ptr)
            ==>
            self.thread_perms@[t_ptr].value().owning_container == c_ptr 
        &&&
        forall|t_ptr:ThreadPtr| 
            #![trigger self.container_tree.container_dom().contains(self.thread_perms@[t_ptr].value().owning_container)]
            self.thread_perms@.dom().contains(t_ptr) 
            ==>
            self.container_tree.container_dom().contains(self.thread_perms@[t_ptr].value().owning_container) 
            &&
            self.container_tree.get_container(self.thread_perms@[t_ptr].value().owning_container).owned_threads@.contains(t_ptr)
    }

    pub closed spec fn endpoint_perms_wf(&self) -> bool {
        &&&
        forall|e_ptr:EndpointPtr| 
            #![trigger self.endpoint_perms@.dom().contains(e_ptr) ]
            self.endpoint_perms@.dom().contains(e_ptr) 
            ==> 
            self.endpoint_perms@[e_ptr].is_init()
            &&
            self.endpoint_perms@[e_ptr].addr() == e_ptr
            &&
            self.endpoint_perms@[e_ptr].value().queue.wf()
            &&
            self.endpoint_perms@[e_ptr].value().queue.unique()
            &&
            self.endpoint_perms@[e_ptr].value().owning_threads@.finite()
            &&
            self.endpoint_perms@[e_ptr].value().rf_counter == self.endpoint_perms@[e_ptr].value().owning_threads@.len()
            &&
            self.endpoint_perms@[e_ptr].value().owning_threads@.subset_of(self.thread_perms@.dom())
    }

    pub closed spec fn threads_endpoint_descriptors_wf(&self) -> bool {
        &&&
        forall|t_ptr:ThreadPtr, i: usize|
            #![trigger self.thread_perms@[t_ptr].value().endpoint_descriptors@[i as int]]
            self.thread_perms@.dom().contains(t_ptr) && 0 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS
            &&
            self.thread_perms@[t_ptr].value().endpoint_descriptors@[i as int].is_Some()
            ==>
            self.endpoint_perms@.dom().contains(self.thread_perms@[t_ptr].value().endpoint_descriptors@[i as int].unwrap())
            &&
            self.endpoint_perms@[self.thread_perms@[t_ptr].value().endpoint_descriptors@[i as int].unwrap()].value().owning_threads@.contains(t_ptr)
        &&&
        forall|e_ptr:EndpointPtr, t_ptr:ThreadPtr| 
            #![trigger self.endpoint_perms@[e_ptr].value().owning_threads@.contains(t_ptr)]
            #![trigger self.spec_get_thread_owns_endpoint(t_ptr, e_ptr)]
            self.endpoint_perms@.dom().contains(e_ptr) 
            &&
            self.endpoint_perms@[e_ptr].value().owning_threads@.contains(t_ptr)
            ==>
            self.thread_perms@.dom().contains(t_ptr)
            &&
            self.spec_get_thread_owns_endpoint(t_ptr, e_ptr)
            // &&
            // ( exists|i:int| 
            //     #![trigger self.thread_perms@[t_ptr].value().endpoint_descriptors@[i]]
            //     0 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS 
            //     &&
            //     self.thread_perms@[t_ptr].value().endpoint_descriptors@[i].is_Some() || self.thread_perms@[t_ptr].value().endpoint_descriptors@[i].unwrap() == e_ptr
            // )
    }
    
    pub closed spec fn endpoints_queue_wf(&self) -> bool {
        &&&
        forall|t_ptr:ThreadPtr|
            #![trigger self.thread_perms@[t_ptr].value().state]
            #![trigger self.thread_perms@[t_ptr].value().blocking_endpoint_ptr]
            #![trigger self.thread_perms@[t_ptr].value().endpoint_rev_ptr]
            self.thread_perms@.dom().contains(t_ptr)
            &&
            self.thread_perms@[t_ptr].value().state == ThreadState::BLOCKED
            ==>
            self.thread_perms@[t_ptr].value().blocking_endpoint_ptr.is_Some()
            &&
            self.thread_perms@[t_ptr].value().endpoint_rev_ptr.is_Some()
            &&
            self.endpoint_perms@.dom().contains(self.thread_perms@[t_ptr].value().blocking_endpoint_ptr.unwrap())
            &&
            self.endpoint_perms@[self.thread_perms@[t_ptr].value().blocking_endpoint_ptr.unwrap()].value().queue@.contains(t_ptr)
            &&
            self.endpoint_perms@[self.thread_perms@[t_ptr].value().blocking_endpoint_ptr.unwrap()].value().queue.node_ref_valid(self.thread_perms@[t_ptr].value().endpoint_rev_ptr.unwrap())
            &&
            self.endpoint_perms@[self.thread_perms@[t_ptr].value().blocking_endpoint_ptr.unwrap()].value().queue.node_ref_resolve(self.thread_perms@[t_ptr].value().endpoint_rev_ptr.unwrap()) == t_ptr
        &&&
        forall|e_ptr:EndpointPtr, i:int| 
            #![trigger self.endpoint_perms@[e_ptr].value().queue@[i]]
            self.endpoint_perms@.dom().contains(e_ptr) && 0 <= i < self.endpoint_perms@[e_ptr].value().queue@.len()
            ==>
            self.thread_perms@.dom().contains(self.endpoint_perms@[e_ptr].value().queue@[i])
            &&
            self.thread_perms@[self.endpoint_perms@[e_ptr].value().queue@[i]].value().blocking_endpoint_ptr == Some(e_ptr)
            &&
            self.endpoint_perms@[e_ptr].value().owning_threads@.contains(self.endpoint_perms@[e_ptr].value().queue@[i])
            &&
            self.thread_perms@[self.endpoint_perms@[e_ptr].value().queue@[i]].value().state == ThreadState::BLOCKED
    }

    pub closed spec fn endpoints_container_wf(&self) -> bool{
        &&&
        forall|c_ptr:ContainerPtr, child_e_ptr:EndpointPtr| 
            #![trigger self.container_tree.get_container(c_ptr).owned_endpoints@.contains(child_e_ptr)]
            self.container_tree.container_dom().contains(c_ptr) && self.container_tree.get_container(c_ptr).owned_endpoints@.contains(child_e_ptr)
            ==> self.endpoint_perms@.dom().contains(child_e_ptr)
                &&
                self.endpoint_perms@[child_e_ptr].value().owning_container == c_ptr
        &&&
        forall|e_ptr:EndpointPtr| 
            #![trigger self.endpoint_perms@[e_ptr].value().owning_container]
            self.endpoint_perms@.dom().contains(e_ptr)
            ==>
            self.container_tree.container_dom().contains(self.endpoint_perms@[e_ptr].value().owning_container)
            &&
            self.container_tree.get_container(self.endpoint_perms@[e_ptr].value().owning_container).owned_endpoints@.to_set().contains(e_ptr)
            &&
            self.container_tree.get_container(self.endpoint_perms@[e_ptr].value().owning_container).owned_endpoints.node_ref_valid(self.endpoint_perms@[e_ptr].value().container_rev_ptr)
            &&
            self.container_tree.get_container(self.endpoint_perms@[e_ptr].value().owning_container).owned_endpoints.node_ref_resolve(self.endpoint_perms@[e_ptr].value().container_rev_ptr) == e_ptr
        }

    pub closed spec fn schedulers_wf(&self) -> bool{
        &&&
        forall|t_ptr:ThreadPtr|
            #![trigger self.thread_perms@[t_ptr].value().state]
            #![trigger self.thread_perms@[t_ptr].value().scheduler_rev_ptr]
            self.thread_perms@.dom().contains(t_ptr)
            &&
            self.thread_perms@[t_ptr].value().state == ThreadState::SCHEDULED
            ==>
            self.container_tree.get_container(self.thread_perms@[t_ptr].value().owning_container).scheduler@.contains(t_ptr)
            &&
            self.thread_perms@[t_ptr].value().scheduler_rev_ptr.is_Some() 
            &&
            self.container_tree.get_container(self.thread_perms@[t_ptr].value().owning_container).scheduler.node_ref_valid(self.thread_perms@[t_ptr].value().scheduler_rev_ptr.unwrap())
            && 
            self.container_tree.get_container(self.thread_perms@[t_ptr].value().owning_container).scheduler.node_ref_resolve(self.thread_perms@[t_ptr].value().scheduler_rev_ptr.unwrap()) == t_ptr
        &&&
        forall|c_ptr:ContainerPtr, t_ptr:ThreadPtr|
            #![trigger self.container_tree.get_container(c_ptr).scheduler@.contains(t_ptr)]
            #![trigger self.container_tree.container_dom().contains(c_ptr), self.thread_perms@[t_ptr].value().owning_container]
            #![trigger self.container_tree.container_dom().contains(c_ptr), self.thread_perms@[t_ptr].value().state]
            self.container_tree.container_dom().contains(c_ptr) &&  self.container_tree.get_container(c_ptr).scheduler@.contains(t_ptr)
            ==>
            self.thread_perms@.dom().contains(t_ptr)
            &&
            self.thread_perms@[t_ptr].value().owning_container == c_ptr
            &&
            self.thread_perms@[t_ptr].value().state == ThreadState::SCHEDULED
    }

    pub closed spec fn pcid_ioid_wf(&self) -> bool{
        &&&
        forall|p_ptr_i:ProcPtr, p_ptr_j:ProcPtr| 
            #![trigger self.process_perms@[p_ptr_i].value().pcid, self.process_perms@[p_ptr_j].value().pcid]
            self.process_perms@.dom().contains(p_ptr_i) && self.process_perms@.dom().contains(p_ptr_j) && p_ptr_i != p_ptr_j
            ==>
            self.process_perms@[p_ptr_i].value().pcid != self.process_perms@[p_ptr_j].value().pcid
        &&&
        forall|p_ptr_i:ProcPtr, p_ptr_j:ProcPtr| 
            #![trigger self.process_perms@[p_ptr_i].value().ioid, self.process_perms@[p_ptr_j].value().ioid]
            self.process_perms@.dom().contains(p_ptr_i) && self.process_perms@.dom().contains(p_ptr_j) && p_ptr_i != p_ptr_j
            &&
            self.process_perms@[p_ptr_i].value().ioid.is_Some() && self.process_perms@[p_ptr_j].value().ioid.is_Some() 
            ==>
            self.process_perms@[p_ptr_i].value().ioid.unwrap() != self.process_perms@[p_ptr_j].value().ioid.unwrap()
    }

    pub closed spec fn wf(&self) -> bool{
        &&&
        self.container_tree.wf()
        &&&
        self.cpus_wf()
        &&&
        self.container_cpu_wf()
        &&&
        self.memory_disjoint()
        &&&
        self.container_perms_wf()
        &&&
        self.processes_container_wf()
        &&&
        self.processes_wf()
        &&&
        self.threads_process_wf()
        &&&
        self.threads_perms_wf()
        &&&
        self.endpoint_perms_wf()
        &&&
        self.threads_endpoint_descriptors_wf()
        &&&
        self.endpoints_queue_wf()
        &&&
        self.endpoints_container_wf()
        &&&
        self.schedulers_wf()
        &&&
        self.pcid_ioid_wf()
        &&&
        self.threads_cpu_wf()
        &&&
        self.threads_container_wf()
    }
}

//proofs
impl ProcessManager{
    pub proof fn container_thread_inv_1(&self)
        requires
            self.wf()
        ensures
            forall|c_ptr:ContainerPtr, t_ptr:ThreadPtr|
                #![auto]
                self.container_dom().contains(c_ptr)
                &&
                self.thread_dom().contains(t_ptr)
                &&
                self.get_container(c_ptr).owned_threads@.contains(t_ptr) == false
                ==>
                self.get_thread(t_ptr).owning_container != c_ptr
    {}

    pub proof fn proc_thread_inv_1(&self)
        requires
            self.wf()
        ensures
            forall|p_ptr:ProcPtr, t_ptr:ThreadPtr|
                #![auto]
                self.proc_dom().contains(p_ptr)
                &&
                self.thread_dom().contains(t_ptr)
                &&
                self.get_proc(p_ptr).owned_threads@.contains(t_ptr) == false
                ==>
                self.get_thread(t_ptr).owning_proc != p_ptr
    {}

    pub proof fn thread_inv(&self)
        requires
            self.wf()
        ensures
            forall|t_ptr:ThreadPtr|
                #![trigger self.thread_dom().contains(t_ptr)]
                #![trigger self.get_thread(t_ptr).owning_container]
                #![trigger self.get_thread(t_ptr).owning_proc]
                self.thread_dom().contains(t_ptr)
                ==>
                self.container_dom().contains(self.get_thread(t_ptr).owning_container)
                &&
                self.proc_dom().contains(self.get_thread(t_ptr).owning_proc)
                &&
                self.get_thread(t_ptr).endpoint_descriptors.wf()
                &&
                (self.get_thread(t_ptr).ipc_payload.get_payload_as_va_range().is_Some() ==> self.get_thread(t_ptr).ipc_payload.get_payload_as_va_range().unwrap().wf())
                &&
                (
                    forall|i:int| #![auto] 
                        0 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS && self.get_thread(t_ptr).endpoint_descriptors@[i].is_Some() 
                        ==> 
                        self.endpoint_dom().contains(self.get_thread(t_ptr).endpoint_descriptors@[i].unwrap())
                )
                &&
                self.get_proc(self.get_thread(t_ptr).owning_proc).owning_container == self.get_thread(t_ptr).owning_container
                &&
                (
                    self.get_thread(t_ptr).state == ThreadState::BLOCKED 
                    ==>
                    self.get_thread(t_ptr).blocking_endpoint_ptr.is_Some()
                    &&
                    self.endpoint_dom().contains(self.get_thread(t_ptr).blocking_endpoint_ptr.unwrap())
                )
    {}
    pub proof fn process_inv(&self)
        requires
            self.wf()
        ensures
            forall|p_ptr:ProcPtr|
                #![trigger self.proc_dom().contains(p_ptr)]
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr)
                ==>
                self.container_dom().contains(self.get_proc(p_ptr).owning_container)
    {}

    pub proof fn container_subtree_inv(&self)
        requires
            self.wf()
        ensures
            forall|c_ptr:ContainerPtr|
                #![trigger self.container_dom().contains(c_ptr)]
                #![trigger self.get_container(c_ptr)]
                self.container_dom().contains(c_ptr)
                ==>
                self.get_container(c_ptr).subtree_set@.subset_of(self.container_dom())
                &&
                self.get_container(c_ptr).subtree_set@.contains(c_ptr) == false
    {
        self.container_tree.container_subtree_inv();
    }

    pub proof fn container_inv(&self)
        requires
            self.wf()
        ensures
            forall|c_ptr:ContainerPtr|
                #![trigger self.container_dom().contains(c_ptr)]
                #![trigger self.get_container(c_ptr).owned_cpus.wf()]
                #![trigger self.get_container(c_ptr).scheduler.wf()]
                #![trigger self.get_container(c_ptr).owned_endpoints.wf()]
                self.container_dom().contains(c_ptr)
                ==>
                self.get_container(c_ptr).owned_cpus.wf()
                &&
                self.get_container(c_ptr).scheduler.wf()
                &&
                self.get_container(c_ptr).owned_endpoints.wf(),
            forall|c_ptr:ContainerPtr, p_ptr:ProcPtr|
                #![auto]
                self.container_dom().contains(c_ptr)
                &&
                self.get_container(c_ptr).owned_procs@.contains(p_ptr)
                ==>
                self.proc_dom().contains(p_ptr),
            forall|c_ptr:ContainerPtr, t_ptr:ThreadPtr|
                #![auto]
                self.container_dom().contains(c_ptr)
                &&
                self.get_container(c_ptr).owned_threads@.contains(t_ptr)
                ==>
                self.thread_dom().contains(t_ptr),
            forall|c_ptr_i:ContainerPtr, c_ptr_j:ContainerPtr, t_ptr:ThreadPtr|
                #![auto]
                c_ptr_i != c_ptr_j 
                && 
                self.container_dom().contains(c_ptr_i)
                &&
                self.container_dom().contains(c_ptr_j)
                &&
                self.get_container(c_ptr_i).owned_threads@.contains(t_ptr)
                ==>
                self.get_container(c_ptr_j).owned_threads@.contains(t_ptr) == false
    {}
    pub proof fn endpoint_inv(&self)
        requires 
            self.wf(),
        ensures
            forall|e_ptr:EndpointPtr|
                #![trigger self.endpoint_dom().contains(e_ptr)]
                #![trigger self.get_endpoint(e_ptr).queue.wf()]
                self.endpoint_dom().contains(e_ptr)
                ==>
                self.get_endpoint(e_ptr).queue.wf(),
            forall|e_ptr:EndpointPtr, i:int|
                #![trigger self.get_endpoint(e_ptr).queue@[i]]
                self.endpoint_dom().contains(e_ptr) && 0 <= i < self.get_endpoint(e_ptr).queue.len()
                ==>
                self.thread_dom().contains(self.get_endpoint(e_ptr).queue@[i])
                &&
                self.get_thread(self.get_endpoint(e_ptr).queue@[i]).state == ThreadState::BLOCKED,
    {}

    pub proof fn cpu_inv(&self)
        requires 
            self.wf(),
        ensures
            self.cpu_list.wf(),
            forall|cpu_i:CpuId|
                #![auto]
                0 <= cpu_i < NUM_CPUS
                ==>
                self.container_dom().contains(self.cpu_list@[cpu_i as int].owning_container)
                &&
                (self.cpu_list@[cpu_i as int].current_thread.is_Some() ==> self.thread_dom().contains(self.cpu_list@[cpu_i as int].current_thread.unwrap())),
            
    {}

    pub proof fn pcid_unique(&self, proc_ptr:ProcPtr)
        requires
            self.wf(),
            self.proc_dom().contains(proc_ptr) 
        ensures
            forall|p_ptr:ProcPtr| #![auto] self.proc_dom().contains(p_ptr) && proc_ptr != p_ptr ==> self.get_proc(p_ptr).pcid != self.get_proc(proc_ptr).pcid,
    {}

    pub proof fn wf_imply_proc_to_unique_pcid(&self) 
        requires
            self.wf(),
        ensures
            forall|p_ptr_i:ProcPtr, p_ptr_j:ProcPtr|
                #![trigger self.get_proc(p_ptr_i).pcid, self.get_proc(p_ptr_j).pcid]
                self.proc_dom().contains(p_ptr_i) && self.proc_dom().contains(p_ptr_j) 
                &&
                p_ptr_i != p_ptr_j
                ==>
                self.get_proc(p_ptr_i).pcid != self.get_proc(p_ptr_j).pcid
    {
    }

    // pub proof fn wf_imply_container_proc_disjoint(&self)
    //     requires
    //         self.wf(),
    //     ensures
    //         forall|c_ptr_i:ContainerPtr, c_ptr_j: ContainerPtr|
    //             self.container_tree.container_dom().contains(c_ptr_i) && self.container_tree.container_dom().contains(c_ptr_j) && c_ptr_i != c_ptr_j
    //             ==>
    //             self.container_perms@[c_ptr_i].value().children@.to_set().disjoint(self.container_perms@[c_ptr_j].value().children@.to_set()),
    //         forall|c_ptr_i:ContainerPtr, c_ptr_j: ContainerPtr|
    //             self.container_tree.container_dom().contains(c_ptr_i) && self.container_tree.container_dom().contains(c_ptr_j) && c_ptr_i != c_ptr_j
    //             ==>
    //             self.container_perms@[c_ptr_i].value().owned_procs@.to_set().disjoint(self.container_perms@[c_ptr_j].value().owned_procs@.to_set()),
    //         forall|c_ptr_i:ContainerPtr, c_ptr_j: ContainerPtr|
    //             self.container_tree.container_dom().contains(c_ptr_i) && self.container_tree.container_dom().contains(c_ptr_j) && c_ptr_i != c_ptr_j
    //             ==>
    //             self.container_perms@[c_ptr_i].value().owned_endpoints@.to_set().disjoint(self.container_perms@[c_ptr_j].value().owned_endpoints@.to_set()),
    //         forall|p_ptr_i:ProcPtr, p_ptr_j: ProcPtr|
    //             self.process_perms@.dom().contains(p_ptr_i) && self.process_perms@.dom().contains(p_ptr_j) && p_ptr_i != p_ptr_j
    //             ==>
    //             self.process_perms@[p_ptr_i].value().owned_threads@.to_set().disjoint(self.process_perms@[p_ptr_j].value().owned_threads@.to_set()),
    // {
    //     // assert(false);
    // }
}

//exec
impl ProcessManager{

    pub fn new() -> (ret:Self)
    {
        ProcessManager{
            container_tree: ContainerTree::new(),

            process_perms: Tracked(Map::tracked_empty()),
            thread_perms: Tracked(Map::tracked_empty()),
            endpoint_perms: Tracked(Map::tracked_empty()),
        
            cpu_list: Array::<Cpu, NUM_CPUS>::new(),
        }
    }
    
    #[verifier(external_body)]
    pub fn init(&mut self, dom_0_container_ptr:ContainerPtr, dom_0_proc_ptr:ProcPtr, dom_0_thread_ptr:ThreadPtr, init_quota:usize, page_perm_0: Tracked<PagePerm4k>, page_perm_1: Tracked<PagePerm4k>, page_perm_2: Tracked<PagePerm4k>)
    {
        unsafe{
            self.container_tree.root_container = dom_0_container_ptr;
            let root_container_ptr = dom_0_container_ptr as *mut MaybeUninit<Container>;
            (*root_container_ptr).assume_init_mut().owned_procs.init();

            let sll1 = (*root_container_ptr).assume_init_mut().owned_procs.push(&dom_0_proc_ptr);
            (*root_container_ptr).assume_init_mut().parent = None;
            (*root_container_ptr).assume_init_mut().parent_rev_ptr = None;
            (*root_container_ptr).assume_init_mut().children.init();
            (*root_container_ptr).assume_init_mut().owned_endpoints.init();
            (*root_container_ptr).assume_init_mut().mem_quota = init_quota;
            (*root_container_ptr).assume_init_mut().mem_used = 0;
            (*root_container_ptr).assume_init_mut().owned_cpus.init();
            (*root_container_ptr).assume_init_mut().scheduler.init();
            let sll2 = (*root_container_ptr).assume_init_mut().scheduler.push(&dom_0_thread_ptr);
            (*root_container_ptr).assume_init_mut().depth = 0;

            let root_proc_ptr = dom_0_proc_ptr as *mut MaybeUninit<Process>;
            (*root_proc_ptr).assume_init_mut().owning_container = dom_0_container_ptr;
            (*root_proc_ptr).assume_init_mut().rev_ptr = sll2;
            (*root_proc_ptr).assume_init_mut().pcid = 0;
            (*root_proc_ptr).assume_init_mut().ioid = None;
            (*root_proc_ptr).assume_init_mut().owned_threads.init(); 
            let sll3 = (*root_proc_ptr).assume_init_mut().owned_threads.push(&dom_0_thread_ptr);
            
            let root_thread_ptr = dom_0_thread_ptr as *mut MaybeUninit<Thread>;
            (*root_thread_ptr).assume_init_mut().owning_container = dom_0_container_ptr;
            (*root_thread_ptr).assume_init_mut().owning_proc = dom_0_proc_ptr;
            (*root_thread_ptr).assume_init_mut().state = ThreadState::SCHEDULED;
            (*root_thread_ptr).assume_init_mut().proc_rev_ptr = sll3;
            (*root_thread_ptr).assume_init_mut().scheduler_rev_ptr = Some(sll2);
            (*root_thread_ptr).assume_init_mut().blocking_endpoint_ptr = None;
            (*root_thread_ptr).assume_init_mut().endpoint_rev_ptr = None;
            (*root_thread_ptr).assume_init_mut().running_cpu = None;
            (*root_thread_ptr).assume_init_mut().endpoint_descriptors.init2none();
            (*root_thread_ptr).assume_init_mut().ipc_payload = IPCPayLoad::Empty;
            (*root_thread_ptr).assume_init_mut().error_code = None;

            for i in 0..2{
                (*root_container_ptr).assume_init_mut().owned_cpus.insert(i);
                self.cpu_list.set(i,
                    Cpu{
                        owning_container: dom_0_container_ptr,
                        active: true,
                        current_thread: None,
                    }
                );
            }
            for i in 2..NUM_CPUS{
                (*root_container_ptr).assume_init_mut().owned_cpus.insert(i);
                self.cpu_list.set(i,
                    Cpu{
                        owning_container: dom_0_container_ptr,
                        active: false,
                        current_thread: None,
                    }
                );
            }
        }
    }

    pub fn set_container_mem_quota(&mut self, container_ptr:ContainerPtr, new_quota:usize)
        requires
            old(self).wf(),
            old(self).container_dom().contains(container_ptr),
        ensures
            self.wf(),
            self.proc_dom() =~= old(self).proc_dom(),
            self.thread_dom() =~= old(self).thread_dom(),
            self.container_dom() =~= old(self).container_dom(),
            self.endpoint_dom() =~= old(self).endpoint_dom(), 
            self.page_closure() =~= old(self).page_closure(),
            forall|p_ptr:ProcPtr|
                #![auto]
                self.proc_dom().contains(p_ptr)
                ==>
                self.get_proc(p_ptr) =~= old(self).get_proc(p_ptr),
            forall|t_ptr:ThreadPtr|
                #![auto]
                self.thread_dom().contains(t_ptr)
                ==>
                self.get_thread(t_ptr) =~= old(self).get_thread(t_ptr),
            forall|c_ptr:ContainerPtr|
                #![auto]
                self.container_dom().contains(c_ptr) && c_ptr != container_ptr
                ==>
                self.get_container(c_ptr) =~= old(self).get_container(c_ptr),
            forall|e_ptr:EndpointPtr|
                #![auto]
                self.endpoint_dom().contains(e_ptr)
                ==>
                self.get_endpoint(e_ptr) =~= old(self).get_endpoint(e_ptr),
            self.get_container(container_ptr).owned_procs =~= old(self).get_container(container_ptr).owned_procs,
            self.get_container(container_ptr).parent =~= old(self).get_container(container_ptr).parent,
            self.get_container(container_ptr).parent_rev_ptr =~= old(self).get_container(container_ptr).parent_rev_ptr,
            self.get_container(container_ptr).children =~= old(self).get_container(container_ptr).children,
            self.get_container(container_ptr).owned_endpoints =~= old(self).get_container(container_ptr).owned_endpoints,
            self.get_container(container_ptr).owned_threads =~= old(self).get_container(container_ptr).owned_threads,
            // self.get_container(container_ptr).mem_quota =~= old(self).get_container(container_ptr).mem_quota,
            self.get_container(container_ptr).mem_used =~= old(self).get_container(container_ptr).mem_used,
            self.get_container(container_ptr).owned_cpus =~= old(self).get_container(container_ptr).owned_cpus,
            self.get_container(container_ptr).scheduler =~= old(self).get_container(container_ptr).scheduler,
            self.get_container(container_ptr).depth =~= old(self).get_container(container_ptr).depth,
            self.get_container(container_ptr).uppertree_seq =~= old(self).get_container(container_ptr).uppertree_seq,
            self.get_container(container_ptr).subtree_set =~= old(self).get_container(container_ptr).subtree_set,
            self.get_container(container_ptr).mem_quota =~= new_quota,
    {
        self.container_tree.container_tree_set_quota(container_ptr, new_quota);
        assert(self.container_tree.wf());
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.container_perms_wf());
        assert(self.processes_container_wf());
        assert(self.processes_wf());
        assert(self.threads_process_wf());
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf());
        assert(self.threads_endpoint_descriptors_wf());
        assert(self.endpoints_queue_wf());
        assert(self.endpoints_container_wf());
        assert(self.schedulers_wf());
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf());
        
    }

    pub fn new_thread(&mut self, proc_ptr:ProcPtr, pt_regs:Registers, page_ptr: PagePtr, page_perm: Tracked<PagePerm4k>) -> (ret:ThreadPtr)
        requires
            old(self).wf(),
            old(self).proc_dom().contains(proc_ptr),
            old(self).page_closure().contains(page_ptr) == false,
            old(self).get_proc(proc_ptr).owned_threads.len() < MAX_NUM_THREADS_PER_PROC,
            old(self).get_container_by_proc_ptr(proc_ptr).mem_quota > 0,
            old(self).get_container_by_proc_ptr(proc_ptr).scheduler.len() < MAX_CONTAINER_SCHEDULER_LEN,
            page_perm@.is_init(),
            page_perm@.addr() == page_ptr,
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure().insert(page_ptr),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom().insert(ret),
            old(self).get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota - 1 == self.get_container(self.get_proc(proc_ptr).owning_container).mem_quota,
            old(self).get_proc(proc_ptr).pcid =~= self.get_proc(proc_ptr).pcid,
            old(self).get_proc(proc_ptr).ioid =~= self.get_proc(proc_ptr).ioid,
            forall|p_ptr:ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) && p_ptr != proc_ptr
                ==> 
                self.get_proc(p_ptr) =~= old(self).get_proc(p_ptr),
            forall|container_ptr:ContainerPtr|
                #![trigger self.get_container(container_ptr).owned_procs]
                self.container_dom().contains(container_ptr) && container_ptr != self.get_proc(proc_ptr).owning_container
                ==> 
                self.get_container(container_ptr).owned_procs =~= old(self).get_container(container_ptr).owned_procs,
    {
        proof{seq_push_lemma::<ThreadPtr>();}
        let container_ptr = self.get_proc(proc_ptr).owning_container;
        let old_mem_quota =  self.get_container(container_ptr).mem_quota;
        let old_owned_threads = self.get_container(container_ptr).owned_threads;
        let mut proc_perm = Tracked(self.process_perms.borrow_mut().tracked_remove(proc_ptr));
        let proc_node_ref = proc_push_thread(proc_ptr,&mut proc_perm, &page_ptr);
        proof {
            self.process_perms.borrow_mut().tracked_insert(proc_ptr, proc_perm.get());
        }

        let scheduler_node_ref = self.container_tree.container_tree_scheduler_push_thread(container_ptr, page_ptr);
        self.container_tree.container_tree_set_quota(container_ptr, old_mem_quota - 1);
        self.container_tree.container_tree_set_owned_threads(container_ptr, Ghost(old_owned_threads@.insert(page_ptr)));

        let (thread_ptr, thread_perm) = page_to_thread(page_ptr, page_perm, &pt_regs, container_ptr, proc_ptr, proc_node_ref, scheduler_node_ref);
        
        proof {
            self.thread_perms.borrow_mut().tracked_insert(thread_ptr, thread_perm.get());
        }
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.container_perms_wf());
        assert(self.processes_container_wf());
        assert(self.processes_wf());

        assert(self.threads_process_wf()) by {
            assert(self.process_perms@[proc_ptr].value().owned_threads@ =~= old(self).process_perms@[proc_ptr].value().owned_threads@.push(page_ptr));
            assert(
                forall|child_t_ptr:ThreadPtr| 
                #![auto]
                old(self).process_perms@[proc_ptr].value().owned_threads@.contains(child_t_ptr)
                ==> self.thread_perms@.dom().contains(child_t_ptr)
                    &&
                    self.thread_perms@[child_t_ptr].value().owning_proc == proc_ptr
            );
        };
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf());
        assert(self.threads_endpoint_descriptors_wf());
        assert(self.endpoints_queue_wf());
        assert(self.endpoints_container_wf()) by {
            assert(
                forall|c_ptr:ContainerPtr| 
                    #![trigger self.container_tree.get_container(c_ptr)]
                    self.container_tree.container_dom().contains(c_ptr)
                    ==> 
                    self.container_tree.get_container(c_ptr).owned_endpoints =~= old(self).container_tree.get_container(c_ptr).owned_endpoints
            );
            assert(
                forall|child_e_ptr:EndpointPtr| 
                    #![trigger self.endpoint_perms@.dom().contains(child_e_ptr)]
                    self.endpoint_perms@.dom().contains(child_e_ptr)
                    ==> 
                    self.endpoint_perms@[child_e_ptr].value() =~= old(self).endpoint_perms@[child_e_ptr].value()
            );
            assert(
                forall|c_ptr:ContainerPtr, child_e_ptr:EndpointPtr| 
                    #![trigger self.container_tree.get_container(c_ptr).owned_endpoints@.contains(child_e_ptr)]
                    self.container_tree.container_dom().contains(c_ptr) && self.container_tree.get_container(c_ptr).owned_endpoints@.contains(child_e_ptr)
                    ==> self.endpoint_perms@.dom().contains(child_e_ptr)
                        &&
                        self.endpoint_perms@[child_e_ptr].value().owning_container == c_ptr);
            assert(
                forall|e_ptr:EndpointPtr| 
                    #![trigger self.endpoint_perms@[e_ptr].value().owning_container]
                    self.endpoint_perms@.dom().contains(e_ptr)
                    ==>
                    self.container_tree.container_dom().contains(self.endpoint_perms@[e_ptr].value().owning_container)
                    &&
                    self.container_tree.get_container(self.endpoint_perms@[e_ptr].value().owning_container).owned_endpoints@.to_set().contains(e_ptr)
                    &&
                    self.container_tree.get_container(self.endpoint_perms@[e_ptr].value().owning_container).owned_endpoints.node_ref_valid(self.endpoint_perms@[e_ptr].value().container_rev_ptr)
                    &&
                    self.container_tree.get_container(self.endpoint_perms@[e_ptr].value().owning_container).owned_endpoints.node_ref_resolve(self.endpoint_perms@[e_ptr].value().container_rev_ptr) == e_ptr);
        };
        assert(self.schedulers_wf()) by {
            assert(self.container_tree.get_container(container_ptr).scheduler@ =~= old(self).container_tree.get_container(container_ptr).scheduler@.push(page_ptr));
            assert(
                forall|child_t_ptr:ThreadPtr| 
                #![auto]
                old(self).container_tree.get_container(container_ptr).scheduler@.contains(child_t_ptr)
                ==> self.thread_perms@.dom().contains(child_t_ptr)
                    &&
                    self.thread_perms@[child_t_ptr].value().owning_container == container_ptr
            );
        };
        thread_ptr
    }        


    pub fn new_thread_with_endpoint(&mut self, thread_ptr:ThreadPtr, endpoint_index:EndpointIdx, proc_ptr:ProcPtr, pt_regs:&Registers, page_ptr: PagePtr, page_perm: Tracked<PagePerm4k>) -> (ret:ThreadPtr)
        requires
            old(self).wf(),
            old(self).proc_dom().contains(proc_ptr),
            old(self).thread_dom().contains(thread_ptr),
            old(self).page_closure().contains(page_ptr) == false,
            old(self).get_proc(proc_ptr).owned_threads.len() < MAX_NUM_THREADS_PER_PROC,
            old(self).get_container_by_proc_ptr(proc_ptr).mem_quota > 0,
            old(self).get_container_by_proc_ptr(proc_ptr).scheduler.len() < MAX_CONTAINER_SCHEDULER_LEN,
            old(self).get_thread(thread_ptr).owning_proc == proc_ptr,
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_endpoint_by_endpoint_idx(thread_ptr, endpoint_index).is_Some() || old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).is_Some(),
            old(self).get_endpoint_by_endpoint_idx(thread_ptr, endpoint_index).unwrap().rf_counter_is_full() == false || old(self).get_endpoint(old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap()).rf_counter_is_full() == false,
            page_perm@.is_init(),
            page_perm@.addr() == page_ptr,
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure().insert(page_ptr),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom().insert(ret),
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).mem_quota - 1 == self.get_container(self.get_thread(thread_ptr).owning_container).mem_quota,
            old(self).get_proc(proc_ptr).pcid =~= self.get_proc(proc_ptr).pcid,
            old(self).get_proc(proc_ptr).ioid =~= self.get_proc(proc_ptr).ioid,
            forall|p_ptr:ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) && p_ptr != proc_ptr
                ==> 
                self.get_proc(p_ptr) =~= old(self).get_proc(p_ptr),
            forall|container_ptr:ContainerPtr|
                #![trigger self.get_container(container_ptr)]
                self.container_dom().contains(container_ptr) && container_ptr != self.get_thread(thread_ptr).owning_container
                ==> 
                self.get_container(container_ptr) =~= old(self).get_container(container_ptr)
                &&
                self.get_container(container_ptr).owned_threads@.contains(ret) == false,
            forall|t_ptr:ThreadPtr| 
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr)
                ==>
                old(self).get_thread(t_ptr) =~= self.get_thread(t_ptr),
            forall|e_ptr:EndpointPtr| 
                #![trigger self.get_endpoint(e_ptr)]
                self.endpoint_dom().contains(e_ptr) && e_ptr != old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap()
                ==> 
                old(self).get_endpoint(e_ptr) =~= self.get_endpoint(e_ptr),
            self.get_proc(proc_ptr).owned_threads@ == old(self).get_proc(proc_ptr).owned_threads@.push(ret),
            self.get_container(self.get_thread(thread_ptr).owning_container).owned_procs =~= old(self).get_container(self.get_thread(thread_ptr).owning_container).owned_procs,
            self.get_container(self.get_thread(thread_ptr).owning_container).owned_endpoints@ =~= old(self).get_container(self.get_thread(thread_ptr).owning_container).owned_endpoints@,
            self.get_container(self.get_thread(thread_ptr).owning_container).subtree_set =~= old(self).get_container(self.get_thread(thread_ptr).owning_container).subtree_set,
            self.get_container(self.get_thread(thread_ptr).owning_container).depth =~= old(self).get_container(self.get_thread(thread_ptr).owning_container).depth,
            self.get_container(self.get_thread(thread_ptr).owning_container).owned_threads@ =~= old(self).get_container(self.get_thread(thread_ptr).owning_container).owned_threads@.insert(ret),
            self.get_thread(ret).owning_container == old(self).get_thread(thread_ptr).owning_container,
            self.get_thread(ret).endpoint_descriptors@ =~= Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat,|i: int| {None}).update(0, Some(old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap())),
            self.get_endpoint(old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap()).owning_threads@ =~= old(self).get_endpoint(old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap()).owning_threads@.insert(ret),
            self.get_endpoint(old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap()).queue_state =~= old(self).get_endpoint(old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap()).queue_state,
    {
        let container_ptr = self.get_proc(proc_ptr).owning_container;
        let old_mem_quota =  self.get_container(container_ptr).mem_quota;
        let old_owned_threads = self.get_container(container_ptr).owned_threads;
        let endpoint_ptr = self.get_thread(thread_ptr).endpoint_descriptors.get(endpoint_index).unwrap();
        let mut proc_perm = Tracked(self.process_perms.borrow_mut().tracked_remove(proc_ptr));
        let proc_node_ref = proc_push_thread(proc_ptr,&mut proc_perm, &page_ptr);
        proof {
            self.process_perms.borrow_mut().tracked_insert(proc_ptr, proc_perm.get());
        }

        let scheduler_node_ref = self.container_tree.container_tree_scheduler_push_thread(container_ptr, page_ptr);
        self.container_tree.container_tree_set_quota(container_ptr, old_mem_quota - 1);
        self.container_tree.container_tree_set_owned_threads(container_ptr, Ghost(old_owned_threads@.insert(page_ptr)));

        let (new_thread_ptr, new_thread_perm) = page_to_thread_with_endpoint(page_ptr, page_perm, pt_regs, container_ptr, proc_ptr, proc_node_ref, scheduler_node_ref, endpoint_ptr);
        proof {
            self.thread_perms.borrow_mut().tracked_insert(new_thread_ptr, new_thread_perm.get());
        }

        let mut endpoint_perm = Tracked(self.endpoint_perms.borrow_mut().tracked_remove(endpoint_ptr));
        endpoint_add_ref(endpoint_ptr,&mut endpoint_perm, page_ptr);
        proof {
            self.endpoint_perms.borrow_mut().tracked_insert(endpoint_ptr, endpoint_perm.get());
        }
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.container_perms_wf());
        assert(self.processes_container_wf());
        assert(self.processes_wf());

        assert(self.threads_process_wf()) by {
            seq_push_lemma::<ThreadPtr>();
            assert(self.process_perms@[proc_ptr].value().owned_threads@ =~= old(self).process_perms@[proc_ptr].value().owned_threads@.push(page_ptr));
            assert(
                forall|child_t_ptr:ThreadPtr| 
                #![auto]
                old(self).process_perms@[proc_ptr].value().owned_threads@.contains(child_t_ptr)
                ==> self.thread_perms@.dom().contains(child_t_ptr)
                    &&
                    self.thread_perms@[child_t_ptr].value().owning_proc == proc_ptr
            );
            assert(forall|p_ptr:ProcPtr| 
                #![trigger self.process_perms@.dom().contains(p_ptr)]
                self.process_perms@.dom().contains(p_ptr)
                ==>
                self.process_perms@[p_ptr].value().owned_threads.wf()
                &&
                self.process_perms@[p_ptr].value().owned_threads.unique()
            );
            assert(forall|p_ptr:ProcPtr, child_t_ptr:ThreadPtr| 
                #![trigger self.process_perms@.dom().contains(p_ptr), self.thread_perms@[child_t_ptr].value().owning_proc]
                #![trigger self.process_perms@[p_ptr].value().owned_threads@.contains(child_t_ptr)]
                self.process_perms@.dom().contains(p_ptr) && self.process_perms@[p_ptr].value().owned_threads@.contains(child_t_ptr)
                ==> self.thread_perms@.dom().contains(child_t_ptr)
                    &&
                    self.thread_perms@[child_t_ptr].value().owning_proc == p_ptr
                );
            assert(forall|t_ptr:ThreadPtr| 
                #![trigger self.thread_perms@[t_ptr].value().owning_container]
                #![trigger self.thread_perms@[t_ptr].value().owning_proc]
                self.thread_perms@.dom().contains(t_ptr)
                ==>
                self.container_tree.container_dom().contains(self.thread_perms@[t_ptr].value().owning_container)
                &&
                self.process_perms@.dom().contains(self.thread_perms@[t_ptr].value().owning_proc)
                &&
                self.process_perms@[self.thread_perms@[t_ptr].value().owning_proc].value().owned_threads@.contains(t_ptr)
                &&
                self.process_perms@[self.thread_perms@[t_ptr].value().owning_proc].value().owned_threads.node_ref_valid(self.thread_perms@[t_ptr].value().proc_rev_ptr)
                &&
                self.process_perms@[self.thread_perms@[t_ptr].value().owning_proc].value().owned_threads.node_ref_resolve(self.thread_perms@[t_ptr].value().proc_rev_ptr) == t_ptr
                &&
                self.process_perms@[self.thread_perms@[t_ptr].value().owning_proc].value().owning_container == self.thread_perms@[t_ptr].value().owning_container
            );
        };
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf());
        assert(self.threads_endpoint_descriptors_wf()) by {
            seq_update_lemma::<Option<EndpointPtr>>();
            assert(forall|i:int| #![auto] 1 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS ==> self.thread_perms@[new_thread_ptr].value().endpoint_descriptors@[i].is_None());
            assert(self.thread_perms@[new_thread_ptr].value().endpoint_descriptors@[0] =~= Some(endpoint_ptr));
        };
        assert(self.endpoints_queue_wf());
        assert(self.endpoints_container_wf()) by {
            // assert(
            //     forall|c_ptr:ContainerPtr| 
            //         #![trigger self.container_perms@[c_ptr]]
            //         self.container_tree.container_dom().contains(c_ptr)
            //         ==> 
            //         self.container_tree.get_container(c_ptr).owned_endpoints =~= old(self).container_tree.get_container(c_ptr).owned_endpoints
            // );
            // assert(
            //     forall|child_e_ptr:EndpointPtr| 
            //         #![trigger self.endpoint_perms@.dom().contains(child_e_ptr)]
            //         self.endpoint_perms@.dom().contains(child_e_ptr) && child_e_ptr != endpoint_ptr
            //         ==> 
            //         self.endpoint_perms@[child_e_ptr].value() =~= old(self).endpoint_perms@[child_e_ptr].value()
            // );
            // assert(
            //     forall|c_ptr:ContainerPtr, child_e_ptr:EndpointPtr| 
            //         #![trigger self.container_tree.get_container(c_ptr).owned_endpoints@.contains(child_e_ptr)]
            //         self.container_tree.container_dom().contains(c_ptr) && self.container_tree.get_container(c_ptr).owned_endpoints@.contains(child_e_ptr)
            //         ==> self.endpoint_perms@.dom().contains(child_e_ptr)
            //             &&
            //             self.endpoint_perms@[child_e_ptr].value().owning_container == c_ptr);
            // assert(
            //     forall|e_ptr:EndpointPtr| 
            //         #![trigger self.endpoint_perms@[e_ptr].value().owning_container]
            //         self.endpoint_perms@.dom().contains(e_ptr)
            //         ==>
            //         self.container_tree.container_dom().contains(self.endpoint_perms@[e_ptr].value().owning_container)
            //         &&
            //         self.container_perms@[self.endpoint_perms@[e_ptr].value().owning_container].value().owned_endpoints@.to_set().contains(e_ptr)
            //         &&
            //         self.container_perms@[self.endpoint_perms@[e_ptr].value().owning_container].value().owned_endpoints.node_ref_valid(self.endpoint_perms@[e_ptr].value().container_rev_ptr)
            //         &&
            //         self.container_perms@[self.endpoint_perms@[e_ptr].value().owning_container].value().owned_endpoints.node_ref_resolve(self.endpoint_perms@[e_ptr].value().container_rev_ptr) == e_ptr);
        };
        assert(self.schedulers_wf()) by {
            seq_push_lemma::<ThreadPtr>();
            assert(self.container_tree.get_container(container_ptr).scheduler@ =~= old(self).container_tree.get_container(container_ptr).scheduler@.push(page_ptr));
            assert(
                forall|child_t_ptr:ThreadPtr| 
                #![auto]
                old(self).container_tree.get_container(container_ptr).scheduler@.contains(child_t_ptr)
                ==> self.thread_perms@.dom().contains(child_t_ptr)
                    &&
                    self.thread_perms@[child_t_ptr].value().owning_container == container_ptr
            );
        };
        new_thread_ptr
    } 


    pub fn new_proc_with_endpoint(&mut self, thread_ptr:ThreadPtr, endpoint_index:EndpointIdx, pt_regs:&Registers, page_ptr_1: PagePtr, page_perm_1: Tracked<PagePerm4k>, page_ptr_2: PagePtr, page_perm_2: Tracked<PagePerm4k>, new_pcid:Pcid)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            old(self).page_closure().contains(page_ptr_1) == false,
            old(self).page_closure().contains(page_ptr_2) == false,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).mem_quota >= 2,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).owned_procs.len() < CONTAINER_PROC_LIST_LEN,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).scheduler.len() < MAX_CONTAINER_SCHEDULER_LEN,
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_endpoint_by_endpoint_idx(thread_ptr, endpoint_index).is_Some() || old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).is_Some(),
            old(self).get_endpoint_by_endpoint_idx(thread_ptr, endpoint_index).unwrap().rf_counter_is_full() == false || old(self).get_endpoint(old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap()).rf_counter_is_full() == false,
            forall|p_ptr_i:ProcPtr| 
                #![trigger old(self).proc_dom().contains(p_ptr_i) ]
                old(self).proc_dom().contains(p_ptr_i) 
                ==>
                old(self).get_proc(p_ptr_i).pcid != new_pcid,
            page_perm_1@.is_init(),
            page_perm_1@.addr() == page_ptr_1,
            page_perm_2@.is_init(),
            page_perm_2@.addr() == page_ptr_2,
            page_ptr_1 != page_ptr_2,
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure().insert(page_ptr_1).insert(page_ptr_2),
            self.proc_dom() =~= old(self).proc_dom().insert(page_ptr_1),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom().insert(page_ptr_2),
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).mem_quota - 2 == self.get_container(self.get_thread(thread_ptr).owning_container).mem_quota,
            forall|p_ptr:ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                old(self).proc_dom().contains(p_ptr)
                ==> 
                self.get_proc(p_ptr) =~= old(self).get_proc(p_ptr),
            forall|container_ptr:ContainerPtr|
                #![trigger self.get_container(container_ptr)]
                self.container_dom().contains(container_ptr) && container_ptr != self.get_thread(thread_ptr).owning_container
                ==> 
                self.get_container(container_ptr) =~= old(self).get_container(container_ptr),
            forall|t_ptr:ThreadPtr| 
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr)
                ==>
                old(self).get_thread(t_ptr) =~= self.get_thread(t_ptr),
            forall|e_ptr:EndpointPtr| 
                #![trigger self.get_endpoint(e_ptr)]
                self.endpoint_dom().contains(e_ptr) && e_ptr != old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap()
                ==> 
                old(self).get_endpoint(e_ptr) =~= self.get_endpoint(e_ptr),
            self.get_proc(page_ptr_1).pcid =~= new_pcid,
            self.get_proc(page_ptr_1).ioid.is_None(),
            self.get_proc(page_ptr_1).owned_threads@ == Seq::<ThreadPtr>::empty().push(page_ptr_2),
            self.get_proc(page_ptr_1).owning_container == self.get_thread(thread_ptr).owning_container,
            self.get_container(self.get_thread(thread_ptr).owning_container).owned_procs@ =~= old(self).get_container(self.get_thread(thread_ptr).owning_container).owned_procs@.push(page_ptr_1),
            self.get_container(self.get_thread(thread_ptr).owning_container).owned_endpoints@ =~= old(self).get_container(self.get_thread(thread_ptr).owning_container).owned_endpoints@,
            self.get_container(self.get_thread(thread_ptr).owning_container).owned_threads@ =~= old(self).get_container(self.get_thread(thread_ptr).owning_container).owned_threads@.insert(page_ptr_2),
            self.get_thread(page_ptr_2).owning_container == old(self).get_thread(thread_ptr).owning_container,
            self.get_thread(page_ptr_2).endpoint_descriptors@ =~= Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat,|i: int| {None}).update(0, Some(old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap())),
            self.get_endpoint(old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap()).owning_threads@ =~= old(self).get_endpoint(old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap()).owning_threads@.insert(page_ptr_2),
    {
        // proof{seq_push_lemma::<ThreadPtr>();}
        let container_ptr = self.get_thread(thread_ptr).owning_container;
        let old_mem_quota =  self.get_container(container_ptr).mem_quota;
        let old_owned_threads = self.get_container(container_ptr).owned_threads;
        let endpoint_ptr = self.get_thread(thread_ptr).endpoint_descriptors.get(endpoint_index).unwrap();

        let proc_list_node_ref = self.container_tree.container_tree_push_proc(container_ptr, page_ptr_1);
        let scheduler_node_ref = self.container_tree.container_tree_scheduler_push_thread(container_ptr, page_ptr_2);
        self.container_tree.container_tree_set_quota(container_ptr, old_mem_quota - 2);
        self.container_tree.container_tree_set_owned_threads(container_ptr, Ghost(old_owned_threads@.insert(page_ptr_2)));

        let (new_proc_ptr, mut proc_perm, proc_thread_list_node_ref) = page_to_proc_with_first_thread(page_ptr_1, page_perm_1, container_ptr, proc_list_node_ref, new_pcid, None, page_ptr_2);
        proof {
            self.process_perms.borrow_mut().tracked_insert(new_proc_ptr, proc_perm.get());
        }

        let (new_thread_ptr, thread_perm) = page_to_thread_with_endpoint(page_ptr_2, page_perm_2, pt_regs, container_ptr, new_proc_ptr, proc_thread_list_node_ref, scheduler_node_ref, endpoint_ptr);
        proof {
            self.thread_perms.borrow_mut().tracked_insert(new_thread_ptr, thread_perm.get());
        }

        let mut endpoint_perm = Tracked(self.endpoint_perms.borrow_mut().tracked_remove(endpoint_ptr));
        endpoint_add_ref(endpoint_ptr,&mut endpoint_perm, new_thread_ptr);
        proof {
            self.endpoint_perms.borrow_mut().tracked_insert(endpoint_ptr, endpoint_perm.get());
        }

        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.container_perms_wf());
        assert(self.processes_container_wf()) by {
            seq_push_lemma::<ProcPtr>();
            assert(self.process_perms@[new_proc_ptr].value().owning_container == container_ptr);
            assert(self.process_perms@.dom().contains(new_proc_ptr));
            assert(
                forall|child_p_ptr:ProcPtr| 
                    #![trigger old(self).container_tree.get_container(container_ptr).owned_procs@.contains(child_p_ptr) ]
                    (old(self).container_tree.get_container(container_ptr).owned_procs@.contains(child_p_ptr) || child_p_ptr == new_proc_ptr)
                    <==> 
                    self.container_tree.get_container(container_ptr).owned_procs@.contains(child_p_ptr)
            );
            // assert(forall|c_ptr:ContainerPtr, child_p_ptr:ProcPtr| 
            //     #![trigger self.container_tree.get_container(c_ptr).owned_procs@.contains(child_p_ptr)]
            //     self.container_tree.container_dom().contains(c_ptr) && self.container_tree.get_container(c_ptr).owned_procs@.contains(child_p_ptr) && c_ptr != container_ptr
            //     ==> 
            //     self.process_perms@.dom().contains(child_p_ptr)
            //     &&
            //     self.process_perms@[child_p_ptr].value().owning_container == c_ptr);
            assert(forall|c_ptr:ContainerPtr, child_p_ptr:ProcPtr| 
                #![trigger self.container_tree.get_container(c_ptr).owned_procs@.contains(child_p_ptr)]
                self.container_tree.container_dom().contains(c_ptr) && old(self).container_tree.get_container(c_ptr).owned_procs@.contains(child_p_ptr) && c_ptr == container_ptr 
                ==> 
                self.process_perms@.dom().contains(child_p_ptr)
                &&
                self.process_perms@[child_p_ptr].value().owning_container == c_ptr);
            assert(forall|c_ptr:ContainerPtr, child_p_ptr:ProcPtr| 
                #![trigger self.container_tree.get_container(c_ptr).owned_procs@.contains(child_p_ptr)]
                self.container_tree.container_dom().contains(c_ptr) && self.container_tree.get_container(c_ptr).owned_procs@.contains(child_p_ptr) && c_ptr == container_ptr 
                ==> 
                self.process_perms@.dom().contains(child_p_ptr)
                &&
                self.process_perms@[child_p_ptr].value().owning_container == c_ptr);
            // assert(forall|p_ptr:ProcPtr| 
            //     #![trigger self.process_perms@[p_ptr].value().owning_container]
            //     self.process_perms@.dom().contains(p_ptr)
            //     ==>
            //     self.container_tree.container_dom().contains(self.process_perms@[p_ptr].value().owning_container)
            //     &&
            //     self.container_perms@[self.process_perms@[p_ptr].value().owning_container].value().owned_procs@.to_set().contains(p_ptr)
            //     &&
            //     self.container_perms@[self.process_perms@[p_ptr].value().owning_container].value().owned_procs.node_ref_valid(self.process_perms@[p_ptr].value().rev_ptr)
            //     &&
            //     self.container_perms@[self.process_perms@[p_ptr].value().owning_container].value().owned_procs.node_ref_resolve(self.process_perms@[p_ptr].value().rev_ptr) == p_ptr);
        };
        assert(self.processes_wf());

        assert(self.threads_process_wf()) by {
            seq_push_lemma::<ThreadPtr>();
            // assert(self.process_perms@[new_proc_ptr].value().owned_threads@ =~= Seq::<ThreadPtr>::empty().push(new_thread_ptr));
            // assert(
            //     forall|child_t_ptr:ThreadPtr| 
            //     #![auto]
            //     self.process_perms@[new_proc_ptr].value().owned_threads@.contains(child_t_ptr)
            //     ==> self.thread_perms@.dom().contains(child_t_ptr)
            //         &&
            //         self.thread_perms@[child_t_ptr].value().owning_proc == new_proc_ptr
            // );
        };
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf());
        assert(self.threads_endpoint_descriptors_wf()) by {
            seq_update_lemma::<Option<EndpointPtr>>();
            assert(forall|i:int| #![auto] 1 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS ==> self.thread_perms@[new_thread_ptr].value().endpoint_descriptors@[i].is_None());
            assert(self.thread_perms@[new_thread_ptr].value().endpoint_descriptors@[0] =~= Some(endpoint_ptr));
        };
        assert(self.endpoints_queue_wf());
        assert(self.endpoints_container_wf());
        assert(self.schedulers_wf()) by {
            seq_push_lemma::<ThreadPtr>();
            assert(self.container_tree.get_container(container_ptr).scheduler@ =~= old(self).container_tree.get_container(container_ptr).scheduler@.push(new_thread_ptr));
            assert(
                forall|child_t_ptr:ThreadPtr| 
                #![auto]
                old(self).container_tree.get_container(container_ptr).scheduler@.contains(child_t_ptr)
                ==> self.thread_perms@.dom().contains(child_t_ptr)
                    &&
                    self.thread_perms@[child_t_ptr].value().owning_container == container_ptr
            );
        };
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf());
    } 

    pub fn new_container_with_endpoint(&mut self, thread_ptr:ThreadPtr, endpoint_index:EndpointIdx, pt_regs:Registers, new_pcid:Pcid, new_quota:usize, page_ptr_1: PagePtr, page_perm_1: Tracked<PagePerm4k>, page_ptr_2: PagePtr, page_perm_2: Tracked<PagePerm4k>, page_ptr_3: PagePtr, page_perm_3: Tracked<PagePerm4k>)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            old(self).page_closure().contains(page_ptr_1) == false,
            old(self).page_closure().contains(page_ptr_2) == false,
            old(self).page_closure().contains(page_ptr_3) == false,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).depth != usize::MAX,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).mem_quota >= 3 + new_quota,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).children.len() < CONTAINER_CHILD_LIST_LEN,
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_endpoint_by_endpoint_idx(thread_ptr, endpoint_index).is_Some() || old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).is_Some(),
            old(self).get_endpoint_by_endpoint_idx(thread_ptr, endpoint_index).unwrap().rf_counter_is_full() == false || old(self).get_endpoint(old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap()).rf_counter_is_full() == false,
            forall|p_ptr_i:ProcPtr| 
                #![trigger old(self).proc_dom().contains(p_ptr_i) ]
                old(self).proc_dom().contains(p_ptr_i) 
                ==>
                old(self).get_proc(p_ptr_i).pcid != new_pcid,
            page_perm_1@.is_init(),
            page_perm_1@.addr() == page_ptr_1,
            page_perm_2@.is_init(),
            page_perm_2@.addr() == page_ptr_2,
            page_perm_3@.is_init(),
            page_perm_3@.addr() == page_ptr_3,
            page_ptr_1 != page_ptr_2,
            page_ptr_1 != page_ptr_3,
            page_ptr_2 != page_ptr_3,
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure().insert(page_ptr_1).insert(page_ptr_2).insert(page_ptr_3),
            self.proc_dom() =~= old(self).proc_dom().insert(page_ptr_2),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom().insert(page_ptr_1),
            self.thread_dom() == old(self).thread_dom().insert(page_ptr_3),
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).mem_quota - 3 - new_quota == self.get_container(self.get_thread(thread_ptr).owning_container).mem_quota,
            forall|p_ptr:ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                old(self).proc_dom().contains(p_ptr)
                ==> 
                self.get_proc(p_ptr) =~= old(self).get_proc(p_ptr),
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_dom().contains(c_ptr)]
                old(self).container_dom().contains(c_ptr) && c_ptr != old(self).get_thread(thread_ptr).owning_container
                ==> 
                self.get_container(c_ptr).owned_procs =~= old(self).get_container(c_ptr).owned_procs
                &&                
                self.get_container(c_ptr).parent =~= old(self).get_container(c_ptr).parent
                &&                
                self.get_container(c_ptr).parent_rev_ptr =~= old(self).get_container(c_ptr).parent_rev_ptr
                &&
                self.get_container(c_ptr).children =~= old(self).get_container(c_ptr).children
                &&
                self.get_container(c_ptr).owned_endpoints =~= old(self).get_container(c_ptr).owned_endpoints
                &&
                self.get_container(c_ptr).mem_quota =~= old(self).get_container(c_ptr).mem_quota
                &&
                self.get_container(c_ptr).mem_used =~= old(self).get_container(c_ptr).mem_used
                &&
                self.get_container(c_ptr).owned_cpus =~= old(self).get_container(c_ptr).owned_cpus
                &&
                self.get_container(c_ptr).scheduler =~= old(self).get_container(c_ptr).scheduler
                &&
                self.get_container(c_ptr).owned_threads =~= old(self).get_container(c_ptr).owned_threads
                &&
                self.get_container(c_ptr).depth =~= old(self).get_container(c_ptr).depth
                &&
                self.get_container(c_ptr).uppertree_seq =~= old(self).get_container(c_ptr).uppertree_seq,
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_dom().contains(c_ptr)]
                self.container_dom().contains(c_ptr) && self.get_container(page_ptr_1).uppertree_seq@.contains(c_ptr)
                ==>
                self.get_container(c_ptr).subtree_set@ =~= self.get_container(c_ptr).subtree_set@.insert(page_ptr_1),
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_dom().contains(c_ptr)]
                self.container_dom().contains(c_ptr) && self.get_container(page_ptr_1).uppertree_seq@.contains(c_ptr) == false
                ==>
                self.get_container(c_ptr).subtree_set =~= self.get_container(c_ptr).subtree_set,
            self.get_container(old(self).get_thread(thread_ptr).owning_container).owned_procs =~= old(self).get_container(old(self).get_thread(thread_ptr).owning_container).owned_procs,
            self.get_container(old(self).get_thread(thread_ptr).owning_container).parent =~= old(self).get_container(old(self).get_thread(thread_ptr).owning_container).parent,
            self.get_container(old(self).get_thread(thread_ptr).owning_container).children@ =~= old(self).get_container(old(self).get_thread(thread_ptr).owning_container).children@.push(page_ptr_1),
            self.get_container(old(self).get_thread(thread_ptr).owning_container).owned_endpoints =~= old(self).get_container(old(self).get_thread(thread_ptr).owning_container).owned_endpoints,
            self.get_container(old(self).get_thread(thread_ptr).owning_container).mem_quota as int =~= old(self).get_container(old(self).get_thread(thread_ptr).owning_container).mem_quota - new_quota - 3,
            self.get_container(old(self).get_thread(thread_ptr).owning_container).mem_used =~= old(self).get_container(old(self).get_thread(thread_ptr).owning_container).mem_used,
            self.get_container(old(self).get_thread(thread_ptr).owning_container).owned_cpus =~= old(self).get_container(old(self).get_thread(thread_ptr).owning_container).owned_cpus,
            self.get_container(old(self).get_thread(thread_ptr).owning_container).scheduler =~= old(self).get_container(old(self).get_thread(thread_ptr).owning_container).scheduler,
            self.get_container(old(self).get_thread(thread_ptr).owning_container).owned_threads =~= old(self).get_container(old(self).get_thread(thread_ptr).owning_container).owned_threads,
            self.get_container(old(self).get_thread(thread_ptr).owning_container).depth =~= old(self).get_container(old(self).get_thread(thread_ptr).owning_container).depth,
            self.get_container(old(self).get_thread(thread_ptr).owning_container).uppertree_seq =~= old(self).get_container(old(self).get_thread(thread_ptr).owning_container).uppertree_seq,
            self.get_container(old(self).get_thread(thread_ptr).owning_container).subtree_set@ =~= old(self).get_container(old(self).get_thread(thread_ptr).owning_container).subtree_set@.insert(page_ptr_1),

            self.get_container(page_ptr_1).owned_procs@ =~= Seq::<ProcPtr>::empty().push(page_ptr_2),
            self.get_container(page_ptr_1).parent =~= Some(old(self).get_thread(thread_ptr).owning_container),
            self.get_container(page_ptr_1).children@ =~= Seq::<ContainerPtr>::empty(),
            self.get_container(page_ptr_1).owned_endpoints.wf(),
            self.get_container(page_ptr_1).owned_endpoints@ =~= Seq::<EndpointPtr>::empty(),
            self.get_container(page_ptr_1).mem_quota =~= new_quota,
            self.get_container(page_ptr_1).mem_used =~= 0,
            self.get_container(page_ptr_1).owned_cpus.wf(),
            self.get_container(page_ptr_1).owned_cpus@ =~= Set::<CpuId>::empty(),
            self.get_container(page_ptr_1).scheduler.wf(),
            self.get_container(page_ptr_1).scheduler@ =~= Seq::<ThreadPtr>::empty().push(page_ptr_3),
            self.get_container(page_ptr_1).owned_threads@.finite(),
            self.get_container(page_ptr_1).owned_threads@ =~= Set::<ThreadPtr>::empty().insert(page_ptr_3),
            self.get_container(page_ptr_1).depth as int =~= self.get_container(old(self).get_thread(thread_ptr).owning_container).depth + 1,
            self.get_container(page_ptr_1).uppertree_seq@ =~= self.get_container(old(self).get_thread(thread_ptr).owning_container).uppertree_seq@.push(old(self).get_thread(thread_ptr).owning_container),
            self.get_container(page_ptr_1).subtree_set@ =~= Set::<ContainerPtr>::empty(),

            forall|t_ptr:ThreadPtr| 
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr)
                ==>
                old(self).get_thread(t_ptr) =~= self.get_thread(t_ptr),
            forall|e_ptr:EndpointPtr| 
                #![trigger self.get_endpoint(e_ptr)]
                self.endpoint_dom().contains(e_ptr) && e_ptr != old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap()
                ==> 
                old(self).get_endpoint(e_ptr) =~= self.get_endpoint(e_ptr),
            self.get_container(page_ptr_1).children@ == Seq::<ContainerPtr>::empty(),
            self.get_container(page_ptr_1).owned_procs@ == Seq::<ProcPtr>::empty().push(page_ptr_2),
            self.get_container(page_ptr_1).owned_threads@ == Set::<ThreadPtr>::empty().insert(page_ptr_3),
            self.get_container(page_ptr_1).mem_quota == new_quota,
            self.get_proc(page_ptr_2).pcid =~= new_pcid,
            self.get_proc(page_ptr_2).ioid.is_None(),
            self.get_proc(page_ptr_2).owned_threads@ == Seq::<ThreadPtr>::empty().push(page_ptr_3),
            self.get_proc(page_ptr_2).owning_container == page_ptr_1,
            self.get_thread(page_ptr_3).owning_container == page_ptr_1,
            self.get_thread(page_ptr_3).endpoint_descriptors@ =~= Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat,|i: int| {None}).update(0, Some(old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap())),
            self.get_container(self.get_thread(thread_ptr).owning_container).children@ =~= old(self).get_container(self.get_thread(thread_ptr).owning_container).children@.push(page_ptr_1),
            self.get_container(self.get_thread(thread_ptr).owning_container).owned_procs@ =~= old(self).get_container(self.get_thread(thread_ptr).owning_container).owned_procs@,
            self.get_container(self.get_thread(thread_ptr).owning_container).owned_endpoints@ =~= old(self).get_container(self.get_thread(thread_ptr).owning_container).owned_endpoints@,
            self.get_container(self.get_thread(thread_ptr).owning_container).owned_threads@ =~= old(self).get_container(self.get_thread(thread_ptr).owning_container).owned_threads@,
            self.get_endpoint(old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap()).owning_threads@ =~= old(self).get_endpoint(old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap()).owning_threads@.insert(page_ptr_3),
    {
        let container_ptr = self.get_thread(thread_ptr).owning_container;
        let old_mem_quota =  self.get_container(container_ptr).mem_quota;
        let endpoint_ptr = self.get_thread(thread_ptr).endpoint_descriptors.get(endpoint_index).unwrap();

        self.container_tree.new_container(container_ptr, new_quota, page_ptr_1, page_perm_1);
        let proc_list_node_ref = self.container_tree.container_tree_push_proc(page_ptr_1, page_ptr_2);
        let scheduler_node_ref = self.container_tree.container_tree_scheduler_push_thread(page_ptr_1, page_ptr_3);
        self.container_tree.container_tree_set_owned_threads(page_ptr_1, Ghost(Set::<ThreadPtr>::empty().insert(page_ptr_3)));

        let (new_proc_ptr, mut proc_perm, proc_thread_list_node_ref) = page_to_proc_with_first_thread(page_ptr_2, page_perm_2, page_ptr_1, proc_list_node_ref, new_pcid, None, page_ptr_3);
        proof {
            self.process_perms.borrow_mut().tracked_insert(new_proc_ptr, proc_perm.get());
        }

        let (new_thread_ptr, thread_perm) = page_to_thread_with_endpoint(page_ptr_3, page_perm_3, &pt_regs, page_ptr_1, new_proc_ptr, proc_thread_list_node_ref, scheduler_node_ref, endpoint_ptr);
        proof {
            self.thread_perms.borrow_mut().tracked_insert(new_thread_ptr, thread_perm.get());
        }

        let mut endpoint_perm = Tracked(self.endpoint_perms.borrow_mut().tracked_remove(endpoint_ptr));
        endpoint_add_ref(endpoint_ptr,&mut endpoint_perm, new_thread_ptr);
        proof {
            self.endpoint_perms.borrow_mut().tracked_insert(endpoint_ptr, endpoint_perm.get());
        }

        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint()) by {
        };
        assert(self.container_perms_wf());
        assert(self.processes_container_wf()) by {
            seq_push_lemma::<ProcPtr>();
        };
        assert(self.processes_wf());

        assert(self.threads_process_wf()) by {
            seq_push_lemma::<ThreadPtr>();
        };
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf());
        assert(self.threads_endpoint_descriptors_wf()) by {
            seq_update_lemma::<Option<EndpointPtr>>();
            assert(forall|i:int| #![auto] 1 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS ==> self.thread_perms@[new_thread_ptr].value().endpoint_descriptors@[i].is_None());
            assert(self.thread_perms@[new_thread_ptr].value().endpoint_descriptors@[0] =~= Some(endpoint_ptr));
        };
        assert(self.endpoints_queue_wf());
        assert(self.endpoints_container_wf());
        assert(self.schedulers_wf()) by {
            seq_push_lemma::<ThreadPtr>();
        };
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf());

    }

    pub fn schedule_blocked_thread(&mut self, endpoint_ptr:EndpointPtr)
        requires
            old(self).wf(),
            old(self).endpoint_dom().contains(endpoint_ptr),
            old(self).get_endpoint(endpoint_ptr).queue.len() > 0,
            old(self).get_container(old(self).get_thread(old(self).get_endpoint(endpoint_ptr).queue@[0]).owning_container).scheduler.len() < MAX_CONTAINER_SCHEDULER_LEN,
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure(),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom(),
            forall|p_ptr:ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                old(self).proc_dom().contains(p_ptr)
                ==> 
                self.get_proc(p_ptr) =~= old(self).get_proc(p_ptr),
            forall|container_ptr:ContainerPtr|
                #![trigger self.get_container(container_ptr)]
                old(self).container_dom().contains(container_ptr) && container_ptr != old(self).get_thread(old(self).get_endpoint(endpoint_ptr).queue@[0]).owning_container
                ==> 
                self.get_container(container_ptr) =~= old(self).get_container(container_ptr),
            forall|t_ptr:ThreadPtr| 
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr) && t_ptr != old(self).get_endpoint(endpoint_ptr).queue@[0]
                ==>
                old(self).get_thread(t_ptr) =~= self.get_thread(t_ptr),
            forall|e_ptr:EndpointPtr| 
                #![trigger self.get_endpoint(e_ptr)]
                self.endpoint_dom().contains(e_ptr) && e_ptr != endpoint_ptr
                ==> 
                old(self).get_endpoint(e_ptr) =~= self.get_endpoint(e_ptr),
            self.get_thread(old(self).get_endpoint(endpoint_ptr).queue@[0]).endpoint_descriptors =~= old(self).get_thread(old(self).get_endpoint(endpoint_ptr).queue@[0]).endpoint_descriptors,
            self.get_container(old(self).get_thread(old(self).get_endpoint(endpoint_ptr).queue@[0]).owning_container).owned_procs =~= old(self).get_container(old(self).get_thread(old(self).get_endpoint(endpoint_ptr).queue@[0]).owning_container).owned_procs,
            self.get_container(old(self).get_thread(old(self).get_endpoint(endpoint_ptr).queue@[0]).owning_container).owned_threads =~= old(self).get_container(old(self).get_thread(old(self).get_endpoint(endpoint_ptr).queue@[0]).owning_container).owned_threads,
            self.get_container(old(self).get_thread(old(self).get_endpoint(endpoint_ptr).queue@[0]).owning_container).children =~= old(self).get_container(old(self).get_thread(old(self).get_endpoint(endpoint_ptr).queue@[0]).owning_container).children,
            self.get_endpoint(endpoint_ptr).queue@ == old(self).get_endpoint(endpoint_ptr).queue@.skip(1),
            self.get_endpoint(endpoint_ptr).owning_threads == old(self).get_endpoint(endpoint_ptr).owning_threads,
            self.get_endpoint(endpoint_ptr).rf_counter == old(self).get_endpoint(endpoint_ptr).rf_counter,
            self.get_endpoint(endpoint_ptr).queue_state == old(self).get_endpoint(endpoint_ptr).queue_state,
    {
        let thread_ptr = self.get_endpoint(endpoint_ptr).queue.get_head();
        let container_ptr = self.get_thread(thread_ptr).owning_container;


        let scheduler_node_ref = self.container_tree.container_tree_scheduler_push_thread(container_ptr, thread_ptr);


        let mut endpoint_perm = Tracked(self.endpoint_perms.borrow_mut().tracked_remove(endpoint_ptr));
        let (ret_thread_ptr, sll) = endpoint_pop_head(endpoint_ptr,&mut endpoint_perm);
        assert(thread_ptr == ret_thread_ptr);
        proof {
            self.endpoint_perms.borrow_mut().tracked_insert(endpoint_ptr, endpoint_perm.get());
        }

        let mut thread_perm = Tracked(self.thread_perms.borrow_mut().tracked_remove(thread_ptr));
        thread_set_blocking_endpoint_endpoint_ref_scheduler_ref_state_and_ipc_payload(thread_ptr, &mut thread_perm, None, None, Some(scheduler_node_ref), ThreadState::SCHEDULED, IPCPayLoad::Empty);
        proof {
            self.thread_perms.borrow_mut().tracked_insert(thread_ptr, thread_perm.get());
        }

        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint()) by {
        };
        assert(self.container_perms_wf());
        assert(self.processes_container_wf()) by {
            seq_push_lemma::<ProcPtr>();
        };
        assert(self.processes_wf());

        assert(self.threads_process_wf()) by {
            seq_push_lemma::<ThreadPtr>();
        };
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf()) by {
            seq_skip_lemma::<ThreadPtr>();
        };
        assert(self.threads_endpoint_descriptors_wf());
        assert(self.endpoints_queue_wf()) by {
            seq_skip_lemma::<ThreadPtr>();
            old(self).get_endpoint(endpoint_ptr).queue.unique_implys_no_duplicates();
        };
        assert(self.endpoints_container_wf());
        assert(self.schedulers_wf()) by {
            seq_push_lemma::<ThreadPtr>();
        };
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf());
    }
    
    /// Overview:
    /// yield the given thread 
    /// save the payload onto given thread
    /// push given thread onto endpoint queue 
    pub fn block_running_thread(&mut self, thread_ptr:ThreadPtr, endpoint_index:EndpointIdx, ipc_payload:IPCPayLoad)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].is_Some(),
            old(self).get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).queue.len() < MAX_NUM_THREADS_PER_ENDPOINT,
            old(self).get_thread(thread_ptr).state == ThreadState::RUNNING,
            ipc_payload.get_payload_as_va_range().is_Some() ==> ipc_payload.get_payload_as_va_range().unwrap().wf(),
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure(),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom(),
            forall|p_ptr:ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                old(self).proc_dom().contains(p_ptr)
                ==> 
                self.get_proc(p_ptr) =~= old(self).get_proc(p_ptr),
            forall|container_ptr:ContainerPtr|
                #![trigger self.get_container(container_ptr)]
                old(self).container_dom().contains(container_ptr)
                ==> 
                self.get_container(container_ptr) =~= old(self).get_container(container_ptr),
            forall|t_ptr:ThreadPtr| 
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr) && t_ptr != thread_ptr
                ==>
                old(self).get_thread(t_ptr) =~= self.get_thread(t_ptr),
            forall|e_ptr:EndpointPtr| 
                #![trigger self.get_endpoint(e_ptr)]
                self.endpoint_dom().contains(e_ptr) && e_ptr != old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()
                ==> 
                old(self).get_endpoint(e_ptr) =~= self.get_endpoint(e_ptr),
            self.get_thread(thread_ptr).endpoint_descriptors =~= old(self).get_thread(thread_ptr).endpoint_descriptors,
            self.get_thread(thread_ptr).ipc_payload =~= ipc_payload,
            self.get_thread(thread_ptr).state == ThreadState::BLOCKED,
            self.get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).queue_state == old(self).get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).queue_state,
            self.get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).owning_threads == old(self).get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).owning_threads,
            self.get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).queue@ == old(self).get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).queue@.push(thread_ptr),
    {
        proof{old(self).get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).queue.unique_implys_no_duplicates();}
        let endpoint_ptr = self.get_thread(thread_ptr).endpoint_descriptors.get(endpoint_index).unwrap();
        let cpu_id = self.get_thread(thread_ptr).running_cpu.unwrap();
        let old_cpu = *self.cpu_list.get(cpu_id);

        let mut endpoint_perm = Tracked(self.endpoint_perms.borrow_mut().tracked_remove(endpoint_ptr));
        let sll = endpoint_push(endpoint_ptr,&mut endpoint_perm, thread_ptr);
        proof {
            self.endpoint_perms.borrow_mut().tracked_insert(endpoint_ptr, endpoint_perm.get());
        }
        let mut thread_perm = Tracked(self.thread_perms.borrow_mut().tracked_remove(thread_ptr));
        thread_set_blocking_endpoint_endpoint_ref_scheduler_ref_state_and_ipc_payload(thread_ptr, &mut thread_perm, Some(endpoint_ptr), Some(sll), None, ThreadState::BLOCKED, ipc_payload);
        proof {
            self.thread_perms.borrow_mut().tracked_insert(thread_ptr, thread_perm.get());
        }

        self.cpu_list.set(cpu_id, Cpu{ owning_container: old_cpu.owning_container, active: old_cpu.active, current_thread: None});

        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint()) by {
        };
        assert(self.container_perms_wf());
        assert(self.processes_container_wf()) by {
        };
        assert(self.processes_wf());

        assert(self.threads_process_wf()) by {
        };
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf()) by {
            seq_push_lemma::<ThreadPtr>();
        };
        assert(self.threads_endpoint_descriptors_wf());
        assert(self.endpoints_queue_wf()) by {
            seq_push_lemma::<ThreadPtr>();
        };
        assert(self.endpoints_container_wf());
        assert(self.schedulers_wf()) by {
        };
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf());
    }

    pub fn block_running_thread_and_set_trap_frame(&mut self, thread_ptr:ThreadPtr, endpoint_index:EndpointIdx, ipc_payload:IPCPayLoad, pt_regs:&Registers)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].is_Some(),
            old(self).get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).queue.len() < MAX_NUM_THREADS_PER_ENDPOINT,
            old(self).get_thread(thread_ptr).state == ThreadState::RUNNING,
            ipc_payload.get_payload_as_va_range().is_Some() ==> ipc_payload.get_payload_as_va_range().unwrap().wf(),
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure(),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom(),
            forall|p_ptr:ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                old(self).proc_dom().contains(p_ptr)
                ==> 
                self.get_proc(p_ptr) =~= old(self).get_proc(p_ptr),
            forall|container_ptr:ContainerPtr|
                #![trigger self.get_container(container_ptr)]
                old(self).container_dom().contains(container_ptr)
                ==> 
                self.get_container(container_ptr) =~= old(self).get_container(container_ptr),
            forall|t_ptr:ThreadPtr| 
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr) && t_ptr != thread_ptr
                ==>
                old(self).get_thread(t_ptr) =~= self.get_thread(t_ptr),
            forall|e_ptr:EndpointPtr| 
                #![trigger self.get_endpoint(e_ptr)]
                self.endpoint_dom().contains(e_ptr) && e_ptr != old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()
                ==> 
                old(self).get_endpoint(e_ptr) =~= self.get_endpoint(e_ptr),
            self.get_thread(thread_ptr).endpoint_descriptors =~= old(self).get_thread(thread_ptr).endpoint_descriptors,
            self.get_thread(thread_ptr).ipc_payload =~= ipc_payload,
            self.get_thread(thread_ptr).state == ThreadState::BLOCKED,
            self.get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).queue_state == old(self).get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).queue_state,
            self.get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).owning_threads == old(self).get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).owning_threads,
            self.get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).queue@ == old(self).get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).queue@.push(thread_ptr),
    {
        proof{old(self).get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).queue.unique_implys_no_duplicates();}
        let endpoint_ptr = self.get_thread(thread_ptr).endpoint_descriptors.get(endpoint_index).unwrap();
        let cpu_id = self.get_thread(thread_ptr).running_cpu.unwrap();
        let old_cpu = *self.cpu_list.get(cpu_id);

        let mut endpoint_perm = Tracked(self.endpoint_perms.borrow_mut().tracked_remove(endpoint_ptr));
        let sll = endpoint_push(endpoint_ptr,&mut endpoint_perm, thread_ptr);
        proof {
            self.endpoint_perms.borrow_mut().tracked_insert(endpoint_ptr, endpoint_perm.get());
        }
        let mut thread_perm = Tracked(self.thread_perms.borrow_mut().tracked_remove(thread_ptr));
        thread_set_blocking_endpoint_endpoint_ref_scheduler_ref_state_and_ipc_payload(thread_ptr, &mut thread_perm, Some(endpoint_ptr), Some(sll), None, ThreadState::BLOCKED, ipc_payload);
        thread_set_trap_frame_fast(thread_ptr, &mut thread_perm, pt_regs);
        proof {
            self.thread_perms.borrow_mut().tracked_insert(thread_ptr, thread_perm.get());
        }

        self.cpu_list.set(cpu_id, Cpu{ owning_container: old_cpu.owning_container, active: old_cpu.active, current_thread: None});

        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint()) by {
        };
        assert(self.container_perms_wf());
        assert(self.processes_container_wf()) by {
        };
        assert(self.processes_wf());

        assert(self.threads_process_wf()) by {
        };
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf()) by {
            seq_push_lemma::<ThreadPtr>();
        };
        assert(self.threads_endpoint_descriptors_wf());
        assert(self.endpoints_queue_wf()) by {
            seq_push_lemma::<ThreadPtr>();
        };
        assert(self.endpoints_container_wf());
        assert(self.schedulers_wf()) by {
        };
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf());
    }

    pub fn block_running_thread_and_change_queue_state(&mut self, thread_ptr:ThreadPtr, endpoint_index:EndpointIdx, ipc_payload:IPCPayLoad, queue_state:EndpointState)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].is_Some(),
            old(self).get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).queue.len() < MAX_NUM_THREADS_PER_ENDPOINT,
            old(self).get_thread(thread_ptr).state == ThreadState::RUNNING,
            ipc_payload.get_payload_as_va_range().is_Some() ==> ipc_payload.get_payload_as_va_range().unwrap().wf(),
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure(),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom(),
            forall|p_ptr:ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                old(self).proc_dom().contains(p_ptr)
                ==> 
                self.get_proc(p_ptr) =~= old(self).get_proc(p_ptr),
            forall|container_ptr:ContainerPtr|
                #![trigger self.get_container(container_ptr)]
                old(self).container_dom().contains(container_ptr)
                ==> 
                self.get_container(container_ptr) =~= old(self).get_container(container_ptr),
            forall|t_ptr:ThreadPtr| 
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr) && t_ptr != thread_ptr
                ==>
                old(self).get_thread(t_ptr) =~= self.get_thread(t_ptr),
            forall|e_ptr:EndpointPtr| 
                #![trigger self.get_endpoint(e_ptr)]
                self.endpoint_dom().contains(e_ptr) && e_ptr != old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()
                ==> 
                old(self).get_endpoint(e_ptr) =~= self.get_endpoint(e_ptr),
            self.get_thread(thread_ptr).endpoint_descriptors =~= old(self).get_thread(thread_ptr).endpoint_descriptors,
            self.get_thread(thread_ptr).ipc_payload =~= ipc_payload,
            self.get_thread(thread_ptr).state == ThreadState::BLOCKED,
            self.get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).queue_state == queue_state,
            self.get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).owning_threads == old(self).get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).owning_threads,
            self.get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).queue@ == old(self).get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).queue@.push(thread_ptr),
    {
        let endpoint_ptr = self.get_thread(thread_ptr).endpoint_descriptors.get(endpoint_index).unwrap();
        proof{old(self).get_endpoint(endpoint_ptr).queue.unique_implys_no_duplicates();}
        let cpu_id = self.get_thread(thread_ptr).running_cpu.unwrap();
        let old_cpu = *self.cpu_list.get(cpu_id);

        let mut endpoint_perm = Tracked(self.endpoint_perms.borrow_mut().tracked_remove(endpoint_ptr));
        let sll = endpoint_push_and_set_state(endpoint_ptr,&mut endpoint_perm, thread_ptr, queue_state);
        proof {
            self.endpoint_perms.borrow_mut().tracked_insert(endpoint_ptr, endpoint_perm.get());
        }
        let mut thread_perm = Tracked(self.thread_perms.borrow_mut().tracked_remove(thread_ptr));
        thread_set_blocking_endpoint_endpoint_ref_scheduler_ref_state_and_ipc_payload(thread_ptr, &mut thread_perm, Some(endpoint_ptr), Some(sll), None, ThreadState::BLOCKED, ipc_payload);
        proof {
            self.thread_perms.borrow_mut().tracked_insert(thread_ptr, thread_perm.get());
        }

        self.cpu_list.set(cpu_id, Cpu{ owning_container: old_cpu.owning_container, active: old_cpu.active, current_thread: None});

        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint()) by {
        };
        assert(self.container_perms_wf());
        assert(self.processes_container_wf()) by {
        };
        assert(self.processes_wf());

        assert(self.threads_process_wf()) by {
        };
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf()) by {
            seq_push_lemma::<ThreadPtr>();
        };
        assert(self.threads_endpoint_descriptors_wf());
        assert(self.endpoints_queue_wf()) by {
            seq_push_lemma::<ThreadPtr>();
        };
        assert(self.endpoints_container_wf());
        assert(self.schedulers_wf()) by {
        };
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf());

    }

    pub fn block_running_thread_and_change_queue_state_and_set_trap_frame(&mut self, thread_ptr:ThreadPtr, endpoint_index:EndpointIdx, ipc_payload:IPCPayLoad, queue_state:EndpointState, pt_regs:&Registers)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].is_Some(),
            old(self).get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).queue.len() < MAX_NUM_THREADS_PER_ENDPOINT,
            old(self).get_thread(thread_ptr).state == ThreadState::RUNNING,
            ipc_payload.get_payload_as_va_range().is_Some() ==> ipc_payload.get_payload_as_va_range().unwrap().wf(),
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure(),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom(),
            forall|p_ptr:ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                old(self).proc_dom().contains(p_ptr)
                ==> 
                self.get_proc(p_ptr) =~= old(self).get_proc(p_ptr),
            forall|container_ptr:ContainerPtr|
                #![trigger self.get_container(container_ptr)]
                old(self).container_dom().contains(container_ptr)
                ==> 
                self.get_container(container_ptr) =~= old(self).get_container(container_ptr),
            forall|t_ptr:ThreadPtr| 
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr) && t_ptr != thread_ptr
                ==>
                old(self).get_thread(t_ptr) =~= self.get_thread(t_ptr),
            forall|e_ptr:EndpointPtr| 
                #![trigger self.get_endpoint(e_ptr)]
                self.endpoint_dom().contains(e_ptr) && e_ptr != old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()
                ==> 
                old(self).get_endpoint(e_ptr) =~= self.get_endpoint(e_ptr),
            self.get_thread(thread_ptr).endpoint_descriptors =~= old(self).get_thread(thread_ptr).endpoint_descriptors,
            self.get_thread(thread_ptr).ipc_payload =~= ipc_payload,
            self.get_thread(thread_ptr).state == ThreadState::BLOCKED,
            self.get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).queue_state == queue_state,
            self.get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).owning_threads == old(self).get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).owning_threads,
            self.get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).queue@ == old(self).get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap()).queue@.push(thread_ptr),
    {
        let endpoint_ptr = self.get_thread(thread_ptr).endpoint_descriptors.get(endpoint_index).unwrap();
        proof{old(self).get_endpoint(endpoint_ptr).queue.unique_implys_no_duplicates();}
        let cpu_id = self.get_thread(thread_ptr).running_cpu.unwrap();
        let old_cpu = *self.cpu_list.get(cpu_id);

        let mut endpoint_perm = Tracked(self.endpoint_perms.borrow_mut().tracked_remove(endpoint_ptr));
        let sll = endpoint_push_and_set_state(endpoint_ptr,&mut endpoint_perm, thread_ptr, queue_state);
        proof {
            self.endpoint_perms.borrow_mut().tracked_insert(endpoint_ptr, endpoint_perm.get());
        }
        let mut thread_perm = Tracked(self.thread_perms.borrow_mut().tracked_remove(thread_ptr));
        thread_set_blocking_endpoint_endpoint_ref_scheduler_ref_state_and_ipc_payload(thread_ptr, &mut thread_perm, Some(endpoint_ptr), Some(sll), None, ThreadState::BLOCKED, ipc_payload);
        thread_set_trap_frame_fast(thread_ptr, &mut thread_perm, pt_regs);
        proof {
            self.thread_perms.borrow_mut().tracked_insert(thread_ptr, thread_perm.get());
        }

        self.cpu_list.set(cpu_id, Cpu{ owning_container: old_cpu.owning_container, active: old_cpu.active, current_thread: None});

        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint()) by {
        };
        assert(self.container_perms_wf());
        assert(self.processes_container_wf()) by {
        };
        assert(self.processes_wf());

        assert(self.threads_process_wf()) by {
        };
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf()) by {
            seq_push_lemma::<ThreadPtr>();
        };
        assert(self.threads_endpoint_descriptors_wf());
        assert(self.endpoints_queue_wf()) by {
            seq_push_lemma::<ThreadPtr>();
        };
        assert(self.endpoints_container_wf());
        assert(self.schedulers_wf()) by {
        };
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf());

    }

    pub fn pass_endpoint(&mut self, src_thread_ptr:ThreadPtr, src_endpoint_index:EndpointIdx, dst_thread_ptr:ThreadPtr, dst_endpoint_index:EndpointIdx)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(src_thread_ptr),
            old(self).thread_dom().contains(dst_thread_ptr),
            src_thread_ptr != dst_thread_ptr,
            0 <= src_endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            0 <= dst_endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(src_thread_ptr).endpoint_descriptors@[src_endpoint_index as int].is_Some(),
            old(self).get_endpoint(old(self).get_thread(src_thread_ptr).endpoint_descriptors@[src_endpoint_index as int].unwrap()).rf_counter != usize::MAX,
            old(self).get_thread(dst_thread_ptr).endpoint_descriptors@[dst_endpoint_index as int].is_None(),
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure(),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom(),
            forall|p_ptr:ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                old(self).proc_dom().contains(p_ptr)
                ==> 
                self.get_proc(p_ptr) =~= old(self).get_proc(p_ptr),
            forall|container_ptr:ContainerPtr|
                #![trigger self.get_container(container_ptr)]
                old(self).container_dom().contains(container_ptr)
                ==> 
                self.get_container(container_ptr) =~= old(self).get_container(container_ptr),
            forall|t_ptr:ThreadPtr| 
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr) && t_ptr != dst_thread_ptr
                ==>
                old(self).get_thread(t_ptr) =~= self.get_thread(t_ptr),
            forall|e_ptr:EndpointPtr| 
                #![trigger self.get_endpoint(e_ptr)]
                self.endpoint_dom().contains(e_ptr) && e_ptr != old(self).get_thread(src_thread_ptr).endpoint_descriptors@[src_endpoint_index as int].unwrap()
                ==> 
                old(self).get_endpoint(e_ptr) =~= self.get_endpoint(e_ptr),
            self.get_thread(dst_thread_ptr).endpoint_descriptors@ =~= old(self).get_thread(dst_thread_ptr).endpoint_descriptors@.update(dst_endpoint_index as int, Some(old(self).get_thread(src_thread_ptr).endpoint_descriptors@[src_endpoint_index as int].unwrap())),
            self.get_endpoint(old(self).get_thread(src_thread_ptr).endpoint_descriptors@[src_endpoint_index as int].unwrap()).owning_threads@ == old(self).get_endpoint(old(self).get_thread(src_thread_ptr).endpoint_descriptors@[src_endpoint_index as int].unwrap()).owning_threads@.insert(dst_thread_ptr),
            self.get_endpoint(old(self).get_thread(src_thread_ptr).endpoint_descriptors@[src_endpoint_index as int].unwrap()).queue == old(self).get_endpoint(old(self).get_thread(src_thread_ptr).endpoint_descriptors@[src_endpoint_index as int].unwrap()).queue,
            self.get_endpoint(self.get_thread(src_thread_ptr).endpoint_descriptors@[src_endpoint_index as int].unwrap()).queue_state == old(self).get_endpoint(old(self).get_thread(src_thread_ptr).endpoint_descriptors@[src_endpoint_index as int].unwrap()).queue_state,
    {
        let src_endpoint_ptr = self.get_thread(src_thread_ptr).endpoint_descriptors.get(src_endpoint_index).unwrap();
        let is_dst_thread_owns_src_endpoint = self.get_thread_owns_endpoint(dst_thread_ptr, src_endpoint_ptr);

        let mut dst_thread_perm = Tracked(self.thread_perms.borrow_mut().tracked_remove(dst_thread_ptr));
        thread_set_endpoint_descriptor(dst_thread_ptr, &mut dst_thread_perm, dst_endpoint_index, Some(src_endpoint_ptr));
        proof {
            self.thread_perms.borrow_mut().tracked_insert(dst_thread_ptr, dst_thread_perm.get());
        }

        if is_dst_thread_owns_src_endpoint == false {
            let mut src_endpoint_perm = Tracked(self.endpoint_perms.borrow_mut().tracked_remove(src_endpoint_ptr));
            endpoint_add_ref(src_endpoint_ptr,&mut src_endpoint_perm, dst_thread_ptr);
            proof {
                self.endpoint_perms.borrow_mut().tracked_insert(src_endpoint_ptr, src_endpoint_perm.get());
            }
        }else{
            assert(self.get_endpoint(old(self).get_thread(src_thread_ptr).endpoint_descriptors@[src_endpoint_index as int].unwrap()).owning_threads@.contains(dst_thread_ptr));
            assert(self.get_endpoint(old(self).get_thread(src_thread_ptr).endpoint_descriptors@[src_endpoint_index as int].unwrap()).owning_threads@.insert(dst_thread_ptr) == 
                    self.get_endpoint(old(self).get_thread(src_thread_ptr).endpoint_descriptors@[src_endpoint_index as int].unwrap()).owning_threads@) by {
                        set_insert_lemma::<ThreadPtr>();
                    };
        }
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint()) by {
        };
        assert(self.container_perms_wf());
        assert(self.processes_container_wf()) by {
        };
        assert(self.processes_wf());

        assert(self.threads_process_wf()) by {
        };
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf()) by {
            seq_push_lemma::<ThreadPtr>();
        };
        assert(self.threads_endpoint_descriptors_wf()) by {
            seq_update_lemma::<Option<EndpointPtr>>();
            assert(forall|i:int| #![auto] 0 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS && i != dst_endpoint_index ==> self.thread_perms@[dst_thread_ptr].value().endpoint_descriptors@[i] == old(self).thread_perms@[dst_thread_ptr].value().endpoint_descriptors@[i]);
            assert(self.thread_perms@[dst_thread_ptr].value().endpoint_descriptors@[dst_endpoint_index as int ] =~= Some(src_endpoint_ptr));
        };
        assert(self.endpoints_queue_wf()) by {
            seq_push_lemma::<ThreadPtr>();
        };
        assert(self.endpoints_container_wf());
        assert(self.schedulers_wf()) by {
        };
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf());
        // assert(self.wf());
    }

    pub fn new_endpoint(&mut self, thread_ptr:ThreadPtr, endpoint_index:EndpointIdx, page_ptr_1: PagePtr, page_perm_1: Tracked<PagePerm4k>)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].is_None(),
            old(self).page_closure().contains(page_ptr_1) == false,
            page_perm_1@.is_init(),
            page_perm_1@.addr() == page_ptr_1,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).mem_quota > 0,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).owned_endpoints.len() < CONTAINER_ENDPOINT_LIST_LEN,
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure().insert(page_ptr_1),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom().insert(page_ptr_1),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom(),
            forall|p_ptr:ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr)
                ==> 
                self.get_proc(p_ptr) =~= old(self).get_proc(p_ptr),
            forall|container_ptr:ContainerPtr|
                #![trigger self.get_container(container_ptr)]
                self.container_dom().contains(container_ptr) && container_ptr != old(self).get_thread(thread_ptr).owning_container
                ==> 
                self.get_container(container_ptr) =~= old(self).get_container(container_ptr),
            forall|t_ptr:ThreadPtr| 
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr) && t_ptr != thread_ptr
                ==>
                old(self).get_thread(t_ptr) =~= self.get_thread(t_ptr),
            forall|e_ptr:EndpointPtr| 
                #![trigger self.get_endpoint(e_ptr)]
                old(self).endpoint_dom().contains(e_ptr)
                ==> 
                old(self).get_endpoint(e_ptr) =~= self.get_endpoint(e_ptr),
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).mem_quota - 1 == self.get_container(old(self).get_thread(thread_ptr).owning_container).mem_quota,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).owned_cpus == self.get_container(old(self).get_thread(thread_ptr).owning_container).owned_cpus,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).owned_threads == self.get_container(old(self).get_thread(thread_ptr).owning_container).owned_threads,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).scheduler == self.get_container(old(self).get_thread(thread_ptr).owning_container).scheduler,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).owned_endpoints@.push(page_ptr_1) == self.get_container(old(self).get_thread(thread_ptr).owning_container).owned_endpoints@,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).children == self.get_container(old(self).get_thread(thread_ptr).owning_container).children,
            old(self).get_thread(thread_ptr).ipc_payload =~= self.get_thread(thread_ptr).ipc_payload,
            old(self).get_thread(thread_ptr).state =~= self.get_thread(thread_ptr).state, 
            self.get_thread(thread_ptr).endpoint_descriptors@ =~= old(self).get_thread(thread_ptr).endpoint_descriptors@.update(endpoint_index as int, Some(page_ptr_1)),
            self.get_endpoint(page_ptr_1).queue@ =~= Seq::<ThreadPtr>::empty(),
            self.get_endpoint(page_ptr_1).queue_state =~= EndpointState::SEND,
            self.get_endpoint(page_ptr_1).rf_counter =~= 1,
            self.get_endpoint(page_ptr_1).owning_threads@ =~= Set::<ThreadPtr>::empty().insert(thread_ptr),
            self.get_endpoint(page_ptr_1).owning_container =~= old(self).get_thread(thread_ptr).owning_container,
    {
        let container_ptr = self.get_thread(thread_ptr).owning_container;
        let old_mem_quota = self.get_container(container_ptr).mem_quota;

        self.container_tree.container_tree_set_quota(container_ptr, old_mem_quota - 1);
        let sll_index = self.container_tree.container_tree_push_endpoint(container_ptr, page_ptr_1);

        let (endpoint_ptr, endpoint_perm) = page_to_endpoint_with_thread_and_container(container_ptr, thread_ptr, sll_index, page_ptr_1, page_perm_1);
        proof {
            self.endpoint_perms.borrow_mut().tracked_insert(endpoint_ptr, endpoint_perm.get());
        }

        let mut thread_perm = Tracked(self.thread_perms.borrow_mut().tracked_remove(thread_ptr));
        thread_set_endpoint_descriptor(thread_ptr, &mut thread_perm, endpoint_index, Some(endpoint_ptr));
        proof {
            self.thread_perms.borrow_mut().tracked_insert(thread_ptr, thread_perm.get());
        }

        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint()) by {
        };
        assert(self.container_perms_wf());
        assert(self.processes_container_wf()) by {
        };
        assert(self.processes_wf());

        assert(self.threads_process_wf()) by {
        };
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf()) by {
            seq_push_lemma::<ThreadPtr>();
        };
        assert(self.threads_endpoint_descriptors_wf()) by {
            seq_update_lemma::<Option<EndpointPtr>>();
            assert(self.thread_perms@[thread_ptr].value().endpoint_descriptors@[endpoint_index as int].is_Some() && self.thread_perms@[thread_ptr].value().endpoint_descriptors@[endpoint_index as int].unwrap() == endpoint_ptr);
            assert(
                self.spec_get_thread_owns_endpoint(thread_ptr, endpoint_ptr)
            );
            assert(
                forall|e_ptr:EndpointPtr| 
                #![trigger self.endpoint_perms@[e_ptr].value().owning_threads@.contains(thread_ptr)]
                #![trigger self.spec_get_thread_owns_endpoint(thread_ptr, e_ptr)]
                old(self).endpoint_perms@.dom().contains(e_ptr) 
                &&
                old(self).endpoint_perms@[e_ptr].value().owning_threads@.contains(thread_ptr)
                ==>
                old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].is_None()
                &&
                old(self).spec_get_thread_owns_endpoint(thread_ptr, e_ptr)
            );
            assert(
                forall|e_ptr:EndpointPtr| 
                #![auto]
                old(self).endpoint_perms@.dom().contains(e_ptr) 
                &&
                old(self).endpoint_perms@[e_ptr].value().owning_threads@.contains(thread_ptr)
                ==>
                (
                    exists|i:int| 
                    #![auto]
                    0 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS && endpoint_index != i
                    &&
                    old(self).thread_perms@[thread_ptr].value().endpoint_descriptors@[i].is_Some() && old(self).thread_perms@[thread_ptr].value().endpoint_descriptors@[i].unwrap() == e_ptr
                )
            );
            assert(forall|i:int|
                #![auto]
                0 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS && endpoint_index != i
                ==>
                old(self).thread_perms@[thread_ptr].value().endpoint_descriptors@[i] === self.thread_perms@[thread_ptr].value().endpoint_descriptors@[i]);
            assert(
                forall|e_ptr:EndpointPtr| 
                #![auto]
                old(self).endpoint_perms@.dom().contains(e_ptr) 
                &&
                self.endpoint_perms@[e_ptr].value().owning_threads@.contains(thread_ptr)
                ==>
                (
                    exists|i:int| 
                    #![auto]
                    0 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS && endpoint_index != i
                    &&
                    self.thread_perms@[thread_ptr].value().endpoint_descriptors@[i].is_Some() && self.thread_perms@[thread_ptr].value().endpoint_descriptors@[i].unwrap() == e_ptr
                )
            );

        };
        assert(self.endpoints_queue_wf()) by {
        };
        assert(self.endpoints_container_wf()) by {
            seq_push_lemma::<EndpointPtr>();
        };
        assert(self.schedulers_wf()) by {
        };
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf());
    }

    pub fn pop_scheduler_for_idle_cpu(&mut self, cpu_id: CpuId, pt_regs:&mut Registers) -> (ret:ThreadPtr)
        requires
            old(self).wf(),
            0 <= cpu_id < NUM_CPUS,
            old(self).cpu_list@[cpu_id as int].active == true,
            old(self).cpu_list@[cpu_id as int].current_thread.is_None(),
            old(self).get_container(old(self).cpu_list@[cpu_id as int].owning_container).scheduler.len() != 0,
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure(),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom(),
            self.thread_dom().contains(ret),
            forall|p_ptr:ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr)
                ==> 
                self.get_proc(p_ptr) =~= old(self).get_proc(p_ptr),
            forall|container_ptr:ContainerPtr|
                #![trigger self.get_container(container_ptr)]
                self.container_dom().contains(container_ptr) && container_ptr != old(self).cpu_list@[cpu_id as int].owning_container
                ==> 
                self.get_container(container_ptr) =~= old(self).get_container(container_ptr),
            forall|t_ptr:ThreadPtr| 
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr) && t_ptr != ret
                ==>
                old(self).get_thread(t_ptr) =~= self.get_thread(t_ptr),
            forall|e_ptr:EndpointPtr| 
                #![trigger self.get_endpoint(e_ptr)]
                old(self).endpoint_dom().contains(e_ptr)
                ==> 
                old(self).get_endpoint(e_ptr) =~= self.get_endpoint(e_ptr),
            old(self).get_container(old(self).cpu_list@[cpu_id as int].owning_container).mem_quota == self.get_container(old(self).cpu_list@[cpu_id as int].owning_container).mem_quota,
            old(self).get_container(old(self).cpu_list@[cpu_id as int].owning_container).owned_cpus == self.get_container(old(self).cpu_list@[cpu_id as int].owning_container).owned_cpus,
            old(self).get_container(old(self).cpu_list@[cpu_id as int].owning_container).owned_threads == self.get_container(old(self).cpu_list@[cpu_id as int].owning_container).owned_threads,
            old(self).get_container(old(self).cpu_list@[cpu_id as int].owning_container).scheduler@.skip(1) == self.get_container(old(self).cpu_list@[cpu_id as int].owning_container).scheduler@,
            old(self).get_container(old(self).cpu_list@[cpu_id as int].owning_container).owned_endpoints == self.get_container(old(self).cpu_list@[cpu_id as int].owning_container).owned_endpoints,
            old(self).get_container(old(self).cpu_list@[cpu_id as int].owning_container).children == self.get_container(old(self).cpu_list@[cpu_id as int].owning_container).children,

            old(self).get_thread(ret).ipc_payload =~= self.get_thread(ret).ipc_payload,
            self.get_thread(ret).state =~= ThreadState::RUNNING,
            old(self).get_thread(ret).endpoint_descriptors =~= self.get_thread(ret).endpoint_descriptors,
    {
        let container_ptr = self.cpu_list.get(cpu_id).owning_container;
        assert(self.container_tree.container_dom().contains(container_ptr)) by {
            assert(old(self).cpu_list@[cpu_id as int].owning_container == container_ptr);
            assert(self.container_cpu_wf());
            assert(
                forall|cpu_i:CpuId|
                #![auto]
                0 <= cpu_i < NUM_CPUS 
                ==> 
                old(self).container_dom().contains(old(self).cpu_list@[cpu_i as int].owning_container)
            );
        };

        let (ret_thread_ptr, sll) = self.container_tree.container_tree_scheduler_pop_head(container_ptr);

        assert(old(self).get_container(container_ptr).scheduler@.contains(ret_thread_ptr));

        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(ret_thread_ptr);
        let thread : &Thread = PPtr::<Thread>::from_usize(ret_thread_ptr).borrow(Tracked(thread_perm));
        pt_regs.set_self_fast(thread.trap_frame.unwrap());

        let mut thread_perm = Tracked(self.thread_perms.borrow_mut().tracked_remove(ret_thread_ptr));

        thread_set_current_cpu(ret_thread_ptr, &mut thread_perm, Some(cpu_id));
        thread_set_state(ret_thread_ptr, &mut thread_perm, ThreadState::RUNNING);
        proof {
            self.thread_perms.borrow_mut().tracked_insert(ret_thread_ptr, thread_perm.get());
        }

        self.cpu_list.set(cpu_id, 
            Cpu{
                owning_container: container_ptr,
                active: true,
                current_thread: Some(ret_thread_ptr),
            }
        );

        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint()) by {
        };
        assert(self.container_perms_wf());
        assert(self.processes_container_wf()) by {
        };
        assert(self.processes_wf());

        assert(self.threads_process_wf()) by {
        };
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf()) by {
            seq_push_lemma::<ThreadPtr>();
        };
        assert(self.threads_endpoint_descriptors_wf()) by {
            seq_update_lemma::<Option<EndpointPtr>>();
        };
        assert(self.endpoints_queue_wf()) by {
        };
        assert(self.endpoints_container_wf()) by {
            seq_push_lemma::<EndpointPtr>();
        };
        assert(self.schedulers_wf()) by {
            seq_skip_lemma::<ThreadPtr>();
            assert(old(self).get_container(container_ptr).scheduler@.no_duplicates()) by {
                old(self).get_container(container_ptr).scheduler.unique_implys_no_duplicates()
            };
        };
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf());

        return ret_thread_ptr;
    }


}

}


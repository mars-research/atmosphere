use vstd::prelude::*;
verus! {

use crate::kernel::Kernel;
use crate::define::*;
use crate::process_manager::process::Process;
use crate::process_manager::thread::Thread;
use crate::process_manager::container::Container;
use crate::process_manager::endpoint::Endpoint;
use crate::process_manager::cpu::*;
use crate::pagetable::entry::MapEntry;
use crate::quota::Quota;

impl Kernel {
    pub open spec fn proc_dom(&self) -> Set<ProcPtr> {
        self.proc_man.proc_dom()
    }

    pub open spec fn thread_dom(&self) -> Set<ThreadPtr> {
        self.proc_man.thread_dom()
    }

    pub open spec fn container_dom(&self) -> Set<ContainerPtr> {
        self.proc_man.container_dom()
    }

    pub open spec fn endpoint_dom(&self) -> Set<EndpointPtr> {
        self.proc_man.endpoint_dom()
    }

    pub open spec fn get_proc(&self, p_ptr: ProcPtr) -> &Process
        recommends
            self.proc_man.wf(),
            self.proc_dom().contains(p_ptr),
    {
        self.proc_man.get_proc(p_ptr)
    }

    pub open spec fn get_thread(&self, t_ptr: ThreadPtr) -> &Thread
        recommends
            self.proc_man.wf(),
            self.thread_dom().contains(t_ptr),
    {
        self.proc_man.get_thread(t_ptr)
    }

    pub open spec fn get_container(&self, c_ptr: ContainerPtr) -> &Container
        recommends
            self.proc_man.wf(),
            self.container_dom().contains(c_ptr),
    {
        self.proc_man.get_container(c_ptr)
    }

    pub open spec fn get_container_quota(&self, c_ptr: ContainerPtr) -> Quota
        recommends
            self.wf(),
            self.container_dom().contains(c_ptr),
    {
        self.proc_man.get_container(c_ptr).quota
    }

    pub open spec fn get_endpoint(&self, e_ptr: EndpointPtr) -> &Endpoint
        recommends
            self.wf(),
            self.endpoint_dom().contains(e_ptr),
    {
        self.proc_man.get_endpoint(e_ptr)
    }

    pub open spec fn get_address_space(&self, p_ptr: ProcPtr) -> Map<VAddr, MapEntry>
        recommends
            self.wf(),
            self.proc_dom().contains(p_ptr),
    {
        self.mem_man.get_pagetable_mapping_by_pcid(self.get_proc(p_ptr).pcid)
    }

    pub open spec fn get_proc_has_iommu_table(&self, p_ptr: ProcPtr) -> bool
        recommends
            self.wf(),
            self.proc_dom().contains(p_ptr),
    {
        self.get_proc(p_ptr).ioid.is_Some()
    }

    pub open spec fn get_io_space(&self, p_ptr: ProcPtr) -> Map<VAddr, MapEntry>
        recommends
            self.wf(),
            self.proc_dom().contains(p_ptr),
            self.get_proc_has_iommu_table(p_ptr),
    {
        self.mem_man.get_iommu_table_mapping_by_ioid(self.get_proc(p_ptr).ioid.unwrap())
    }

    pub open spec fn get_container_owned_pages(&self, c_ptr: ContainerPtr) -> Set<PagePtr>
        recommends
            self.wf(),
            self.container_dom().contains(c_ptr),
    {
        self.page_alloc.get_container_owned_pages(c_ptr)
    }

    pub open spec fn get_physical_page_mapping(&self) -> Map<PagePtr, Set<(ProcPtr, VAddr)>> {
        self.page_mapping@
    }

    pub open spec fn get_physical_page_mapping_of_page(&self, page_ptr: PagePtr) -> Set<
        (ProcPtr, VAddr),
    > {
        self.page_mapping@[page_ptr]
    }

    pub open spec fn get_is_cpu_running(&self, cpu_i: CpuId) -> bool
        recommends
            self.wf(),
            0 <= cpu_i < NUM_CPUS,
    {
        self.proc_man.get_is_cpu_running(cpu_i)
    }

    pub open spec fn get_is_process_thread_list_full(&self, p_ptr: ProcPtr) -> bool
        recommends
            self.wf(),
            self.proc_dom().contains(p_ptr),
    {
        self.get_proc(p_ptr).owned_threads.len() >= MAX_NUM_THREADS_PER_PROC
    }

    pub open spec fn get_is_process_childern_list_full(&self, p_ptr: ProcPtr) -> bool
        recommends
            self.wf(),
            self.proc_dom().contains(p_ptr),
    {
        self.get_proc(p_ptr).children.len() >= PROC_CHILD_LIST_LEN
    }

    pub open spec fn get_is_process_depth_overflow(&self, p_ptr: ProcPtr) -> bool
        recommends
            self.wf(),
            self.proc_dom().contains(p_ptr),
    {
        self.get_proc(p_ptr).depth >= usize::MAX
    }

    pub open spec fn get_proc_ptr_by_cpu_id(&self, cpu_id: CpuId) -> (ret: Option<ProcPtr>)
        recommends
            self.wf(),
            0 <= cpu_id < NUM_CPUS,
    {
        if self.get_is_cpu_running(cpu_id) {
            Some(
                self.get_thread(
                    self.proc_man.cpu_list@[cpu_id as int].current_thread.unwrap(),
                ).owning_proc,
            )
        } else {
            None
        }
    }

    pub open spec fn get_thread_ptr_by_cpu_id(&self, cpu_id: CpuId) -> (ret: Option<ThreadPtr>)
        recommends
            self.wf(),
            0 <= cpu_id < NUM_CPUS,
    {
        self.proc_man.get_thread_ptr_by_cpu_id(cpu_id)
    }

    pub open spec fn get_owning_proc_by_thread_ptr(&self, t_ptr: ThreadPtr) -> ProcPtr
        recommends
            self.wf(),
            self.thread_dom().contains(t_ptr),
    {
        self.get_thread(t_ptr).owning_proc
    }

    pub open spec fn get_cpu(&self, cpu_id: CpuId) -> &Cpu
        recommends
            self.wf(),
            0 <= cpu_id < NUM_CPUS,
    {
        self.proc_man.get_cpu(cpu_id)
    }

    pub open spec fn get_proc_owning_container(&self, p_ptr: ProcPtr) -> ContainerPtr
        recommends
            self.wf(),
            self.proc_dom().contains(p_ptr),
    {
        self.get_proc(p_ptr).owning_container
    }

    pub open spec fn get_is_scheduler_full(&self, c_ptr: ContainerPtr) -> bool
        recommends
            self.wf(),
            self.container_dom().contains(c_ptr),
    {
        self.get_container(c_ptr).scheduler.len() >= MAX_CONTAINER_SCHEDULER_LEN
    }

    pub open spec fn get_is_proc_list_full(&self, c_ptr: ContainerPtr) -> bool
        recommends
            self.wf(),
            self.container_dom().contains(c_ptr),
    {
        self.get_container(c_ptr).owned_procs.len() >= CONTAINER_PROC_LIST_LEN
    }

    pub open spec fn get_is_children_list_full(&self, c_ptr: ContainerPtr) -> bool
        recommends
            self.wf(),
            self.container_dom().contains(c_ptr),
    {
        self.get_container(c_ptr).children.len() >= CONTAINER_CHILD_LIST_LEN
    }

    pub open spec fn get_num_of_free_pages(&self) -> usize
        recommends
            self.wf(),
    {
        self.page_alloc.free_pages_4k.len()
    }

    pub open spec fn get_is_pcid_exhausted(&self) -> bool {
        self.mem_man.free_pcids.len() == 0
    }

    pub open spec fn get_thread_endpoint_descriptors(&self, t_ptr: ThreadPtr) -> Seq<
        Option<EndpointPtr>,
    >
        recommends
            self.wf(),
            self.thread_dom().contains(t_ptr),
    {
        self.proc_man.get_thread(t_ptr).endpoint_descriptors@
    }

    pub open spec fn get_endpoint_exists(
        &self,
        t_ptr: ThreadPtr,
        endpoint_index: EndpointIdx,
    ) -> bool
        recommends
            self.wf(),
            self.thread_dom().contains(t_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
    {
        self.proc_man.get_thread(t_ptr).endpoint_descriptors@[endpoint_index as int].is_Some()
    }

    pub open spec fn get_endpoint_ptr_by_endpoint_idx(
        &self,
        t_ptr: ThreadPtr,
        endpoint_index: EndpointIdx,
    ) -> Option<EndpointPtr>
        recommends
            self.wf(),
            self.thread_dom().contains(t_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
    {
        self.proc_man.get_thread(t_ptr).endpoint_descriptors@[endpoint_index as int]
    }

    pub open spec fn get_endpoint_shareable(
        &self,
        t_ptr: ThreadPtr,
        endpoint_index: EndpointIdx,
    ) -> bool
        recommends
            self.wf(),
            self.thread_dom().contains(t_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
    {
        &&& self.get_endpoint_ptr_by_endpoint_idx(t_ptr, endpoint_index).is_Some()
        &&& self.get_endpoint(
            self.get_endpoint_ptr_by_endpoint_idx(t_ptr, endpoint_index).unwrap(),
        ).rf_counter != usize::MAX
    }

    pub open spec fn get_endpoint_has_receiver(
        &self,
        t_ptr: ThreadPtr,
        endpoint_index: EndpointIdx,
    ) -> bool
        recommends
            self.wf(),
            self.thread_dom().contains(t_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
    {
        &&& self.get_endpoint_ptr_by_endpoint_idx(t_ptr, endpoint_index).is_Some()
        &&& self.get_endpoint(
            self.get_endpoint_ptr_by_endpoint_idx(t_ptr, endpoint_index).unwrap(),
        ).queue_state == EndpointState::RECEIVE
        &&& self.get_endpoint(
            self.get_endpoint_ptr_by_endpoint_idx(t_ptr, endpoint_index).unwrap(),
        ).queue.len() != 0
    }

    pub open spec fn get_endpoint_has_sender(
        &self,
        t_ptr: ThreadPtr,
        endpoint_index: EndpointIdx,
    ) -> bool
        recommends
            self.wf(),
            self.thread_dom().contains(t_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
    {
        &&& self.get_endpoint_ptr_by_endpoint_idx(t_ptr, endpoint_index).is_Some()
        &&& self.get_endpoint(
            self.get_endpoint_ptr_by_endpoint_idx(t_ptr, endpoint_index).unwrap(),
        ).queue_state == EndpointState::SEND
        &&& self.get_endpoint(
            self.get_endpoint_ptr_by_endpoint_idx(t_ptr, endpoint_index).unwrap(),
        ).queue.len() != 0
    }

    pub open spec fn get_physical_page_reference_counter(&self, page_ptr: PagePtr) -> nat
        recommends
            self.wf(),
            self.get_physical_page_mapping().dom().contains(page_ptr),
    {
        self.page_alloc.page_mappings(page_ptr).len() + self.page_alloc.page_io_mappings(
            page_ptr,
        ).len()
    }
}

} // verus!

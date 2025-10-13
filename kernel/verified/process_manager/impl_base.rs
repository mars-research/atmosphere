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
use crate::process_manager::spec_proof::*;
//exec
impl ProcessManager {
    pub fn new() -> (ret: Self) {
        ProcessManager {
            root_container: 0,
            container_perms: Tracked(Map::tracked_empty()),
            process_perms: Tracked(Map::tracked_empty()),
            thread_perms: Tracked(Map::tracked_empty()),
            endpoint_perms: Tracked(Map::tracked_empty()),
            cpu_list: Array::<Cpu, NUM_CPUS>::new(),
        }
    }

    #[verifier(external_body)]
    pub fn init(
        &mut self,
        dom_0_container_ptr: ContainerPtr,
        dom_0_proc_ptr: ProcPtr,
        dom_0_thread_ptr: ThreadPtr,
        init_quota: Quota,
        page_perm_0: Tracked<PagePerm4k>,
        page_perm_1: Tracked<PagePerm4k>,
        page_perm_2: Tracked<PagePerm4k>,
    ) {
        unsafe {
            self.root_container = dom_0_container_ptr;
            let root_container_ptr = dom_0_container_ptr as *mut MaybeUninit<Container>;
            (*root_container_ptr).assume_init_mut().owned_procs.init();

            let sll1 = (*root_container_ptr).assume_init_mut().owned_procs.push(&dom_0_proc_ptr);
            (*root_container_ptr).assume_init_mut().root_process = Some(dom_0_proc_ptr);
            (*root_container_ptr).assume_init_mut().parent = None;
            (*root_container_ptr).assume_init_mut().parent_rev_ptr = None;
            (*root_container_ptr).assume_init_mut().children.init();
            (*root_container_ptr).assume_init_mut().quota = init_quota;
            // (*root_container_ptr).assume_init_mut().mem_used = 0;
            (*root_container_ptr).assume_init_mut().owned_cpus.init();
            (*root_container_ptr).assume_init_mut().scheduler.init();
            let sll2 = (*root_container_ptr).assume_init_mut().scheduler.push(&dom_0_thread_ptr);
            (*root_container_ptr).assume_init_mut().depth = 0;

            let root_proc_ptr = dom_0_proc_ptr as *mut MaybeUninit<Process>;
            (*root_proc_ptr).assume_init_mut().owning_container = dom_0_container_ptr;
            (*root_proc_ptr).assume_init_mut().rev_ptr = sll2;
            (*root_proc_ptr).assume_init_mut().pcid = 0;
            (*root_proc_ptr).assume_init_mut().ioid = Some(0);
            (*root_proc_ptr).assume_init_mut().owned_threads.init();
            (*root_proc_ptr).assume_init_mut().parent = None;
            (*root_proc_ptr).assume_init_mut().parent_rev_ptr = None;
            (*root_proc_ptr).assume_init_mut().children.init();
            (*root_proc_ptr).assume_init_mut().depth = 0;
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

            for i in 0..2 {
                (*root_container_ptr).assume_init_mut().owned_cpus.insert(i);
                self.cpu_list.set(
                    i,
                    Cpu {
                        owning_container: dom_0_container_ptr,
                        active: true,
                        current_thread: None,
                    },
                );
            }

            for i in 2..NUM_CPUS {
                (*root_container_ptr).assume_init_mut().owned_cpus.insert(i);
                self.cpu_list.set(
                    i,
                    Cpu {
                        owning_container: dom_0_container_ptr,
                        active: false,
                        current_thread: None,
                    },
                );
            }
        }
    }

    pub fn set_container_mem_quota_mem_4k(&mut self, container_ptr: ContainerPtr, new_quota: usize)
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
            forall|p_ptr: ProcPtr|
                #![auto]
                self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
                    p_ptr,
                ),
            forall|t_ptr: ThreadPtr|
                #![auto]
                self.thread_dom().contains(t_ptr) ==> self.get_thread(t_ptr) =~= old(
                    self,
                ).get_thread(t_ptr),
            forall|c_ptr: ContainerPtr|
                #![auto]
                self.container_dom().contains(c_ptr) && c_ptr != container_ptr
                    ==> self.get_container(c_ptr) =~= old(self).get_container(c_ptr),
            forall|e_ptr: EndpointPtr|
                #![auto]
                self.endpoint_dom().contains(e_ptr) ==> self.get_endpoint(e_ptr) =~= old(
                    self,
                ).get_endpoint(e_ptr),
            self.get_container(container_ptr).owned_procs =~= old(self).get_container(
                container_ptr,
            ).owned_procs,
            self.get_container(container_ptr).parent =~= old(self).get_container(
                container_ptr,
            ).parent,
            self.get_container(container_ptr).parent_rev_ptr =~= old(self).get_container(
                container_ptr,
            ).parent_rev_ptr,
            self.get_container(container_ptr).children =~= old(self).get_container(
                container_ptr,
            ).children,
            self.get_container(container_ptr).owned_endpoints =~= old(self).get_container(
                container_ptr,
            ).owned_endpoints,
            self.get_container(container_ptr).owned_threads =~= old(self).get_container(
                container_ptr,
            ).owned_threads,
            // self.get_container(container_ptr).mem_quota =~= old(self).get_container(container_ptr).mem_quota,
            // self.get_container(container_ptr).mem_used =~= old(self).get_container(container_ptr).mem_used,
            self.get_container(container_ptr).owned_cpus =~= old(self).get_container(
                container_ptr,
            ).owned_cpus,
            self.get_container(container_ptr).scheduler =~= old(self).get_container(
                container_ptr,
            ).scheduler,
            self.get_container(container_ptr).depth =~= old(self).get_container(
                container_ptr,
            ).depth,
            self.get_container(container_ptr).uppertree_seq =~= old(self).get_container(
                container_ptr,
            ).uppertree_seq,
            self.get_container(container_ptr).subtree_set =~= old(self).get_container(
                container_ptr,
            ).subtree_set,
            self.get_container(container_ptr).root_process =~= old(self).get_container(
                container_ptr,
            ).root_process,
            self.get_container(container_ptr).quota =~= old(self).get_container(
                container_ptr,
            ).quota.spec_set_mem_4k(new_quota),
    {
        broadcast use ProcessManager::reveal_process_manager_wf;

        let mut container_perm = Tracked(
            self.container_perms.borrow_mut().tracked_remove(container_ptr),
        );
        container_set_quota_mem_4k(container_ptr, &mut container_perm, new_quota);
        proof {
            self.container_perms.borrow_mut().tracked_insert(container_ptr, container_perm.get());
        }

        assert(self.container_perms_wf());
        assert(self.container_tree_wf()) by {
            container_no_change_to_tree_fields_imply_wf(
                self.root_container,
                old(self).container_perms@,
                self.container_perms@,
            );
        };
        assert(self.container_fields_wf());
        assert(self.proc_perms_wf());
        assert(self.process_trees_wf()) by {
            // seq_to_set_lemma::<ProcPtr>();
            assert forall|c_ptr: ContainerPtr|
                #![trigger self.container_dom().contains(c_ptr)]
                #![trigger self.process_tree_wf(c_ptr)]
                self.container_dom().contains(c_ptr) && self.get_container(
                    c_ptr,
                ).root_process.is_Some() implies self.process_tree_wf(c_ptr) by {
                process_no_change_to_trees_fields_imply_wf(
                    self.get_container(c_ptr).root_process.unwrap(),
                    self.get_container(c_ptr).owned_procs@.to_set(),
                    old(self).process_perms@,
                    self.process_perms@,
                );
            };
        };
        assert(self.process_fields_wf()) by {
            assert(forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
                    p_ptr,
                ));
        };
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.container_perms_wf());
        assert(self.processes_container_wf());
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

    pub fn schedule_running_thread(&mut self, cpu_id: CpuId, pt_regs: &Registers)
        requires
            old(self).wf(),
            0 <= cpu_id < NUM_CPUS,
            old(self).get_cpu(cpu_id).current_thread.is_some(),
            old(self).get_container(
                old(self).get_thread(
                    old(self).get_cpu(cpu_id).current_thread.unwrap(),
                ).owning_container,
            ).scheduler.len() < MAX_CONTAINER_SCHEDULER_LEN,
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure(),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom(),
            forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                old(self).proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(
                    self,
                ).get_proc(p_ptr),
            forall|container_ptr: ContainerPtr|
                #![trigger self.get_container(container_ptr)]
                old(self).container_dom().contains(container_ptr) && container_ptr != old(
                    self,
                ).get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container
                    ==> self.get_container(container_ptr) =~= old(self).get_container(
                    container_ptr,
                ),
            forall|t_ptr: ThreadPtr|
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr) && t_ptr != old(self).get_cpu(
                    cpu_id,
                ).current_thread.unwrap() ==> old(self).get_thread(t_ptr) =~= self.get_thread(
                    t_ptr,
                ),
            forall|e_ptr: EndpointPtr|
                #![trigger self.get_endpoint(e_ptr)]
                self.endpoint_dom().contains(e_ptr) ==> old(self).get_endpoint(e_ptr)
                    =~= self.get_endpoint(e_ptr),
            forall|cpu_i: CpuId|
                #![trigger self.get_cpu(cpu_i)]
                0 <= cpu_i < NUM_CPUS && cpu_i != cpu_id ==> old(self).get_cpu(cpu_i)
                    == self.get_cpu(cpu_i),
            self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container
                == old(self).get_thread(
                old(self).get_cpu(cpu_id).current_thread.unwrap(),
            ).owning_container,
            self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_proc == old(
                self,
            ).get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_proc,
            self.get_thread(
                old(self).get_cpu(cpu_id).current_thread.unwrap(),
            ).blocking_endpoint_ptr.is_None(),
            self.get_thread(
                old(self).get_cpu(cpu_id).current_thread.unwrap(),
            ).blocking_endpoint_index.is_None(),
            self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).endpoint_descriptors
                == old(self).get_thread(
                old(self).get_cpu(cpu_id).current_thread.unwrap(),
            ).endpoint_descriptors,
            self.get_thread(
                old(self).get_cpu(cpu_id).current_thread.unwrap(),
            ).running_cpu.is_None(),
            self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).state
                == ThreadState::SCHEDULED,
            self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).ipc_payload
                == IPCPayLoad::Empty,
            self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).error_code.is_None(),
            self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).trap_frame.is_Some(),
            self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).trap_frame.unwrap()
                == *pt_regs,
            self.get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).parent == old(self).get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).parent,
            self.get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).children == old(self).get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).children,
            self.get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).depth == old(self).get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).depth,
            self.get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).uppertree_seq == old(self).get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).uppertree_seq,
            self.get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).subtree_set == old(self).get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).subtree_set,
            self.get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).root_process == old(self).get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).root_process,
            self.get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).owned_procs == old(self).get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).owned_procs,
            self.get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).owned_endpoints == old(self).get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).owned_endpoints,
            self.get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).owned_threads == old(self).get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).owned_threads,
            self.get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).quota == old(self).get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).quota,
            self.get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).owned_cpus == old(self).get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).owned_cpus,
            self.get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).can_have_children == old(self).get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).can_have_children,
            self.get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).scheduler@ == old(self).get_container(
                self.get_thread(old(self).get_cpu(cpu_id).current_thread.unwrap()).owning_container,
            ).scheduler@.push(old(self).get_cpu(cpu_id).current_thread.unwrap()),
            self.get_cpu(cpu_id).owning_container == old(self).get_cpu(cpu_id).owning_container,
            self.get_cpu(cpu_id).active == old(self).get_cpu(cpu_id).active,
            self.get_cpu(cpu_id).current_thread.is_None(),
    {
        broadcast use ProcessManager::reveal_process_manager_wf;
        
        assert(self.get_cpu(cpu_id).active);
        let old_cpu = *self.cpu_list.get(cpu_id);
        let t_ptr = old_cpu.current_thread.unwrap();
        let c_ptr = self.get_thread(t_ptr).owning_container;
        let mut c_perm = Tracked(self.container_perms.borrow_mut().tracked_remove(c_ptr));

        let scheduler_node_ref = scheduler_push_thread(c_ptr, &mut c_perm, &t_ptr);
        proof {
            self.container_perms.borrow_mut().tracked_insert(c_ptr, c_perm.get());
        }
        let mut t_perm = Tracked(self.thread_perms.borrow_mut().tracked_remove(t_ptr));
        thread_set_blocking_endpoint_endpoint_ref_scheduler_ref_state_and_ipc_payload(
            t_ptr,
            &mut t_perm,
            None,
            None,
            Some(scheduler_node_ref),
            ThreadState::SCHEDULED,
            IPCPayLoad::Empty,
            None,
        );
        thread_set_trap_frame_fast(t_ptr, &mut t_perm, pt_regs);
        thread_set_error_code(t_ptr, &mut t_perm, None);
        proof {
            self.thread_perms.borrow_mut().tracked_insert(t_ptr, t_perm.get());
        }
        self.cpu_list.set(
            cpu_id,
            Cpu {
                owning_container: old_cpu.owning_container,
                active: old_cpu.active,
                current_thread: None,
            },
        );

        assert(self.container_perms_wf());
        assert(self.container_tree_wf()) by {
            container_no_change_to_tree_fields_imply_wf(
                self.root_container,
                old(self).container_perms@,
                self.container_perms@,
            );
        };
        assert(self.container_fields_wf());
        assert(self.proc_perms_wf());
        assert(self.process_trees_wf()) by {
            assert forall|c_ptr: ContainerPtr|
                #![trigger self.container_dom().contains(c_ptr)]
                #![trigger self.process_tree_wf(c_ptr)]
                self.container_dom().contains(c_ptr) && self.get_container(
                    c_ptr,
                ).root_process.is_Some() implies self.process_tree_wf(c_ptr) by {
                process_no_change_to_trees_fields_imply_wf(
                    self.get_container(c_ptr).root_process.unwrap(),
                    self.get_container(c_ptr).owned_procs@.to_set(),
                    old(self).process_perms@,
                    self.process_perms@,
                );
            };
        };
        assert(self.process_fields_wf()) by {
            assert(forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
                    p_ptr,
                ));
        };
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.container_perms_wf());
        assert(self.processes_container_wf());
        assert(self.threads_process_wf());
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf());
        assert(self.threads_endpoint_descriptors_wf());
        assert(self.endpoints_queue_wf());
        assert(self.endpoints_container_wf());
        assert(self.schedulers_wf()) by {
            seq_push_lemma::<ThreadPtr>();
            assert(old(self).get_container(c_ptr).scheduler@.no_duplicates()) by {
                old(self).get_container(c_ptr).scheduler.unique_implys_no_duplicates()
            };
        };
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf());

    }

    pub fn run_blocked_thread(
        &mut self,
        cpu_id: CpuId,
        endpoint_ptr: EndpointPtr,
        pt_regs: &mut Registers,
    ) -> (ret: Option<RetValueType>)
        requires
            old(self).wf(),
            old(self).endpoint_dom().contains(endpoint_ptr),
            old(self).get_endpoint(endpoint_ptr).queue.len() > 0,
            0 <= cpu_id < NUM_CPUS,
            old(self).get_cpu(cpu_id).current_thread.is_none(),
            old(self).get_cpu(cpu_id).active,
            old(self).get_cpu(cpu_id).owning_container == old(self).get_thread(
                old(self).get_endpoint(endpoint_ptr).queue@[0],
            ).owning_container,
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure(),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom(),
            forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                old(self).proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(
                    self,
                ).get_proc(p_ptr),
            forall|container_ptr: ContainerPtr|
                #![trigger self.get_container(container_ptr)]
                old(self).container_dom().contains(container_ptr) ==> self.get_container(
                    container_ptr,
                ) =~= old(self).get_container(container_ptr),
            forall|t_ptr: ThreadPtr|
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr) && t_ptr != old(self).get_endpoint(
                    endpoint_ptr,
                ).queue@[0] ==> old(self).get_thread(t_ptr) =~= self.get_thread(t_ptr),
            forall|e_ptr: EndpointPtr|
                #![trigger self.get_endpoint(e_ptr)]
                self.endpoint_dom().contains(e_ptr) && e_ptr != endpoint_ptr ==> old(
                    self,
                ).get_endpoint(e_ptr) =~= self.get_endpoint(e_ptr),
            self.get_thread(old(self).get_endpoint(endpoint_ptr).queue@[0]).endpoint_descriptors
                =~= old(self).get_thread(
                old(self).get_endpoint(endpoint_ptr).queue@[0],
            ).endpoint_descriptors,
            self.get_container(
                old(self).get_thread(
                    old(self).get_endpoint(endpoint_ptr).queue@[0],
                ).owning_container,
            ).owned_procs =~= old(self).get_container(
                old(self).get_thread(
                    old(self).get_endpoint(endpoint_ptr).queue@[0],
                ).owning_container,
            ).owned_procs,
            self.get_endpoint(endpoint_ptr).queue@ == old(self).get_endpoint(
                endpoint_ptr,
            ).queue@.skip(1),
            self.get_endpoint(endpoint_ptr).owning_threads == old(self).get_endpoint(
                endpoint_ptr,
            ).owning_threads,
            self.get_endpoint(endpoint_ptr).rf_counter == old(self).get_endpoint(
                endpoint_ptr,
            ).rf_counter,
            self.get_endpoint(endpoint_ptr).queue_state == old(self).get_endpoint(
                endpoint_ptr,
            ).queue_state,
            self.get_thread(old(self).get_endpoint(endpoint_ptr).queue@[0]).state
                == ThreadState::RUNNING,
            self.get_cpu(cpu_id).current_thread.is_Some(),
            self.get_cpu(cpu_id).current_thread.unwrap() == old(self).get_endpoint(
                endpoint_ptr,
            ).queue@[0],
    {
        broadcast use ProcessManager::reveal_process_manager_wf;
        
        let thread_ptr = self.get_endpoint(endpoint_ptr).queue.get_head();
        assert(self.get_endpoint(endpoint_ptr).queue@.contains(thread_ptr));
        let thread_ref = self.get_thread(thread_ptr);
        let proc_ref = self.get_proc(thread_ref.owning_proc);
        let new_pcid = proc_ref.pcid;
        let old_cpu = *self.cpu_list.get(cpu_id);
        pt_regs.set_self_fast(thread_ref.trap_frame.unwrap());
        let ret_value = thread_ref.error_code;
        let mut endpoint_perm = Tracked(
            self.endpoint_perms.borrow_mut().tracked_remove(endpoint_ptr),
        );
        let (ret_thread_ptr, sll) = endpoint_pop_head(endpoint_ptr, &mut endpoint_perm);
        assert(thread_ptr == ret_thread_ptr);
        proof {
            self.endpoint_perms.borrow_mut().tracked_insert(endpoint_ptr, endpoint_perm.get());
        }

        let mut thread_perm = Tracked(self.thread_perms.borrow_mut().tracked_remove(thread_ptr));
        thread_set_blocking_endpoint_endpoint_ref_scheduler_ref_state_and_ipc_payload(
            thread_ptr,
            &mut thread_perm,
            None,
            None,
            None,
            ThreadState::RUNNING,
            IPCPayLoad::Empty,
            None,
        );
        thread_set_current_cpu(thread_ptr, &mut thread_perm, Some(cpu_id));
        proof {
            self.thread_perms.borrow_mut().tracked_insert(thread_ptr, thread_perm.get());
        }
        self.cpu_list.set(
            cpu_id,
            Cpu {
                owning_container: old_cpu.owning_container,
                active: old_cpu.active,
                current_thread: Some(thread_ptr),
            },
        );

        assert(self.container_perms_wf());
        assert(self.container_tree_wf()) by {
            container_no_change_to_tree_fields_imply_wf(
                self.root_container,
                old(self).container_perms@,
                self.container_perms@,
            );
        };
        assert(self.container_fields_wf());
        assert(self.proc_perms_wf());
        assert(self.process_trees_wf()) by {
            assert forall|c_ptr: ContainerPtr|
                #![trigger self.container_dom().contains(c_ptr)]
                #![trigger self.process_tree_wf(c_ptr)]
                self.container_dom().contains(c_ptr) && self.get_container(
                    c_ptr,
                ).root_process.is_Some() implies self.process_tree_wf(c_ptr) by {
                process_no_change_to_trees_fields_imply_wf(
                    self.get_container(c_ptr).root_process.unwrap(),
                    self.get_container(c_ptr).owned_procs@.to_set(),
                    old(self).process_perms@,
                    self.process_perms@,
                );
            };
        };
        assert(self.process_fields_wf()) by {
            assert(forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
                    p_ptr,
                ));
        };
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.container_perms_wf());
        assert(self.processes_container_wf());
        assert(self.threads_process_wf());
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf());
        assert(self.threads_endpoint_descriptors_wf());
        assert(self.endpoints_queue_wf()) by {
            seq_skip_lemma::<ThreadPtr>();
            old(self).get_endpoint(endpoint_ptr).queue.unique_implys_no_duplicates();
        };
        assert(self.endpoints_container_wf());
        assert(self.schedulers_wf());
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf());

        return ret_value;
    }

    pub fn schedule_blocked_thread(&mut self, endpoint_ptr: EndpointPtr)
        requires
            old(self).wf(),
            old(self).endpoint_dom().contains(endpoint_ptr),
            old(self).get_endpoint(endpoint_ptr).queue.len() > 0,
            old(self).get_container(
                old(self).get_thread(
                    old(self).get_endpoint(endpoint_ptr).queue@[0],
                ).owning_container,
            ).scheduler.len() < MAX_CONTAINER_SCHEDULER_LEN,
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure(),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom(),
            forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                old(self).proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(p_ptr),
            forall|container_ptr: ContainerPtr|
                #![trigger self.get_container(container_ptr)]
                old(self).container_dom().contains(container_ptr) && container_ptr != old(self).get_thread(old(self).get_endpoint(endpoint_ptr).queue@[0]).owning_container
                ==> 
                self.get_container(container_ptr) =~= old(self).get_container(container_ptr),
            forall|container_ptr: ContainerPtr|
                #![trigger self.get_container(container_ptr)]
                old(self).container_dom().contains(container_ptr)
                ==> 
                self.get_container(container_ptr).subtree_set =~= old(self).get_container(container_ptr).subtree_set,
            forall|t_ptr: ThreadPtr|
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr) && t_ptr != old(self).get_endpoint(endpoint_ptr).queue@[0] ==> old(self).get_thread(t_ptr) =~= self.get_thread(t_ptr),
            forall|t_ptr: ThreadPtr|
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr) ==> old(self).get_thread(t_ptr).endpoint_descriptors =~= self.get_thread(t_ptr).endpoint_descriptors,
            forall|e_ptr: EndpointPtr|
                #![trigger self.get_endpoint(e_ptr)]
                self.endpoint_dom().contains(e_ptr) && e_ptr != endpoint_ptr ==> old(self).get_endpoint(e_ptr) =~= self.get_endpoint(e_ptr),
            forall|e_ptr: EndpointPtr|
                #![trigger self.get_endpoint(e_ptr)]
                self.endpoint_dom().contains(e_ptr) ==> old(self).get_endpoint(e_ptr).owning_container =~= self.get_endpoint(e_ptr).owning_container,
            self.get_thread(old(self).get_endpoint(endpoint_ptr).queue@[0]).endpoint_descriptors
                =~= old(self).get_thread(old(self).get_endpoint(endpoint_ptr).queue@[0],).endpoint_descriptors,
            self.get_container(old(self).get_thread(old(self).get_endpoint(endpoint_ptr).queue@[0]).owning_container).owned_procs 
                =~= old(self).get_container(old(self).get_thread(old(self).get_endpoint(endpoint_ptr).queue@[0]).owning_container).owned_procs,
            self.get_container(old(self).get_thread(old(self).get_endpoint(endpoint_ptr).queue@[0]).owning_container).owned_threads 
                =~= old(self).get_container(old(self).get_thread(old(self).get_endpoint(endpoint_ptr).queue@[0]).owning_container).owned_threads,
            self.get_container(old(self).get_thread(old(self).get_endpoint(endpoint_ptr).queue@[0],).owning_container).children 
                =~= old(self).get_container(old(self).get_thread(old(self).get_endpoint(endpoint_ptr).queue@[0],).owning_container).children,
            self.get_endpoint(endpoint_ptr).queue@ == old(self).get_endpoint(endpoint_ptr).queue@.skip(1),
            self.get_endpoint(endpoint_ptr).owning_threads == old(self).get_endpoint(endpoint_ptr).owning_threads,
            self.get_endpoint(endpoint_ptr).rf_counter == old(self).get_endpoint(endpoint_ptr).rf_counter,
            self.get_endpoint(endpoint_ptr).queue_state == old(self).get_endpoint(endpoint_ptr).queue_state,
    {
        broadcast use ProcessManager::reveal_process_manager_wf;
        
        proof {
            seq_push_lemma::<usize>();
            seq_push_unique_lemma::<usize>();
        }

        let thread_ptr = self.get_endpoint(endpoint_ptr).queue.get_head();

        assert(self.get_endpoint(endpoint_ptr).queue@.contains(thread_ptr));
        let container_ptr = self.get_thread(thread_ptr).owning_container;

        assert(self.get_endpoint(endpoint_ptr).queue@.contains(self.get_endpoint(endpoint_ptr).queue@[0]));
        assert(self.get_thread(thread_ptr).state == ThreadState::BLOCKED);

        let mut container_perm = Tracked(
            self.container_perms.borrow_mut().tracked_remove(container_ptr),
        );
        let scheduler_node_ref = scheduler_push_thread(
            container_ptr,
            &mut container_perm,
            &thread_ptr,
        );
        proof {
            self.container_perms.borrow_mut().tracked_insert(container_ptr, container_perm.get());
        }

        let mut endpoint_perm = Tracked(
            self.endpoint_perms.borrow_mut().tracked_remove(endpoint_ptr),
        );
        let (ret_thread_ptr, sll) = endpoint_pop_head(endpoint_ptr, &mut endpoint_perm);
        assert(thread_ptr == ret_thread_ptr);
        proof {
            self.endpoint_perms.borrow_mut().tracked_insert(endpoint_ptr, endpoint_perm.get());
        }

        let mut thread_perm = Tracked(self.thread_perms.borrow_mut().tracked_remove(thread_ptr));
        thread_set_blocking_endpoint_endpoint_ref_scheduler_ref_state_and_ipc_payload(
            thread_ptr,
            &mut thread_perm,
            None,
            None,
            Some(scheduler_node_ref),
            ThreadState::SCHEDULED,
            IPCPayLoad::Empty,
            None,
        );
        proof {
            self.thread_perms.borrow_mut().tracked_insert(thread_ptr, thread_perm.get());
        }

        assert(self.container_perms_wf());
        assert(self.container_tree_wf()) by {
            container_no_change_to_tree_fields_imply_wf(
                self.root_container,
                old(self).container_perms@,
                self.container_perms@,
            );
        };
        assert(self.container_fields_wf());
        assert(self.proc_perms_wf());
        assert(self.process_trees_wf()) by {
            assert forall|c_ptr: ContainerPtr|
                #![trigger self.container_dom().contains(c_ptr)]
                #![trigger self.process_tree_wf(c_ptr)]
                self.container_dom().contains(c_ptr) && self.get_container(
                    c_ptr,
                ).root_process.is_Some() implies self.process_tree_wf(c_ptr) by {
                process_no_change_to_trees_fields_imply_wf(
                    self.get_container(c_ptr).root_process.unwrap(),
                    self.get_container(c_ptr).owned_procs@.to_set(),
                    old(self).process_perms@,
                    self.process_perms@,
                );
            };
        };
        assert(self.process_fields_wf()) by {
            assert(forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
                    p_ptr,
                ));
        };
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.container_perms_wf());
        assert(self.processes_container_wf());
        assert(self.threads_process_wf());
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf());
        assert(self.threads_endpoint_descriptors_wf());
        assert(self.endpoints_queue_wf()) by {
            seq_skip_lemma::<ThreadPtr>();
            old(self).get_endpoint(endpoint_ptr).queue.unique_implys_no_duplicates();
        };
        assert(self.endpoints_container_wf());
        assert(self.schedulers_wf());
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf());
    }

    /// Overview:
    /// yield the given thread
    /// save the payload onto given thread
    /// push given thread onto endpoint queue
    pub fn block_running_thread(
        &mut self,
        thread_ptr: ThreadPtr,
        endpoint_index: EndpointIdx,
        ipc_payload: IPCPayLoad,
    )
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].is_Some(),
            old(self).get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue.len() < MAX_NUM_THREADS_PER_ENDPOINT,
            old(self).get_thread(thread_ptr).state == ThreadState::RUNNING,
            ipc_payload.get_payload_as_va_range().is_Some()
                ==> ipc_payload.get_payload_as_va_range().unwrap().wf(),
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure(),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom(),
            forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                old(self).proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(p_ptr),
            forall|container_ptr: ContainerPtr|
                #![trigger self.get_container(container_ptr)]
                old(self).container_dom().contains(container_ptr) 
                ==> 
                self.get_container(container_ptr) =~= old(self).get_container(container_ptr),
            forall|t_ptr: ThreadPtr|
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr) && t_ptr != thread_ptr 
                ==> 
                old(self).get_thread(t_ptr) =~= self.get_thread(t_ptr),
            forall|e_ptr: EndpointPtr|
                #![trigger self.get_endpoint(e_ptr)]
                self.endpoint_dom().contains(e_ptr) 
                && 
                e_ptr != old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].unwrap() 
                ==> old(self).get_endpoint(e_ptr) =~= self.get_endpoint(e_ptr),
            self.get_thread(thread_ptr).endpoint_descriptors 
                =~= old(self).get_thread(thread_ptr).endpoint_descriptors,
            self.get_thread(thread_ptr).ipc_payload =~= ipc_payload,
            self.get_thread(thread_ptr).state == ThreadState::BLOCKED,
            self.get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue_state == old(self).get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue_state,
            self.get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).owning_threads == old(self).get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).owning_threads,
            self.get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue@ == old(self).get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue@.push(thread_ptr),
    {
        broadcast use ProcessManager::reveal_process_manager_wf;
        
        proof {
            old(self).get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue.unique_implys_no_duplicates();
        }
        let endpoint_ptr = self.get_thread(thread_ptr).endpoint_descriptors.get(
            endpoint_index,
        ).unwrap();
        let cpu_id = self.get_thread(thread_ptr).running_cpu.unwrap();
        let old_cpu = *self.cpu_list.get(cpu_id);

        let mut endpoint_perm = Tracked(
            self.endpoint_perms.borrow_mut().tracked_remove(endpoint_ptr),
        );
        let sll = endpoint_push(endpoint_ptr, &mut endpoint_perm, thread_ptr);
        proof {
            self.endpoint_perms.borrow_mut().tracked_insert(endpoint_ptr, endpoint_perm.get());
        }
        let mut thread_perm = Tracked(self.thread_perms.borrow_mut().tracked_remove(thread_ptr));
        thread_set_blocking_endpoint_endpoint_ref_scheduler_ref_state_and_ipc_payload(
            thread_ptr,
            &mut thread_perm,
            Some(endpoint_ptr),
            Some(sll),
            None,
            ThreadState::BLOCKED,
            ipc_payload,
            Some(endpoint_index),
        );
        proof {
            self.thread_perms.borrow_mut().tracked_insert(thread_ptr, thread_perm.get());
        }

        self.cpu_list.set(
            cpu_id,
            Cpu {
                owning_container: old_cpu.owning_container,
                active: old_cpu.active,
                current_thread: None,
            },
        );

        assert(self.container_perms_wf());
        assert(self.container_tree_wf()) by {
            container_no_change_to_tree_fields_imply_wf(
                self.root_container,
                old(self).container_perms@,
                self.container_perms@,
            );
        };
        assert(self.container_fields_wf());
        assert(self.proc_perms_wf());
        assert(self.process_trees_wf()) by {
            assert forall|c_ptr: ContainerPtr|
                #![trigger self.container_dom().contains(c_ptr)]
                #![trigger self.process_tree_wf(c_ptr)]
                self.container_dom().contains(c_ptr) && self.get_container(
                    c_ptr,
                ).root_process.is_Some() implies self.process_tree_wf(c_ptr) by {
                process_no_change_to_trees_fields_imply_wf(
                    self.get_container(c_ptr).root_process.unwrap(),
                    self.get_container(c_ptr).owned_procs@.to_set(),
                    old(self).process_perms@,
                    self.process_perms@,
                );
            };
        };
        assert(self.process_fields_wf()) by {
            assert(forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
                    p_ptr,
                ));
        };
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.container_perms_wf());
        assert(self.processes_container_wf());
        assert(self.threads_process_wf());
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf());
        assert(self.threads_endpoint_descriptors_wf());
        assert(self.endpoints_queue_wf()) by {
            seq_push_lemma::<usize>();
            seq_push_unique_lemma::<usize>();
        };
        assert(self.endpoints_container_wf());
        assert(self.schedulers_wf());
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf());
    }

    pub fn block_running_thread_and_set_trap_frame(
        &mut self,
        thread_ptr: ThreadPtr,
        endpoint_index: EndpointIdx,
        ipc_payload: IPCPayLoad,
        pt_regs: &Registers,
    )
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].is_Some(),
            old(self).get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue.len() < MAX_NUM_THREADS_PER_ENDPOINT,
            old(self).get_thread(thread_ptr).state == ThreadState::RUNNING,
            ipc_payload.get_payload_as_va_range().is_Some()
                ==> ipc_payload.get_payload_as_va_range().unwrap().wf(),
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure(),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom(),
            forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                old(self).proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(
                    self,
                ).get_proc(p_ptr),
            forall|container_ptr: ContainerPtr|
                #![trigger self.get_container(container_ptr)]
                old(self).container_dom().contains(container_ptr) ==> self.get_container(
                    container_ptr,
                ) =~= old(self).get_container(container_ptr),
            forall|t_ptr: ThreadPtr|
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr) && t_ptr != thread_ptr ==> old(
                    self,
                ).get_thread(t_ptr) =~= self.get_thread(t_ptr),
            forall|e_ptr: EndpointPtr|
                #![trigger self.get_endpoint(e_ptr)]
                self.endpoint_dom().contains(e_ptr) && e_ptr != old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap() ==> old(self).get_endpoint(
                    e_ptr,
                ) =~= self.get_endpoint(e_ptr),
            self.get_thread(thread_ptr).endpoint_descriptors =~= old(self).get_thread(
                thread_ptr,
            ).endpoint_descriptors,
            self.get_thread(thread_ptr).ipc_payload =~= ipc_payload,
            self.get_thread(thread_ptr).state == ThreadState::BLOCKED,
            self.get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue_state == old(self).get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue_state,
            self.get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).owning_threads == old(self).get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).owning_threads,
            self.get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue@ == old(self).get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue@.push(thread_ptr),
    {
        broadcast use ProcessManager::reveal_process_manager_wf;
        
        proof {
            old(self).get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue.unique_implys_no_duplicates();
        }
        let endpoint_ptr = self.get_thread(thread_ptr).endpoint_descriptors.get(
            endpoint_index,
        ).unwrap();
        let cpu_id = self.get_thread(thread_ptr).running_cpu.unwrap();
        let old_cpu = *self.cpu_list.get(cpu_id);

        let mut endpoint_perm = Tracked(
            self.endpoint_perms.borrow_mut().tracked_remove(endpoint_ptr),
        );
        let sll = endpoint_push(endpoint_ptr, &mut endpoint_perm, thread_ptr);
        proof {
            self.endpoint_perms.borrow_mut().tracked_insert(endpoint_ptr, endpoint_perm.get());
        }
        let mut thread_perm = Tracked(self.thread_perms.borrow_mut().tracked_remove(thread_ptr));
        thread_set_blocking_endpoint_endpoint_ref_scheduler_ref_state_and_ipc_payload(
            thread_ptr,
            &mut thread_perm,
            Some(endpoint_ptr),
            Some(sll),
            None,
            ThreadState::BLOCKED,
            ipc_payload,
            Some(endpoint_index),
        );
        thread_set_trap_frame_fast(thread_ptr, &mut thread_perm, pt_regs);
        proof {
            self.thread_perms.borrow_mut().tracked_insert(thread_ptr, thread_perm.get());
        }

        self.cpu_list.set(
            cpu_id,
            Cpu {
                owning_container: old_cpu.owning_container,
                active: old_cpu.active,
                current_thread: None,
            },
        );

        assert(self.container_perms_wf());
        assert(self.container_tree_wf()) by {
            container_no_change_to_tree_fields_imply_wf(
                self.root_container,
                old(self).container_perms@,
                self.container_perms@,
            );
        };
        assert(self.container_fields_wf());
        assert(self.proc_perms_wf());
        assert(self.process_trees_wf()) by {
            assert forall|c_ptr: ContainerPtr|
                #![trigger self.container_dom().contains(c_ptr)]
                #![trigger self.process_tree_wf(c_ptr)]
                self.container_dom().contains(c_ptr) && self.get_container(
                    c_ptr,
                ).root_process.is_Some() implies self.process_tree_wf(c_ptr) by {
                process_no_change_to_trees_fields_imply_wf(
                    self.get_container(c_ptr).root_process.unwrap(),
                    self.get_container(c_ptr).owned_procs@.to_set(),
                    old(self).process_perms@,
                    self.process_perms@,
                );
            };
        };
        assert(self.process_fields_wf()) by {
            assert(forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
                    p_ptr,
                ));
        };
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.container_perms_wf());
        assert(self.processes_container_wf());
        assert(self.threads_process_wf());
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf());
        assert(self.threads_endpoint_descriptors_wf());
        assert(self.endpoints_queue_wf()) by {
            seq_push_lemma::<usize>();
            seq_push_unique_lemma::<usize>();
        };
        assert(self.endpoints_container_wf());
        assert(self.schedulers_wf());
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf());
    }

    pub fn block_running_thread_and_change_queue_state(
        &mut self,
        thread_ptr: ThreadPtr,
        endpoint_index: EndpointIdx,
        ipc_payload: IPCPayLoad,
        queue_state: EndpointState,
    )
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].is_Some(),
            old(self).get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue.len() < MAX_NUM_THREADS_PER_ENDPOINT,
            old(self).get_thread(thread_ptr).state == ThreadState::RUNNING,
            ipc_payload.get_payload_as_va_range().is_Some()
                ==> ipc_payload.get_payload_as_va_range().unwrap().wf(),
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure(),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom(),
            forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                old(self).proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(
                    self,
                ).get_proc(p_ptr),
            forall|container_ptr: ContainerPtr|
                #![trigger self.get_container(container_ptr)]
                old(self).container_dom().contains(container_ptr) ==> self.get_container(
                    container_ptr,
                ) =~= old(self).get_container(container_ptr),
            forall|t_ptr: ThreadPtr|
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr) && t_ptr != thread_ptr ==> old(
                    self,
                ).get_thread(t_ptr) =~= self.get_thread(t_ptr),
            forall|e_ptr: EndpointPtr|
                #![trigger self.get_endpoint(e_ptr)]
                self.endpoint_dom().contains(e_ptr) && e_ptr != old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap() ==> old(self).get_endpoint(
                    e_ptr,
                ) =~= self.get_endpoint(e_ptr),
            self.get_thread(thread_ptr).endpoint_descriptors =~= old(self).get_thread(
                thread_ptr,
            ).endpoint_descriptors,
            self.get_thread(thread_ptr).ipc_payload =~= ipc_payload,
            self.get_thread(thread_ptr).state == ThreadState::BLOCKED,
            self.get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue_state == queue_state,
            self.get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).owning_threads == old(self).get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).owning_threads,
            self.get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue@ == old(self).get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue@.push(thread_ptr),
    {
        broadcast use ProcessManager::reveal_process_manager_wf;
        
        let endpoint_ptr = self.get_thread(thread_ptr).endpoint_descriptors.get(
            endpoint_index,
        ).unwrap();
        proof {
            old(self).get_endpoint(endpoint_ptr).queue.unique_implys_no_duplicates();
        }
        let cpu_id = self.get_thread(thread_ptr).running_cpu.unwrap();
        let old_cpu = *self.cpu_list.get(cpu_id);

        let mut endpoint_perm = Tracked(
            self.endpoint_perms.borrow_mut().tracked_remove(endpoint_ptr),
        );
        let sll = endpoint_push_and_set_state(
            endpoint_ptr,
            &mut endpoint_perm,
            thread_ptr,
            queue_state,
        );
        proof {
            self.endpoint_perms.borrow_mut().tracked_insert(endpoint_ptr, endpoint_perm.get());
        }
        let mut thread_perm = Tracked(self.thread_perms.borrow_mut().tracked_remove(thread_ptr));
        thread_set_blocking_endpoint_endpoint_ref_scheduler_ref_state_and_ipc_payload(
            thread_ptr,
            &mut thread_perm,
            Some(endpoint_ptr),
            Some(sll),
            None,
            ThreadState::BLOCKED,
            ipc_payload,
            Some(endpoint_index),
        );
        proof {
            self.thread_perms.borrow_mut().tracked_insert(thread_ptr, thread_perm.get());
        }

        self.cpu_list.set(
            cpu_id,
            Cpu {
                owning_container: old_cpu.owning_container,
                active: old_cpu.active,
                current_thread: None,
            },
        );

        assert(self.container_perms_wf());
        assert(self.container_tree_wf()) by {
            container_no_change_to_tree_fields_imply_wf(
                self.root_container,
                old(self).container_perms@,
                self.container_perms@,
            );
        };
        assert(self.container_fields_wf());
        assert(self.proc_perms_wf());
        assert(self.process_trees_wf()) by {
            assert forall|c_ptr: ContainerPtr|
                #![trigger self.container_dom().contains(c_ptr)]
                #![trigger self.process_tree_wf(c_ptr)]
                self.container_dom().contains(c_ptr) && self.get_container(
                    c_ptr,
                ).root_process.is_Some() implies self.process_tree_wf(c_ptr) by {
                process_no_change_to_trees_fields_imply_wf(
                    self.get_container(c_ptr).root_process.unwrap(),
                    self.get_container(c_ptr).owned_procs@.to_set(),
                    old(self).process_perms@,
                    self.process_perms@,
                );
            };
        };
        assert(self.process_fields_wf()) by {
            assert(forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
                    p_ptr,
                ));
        };
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.container_perms_wf());
        assert(self.processes_container_wf());
        assert(self.threads_process_wf());
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf());
        assert(self.threads_endpoint_descriptors_wf());
        assert(self.endpoints_queue_wf()) by {
            seq_push_lemma::<usize>();
            seq_push_unique_lemma::<usize>();
        };
        assert(self.endpoints_container_wf());
        assert(self.schedulers_wf());
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf());

    }

    pub fn block_running_thread_and_change_queue_state_and_set_trap_frame(
        &mut self,
        thread_ptr: ThreadPtr,
        endpoint_index: EndpointIdx,
        ipc_payload: IPCPayLoad,
        queue_state: EndpointState,
        pt_regs: &Registers,
    )
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].is_Some(),
            old(self).get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue.len() < MAX_NUM_THREADS_PER_ENDPOINT,
            old(self).get_thread(thread_ptr).state == ThreadState::RUNNING,
            ipc_payload.get_payload_as_va_range().is_Some()
                ==> ipc_payload.get_payload_as_va_range().unwrap().wf(),
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure(),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom(),
            forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                old(self).proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(
                    self,
                ).get_proc(p_ptr),
            forall|container_ptr: ContainerPtr|
                #![trigger self.get_container(container_ptr)]
                old(self).container_dom().contains(container_ptr) ==> self.get_container(
                    container_ptr,
                ) =~= old(self).get_container(container_ptr),
            forall|t_ptr: ThreadPtr|
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr) && t_ptr != thread_ptr ==> old(
                    self,
                ).get_thread(t_ptr) =~= self.get_thread(t_ptr),
            forall|e_ptr: EndpointPtr|
                #![trigger self.get_endpoint(e_ptr)]
                self.endpoint_dom().contains(e_ptr) && e_ptr != old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap() ==> old(self).get_endpoint(
                    e_ptr,
                ) =~= self.get_endpoint(e_ptr),
            self.get_thread(thread_ptr).endpoint_descriptors =~= old(self).get_thread(
                thread_ptr,
            ).endpoint_descriptors,
            self.get_thread(thread_ptr).ipc_payload =~= ipc_payload,
            self.get_thread(thread_ptr).state == ThreadState::BLOCKED,
            self.get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue_state == queue_state,
            self.get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).owning_threads == old(self).get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).owning_threads,
            self.get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue@ == old(self).get_endpoint(
                old(self).get_thread(
                    thread_ptr,
                ).endpoint_descriptors@[endpoint_index as int].unwrap(),
            ).queue@.push(thread_ptr),
    {
        broadcast use ProcessManager::reveal_process_manager_wf;
        
        let endpoint_ptr = self.get_thread(thread_ptr).endpoint_descriptors.get(
            endpoint_index,
        ).unwrap();
        proof {
            old(self).get_endpoint(endpoint_ptr).queue.unique_implys_no_duplicates();
        }
        let cpu_id = self.get_thread(thread_ptr).running_cpu.unwrap();
        let old_cpu = *self.cpu_list.get(cpu_id);

        let mut endpoint_perm = Tracked(
            self.endpoint_perms.borrow_mut().tracked_remove(endpoint_ptr),
        );
        let sll = endpoint_push_and_set_state(
            endpoint_ptr,
            &mut endpoint_perm,
            thread_ptr,
            queue_state,
        );
        proof {
            self.endpoint_perms.borrow_mut().tracked_insert(endpoint_ptr, endpoint_perm.get());
        }
        let mut thread_perm = Tracked(self.thread_perms.borrow_mut().tracked_remove(thread_ptr));
        thread_set_blocking_endpoint_endpoint_ref_scheduler_ref_state_and_ipc_payload(
            thread_ptr,
            &mut thread_perm,
            Some(endpoint_ptr),
            Some(sll),
            None,
            ThreadState::BLOCKED,
            ipc_payload,
            Some(endpoint_index),
        );
        thread_set_trap_frame_fast(thread_ptr, &mut thread_perm, pt_regs);
        proof {
            self.thread_perms.borrow_mut().tracked_insert(thread_ptr, thread_perm.get());
        }

        self.cpu_list.set(
            cpu_id,
            Cpu {
                owning_container: old_cpu.owning_container,
                active: old_cpu.active,
                current_thread: None,
            },
        );

        assert(self.container_perms_wf());
        assert(self.container_tree_wf()) by {
            container_no_change_to_tree_fields_imply_wf(
                self.root_container,
                old(self).container_perms@,
                self.container_perms@,
            );
        };
        assert(self.container_fields_wf());
        assert(self.proc_perms_wf());
        assert(self.process_trees_wf()) by {
            assert forall|c_ptr: ContainerPtr|
                #![trigger self.container_dom().contains(c_ptr)]
                #![trigger self.process_tree_wf(c_ptr)]
                self.container_dom().contains(c_ptr) && self.get_container(
                    c_ptr,
                ).root_process.is_Some() implies self.process_tree_wf(c_ptr) by {
                process_no_change_to_trees_fields_imply_wf(
                    self.get_container(c_ptr).root_process.unwrap(),
                    self.get_container(c_ptr).owned_procs@.to_set(),
                    old(self).process_perms@,
                    self.process_perms@,
                );
            };
        };
        assert(self.process_fields_wf()) by {
            assert(forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
                    p_ptr,
                ));
        };
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.container_perms_wf());
        assert(self.processes_container_wf());
        assert(self.threads_process_wf());
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf());
        assert(self.threads_endpoint_descriptors_wf());
        assert(self.endpoints_queue_wf()) by {
            seq_push_lemma::<usize>();
            seq_push_unique_lemma::<usize>();
        };
        assert(self.endpoints_container_wf());
        assert(self.schedulers_wf());
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf());

    }

    pub fn pass_endpoint(
        &mut self,
        src_thread_ptr: ThreadPtr,
        src_endpoint_index: EndpointIdx,
        dst_thread_ptr: ThreadPtr,
        dst_endpoint_index: EndpointIdx,
    )
        requires
            old(self).wf(),
            old(self).thread_dom().contains(src_thread_ptr),
            old(self).thread_dom().contains(dst_thread_ptr),
            src_thread_ptr != dst_thread_ptr,
            0 <= src_endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            0 <= dst_endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(src_thread_ptr).endpoint_descriptors@[src_endpoint_index as int].is_Some(),
            old(self).get_endpoint(old(self).get_thread(src_thread_ptr).endpoint_descriptors@[src_endpoint_index as int].unwrap()).rf_counter 
                != usize::MAX,
            old(self).get_thread(dst_thread_ptr).endpoint_descriptors@[dst_endpoint_index as int].is_None(),
            ( 
                old(self).get_endpoint(old(self).get_thread(src_thread_ptr).endpoint_descriptors@[src_endpoint_index as int].unwrap()).owning_container
                    == old(self).get_thread(dst_thread_ptr).owning_container
                ||
                old(self).get_container(old(self).get_endpoint(old(self).get_thread(src_thread_ptr).endpoint_descriptors@[src_endpoint_index as int].unwrap()).owning_container).subtree_set@.contains(
                    old(self).get_thread(dst_thread_ptr).owning_container
                )
            ),
                
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure(),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom(),
            forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                old(self).proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(
                    self,
                ).get_proc(p_ptr),
            forall|container_ptr: ContainerPtr|
                #![trigger self.get_container(container_ptr)]
                old(self).container_dom().contains(container_ptr) ==> self.get_container(
                    container_ptr,
                ) =~= old(self).get_container(container_ptr),
            forall|t_ptr: ThreadPtr|
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr) && t_ptr != dst_thread_ptr ==> old(
                    self,
                ).get_thread(t_ptr) =~= self.get_thread(t_ptr),
            forall|e_ptr: EndpointPtr|
                #![trigger self.get_endpoint(e_ptr)]
                self.endpoint_dom().contains(e_ptr) && e_ptr != old(self).get_thread(
                    src_thread_ptr,
                ).endpoint_descriptors@[src_endpoint_index as int].unwrap() ==> old(
                    self,
                ).get_endpoint(e_ptr) =~= self.get_endpoint(e_ptr),
            self.get_thread(dst_thread_ptr).endpoint_descriptors@ =~= old(self).get_thread(
                dst_thread_ptr,
            ).endpoint_descriptors@.update(
                dst_endpoint_index as int,
                Some(
                    old(self).get_thread(
                        src_thread_ptr,
                    ).endpoint_descriptors@[src_endpoint_index as int].unwrap(),
                ),
            ),
            self.get_endpoint(
                old(self).get_thread(
                    src_thread_ptr,
                ).endpoint_descriptors@[src_endpoint_index as int].unwrap(),
            ).owning_threads@ == old(self).get_endpoint(
                old(self).get_thread(
                    src_thread_ptr,
                ).endpoint_descriptors@[src_endpoint_index as int].unwrap(),
            ).owning_threads@.insert((dst_thread_ptr, dst_endpoint_index)),
            self.get_endpoint(
                old(self).get_thread(
                    src_thread_ptr,
                ).endpoint_descriptors@[src_endpoint_index as int].unwrap(),
            ).queue == old(self).get_endpoint(
                old(self).get_thread(
                    src_thread_ptr,
                ).endpoint_descriptors@[src_endpoint_index as int].unwrap(),
            ).queue,
            self.get_endpoint(
                self.get_thread(
                    src_thread_ptr,
                ).endpoint_descriptors@[src_endpoint_index as int].unwrap(),
            ).queue_state == old(self).get_endpoint(
                old(self).get_thread(
                    src_thread_ptr,
                ).endpoint_descriptors@[src_endpoint_index as int].unwrap(),
            ).queue_state,
    {
        broadcast use ProcessManager::reveal_specs_to_wf;
        
        let src_endpoint_ptr = self.get_thread(src_thread_ptr).endpoint_descriptors.get(src_endpoint_index).unwrap();

        let mut dst_thread_perm = Tracked(self.thread_perms.borrow_mut().tracked_remove(dst_thread_ptr));
        thread_set_endpoint_descriptor(
            dst_thread_ptr,
            &mut dst_thread_perm,
            dst_endpoint_index,
            Some(src_endpoint_ptr)
        );
        proof {
            self.thread_perms.borrow_mut().tracked_insert(dst_thread_ptr, dst_thread_perm.get());
        }

        assert(self.endpoint_dom().contains(src_endpoint_ptr)) by {
            broadcast use ProcessManager::reveal_wf_to_threads_endpoint_descriptors_wf;
        };
        assert(self.get_endpoint(src_endpoint_ptr).get_owning_threads().contains((dst_thread_ptr,dst_endpoint_index)) == false) by {
            broadcast use ProcessManager::reveal_wf_to_threads_endpoint_descriptors_wf;};

        let mut src_endpoint_perm = Tracked(
            self.endpoint_perms.borrow_mut().tracked_remove(src_endpoint_ptr),
        );
        endpoint_add_ref(
            src_endpoint_ptr,
            &mut src_endpoint_perm,
            dst_thread_ptr,
            dst_endpoint_index,
        );
        proof {
            self.endpoint_perms.borrow_mut().tracked_insert(
                src_endpoint_ptr,
                src_endpoint_perm.get(),
            );
        }

        assert(self.container_perms_wf());
        assert(self.container_tree_wf()) by {
            broadcast use ProcessManager::reveal_wf_to_container_tree_wf;
            container_no_change_to_tree_fields_imply_wf(
                self.root_container,
                old(self).container_perms@,
                self.container_perms@,
            );
        };
        assert(self.container_fields_wf());
        assert(self.proc_perms_wf());
        assert(self.process_trees_wf()) by {
            broadcast use ProcessManager::reveal_wf_to_process_trees_wf;
            broadcast use ProcessManager::reveal_wf_to_processes_container_wf;
            assert forall|c_ptr: ContainerPtr|
                #![trigger self.container_dom().contains(c_ptr)]
                #![trigger self.process_tree_wf(c_ptr)]
                self.container_dom().contains(c_ptr) && self.get_container(
                    c_ptr,
                ).root_process.is_Some() implies self.process_tree_wf(c_ptr) by {
                process_no_change_to_trees_fields_imply_wf(
                    self.get_container(c_ptr).root_process.unwrap(),
                    self.get_container(c_ptr).owned_procs@.to_set(),
                    old(self).process_perms@,
                    self.process_perms@,
                );
            };
        };
        assert(self.process_fields_wf()) by {
            assert(forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
                    p_ptr,
                ));
        };
        assert(self.cpus_wf()) by { broadcast use ProcessManager::reveal_wf_to_cpus_wf; };
        assert(self.container_cpu_wf()) by { broadcast use ProcessManager::reveal_wf_to_container_cpu_wf; };
        assert(self.memory_disjoint()) by { broadcast use ProcessManager::reveal_wf_to_memory_disjoint; };
        assert(self.container_perms_wf());
        assert(self.processes_container_wf()) by { broadcast use ProcessManager::reveal_wf_to_processes_container_wf; };
        assert(self.threads_process_wf()) by { broadcast use ProcessManager::reveal_wf_to_threads_process_wf; };
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf());
        assert(self.threads_endpoint_descriptors_wf()) by {
            broadcast use ProcessManager::reveal_wf_to_threads_endpoint_descriptors_wf;
            seq_update_lemma::<Option<EndpointPtr>>();
            assert(forall|t_ptr: ThreadPtr, e_idx: EndpointIdx|
                #![trigger self.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int]]
                self.thread_perms@.dom().contains(t_ptr) && 0 <= e_idx
                    < MAX_NUM_ENDPOINT_DESCRIPTORS
                    && self.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int].is_Some()
                    ==> self.endpoint_perms@.dom().contains(
                    self.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int].unwrap(),
                )
                    && self.endpoint_perms@[self.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int].unwrap()].value().owning_threads@.contains(
                (t_ptr, e_idx)));
            assert(forall|e_ptr: EndpointPtr, t_ptr: ThreadPtr, e_idx: EndpointIdx|
                #![trigger self.endpoint_perms@[e_ptr].value().owning_threads@.contains((t_ptr, e_idx))]
                self.endpoint_perms@.dom().contains(e_ptr)
                    && self.endpoint_perms@[e_ptr].value().owning_threads@.contains((t_ptr, e_idx))
                    ==> self.thread_perms@.dom().contains(t_ptr)
                    && self.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int].is_Some()
                    && self.thread_perms@[t_ptr].value().endpoint_descriptors@[e_idx as int].unwrap()
                    == e_ptr);
            // assert(forall|i:int| #![auto] 0 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS && i != dst_endpoint_index ==> self.thread_perms@[dst_thread_ptr].value().endpoint_descriptors@[i] == old(self).thread_perms@[dst_thread_ptr].value().endpoint_descriptors@[i]);
            // assert(self.thread_perms@[dst_thread_ptr].value().endpoint_descriptors@[dst_endpoint_index as int ] =~= Some(src_endpoint_ptr));
        };
        assert(self.endpoints_queue_wf()) by {
            broadcast use ProcessManager::reveal_wf_to_endpoints_queue_wf;
            seq_push_lemma::<usize>();
            seq_push_unique_lemma::<usize>();
            seq_update_lemma::<Option<EndpointPtr>>();
        };
        assert(self.endpoints_container_wf()) by { broadcast use ProcessManager::reveal_wf_to_endpoints_container_wf;};
        assert(self.schedulers_wf()) by { broadcast use ProcessManager::reveal_wf_to_schedulers_wf;};
        assert(self.pcid_ioid_wf()) by { broadcast use ProcessManager::reveal_wf_to_pcid_ioid_wf;};
        assert(self.threads_cpu_wf()) by { broadcast use ProcessManager::reveal_wf_to_threads_cpu_wf;};
        assert(self.threads_container_wf()) by { broadcast use ProcessManager::reveal_wf_to_threads_container_wf;};
        assert(self.endpoints_within_subtree())  by { broadcast use ProcessManager::reveal_wf_to_endpoints_within_subtree;};
    }

    pub fn new_endpoint(
        &mut self,
        thread_ptr: ThreadPtr,
        endpoint_index: EndpointIdx,
        page_ptr_1: PagePtr,
        page_perm_1: Tracked<PagePerm4k>,
    )
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(thread_ptr).endpoint_descriptors@[endpoint_index as int].is_None(),
            old(self).page_closure().contains(page_ptr_1) == false,
            page_perm_1@.is_init(),
            page_perm_1@.addr() == page_ptr_1,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.mem_4k
                > 0,
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure().insert(page_ptr_1),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom().insert(page_ptr_1),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom(),
            forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
                    p_ptr,
                ),
            forall|container_ptr: ContainerPtr|
                #![trigger self.get_container(container_ptr)]
                self.container_dom().contains(container_ptr) && container_ptr != old(
                    self,
                ).get_thread(thread_ptr).owning_container ==> self.get_container(container_ptr)
                    =~= old(self).get_container(container_ptr),
            forall|t_ptr: ThreadPtr|
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr) && t_ptr != thread_ptr ==> old(
                    self,
                ).get_thread(t_ptr) =~= self.get_thread(t_ptr),
            forall|e_ptr: EndpointPtr|
                #![trigger self.get_endpoint(e_ptr)]
                old(self).endpoint_dom().contains(e_ptr) ==> old(self).get_endpoint(e_ptr)
                    =~= self.get_endpoint(e_ptr),
            old(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).quota.spec_subtract_mem_4k(
                self.get_container(old(self).get_thread(thread_ptr).owning_container).quota,
                1,
            ),
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).owned_cpus
                == self.get_container(old(self).get_thread(thread_ptr).owning_container).owned_cpus,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).owned_threads
                == self.get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).owned_threads,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).scheduler
                == self.get_container(old(self).get_thread(thread_ptr).owning_container).scheduler,
            old(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).owned_endpoints@.insert(page_ptr_1) == self.get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).owned_endpoints@,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).children
                == self.get_container(old(self).get_thread(thread_ptr).owning_container).children,
            old(self).get_thread(thread_ptr).ipc_payload =~= self.get_thread(
                thread_ptr,
            ).ipc_payload,
            old(self).get_thread(thread_ptr).state =~= self.get_thread(thread_ptr).state,
            self.get_thread(thread_ptr).endpoint_descriptors@ =~= old(self).get_thread(
                thread_ptr,
            ).endpoint_descriptors@.update(endpoint_index as int, Some(page_ptr_1)),
            self.get_endpoint(page_ptr_1).queue@ =~= Seq::<ThreadPtr>::empty(),
            self.get_endpoint(page_ptr_1).queue_state =~= EndpointState::SEND,
            self.get_endpoint(page_ptr_1).rf_counter =~= 1,
            self.get_endpoint(page_ptr_1).owning_threads@ =~= Set::<
                (ThreadPtr, EndpointIdx),
            >::empty().insert((thread_ptr, endpoint_index)),
            self.get_endpoint(page_ptr_1).owning_container =~= old(self).get_thread(
                thread_ptr,
            ).owning_container,
    {
        broadcast use ProcessManager::reveal_process_manager_wf;
        
        let container_ptr = self.get_thread(thread_ptr).owning_container;
        let old_mem_quota = self.get_container(container_ptr).quota.mem_4k;

        let mut container_perm = Tracked(
            self.container_perms.borrow_mut().tracked_remove(container_ptr),
        );
        container_set_quota_mem_4k(container_ptr, &mut container_perm, old_mem_quota - 1);
        let sll_index = container_push_endpoint(container_ptr, &mut container_perm, page_ptr_1);
        ;
        proof {
            self.container_perms.borrow_mut().tracked_insert(container_ptr, container_perm.get());
        }

        let (endpoint_ptr, endpoint_perm) = page_to_endpoint_with_thread_and_container(
            container_ptr,
            thread_ptr,
            endpoint_index,
            page_ptr_1,
            page_perm_1,
        );
        proof {
            self.endpoint_perms.borrow_mut().tracked_insert(endpoint_ptr, endpoint_perm.get());
        }

        let mut thread_perm = Tracked(self.thread_perms.borrow_mut().tracked_remove(thread_ptr));
        thread_set_endpoint_descriptor(
            thread_ptr,
            &mut thread_perm,
            endpoint_index,
            Some(endpoint_ptr),
        );
        proof {
            self.thread_perms.borrow_mut().tracked_insert(thread_ptr, thread_perm.get());
        }

        assert(self.container_perms_wf());
        assert(self.container_tree_wf()) by {
            container_no_change_to_tree_fields_imply_wf(
                self.root_container,
                old(self).container_perms@,
                self.container_perms@,
            );
        };
        assert(self.container_fields_wf());
        assert(self.proc_perms_wf());
        assert(self.process_trees_wf()) by {
            assert forall|c_ptr: ContainerPtr|
                #![trigger self.container_dom().contains(c_ptr)]
                #![trigger self.process_tree_wf(c_ptr)]
                self.container_dom().contains(c_ptr) && self.get_container(
                    c_ptr,
                ).root_process.is_Some() implies self.process_tree_wf(c_ptr) by {
                process_no_change_to_trees_fields_imply_wf(
                    self.get_container(c_ptr).root_process.unwrap(),
                    self.get_container(c_ptr).owned_procs@.to_set(),
                    old(self).process_perms@,
                    self.process_perms@,
                );
            };
        };
        assert(self.process_fields_wf()) by {
            assert(forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
                    p_ptr,
                ));
        };
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.container_perms_wf());
        assert(self.processes_container_wf());
        assert(self.threads_process_wf());
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf());
        assert(self.threads_endpoint_descriptors_wf()) by {
            seq_update_lemma::<Option<EndpointPtr>>();
        };
        assert(self.endpoints_queue_wf()) by {
            seq_push_lemma::<usize>();
            seq_push_unique_lemma::<usize>();
            seq_update_lemma::<Option<EndpointPtr>>();
            assert(forall|t_ptr: ThreadPtr|
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
                == self.thread_perms@[t_ptr].value().endpoint_rev_ptr.unwrap());
            assert(forall|e_ptr: EndpointPtr|
                #![auto]
                old(self).endpoint_perms@.dom().contains(e_ptr)
                    ==> 
                self.endpoint_perms@.dom().contains(e_ptr)
                &&
                self.get_endpoint(e_ptr) == old(self).get_endpoint(e_ptr)
                    // && self.thread_perms@[t_ptr].value().blocking_endpoint_ptr
                    // == Some(e_ptr)
                    // && self.thread_perms@[t_ptr].value().state
                    // == ThreadState::BLOCKED
                );
            assert(forall|e_ptr: EndpointPtr, t_ptr: ThreadPtr|
                #![auto]
                old(self).endpoint_perms@.dom().contains(e_ptr) && self.endpoint_perms@[e_ptr].value().queue@.contains(t_ptr)
                    ==> 
                    self.thread_perms@.dom().contains(t_ptr)
                    && self.thread_perms@[t_ptr].value().blocking_endpoint_ptr
                    == Some(e_ptr)
                    && self.thread_perms@[t_ptr].value().state
                    == ThreadState::BLOCKED
                );
        };
        assert(self.endpoints_container_wf()) by {
            seq_push_lemma::<usize>();
            seq_push_unique_lemma::<usize>();
        };
        assert(self.schedulers_wf());
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf());
    }

    pub fn pop_scheduler_for_idle_cpu(&mut self, cpu_id: CpuId, pt_regs: &mut Registers) -> (ret:
        ThreadPtr)
        requires
            old(self).wf(),
            0 <= cpu_id < NUM_CPUS,
            old(self).cpu_list@[cpu_id as int].active == true,
            old(self).cpu_list@[cpu_id as int].current_thread.is_None(),
            old(self).get_container(
                old(self).cpu_list@[cpu_id as int].owning_container,
            ).scheduler.len() != 0,
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure(),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom(),
            self.thread_dom().contains(ret),
            forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
                    p_ptr,
                ),
            forall|container_ptr: ContainerPtr|
                #![trigger self.get_container(container_ptr)]
                self.container_dom().contains(container_ptr) && container_ptr != old(
                    self,
                ).cpu_list@[cpu_id as int].owning_container ==> self.get_container(container_ptr)
                    =~= old(self).get_container(container_ptr),
            forall|t_ptr: ThreadPtr|
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr) && t_ptr != ret ==> old(self).get_thread(
                    t_ptr,
                ) =~= self.get_thread(t_ptr),
            forall|e_ptr: EndpointPtr|
                #![trigger self.get_endpoint(e_ptr)]
                old(self).endpoint_dom().contains(e_ptr) ==> old(self).get_endpoint(e_ptr)
                    =~= self.get_endpoint(e_ptr),
            old(self).get_container(old(self).cpu_list@[cpu_id as int].owning_container).quota
                == self.get_container(old(self).cpu_list@[cpu_id as int].owning_container).quota,
            old(self).get_container(old(self).cpu_list@[cpu_id as int].owning_container).owned_cpus
                == self.get_container(
                old(self).cpu_list@[cpu_id as int].owning_container,
            ).owned_cpus,
            old(self).get_container(
                old(self).cpu_list@[cpu_id as int].owning_container,
            ).owned_threads == self.get_container(
                old(self).cpu_list@[cpu_id as int].owning_container,
            ).owned_threads,
            old(self).get_container(
                old(self).cpu_list@[cpu_id as int].owning_container,
            ).scheduler@.skip(1) == self.get_container(
                old(self).cpu_list@[cpu_id as int].owning_container,
            ).scheduler@,
            old(self).get_container(
                old(self).cpu_list@[cpu_id as int].owning_container,
            ).owned_endpoints == self.get_container(
                old(self).cpu_list@[cpu_id as int].owning_container,
            ).owned_endpoints,
            old(self).get_container(old(self).cpu_list@[cpu_id as int].owning_container).children
                == self.get_container(old(self).cpu_list@[cpu_id as int].owning_container).children,
            old(self).get_thread(ret).ipc_payload =~= self.get_thread(ret).ipc_payload,
            self.get_thread(ret).state =~= ThreadState::RUNNING,
            old(self).get_thread(ret).endpoint_descriptors =~= self.get_thread(
                ret,
            ).endpoint_descriptors,
    {
        broadcast use ProcessManager::reveal_process_manager_wf;
        
        let container_ptr = self.cpu_list.get(cpu_id).owning_container;
        assert(self.container_dom().contains(container_ptr)) by {
            assert(old(self).cpu_list@[cpu_id as int].owning_container == container_ptr);
            assert(self.container_cpu_wf());
            assert(forall|cpu_i: CpuId|
                #![auto]
                0 <= cpu_i < NUM_CPUS ==> old(self).container_dom().contains(
                    old(self).cpu_list@[cpu_i as int].owning_container,
                ));
        };

        let mut container_perm = Tracked(
            self.container_perms.borrow_mut().tracked_remove(container_ptr),
        );
        let (ret_thread_ptr, sll) = scheduler_pop_head(container_ptr, &mut container_perm);
        proof {
            self.container_perms.borrow_mut().tracked_insert(container_ptr, container_perm.get());
        }

        assert(old(self).get_container(container_ptr).scheduler@.contains(ret_thread_ptr));

        let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(ret_thread_ptr);
        let thread: &Thread = PPtr::<Thread>::from_usize(ret_thread_ptr).borrow(
            Tracked(thread_perm),
        );
        pt_regs.set_self_fast(thread.trap_frame.unwrap());

        let mut thread_perm = Tracked(
            self.thread_perms.borrow_mut().tracked_remove(ret_thread_ptr),
        );

        thread_set_current_cpu(ret_thread_ptr, &mut thread_perm, Some(cpu_id));
        thread_set_state(ret_thread_ptr, &mut thread_perm, ThreadState::RUNNING);
        proof {
            self.thread_perms.borrow_mut().tracked_insert(ret_thread_ptr, thread_perm.get());
        }

        self.cpu_list.set(
            cpu_id,
            Cpu {
                owning_container: container_ptr,
                active: true,
                current_thread: Some(ret_thread_ptr),
            },
        );

        assert(self.container_perms_wf());
        assert(self.container_tree_wf()) by {
            container_no_change_to_tree_fields_imply_wf(
                self.root_container,
                old(self).container_perms@,
                self.container_perms@,
            );
        };
        assert(self.container_fields_wf());
        assert(self.proc_perms_wf());
        assert(self.process_trees_wf()) by {
            assert forall|c_ptr: ContainerPtr|
                #![trigger self.container_dom().contains(c_ptr)]
                #![trigger self.process_tree_wf(c_ptr)]
                self.container_dom().contains(c_ptr) && self.get_container(
                    c_ptr,
                ).root_process.is_Some() implies self.process_tree_wf(c_ptr) by {
                process_no_change_to_trees_fields_imply_wf(
                    self.get_container(c_ptr).root_process.unwrap(),
                    self.get_container(c_ptr).owned_procs@.to_set(),
                    old(self).process_perms@,
                    self.process_perms@,
                );
            };
        };
        assert(self.process_fields_wf()) by {
            assert(forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
                    p_ptr,
                ));
        };
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.container_perms_wf());
        assert(self.processes_container_wf());
        assert(self.threads_process_wf());
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf());
        assert(self.threads_endpoint_descriptors_wf()) by {
            seq_update_lemma::<Option<EndpointPtr>>();
        };
        assert(self.endpoints_queue_wf()) by {
            seq_push_lemma::<usize>();
            seq_push_unique_lemma::<usize>();
            seq_update_lemma::<Option<EndpointPtr>>();
        };
        assert(self.endpoints_container_wf()) by {
            seq_push_lemma::<usize>();
            seq_push_unique_lemma::<usize>();
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

    pub fn container_check_is_ancestor(&self, ancestor_ptr: ContainerPtr, child_ptr: ContainerPtr) -> (ret:bool)
        requires
            self.wf(),
            self.container_dom().contains(ancestor_ptr),
            self.container_dom().contains(child_ptr),
            // self.get_container(ancestor_ptr).depth < self.get_container(child_ptr).depth,
            // child_ptr != ancestor_ptr,
        ensures
            // ret == self.get_container(child_ptr).uppertree_seq@.contains(ancestor_ptr),
            ret == self.get_container(ancestor_ptr).subtree_set@.contains(child_ptr),
    {
        broadcast use ProcessManager::reveal_process_manager_wf;
        if self.get_container(ancestor_ptr).depth >= self.get_container(child_ptr).depth {
            proof {
                self.same_or_deeper_depth_imply_none_ancestor(ancestor_ptr, child_ptr);
            }
            return false;
        }
        container_tree_check_is_ancestor(
            self.root_container,
            &self.container_perms,
            ancestor_ptr,
            child_ptr,
        )
    }

}

} // verus!

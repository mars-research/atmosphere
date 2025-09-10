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
use crate::process_manager::spec_impl::*;

impl ProcessManager {
    pub fn new_thread(
        &mut self,
        proc_ptr: ProcPtr,
        pt_regs: Registers,
        page_ptr: PagePtr,
        page_perm: Tracked<PagePerm4k>,
    ) -> (ret: ThreadPtr)
        requires
            old(self).wf(),
            old(self).proc_dom().contains(proc_ptr),
            old(self).page_closure().contains(page_ptr) == false,
            old(self).get_proc(proc_ptr).owned_threads.len() < MAX_NUM_THREADS_PER_PROC,
            old(self).get_container_by_proc_ptr(proc_ptr).quota.mem_4k > 0,
            old(self).get_container_by_proc_ptr(proc_ptr).scheduler.len()
                < MAX_CONTAINER_SCHEDULER_LEN,
            page_perm@.is_init(),
            page_perm@.addr() == page_ptr,
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure().insert(page_ptr),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom().insert(ret),
            old(self).get_container(
                old(self).get_proc(proc_ptr).owning_container,
            ).quota.spec_subtract_mem_4k(
                self.get_container(self.get_proc(proc_ptr).owning_container).quota,
                1,
            ),
            old(self).get_proc(proc_ptr).pcid =~= self.get_proc(proc_ptr).pcid,
            old(self).get_proc(proc_ptr).ioid =~= self.get_proc(proc_ptr).ioid,
            forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) && p_ptr != proc_ptr ==> self.get_proc(p_ptr)
                    =~= old(self).get_proc(p_ptr),
            forall|container_ptr: ContainerPtr|
                #![trigger self.get_container(container_ptr).owned_procs]
                self.container_dom().contains(container_ptr) && container_ptr != self.get_proc(
                    proc_ptr,
                ).owning_container ==> self.get_container(container_ptr).owned_procs =~= old(
                    self,
                ).get_container(container_ptr).owned_procs,
    {
        // proof{seq_push_lemma::<ThreadPtr>();}
        broadcast use ProcessManager::reveal_internal_wf;

        let container_ptr = self.get_proc(proc_ptr).owning_container;
        let old_mem_quota = self.get_container(container_ptr).quota.mem_4k;
        let old_owned_threads = self.get_container(container_ptr).owned_threads;
        let mut proc_perm = Tracked(self.process_perms.borrow_mut().tracked_remove(proc_ptr));
        let proc_node_ref = proc_push_thread(proc_ptr, &mut proc_perm, &page_ptr);
        proof {
            self.process_perms.borrow_mut().tracked_insert(proc_ptr, proc_perm.get());
        }

        let mut container_perm = Tracked(
            self.container_perms.borrow_mut().tracked_remove(container_ptr),
        );
        let scheduler_node_ref = scheduler_push_thread(
            container_ptr,
            &mut container_perm,
            &page_ptr,
        );
        container_set_quota_mem_4k(container_ptr, &mut container_perm, old_mem_quota - 1);
        container_set_owned_threads(
            container_ptr,
            &mut container_perm,
            Ghost(old_owned_threads@.insert(page_ptr)),
        );
        proof {
            self.container_perms.borrow_mut().tracked_insert(container_ptr, container_perm.get());
        }

        let (thread_ptr, thread_perm) = page_to_thread(
            page_ptr,
            page_perm,
            &pt_regs,
            container_ptr,
            proc_ptr,
            proc_node_ref,
            scheduler_node_ref,
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
        assert(self.proc_perms_wf()) by {
            assert(forall|p_ptr: ProcPtr|
                #![auto]
                self.process_perms@.dom().contains(p_ptr) && proc_ptr != p_ptr ==> old(
                    self,
                ).process_perms@[p_ptr].value().subtree_set
                    =~= self.process_perms@[p_ptr].value().subtree_set);
        };
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
                self.proc_dom().contains(p_ptr) && proc_ptr != p_ptr ==> self.get_proc(p_ptr)
                    =~= old(self).get_proc(p_ptr));
        };
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.container_perms_wf());
        assert(self.processes_container_wf());
        assert(self.threads_process_wf()) by {
            seq_push_lemma::<ThreadPtr>();
            assert(forall|p_ptr: ProcPtr|
                #![auto]
                self.process_perms@.dom().contains(p_ptr) && p_ptr != proc_ptr ==> old(
                    self,
                ).process_perms@[p_ptr].value().owned_threads
                    =~= self.process_perms@[p_ptr].value().owned_threads);
        };
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf());
        assert(self.threads_endpoint_descriptors_wf());
        assert(self.endpoints_queue_wf());
        assert(self.endpoints_container_wf());
        assert(self.schedulers_wf()) by {
            seq_push_lemma::<ThreadPtr>();
        };
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf());
        thread_ptr
    }

    pub fn new_thread_with_endpoint(
        &mut self,
        thread_ptr: ThreadPtr,
        endpoint_index: EndpointIdx,
        proc_ptr: ProcPtr,
        pt_regs: &Registers,
        page_ptr: PagePtr,
        page_perm: Tracked<PagePerm4k>,
    ) -> (ret: ThreadPtr)
        requires
            old(self).wf(),
            old(self).proc_dom().contains(proc_ptr),
            old(self).thread_dom().contains(thread_ptr),
            old(self).page_closure().contains(page_ptr) == false,
            old(self).get_proc(proc_ptr).owned_threads.len() < MAX_NUM_THREADS_PER_PROC,
            old(self).get_container_by_proc_ptr(proc_ptr).quota.mem_4k > 0,
            old(self).get_container_by_proc_ptr(proc_ptr).scheduler.len()
                < MAX_CONTAINER_SCHEDULER_LEN,
            old(self).get_thread(thread_ptr).owning_proc == proc_ptr,
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_endpoint_by_endpoint_idx(thread_ptr, endpoint_index).is_Some() || old(
                self,
            ).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).is_Some(),
            old(self).get_endpoint_by_endpoint_idx(
                thread_ptr,
                endpoint_index,
            ).unwrap().rf_counter_is_full() == false || old(self).get_endpoint(
                old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap(),
            ).rf_counter_is_full() == false,
            page_perm@.is_init(),
            page_perm@.addr() == page_ptr,
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure().insert(page_ptr),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom().insert(ret),
            old(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).quota.spec_subtract_mem_4k(
                self.get_container(self.get_thread(thread_ptr).owning_container).quota,
                1,
            ),
            old(self).get_proc(proc_ptr).pcid =~= self.get_proc(proc_ptr).pcid,
            old(self).get_proc(proc_ptr).ioid =~= self.get_proc(proc_ptr).ioid,
            forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) && p_ptr != proc_ptr ==> self.get_proc(p_ptr)
                    =~= old(self).get_proc(p_ptr),
            forall|container_ptr: ContainerPtr|
                #![trigger self.get_container(container_ptr)]
                self.container_dom().contains(container_ptr) && container_ptr != self.get_thread(
                    thread_ptr,
                ).owning_container ==> self.get_container(container_ptr) =~= old(
                    self,
                ).get_container(container_ptr) && self.get_container(
                    container_ptr,
                ).owned_threads@.contains(ret) == false,
            forall|t_ptr: ThreadPtr|
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr) ==> old(self).get_thread(t_ptr)
                    =~= self.get_thread(t_ptr),
            forall|e_ptr: EndpointPtr|
                #![trigger self.get_endpoint(e_ptr)]
                self.endpoint_dom().contains(e_ptr) && e_ptr != old(
                    self,
                ).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap() ==> old(
                    self,
                ).get_endpoint(e_ptr) =~= self.get_endpoint(e_ptr),
            self.get_proc(proc_ptr).owned_threads@ == old(self).get_proc(
                proc_ptr,
            ).owned_threads@.push(ret),
            self.get_container(self.get_thread(thread_ptr).owning_container).owned_procs =~= old(
                self,
            ).get_container(self.get_thread(thread_ptr).owning_container).owned_procs,
            self.get_container(self.get_thread(thread_ptr).owning_container).owned_endpoints@
                =~= old(self).get_container(
                self.get_thread(thread_ptr).owning_container,
            ).owned_endpoints@,
            self.get_container(self.get_thread(thread_ptr).owning_container).subtree_set =~= old(
                self,
            ).get_container(self.get_thread(thread_ptr).owning_container).subtree_set,
            self.get_container(self.get_thread(thread_ptr).owning_container).depth =~= old(
                self,
            ).get_container(self.get_thread(thread_ptr).owning_container).depth,
            self.get_container(self.get_thread(thread_ptr).owning_container).owned_threads@ =~= old(
                self,
            ).get_container(self.get_thread(thread_ptr).owning_container).owned_threads@.insert(
                ret,
            ),
            self.get_thread(ret).owning_container == old(self).get_thread(
                thread_ptr,
            ).owning_container,
            self.get_thread(ret).endpoint_descriptors@ =~= Seq::new(
                MAX_NUM_ENDPOINT_DESCRIPTORS as nat,
                |i: int| { None },
            ).update(
                0,
                Some(
                    old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap(),
                ),
            ),
            self.get_endpoint(
                old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap(),
            ).owning_threads@ =~= old(self).get_endpoint(
                old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap(),
            ).owning_threads@.insert((ret, 0)),
            self.get_endpoint(
                old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap(),
            ).queue_state =~= old(self).get_endpoint(
                old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap(),
            ).queue_state,
    {
        proof {
            seq_push_lemma::<ThreadPtr>();
        }
        broadcast use ProcessManager::reveal_internal_wf;

        let container_ptr = self.get_proc(proc_ptr).owning_container;
        let old_mem_quota = self.get_container(container_ptr).quota.mem_4k;
        let old_owned_threads = self.get_container(container_ptr).owned_threads;
        let endpoint_ptr = self.get_thread(thread_ptr).endpoint_descriptors.get(
            endpoint_index,
        ).unwrap();
        let mut proc_perm = Tracked(self.process_perms.borrow_mut().tracked_remove(proc_ptr));
        let proc_node_ref = proc_push_thread(proc_ptr, &mut proc_perm, &page_ptr);
        proof {
            self.process_perms.borrow_mut().tracked_insert(proc_ptr, proc_perm.get());
        }

        let mut container_perm = Tracked(
            self.container_perms.borrow_mut().tracked_remove(container_ptr),
        );
        let scheduler_node_ref = scheduler_push_thread(
            container_ptr,
            &mut container_perm,
            &page_ptr,
        );
        container_set_quota_mem_4k(container_ptr, &mut container_perm, old_mem_quota - 1);
        container_set_owned_threads(
            container_ptr,
            &mut container_perm,
            Ghost(old_owned_threads@.insert(page_ptr)),
        );
        proof {
            self.container_perms.borrow_mut().tracked_insert(container_ptr, container_perm.get());
        }

        let (thread_ptr, thread_perm) = page_to_thread_with_endpoint(
            page_ptr,
            page_perm,
            &pt_regs,
            container_ptr,
            proc_ptr,
            proc_node_ref,
            scheduler_node_ref,
            endpoint_ptr,
        );

        proof {
            self.thread_perms.borrow_mut().tracked_insert(thread_ptr, thread_perm.get());
        }

        let mut endpoint_perm = Tracked(
            self.endpoint_perms.borrow_mut().tracked_remove(endpoint_ptr),
        );
        endpoint_add_ref(endpoint_ptr, &mut endpoint_perm, page_ptr, 0);
        proof {
            self.endpoint_perms.borrow_mut().tracked_insert(endpoint_ptr, endpoint_perm.get());
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
        assert(self.proc_perms_wf()) by {
            assert(forall|p_ptr: ProcPtr|
                #![auto]
                self.process_perms@.dom().contains(p_ptr) && proc_ptr != p_ptr ==> old(
                    self,
                ).process_perms@[p_ptr].value().subtree_set
                    =~= self.process_perms@[p_ptr].value().subtree_set);
        };
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
                self.proc_dom().contains(p_ptr) && proc_ptr != p_ptr ==> self.get_proc(p_ptr)
                    =~= old(self).get_proc(p_ptr));
        };
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.container_perms_wf());
        assert(self.processes_container_wf());
        assert(self.threads_process_wf()) by {
            assert(forall|p_ptr: ProcPtr|
                #![auto]
                self.process_perms@.dom().contains(p_ptr) && p_ptr != proc_ptr ==> old(
                    self,
                ).process_perms@[p_ptr].value().owned_threads
                    =~= self.process_perms@[p_ptr].value().owned_threads);
        };
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf());
        assert(self.threads_endpoint_descriptors_wf());
        assert(self.endpoints_queue_wf());
        assert(self.endpoints_container_wf());
        assert(self.schedulers_wf());
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf()) by {
            assert(forall|c_ptr: ContainerPtr|
             // #![trigger self.container_dom().contains(c_ptr)]

                #![trigger self.get_container(c_ptr).owned_threads]
                self.container_dom().contains(c_ptr) ==> self.get_container(
                    c_ptr,
                ).owned_threads@.subset_of(self.thread_perms@.dom()));
            assert(forall|c_ptr: ContainerPtr, t_ptr: ThreadPtr|
                #![trigger self.get_container(c_ptr).owned_threads@.contains(t_ptr)]
                self.container_dom().contains(c_ptr) && self.get_container(
                    c_ptr,
                ).owned_threads@.contains(t_ptr)
                    ==> self.thread_perms@[t_ptr].value().owning_container == c_ptr);
            assert(forall|t_ptr: ThreadPtr|
                #![trigger self.container_dom().contains(self.thread_perms@[t_ptr].value().owning_container)]
                self.thread_perms@.dom().contains(t_ptr) ==> self.container_dom().contains(
                    self.thread_perms@[t_ptr].value().owning_container,
                ) && self.get_container(
                    self.thread_perms@[t_ptr].value().owning_container,
                ).owned_threads@.contains(t_ptr));
        };
        thread_ptr
    }
}

} // verus!

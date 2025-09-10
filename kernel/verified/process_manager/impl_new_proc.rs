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
    pub fn new_proc_with_endpoint(
        &mut self,
        thread_ptr: ThreadPtr,
        endpoint_index: EndpointIdx,
        pt_regs: &Registers,
        page_ptr_1: PagePtr,
        page_perm_1: Tracked<PagePerm4k>,
        page_ptr_2: PagePtr,
        page_perm_2: Tracked<PagePerm4k>,
        new_pcid: Pcid,
    )
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            old(self).page_closure().contains(page_ptr_1) == false,
            old(self).page_closure().contains(page_ptr_2) == false,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.mem_4k
                >= 2,
            old(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).owned_procs.len() < CONTAINER_PROC_LIST_LEN,
            old(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).scheduler.len() < MAX_CONTAINER_SCHEDULER_LEN,
            old(self).get_proc(old(self).get_thread(thread_ptr).owning_proc).children.len()
                < PROC_CHILD_LIST_LEN,
            old(self).get_proc(old(self).get_thread(thread_ptr).owning_proc).depth != usize::MAX,
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
            forall|p_ptr_i: ProcPtr|
                #![trigger old(self).proc_dom().contains(p_ptr_i) ]
                old(self).proc_dom().contains(p_ptr_i) ==> old(self).get_proc(p_ptr_i).pcid
                    != new_pcid,
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
            old(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).quota.spec_subtract_mem_4k(
                self.get_container(self.get_thread(thread_ptr).owning_container).quota,
                2,
            ),
            forall|p_ptr: ProcPtr|
                #![trigger old(self).proc_dom().contains(p_ptr)]
                old(self).proc_dom().contains(p_ptr) && (self.get_proc(
                    page_ptr_1,
                ).uppertree_seq@.contains(p_ptr) == false || self.get_container(
                    old(self).get_thread(thread_ptr).owning_container,
                ).owned_procs@.contains(p_ptr) == false) ==> self.get_proc(p_ptr) =~= old(
                    self,
                ).get_proc(p_ptr),
            forall|p_ptr: ProcPtr|
                #![trigger old(self).proc_dom().contains(p_ptr)]
                old(self).proc_dom().contains(p_ptr) && self.get_proc(
                    page_ptr_1,
                ).uppertree_seq@.contains(p_ptr) ==> self.get_proc(p_ptr).owning_container =~= old(
                    self,
                ).get_proc(p_ptr).owning_container && self.get_proc(p_ptr).pcid =~= old(
                    self,
                ).get_proc(p_ptr).pcid && self.get_proc(p_ptr).ioid =~= old(self).get_proc(
                    p_ptr,
                ).ioid && self.get_proc(p_ptr).owned_threads =~= old(self).get_proc(
                    p_ptr,
                ).owned_threads && self.get_proc(p_ptr).parent =~= old(self).get_proc(p_ptr).parent
                    && (p_ptr != old(self).get_thread(thread_ptr).owning_proc ==> self.get_proc(
                    p_ptr,
                ).children =~= old(self).get_proc(p_ptr).children) && self.get_proc(
                    p_ptr,
                ).uppertree_seq =~= old(self).get_proc(p_ptr).uppertree_seq && self.get_proc(
                    p_ptr,
                ).depth =~= old(self).get_proc(p_ptr).depth && self.get_proc(p_ptr).subtree_set@
                    =~= old(self).get_proc(p_ptr).subtree_set@.insert(page_ptr_1),
            forall|container_ptr: ContainerPtr|
                #![trigger self.get_container(container_ptr)]
                self.container_dom().contains(container_ptr) && container_ptr != self.get_thread(
                    thread_ptr,
                ).owning_container ==> self.get_container(container_ptr) =~= old(
                    self,
                ).get_container(container_ptr),
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
            self.get_proc(page_ptr_1).pcid =~= new_pcid,
            self.get_proc(page_ptr_1).ioid.is_None(),
            self.get_proc(page_ptr_1).owned_threads@ == Seq::<ThreadPtr>::empty().push(page_ptr_2),
            self.get_proc(page_ptr_1).owning_container == self.get_thread(
                thread_ptr,
            ).owning_container,
            self.get_container(self.get_thread(thread_ptr).owning_container).owned_procs@ =~= old(
                self,
            ).get_container(self.get_thread(thread_ptr).owning_container).owned_procs@.push(
                page_ptr_1,
            ),
            self.get_container(self.get_thread(thread_ptr).owning_container).owned_endpoints@
                =~= old(self).get_container(
                self.get_thread(thread_ptr).owning_container,
            ).owned_endpoints@,
            self.get_container(self.get_thread(thread_ptr).owning_container).owned_threads@ =~= old(
                self,
            ).get_container(self.get_thread(thread_ptr).owning_container).owned_threads@.insert(
                page_ptr_2,
            ),
            self.get_thread(page_ptr_2).owning_container == old(self).get_thread(
                thread_ptr,
            ).owning_container,
            self.get_thread(page_ptr_2).endpoint_descriptors@ =~= Seq::new(
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
            ).owning_threads@.insert((page_ptr_2, 0)),
    {
        proof {
            seq_push_lemma::<ThreadPtr>();
        }
        broadcast use ProcessManager::reveal_internal_wf;

        let container_ptr = self.get_thread(thread_ptr).owning_container;
        let old_proc_ptr = self.get_thread(thread_ptr).owning_proc;
        let old_mem_quota = self.get_container(container_ptr).quota.mem_4k;
        let old_owned_threads = self.get_container(container_ptr).owned_threads;
        let endpoint_ptr = self.get_thread(thread_ptr).endpoint_descriptors.get(
            endpoint_index,
        ).unwrap();

        let old_upper_tree_seq = self.get_proc(old_proc_ptr).uppertree_seq;
        let old_depth = self.get_proc(old_proc_ptr).depth;

        assert forall|p_ptr: ProcPtr|
            #![trigger self.get_proc(p_ptr).children]
            #![trigger self.get_proc(p_ptr).uppertree_seq]
            self.proc_dom().contains(p_ptr) implies self.get_proc(p_ptr).children@.contains(
            page_ptr_1,
        ) == false && self.get_proc(p_ptr).uppertree_seq@.contains(page_ptr_1) == false
            && self.get_proc(p_ptr).uppertree_seq@.contains(p_ptr) == false by {
            proc_tree_wf_imply_childern_uppertree_specs(
                self.get_container(self.get_proc(p_ptr).owning_container).root_process.unwrap(),
                self.get_container(self.get_proc(p_ptr).owning_container).owned_procs@.to_set(),
                self.process_perms@,
            );
        };

        let mut old_proc_perm = Tracked(
            self.process_perms.borrow_mut().tracked_remove(old_proc_ptr),
        );
        let child_list_node_ref = proc_push_child(old_proc_ptr, &mut old_proc_perm, &page_ptr_1);
        proof {
            self.process_perms.borrow_mut().tracked_insert(old_proc_ptr, old_proc_perm.get());
        }

        let mut container_perm = Tracked(
            self.container_perms.borrow_mut().tracked_remove(container_ptr),
        );
        let proc_list_node_ref = container_push_proc(
            container_ptr,
            &mut container_perm,
            page_ptr_1,
        );
        let scheduler_node_ref = scheduler_push_thread(
            container_ptr,
            &mut container_perm,
            &page_ptr_2,
        );
        container_set_quota_mem_4k(container_ptr, &mut container_perm, old_mem_quota - 2);
        container_set_owned_threads(
            container_ptr,
            &mut container_perm,
            Ghost(old_owned_threads@.insert(page_ptr_2)),
        );
        proof {
            self.container_perms.borrow_mut().tracked_insert(container_ptr, container_perm.get());
        }

        let (new_proc_ptr, mut proc_perm, proc_thread_list_node_ref) =
            page_to_proc_with_first_thread(
            page_ptr_1,
            page_perm_1,
            container_ptr,
            proc_list_node_ref,
            new_pcid,
            None,
            page_ptr_2,
            Some(old_proc_ptr),
            Some(child_list_node_ref),
            Ghost(old_upper_tree_seq@.push(old_proc_ptr)),
            Ghost(Set::empty()),
            old_depth + 1,
        );
        proof {
            self.process_perms.borrow_mut().tracked_insert(new_proc_ptr, proc_perm.get());
        }
        let (new_thread_ptr, thread_perm) = page_to_thread_with_endpoint(
            page_ptr_2,
            page_perm_2,
            pt_regs,
            container_ptr,
            new_proc_ptr,
            proc_thread_list_node_ref,
            scheduler_node_ref,
            endpoint_ptr,
        );
        proof {
            self.thread_perms.borrow_mut().tracked_insert(new_thread_ptr, thread_perm.get());
        }

        let mut endpoint_perm = Tracked(
            self.endpoint_perms.borrow_mut().tracked_remove(endpoint_ptr),
        );
        endpoint_add_ref(endpoint_ptr, &mut endpoint_perm, new_thread_ptr, 0);
        proof {
            self.endpoint_perms.borrow_mut().tracked_insert(endpoint_ptr, endpoint_perm.get());
        }

        proc_perms_update_subtree_set(
            &mut self.process_perms,
            Ghost(old_upper_tree_seq@.push(old_proc_ptr)),
            new_proc_ptr,
        );

        assert(forall|p_ptr: ProcPtr|
            #![auto]
            old(self).proc_dom().contains(p_ptr) && self.get_container(
                container_ptr,
            ).owned_procs@.contains(p_ptr) == false ==> self.get_proc(p_ptr) == old(self).get_proc(
                p_ptr,
            )) by {
            proc_tree_wf_imply_uppertree_subset_of_tree(
                old(self).get_container(container_ptr).root_process.unwrap(),
                old(self).get_container(container_ptr).owned_procs@.to_set(),
                old(self).process_perms@,
            );
            assert(forall|p_ptr: ProcPtr|
                #![auto]
                self.get_proc(page_ptr_1).uppertree_seq@.contains(p_ptr) ==> self.get_container(
                    container_ptr,
                ).owned_procs@.contains(p_ptr));
        };

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
            seq_push_lemma::<usize>();
            seq_push_unique_lemma::<usize>();
        };
        assert(self.process_trees_wf()) by {
            // seq_to_set_lemma::<ProcPtr>();
            seq_push_lemma::<usize>();
            seq_push_unique_lemma::<usize>();

            assert forall|c_ptr: ContainerPtr|
                #![trigger self.container_dom().contains(c_ptr)]
                #![trigger self.process_tree_wf(c_ptr)]
                self.container_dom().contains(c_ptr) && self.get_container(
                    c_ptr,
                ).root_process.is_Some() implies self.process_tree_wf(c_ptr) by {
                if c_ptr != container_ptr {
                    assert(forall|p_ptr: ProcPtr|
                        #![auto]
                        Ghost(old_upper_tree_seq@.push(old_proc_ptr))@.contains(p_ptr)
                            ==> self.get_container(c_ptr).owned_procs@.to_set().contains(p_ptr)
                            == false) by {
                        old(self).wf_imply_container_owned_proc_disjoint();
                        proc_tree_wf_imply_uppertree_subset_of_tree(
                            old(self).get_container(container_ptr).root_process.unwrap(),
                            old(self).get_container(container_ptr).owned_procs@.to_set(),
                            old(self).process_perms@,
                        );
                    };
                    process_no_change_to_tree_fields_imply_wf(
                        self.get_container(c_ptr).root_process.unwrap(),
                        self.get_container(c_ptr).owned_procs@.to_set(),
                        old(self).process_perms@,
                        self.process_perms@,
                    );
                    assert(self.process_tree_wf(c_ptr));
                } else {
                    proc_tree_wf_imply_uppertree_subset_of_tree(
                        old(self).get_container(container_ptr).root_process.unwrap(),
                        old(self).get_container(container_ptr).owned_procs@.to_set(),
                        old(self).process_perms@,
                    );

                    new_proc_preserve_tree_inv(
                        self.get_container(container_ptr).root_process.unwrap(),
                        old(self).get_container(container_ptr).owned_procs@.to_set(),
                        old(self).process_perms@,
                        self.process_perms@,
                        old_proc_ptr,
                        new_proc_ptr,
                    );
                    assert(self.get_container(container_ptr).owned_procs@.to_set() =~= old(
                        self,
                    ).get_container(container_ptr).owned_procs@.to_set().insert(new_proc_ptr));
                    assert(self.process_tree_wf(container_ptr));
                }
            };

        };
        assert(self.process_fields_wf()) by {};
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.container_perms_wf());
        assert(self.processes_container_wf()) by {
            seq_push_lemma::<usize>();
            seq_push_unique_lemma::<usize>();
        };
        assert(self.threads_process_wf()) by {
            seq_push_lemma::<usize>();
            seq_push_unique_lemma::<usize>();
        };
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf());
        assert(self.threads_endpoint_descriptors_wf());
        assert(self.endpoints_queue_wf());
        assert(self.endpoints_container_wf());
        assert(self.schedulers_wf()) by {
            seq_push_lemma::<usize>();
            seq_push_unique_lemma::<usize>();
        };
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf()) by {
            seq_push_lemma::<usize>();
            seq_push_unique_lemma::<usize>();
        };
    }
}

} // verus!

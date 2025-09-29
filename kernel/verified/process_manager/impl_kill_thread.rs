use vstd::prelude::*;

use crate::process_manager::endpoint;
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
use crate::process_manager::spec_util::*;

impl ProcessManager {
    pub fn kill_scheduled_thread(
        &mut self,
        thread_ptr: ThreadPtr,
    ) -> (ret: (PagePtr, Tracked<PagePerm4k>))
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            forall|edp_idx:EndpointIdx|
                #![auto]
                0 <= edp_idx < MAX_NUM_ENDPOINT_DESCRIPTORS 
                ==>
                old(self).get_thread(thread_ptr).endpoint_descriptors@[edp_idx as int].is_None(),
            old(self).get_thread(thread_ptr).state == ThreadState::SCHEDULED,
        ensures
            self.wf(),
            self.thread_dom() == old(self).thread_dom().remove(thread_ptr),
            threads_unchanged_except(*old(self), *self, set![]),
            self.proc_dom() == old(self).proc_dom(),
            process_tree_unchanged(*old(self), *self),
            self.container_dom() == old(self).container_dom(),
            containers_tree_unchanged(*old(self), *self),
            self.get_proc(old(self).get_thread(thread_ptr).owning_proc).owned_threads@ == 
              old(self).get_proc(old(self).get_thread(thread_ptr).owning_proc).owned_threads@.remove_value(thread_ptr),  
            self.get_proc(old(self).get_thread(thread_ptr).owning_proc).owned_threads.len() == 
              old(self).get_proc(old(self).get_thread(thread_ptr).owning_proc).owned_threads.len() - 1,  
            
            process_mem_unchanged(*old(self), *self),
            self.page_closure() =~= old(self).page_closure().remove(ret.0),
            old(self).page_closure().contains(ret.0),
            ret.0 == ret.1@.addr(),
            ret.1@.is_init(),
            old(self).container_dom().contains(ret.0) == false,
    {
        broadcast use ProcessManager::reveal_process_manager_wf;
        
        let proc_ptr = self.get_thread(thread_ptr).owning_proc;
        let proc_rev_ptr = self.get_thread(thread_ptr).proc_rev_ptr;

        let container_ptr = self.get_thread(thread_ptr).owning_container;
        let scheduler_rev_ptr = self.get_thread(thread_ptr).scheduler_rev_ptr.unwrap();
        
        let thread_perm = Tracked(self.thread_perms.borrow_mut().tracked_remove(thread_ptr));

        let mut proc_perm = Tracked(self.process_perms.borrow_mut().tracked_remove(proc_ptr));
        proc_remove_thread(proc_ptr, &mut proc_perm, proc_rev_ptr, Ghost(thread_ptr));
        proof{
            self.process_perms.borrow_mut().tracked_insert(proc_ptr, proc_perm.get());
        }

        let mut container_perm = Tracked(self.container_perms.borrow_mut().tracked_remove(container_ptr));
        scheduler_remove_thread(container_ptr, &mut container_perm, scheduler_rev_ptr, Ghost(thread_ptr));
        container_set_owned_threads(container_ptr, &mut container_perm, Ghost(
            old(self).get_container(container_ptr).owned_threads@.remove(thread_ptr)
        ));
        proof{
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
        assert(self.proc_perms_wf()) by {
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
        };
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.container_perms_wf());
        assert(self.processes_container_wf());
        assert(self.threads_process_wf()) by {
            seq_remove_lemma::<ThreadPtr>();
            seq_remove_lemma_2::<ThreadPtr>();
            old(self).proc_owned_threads_disjoint_inv();
            assert(self.proc_dom() =~= old(self).proc_dom());
            old(self).process_perms@[proc_ptr].value().owned_threads.unique_implys_no_duplicates();
            self.process_perms@[proc_ptr].value().owned_threads.unique_implys_no_duplicates();
        };
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf());
        assert(self.threads_endpoint_descriptors_wf());
        assert(self.endpoints_queue_wf());
        assert(self.endpoints_container_wf());
        assert(self.schedulers_wf())by {
            seq_remove_lemma::<ThreadPtr>();
            seq_remove_lemma_2::<ThreadPtr>();
            old(self).get_container(container_ptr).scheduler.unique_implys_no_duplicates();
            self.get_container(container_ptr).scheduler.unique_implys_no_duplicates();
        };
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf());

        thread_to_page(thread_ptr, thread_perm)
    }

    pub fn kill_running_thread(
        &mut self,
        thread_ptr: ThreadPtr,
    ) -> (ret: (PagePtr, Tracked<PagePerm4k>))
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            forall|edp_idx:EndpointIdx|
                #![auto]
                0 <= edp_idx < MAX_NUM_ENDPOINT_DESCRIPTORS 
                ==>
                old(self).get_thread(thread_ptr).endpoint_descriptors@[edp_idx as int].is_None(),
            old(self).get_thread(thread_ptr).state == ThreadState::RUNNING,
        ensures
            self.wf(),
            self.thread_dom() == old(self).thread_dom().remove(thread_ptr),
            threads_unchanged_except(*old(self), *self, set![]),
            self.proc_dom() == old(self).proc_dom(),
            process_tree_unchanged(*old(self), *self),
            self.container_dom() == old(self).container_dom(),
            containers_tree_unchanged(*old(self), *self),
            self.get_proc(old(self).get_thread(thread_ptr).owning_proc).owned_threads@ == 
              old(self).get_proc(old(self).get_thread(thread_ptr).owning_proc).owned_threads@.remove_value(thread_ptr),  
            self.get_proc(old(self).get_thread(thread_ptr).owning_proc).owned_threads.len() == 
              old(self).get_proc(old(self).get_thread(thread_ptr).owning_proc).owned_threads.len() - 1,  

            process_mem_unchanged(*old(self), *self),
            self.page_closure() =~= old(self).page_closure().remove(ret.0),
            old(self).page_closure().contains(ret.0),
            ret.0 == ret.1@.addr(),
            ret.1@.is_init(),
            old(self).container_dom().contains(ret.0) == false,
    {
        broadcast use ProcessManager::reveal_process_manager_wf;

        let proc_ptr = self.get_thread(thread_ptr).owning_proc;
        let proc_rev_ptr = self.get_thread(thread_ptr).proc_rev_ptr;

        let container_ptr = self.get_thread(thread_ptr).owning_container;
        
        let cpu_id = self.get_thread(thread_ptr).running_cpu.unwrap();
        let old_cpu = *self.cpu_list.get(cpu_id);

        let thread_perm = Tracked(self.thread_perms.borrow_mut().tracked_remove(thread_ptr));

        let mut proc_perm = Tracked(self.process_perms.borrow_mut().tracked_remove(proc_ptr));
        proc_remove_thread(proc_ptr, &mut proc_perm, proc_rev_ptr, Ghost(thread_ptr));
        proof{
            self.process_perms.borrow_mut().tracked_insert(proc_ptr, proc_perm.get());
        }

        let mut container_perm = Tracked(self.container_perms.borrow_mut().tracked_remove(container_ptr));
        container_set_owned_threads(container_ptr, &mut container_perm, Ghost(
            old(self).get_container(container_ptr).owned_threads@.remove(thread_ptr)
        ));
        proof{
            self.container_perms.borrow_mut().tracked_insert(container_ptr, container_perm.get());
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
        assert(self.proc_perms_wf()) by {
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
        };
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.container_perms_wf());
        assert(self.processes_container_wf());
        assert(self.threads_process_wf()) by {
            seq_remove_lemma::<ThreadPtr>();
            seq_remove_lemma_2::<ThreadPtr>();
            old(self).proc_owned_threads_disjoint_inv();
            assert(self.proc_dom() =~= old(self).proc_dom());
            old(self).process_perms@[proc_ptr].value().owned_threads.unique_implys_no_duplicates();
            self.process_perms@[proc_ptr].value().owned_threads.unique_implys_no_duplicates();
        };
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf());
        assert(self.threads_endpoint_descriptors_wf());
        assert(self.endpoints_queue_wf());
        assert(self.endpoints_container_wf());
        assert(self.schedulers_wf())by {
        };
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf());

        thread_to_page(thread_ptr, thread_perm)
    }

    pub fn kill_blocked_thread(
        &mut self,
        thread_ptr: ThreadPtr,
    ) -> (ret: ((PagePtr, Tracked<PagePerm4k>), Option<(PagePtr, Tracked<PagePerm4k>)>))
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            old(self).get_thread(thread_ptr).state == ThreadState::BLOCKED,
            old(self).get_thread(thread_ptr).blocking_endpoint_index.is_Some(),
            forall|edp_idx:EndpointIdx|
                #![auto]
                0 <= edp_idx < MAX_NUM_ENDPOINT_DESCRIPTORS 
                ==>
                old(self).get_thread(thread_ptr).blocking_endpoint_index == Some(edp_idx)
                ||
                old(self).get_thread(thread_ptr).endpoint_descriptors@[edp_idx as int].is_None(),
        ensures
            self.wf(),
            self.thread_dom() == old(self).thread_dom().remove(thread_ptr),
            threads_unchanged_except(*old(self), *self, set![]),
            self.proc_dom() == old(self).proc_dom(),
            process_tree_unchanged(*old(self), *self),
            self.container_dom() == old(self).container_dom(),
            containers_tree_unchanged(*old(self), *self),
            self.get_proc(old(self).get_thread(thread_ptr).owning_proc).owned_threads@ == 
              old(self).get_proc(old(self).get_thread(thread_ptr).owning_proc).owned_threads@.remove_value(thread_ptr), 
            self.get_proc(old(self).get_thread(thread_ptr).owning_proc).owned_threads.len() == 
              old(self).get_proc(old(self).get_thread(thread_ptr).owning_proc).owned_threads.len() - 1,  

                        
            process_mem_unchanged(*old(self), *self),
            ret.1.is_Some() ==> {
                &&& self.page_closure() =~= old(self).page_closure().remove(ret.0.0).remove(ret.1.unwrap().0)
                &&& old(self).page_closure().contains(ret.0.0)
                &&& ret.0.0 == ret.0.1@.addr()
                &&& ret.0.1@.is_init()
                &&& old(self).container_dom().contains(ret.0.0) == false
                &&& old(self).page_closure().contains(ret.1.unwrap().0)
                &&& ret.1.unwrap().0 == ret.1.unwrap().1@.addr()
                &&& ret.1.unwrap().1@.is_init()
                &&& old(self).container_dom().contains(ret.1.unwrap().0) == false
                &&& ret.0.0 != ret.1.unwrap().0
            },
            ret.1.is_None() ==> {
                &&& self.page_closure() =~= old(self).page_closure().remove(ret.0.0)
                &&& old(self).page_closure().contains(ret.0.0)
                &&& ret.0.0 == ret.0.1@.addr()
                &&& ret.0.1@.is_init()
                &&& old(self).container_dom().contains(ret.0.0) == false
            },
    {
        broadcast use ProcessManager::reveal_process_manager_wf;

        let proc_ptr = self.get_thread(thread_ptr).owning_proc;
        let proc_rev_ptr = self.get_thread(thread_ptr).proc_rev_ptr;

        let container_ptr = self.get_thread(thread_ptr).owning_container;
        
        let edp_idx = self.get_thread(thread_ptr).blocking_endpoint_index.unwrap();
        let endpoint_ptr = self.get_thread(thread_ptr).blocking_endpoint_ptr.unwrap();
        let endpoint_rev_ptr = self.get_thread(thread_ptr).endpoint_rev_ptr.unwrap();
        let old_rf_counter = 
            self.get_endpoint(endpoint_ptr).rf_counter;
        let endpoint_owning_container = 
            self.get_endpoint(endpoint_ptr).owning_container;

        let thread_perm = Tracked(self.thread_perms.borrow_mut().tracked_remove(thread_ptr));

        let ret_0 = thread_to_page(thread_ptr, thread_perm);

        let mut proc_perm = Tracked(self.process_perms.borrow_mut().tracked_remove(proc_ptr));
        proc_remove_thread(proc_ptr, &mut proc_perm, proc_rev_ptr, Ghost(thread_ptr));
        proof{
            self.process_perms.borrow_mut().tracked_insert(proc_ptr, proc_perm.get());
        }

        let mut container_perm = Tracked(self.container_perms.borrow_mut().tracked_remove(container_ptr));
        container_set_owned_threads(container_ptr, &mut container_perm, Ghost(
            old(self).get_container(container_ptr).owned_threads@.remove(thread_ptr)
        ));
        proof{
            self.container_perms.borrow_mut().tracked_insert(container_ptr, container_perm.get());
        }

        let mut endpoint_perm = Tracked(
            self.endpoint_perms.borrow_mut().tracked_remove(endpoint_ptr),
        );

        endpoint_remove_thread(endpoint_ptr, &mut endpoint_perm, endpoint_rev_ptr, Ghost(thread_ptr));
        endpoint_remove_ref(endpoint_ptr, &mut endpoint_perm, thread_ptr, edp_idx);

        if old_rf_counter == 1 {
            let ret = endpoint_to_page(endpoint_ptr, endpoint_perm);
            let mut container_perm = Tracked(self.container_perms.borrow_mut().tracked_remove(endpoint_owning_container));
            container_pop_endpoint(endpoint_owning_container, &mut container_perm, endpoint_ptr);
            proof {
                self.container_perms.borrow_mut().tracked_insert(endpoint_owning_container, container_perm.get());
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
            };
            assert(self.cpus_wf());
            assert(self.container_cpu_wf());
            assert(self.memory_disjoint());
            assert(self.container_perms_wf());
            assert(self.processes_container_wf());
            assert(self.threads_process_wf()) by {
                seq_remove_lemma::<ThreadPtr>();
                seq_remove_lemma_2::<ThreadPtr>();
                old(self).proc_owned_threads_disjoint_inv();
                assert(self.proc_dom() =~= old(self).proc_dom());
                old(self).process_perms@[proc_ptr].value().owned_threads.unique_implys_no_duplicates();
                self.process_perms@[proc_ptr].value().owned_threads.unique_implys_no_duplicates();
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
            };
            return (ret_0, Some(ret));
        }else{
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
            };
            assert(self.cpus_wf());
            assert(self.container_cpu_wf());
            assert(self.memory_disjoint());
            assert(self.container_perms_wf());
            assert(self.processes_container_wf());
            assert(self.threads_process_wf()) by {
                seq_remove_lemma::<ThreadPtr>();
                seq_remove_lemma_2::<ThreadPtr>();
                old(self).proc_owned_threads_disjoint_inv();
                assert(self.proc_dom() =~= old(self).proc_dom());
                old(self).process_perms@[proc_ptr].value().owned_threads.unique_implys_no_duplicates();
                self.process_perms@[proc_ptr].value().owned_threads.unique_implys_no_duplicates();
            };
            assert(self.threads_perms_wf());
            assert(self.endpoint_perms_wf());
            assert(self.threads_endpoint_descriptors_wf());
            assert(self.endpoints_queue_wf()) by {
                // assume(false);
                // seq_remove_lemma::<ThreadPtr>();
                seq_remove_lemma_2::<ThreadPtr>();
                old(self).endpoint_perms@[endpoint_ptr].value().queue.unique_implys_no_duplicates();
                // self.endpoint_perms@[endpoint_ptr].value().queue.unique_implys_no_duplicates();
                assert(
                forall|t_ptr: ThreadPtr|
                #![trigger self.thread_perms@[t_ptr].value()]
                self.thread_perms@.dom().contains(t_ptr) && self.thread_perms@[t_ptr].value().state == ThreadState::BLOCKED
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
                    && self.endpoint_perms@[self.thread_perms@[t_ptr].value().blocking_endpoint_ptr.unwrap()].value().queue@.contains(t_ptr)
                    && self.endpoint_perms@[self.thread_perms@[t_ptr].value().blocking_endpoint_ptr.unwrap()].value().queue.get_node_ref(t_ptr) == self.thread_perms@[t_ptr].value().endpoint_rev_ptr.unwrap()
                );

            };
            assert(self.endpoints_container_wf());
            assert(self.schedulers_wf());
            assert(self.pcid_ioid_wf());
            assert(self.threads_cpu_wf());
            assert(self.threads_container_wf());
            (ret_0,None)
        }
    }
}

} // verus!

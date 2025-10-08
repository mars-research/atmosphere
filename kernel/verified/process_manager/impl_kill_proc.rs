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
use crate::process_manager::spec_util::*;

impl ProcessManager {
    pub fn kill_process_none_root(
        &mut self,
        proc_ptr: ProcPtr,
    ) -> (ret: (PagePtr, Tracked<PagePerm4k>))
        requires
            old(self).wf(),
            old(self).proc_dom().contains(proc_ptr),
            old(self).get_proc(proc_ptr).owned_threads@ == Seq::<ThreadPtr>::empty(),
            old(self).get_proc(proc_ptr).children@ == Seq::<ProcPtr>::empty(),
            old(self).get_proc(proc_ptr).depth != 0,
        ensures
            self.wf(),
            self.container_dom() == old(self).container_dom(),
            containers_tree_unchanged(*old(self), *self),
            self.proc_dom() == old(self).proc_dom().remove(proc_ptr),
            processes_fields_unchanged(*old(self), *self),
            self.thread_dom() == old(self).thread_dom(),
            threads_unchanged(*old(self), *self),
            self.page_closure() =~= old(self).page_closure().remove(ret.0),
            old(self).page_closure().contains(ret.0),
            ret.0 == ret.1@.addr(),
            ret.1@.is_init(),
            old(self).container_dom().contains(ret.0) == false,
            self.get_proc(old(self).get_proc(proc_ptr).parent.unwrap()).children@ =~= 
                old(self).get_proc(old(self).get_proc(proc_ptr).parent.unwrap()).children@.remove_value(proc_ptr),
            self.get_proc(old(self).get_proc(proc_ptr).parent.unwrap()).children.len() == 
                old(self).get_proc(old(self).get_proc(proc_ptr).parent.unwrap()).children.len() - 1,
            forall|p_ptr:ProcPtr| #![auto] self.proc_dom().contains(p_ptr) && p_ptr != old(self).get_proc(proc_ptr).parent.unwrap()
                ==>
                self.get_proc(p_ptr).children == old(self).get_proc(p_ptr).children,
    {
        broadcast use ProcessManager::reveal_process_manager_wf;

        let container_ptr = self.get_proc(proc_ptr).owning_container;
        let container_rev_ptr = self.get_proc(proc_ptr).rev_ptr;
        proof {
            proc_tree_wf_imply_childern_has_parent(
                old(self).get_container(container_ptr).root_process.unwrap(),
                old(self).get_container(container_ptr).owned_procs@.to_set(),
                old(self).process_perms@,
            );
        }
        let parent_proc_ptr = self.get_proc(proc_ptr).parent.unwrap();
        let parent_rev_ptr = self.get_proc(proc_ptr).parent_rev_ptr.unwrap();

        let upper_tree_seq = self.get_proc(proc_ptr).uppertree_seq;

        let mut container_perm = Tracked(self.container_perms.borrow_mut().tracked_remove(container_ptr));
        container_remove_proc(container_ptr, &mut container_perm, container_rev_ptr, Ghost(proc_ptr));
        proof{
            self.container_perms.borrow_mut().tracked_insert(container_ptr, container_perm.get());
        }

        proc_perms_remove_subtree_set(
            &mut self.process_perms,
            upper_tree_seq,
            proc_ptr,
        );

        let proc_perm = Tracked(self.process_perms.borrow_mut().tracked_remove(proc_ptr));

        let mut parent_proc_perm = Tracked(self.process_perms.borrow_mut().tracked_remove(parent_proc_ptr));
        proc_remove_child(parent_proc_ptr, &mut parent_proc_perm, parent_rev_ptr, Ghost(proc_ptr));
        proof{
            self.process_perms.borrow_mut().tracked_insert(parent_proc_ptr, parent_proc_perm.get());
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
            seq_remove_lemma::<ProcPtr>();
            seq_remove_lemma_2::<ProcPtr>();
            old(self).process_perms@[parent_proc_ptr].value().children.unique_implys_no_duplicates();
        };
        assert(self.process_trees_wf()) by {
            // seq_to_set_lemma::<ProcPtr>();
            assert forall|c_ptr: ContainerPtr|
                #![trigger self.container_dom().contains(c_ptr)]
                #![trigger self.process_tree_wf(c_ptr)]
                self.container_dom().contains(c_ptr) && self.get_container(
                    c_ptr,
                ).root_process.is_Some() implies 
                self.process_tree_wf(c_ptr) by {
                    if c_ptr != container_ptr {
                    assert(forall|p_ptr: ProcPtr|
                        #![auto]
                        upper_tree_seq@.contains(p_ptr)
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
                    seq_remove_lemma::<ProcPtr>();
                    seq_remove_lemma_2::<ProcPtr>();
                    old(self).container_perms@[container_ptr].value().owned_procs.unique_implys_no_duplicates();
                    proc_tree_wf_imply_uppertree_subset_of_tree(
                        old(self).get_container(container_ptr).root_process.unwrap(),
                        old(self).get_container(container_ptr).owned_procs@.to_set(),
                        old(self).process_perms@,
                    );
                    

                    assert(old(self).get_proc(proc_ptr).uppertree_seq@.contains(proc_ptr) == false) by {
                        proc_tree_wf_imply_uppertree_contains_no_self(
                            old(self).get_container(container_ptr).root_process.unwrap(),
                            old(self).get_container(container_ptr).owned_procs@.to_set(),
                            old(self).process_perms@,
                            proc_ptr,
                        );
                    }

                    remove_proc_preserve_tree_inv(
                        self.get_container(container_ptr).root_process.unwrap(),
                        old(self).get_container(container_ptr).owned_procs@.to_set(),
                        old(self).process_perms@,
                        self.process_perms@,
                        proc_ptr,
                    );
                    assert(self.get_container(container_ptr).owned_procs@.to_set() =~= old(
                        self,
                    ).get_container(container_ptr).owned_procs@.to_set().remove(proc_ptr));
                    assert(self.process_tree_wf(container_ptr));
                }
                };
        };
        assert(self.process_fields_wf()) by {
        };
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.container_perms_wf());
        assert(self.processes_container_wf()) by {
            seq_remove_lemma::<ProcPtr>();
            seq_remove_lemma_2::<ProcPtr>();
            old(self).container_perms@[container_ptr].value().owned_procs.unique_implys_no_duplicates();
        };
        assert(self.threads_process_wf()) by {
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

        proc_to_page(proc_ptr, proc_perm)
    }


    pub fn kill_process_root(
        &mut self,
        proc_ptr: ProcPtr,
    ) -> (ret: (PagePtr, Tracked<PagePerm4k>))
        requires
            old(self).wf(),
            old(self).proc_dom().contains(proc_ptr),
            old(self).get_proc(proc_ptr).owned_threads@ == Seq::<ThreadPtr>::empty(),
            old(self).get_proc(proc_ptr).children@ == Seq::<ProcPtr>::empty(),
            old(self).get_container(old(self).get_proc(proc_ptr).owning_container).root_process == Some(proc_ptr),
        ensures
            self.wf(),
            self.container_dom() == old(self).container_dom(),
            containers_tree_unchanged(*old(self), *self),
            self.proc_dom() == old(self).proc_dom().remove(proc_ptr),
            processes_fields_unchanged(*old(self), *self),
            self.thread_dom() == old(self).thread_dom(),
            threads_unchanged(*old(self), *self),
            self.page_closure() =~= old(self).page_closure().remove(ret.0),
            old(self).page_closure().contains(ret.0),
            ret.0 == ret.1@.addr(),
            ret.1@.is_init(),
            old(self).container_dom().contains(ret.0) == false,
            self.get_proc(old(self).get_proc(proc_ptr).parent.unwrap()).children@ =~= 
                old(self).get_proc(old(self).get_proc(proc_ptr).parent.unwrap()).children@.remove_value(proc_ptr),
            self.get_proc(old(self).get_proc(proc_ptr).parent.unwrap()).children.len() == 
                old(self).get_proc(old(self).get_proc(proc_ptr).parent.unwrap()).children.len() - 1,
    {
        broadcast use ProcessManager::reveal_process_manager_wf;

        let container_ptr = self.get_proc(proc_ptr).owning_container;
        let container_rev_ptr = self.get_proc(proc_ptr).rev_ptr;
        proof{
            proc_tree_wf_imply_root_with_no_child_has_empty_dom(
                self.get_container(container_ptr).root_process.unwrap(),
                self.get_container(container_ptr).owned_procs@.to_set(),
                old(self).process_perms@,
            );
        }
       
        assert(self.get_container(container_ptr).owned_procs@.to_set().len() == 1);
        assume(self.get_container(container_ptr).owned_procs@.len() == 1);
        // by {
        //     old(self).container_perms@[container_ptr].value().owned_procs.unique_implys_no_duplicates();
        // };

        let mut container_perm = Tracked(self.container_perms.borrow_mut().tracked_remove(container_ptr));
        container_remove_proc(container_ptr, &mut container_perm, container_rev_ptr, Ghost(proc_ptr));
        container_set_root_proc(container_ptr, &mut container_perm, None);
        proof{
            self.container_perms.borrow_mut().tracked_insert(container_ptr, container_perm.get());
        }

        let proc_perm = Tracked(self.process_perms.borrow_mut().tracked_remove(proc_ptr));


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
        assert(self.get_container(container_ptr).owned_procs@.len() == 0);
        assert(self.process_trees_wf()) by {
            // seq_to_set_lemma::<ProcPtr>();
            assert forall|c_ptr: ContainerPtr|
                #![trigger self.container_dom().contains(c_ptr)]
                #![trigger self.process_tree_wf(c_ptr)]
                self.container_dom().contains(c_ptr) && self.get_container(
                    c_ptr,
                ).root_process.is_Some() implies 
                self.process_tree_wf(c_ptr) by {
                    if c_ptr != container_ptr {
                    old(self).wf_imply_container_owned_proc_disjoint();
                    process_no_change_to_tree_fields_imply_wf(
                        self.get_container(c_ptr).root_process.unwrap(),
                        self.get_container(c_ptr).owned_procs@.to_set(),
                        old(self).process_perms@,
                        self.process_perms@,
                    );
                    assert(self.process_tree_wf(c_ptr));
                } else {
                }
                };
        };
        assert(self.process_fields_wf()) by {
        };
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.container_perms_wf());
        assert(self.processes_container_wf()) by {
            seq_remove_lemma::<ProcPtr>();
            seq_remove_lemma_2::<ProcPtr>();
            old(self).container_perms@[container_ptr].value().owned_procs.unique_implys_no_duplicates();
        };
        assert(self.threads_process_wf()) by {
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

        proc_to_page(proc_ptr, proc_perm)
    }
}

} // verus!

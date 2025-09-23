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
    pub fn kill_container_none_root(
        &mut self,
        container_ptr: ContainerPtr,
    ) -> (ret: (PagePtr, Tracked<PagePerm4k>))
        requires
            old(self).wf(),
            old(self).container_dom().contains(container_ptr),
            old(self).get_container(container_ptr).owned_cpus@ == Set::<CpuId>::empty(),
            old(self).get_container(container_ptr).owned_procs@ == Seq::<ThreadPtr>::empty(),
            old(self).get_container(container_ptr).children@ == Seq::<ContainerPtr>::empty(),
            // old(self).get_container(container_ptr).owned_endpoints@ == Set::<EndpointPtr>::empty(),
            old(self).get_container(container_ptr).depth != 0,
            old(self).root_container != container_ptr,
        ensures
            // self.wf(),
    {
        broadcast use ProcessManager::reveal_process_manager_wf;

        proof{
            container_tree_wf_imply_childern_have_parent(
                self.root_container,
                self.container_perms@,
            );
        }

        assert(old(self).get_container(container_ptr).owned_threads@ == Set::<ThreadPtr>::empty()) by {
            old(self).wf_imply_container_no_proc_to_no_thread(container_ptr);
        };
        assume(old(self).get_container(container_ptr).owned_endpoints@ == Set::<EndpointPtr>::empty());
        let parent_container_ptr = self.get_container(container_ptr).parent.unwrap();
        let parent_rev_ptr = self.get_container(container_ptr).parent_rev_ptr.unwrap();
        let uppertree_seq = self.get_container(container_ptr).uppertree_seq;
        container_perms_subset_remove(
            &mut self.container_perms,
            uppertree_seq,
            container_ptr,
        );
        let mut container_perm = Tracked(self.container_perms.borrow_mut().tracked_remove(container_ptr));

        let mut parent_container_perm = Tracked(self.container_perms.borrow_mut().tracked_remove(parent_container_ptr));
        container_remove_child(parent_container_ptr, &mut parent_container_perm, parent_rev_ptr, Ghost(container_ptr));
        proof {
            self.container_perms.borrow_mut().tracked_insert(parent_container_ptr, parent_container_perm.get());
        }

        assert(self.container_perms_wf()) by {
            seq_remove_lemma::<ContainerPtr>();
            seq_remove_lemma_2::<ContainerPtr>();
            container_childern_disjoint_inv(self.root_container, old(self).container_perms@, parent_container_ptr);
            old(self).container_perms@[parent_container_ptr].value().children.unique_implys_no_duplicates();
        };
        assert(self.container_tree_wf()) by {
            seq_remove_lemma::<ContainerPtr>();
            seq_remove_lemma_2::<ContainerPtr>();
            assume(old(self).get_container(container_ptr).uppertree_seq@.contains(container_ptr) == false);
            assume(forall|c_ptr:ContainerPtr| #![auto] old(self).get_container(container_ptr).uppertree_seq@.contains(c_ptr)
                    ==>
                    old(self).container_dom().contains(c_ptr)
                    &&
                    self.container_dom().contains(c_ptr)
                );
            assert(old(self).get_container(container_ptr).uppertree_seq@.contains(container_ptr) == false) by {
                        // proc_tree_wf_imply_uppertree_contains_no_self(
                        //     old(self).get_container(container_ptr).root_process.unwrap(),
                        //     old(self).get_container(container_ptr).owned_procs@.to_set(),
                        //     old(self).process_perms@,
                        //     proc_ptr,
                        // );
                    };
            remove_container_preserve_tree_inv(
                self.root_container,
                old(self).container_perms@,
                self.container_perms@,
                container_ptr,
            );
        };
        assert(self.container_fields_wf());
        assert(self.proc_perms_wf()) by {
        };
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
        };
        assert(self.cpus_wf());
        assert(self.container_cpu_wf()) by {
        };
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

        container_to_page(container_ptr, container_perm)
    }
}

} // verus!

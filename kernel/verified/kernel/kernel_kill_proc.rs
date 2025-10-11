use vstd::prelude::*;
verus! {
use crate::define::*;
use crate::kernel::Kernel;
use crate::va_range::*;
use crate::process_manager::spec_util::*;
use crate::process_manager::spec_proof::*;

use vstd::set::group_set_axioms;
use vstd::set_lib::*;
use vstd::seq_lib::*;
use crate::lemma::lemma_t::*;
use crate::lemma::lemma_u::*;

impl Kernel {
    pub fn helper_kernel_kill_proc_non_root(&mut self, proc_ptr:ProcPtr)
        requires
            old(self).wf(),
            old(self).proc_dom().contains(proc_ptr),
            old(self).get_proc(proc_ptr).ioid.is_None(),
            old(self).mem_man.get_pagetable_by_pcid(old(self).get_proc(proc_ptr).pcid).unwrap().is_empty(),
            old(self).get_proc(proc_ptr).owned_threads@ == Seq::<ThreadPtr>::empty(),
            old(self).get_proc(proc_ptr).children@ == Seq::<ProcPtr>::empty(),
            old(self).get_proc(proc_ptr).depth != 0,
        ensures
            self.wf(),
            self.thread_dom() == old(self).thread_dom(),
            threads_unchanged_except(old(self).proc_man, self.proc_man, set![]),
            self.proc_dom() == old(self).proc_dom().remove(proc_ptr),
            processes_fields_unchanged(old(self).proc_man, self.proc_man),
            self.container_dom() == old(self).container_dom(),
            containers_tree_unchanged(old(self).proc_man, self.proc_man),
            self.get_proc(old(self).get_proc(proc_ptr).parent.unwrap()).children@ =~= 
                old(self).get_proc(old(self).get_proc(proc_ptr).parent.unwrap()).children@.remove_value(proc_ptr),
            self.get_proc(old(self).get_proc(proc_ptr).parent.unwrap()).children.len() == 
                old(self).get_proc(old(self).get_proc(proc_ptr).parent.unwrap()).children.len() - 1,
            forall|p_ptr:ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) 
                ==>
                old(self).mem_man.get_pagetable_by_pcid(old(self).get_proc(p_ptr).pcid)
                    ==
                self.mem_man.get_pagetable_by_pcid(self.get_proc(p_ptr).pcid),
            forall|p_ptr:ProcPtr| #![auto]  self.proc_dom().contains(p_ptr) && p_ptr != old(self).get_proc(proc_ptr).parent.unwrap()
                ==>
                self.get_proc(p_ptr).children == old(self).get_proc(p_ptr).children, 
            forall|p_p_ptr:ProcPtr|
                #![trigger self.get_proc(p_p_ptr)]
                old(self).get_proc(proc_ptr).uppertree_seq@.contains(p_p_ptr) 
                ==>
                self.get_proc(p_p_ptr).subtree_set@ =~= 
                    old(self).get_proc(p_p_ptr).subtree_set@.remove(proc_ptr),     
            forall|p_ptr:ProcPtr|  #![auto] self.proc_dom().contains(p_ptr)
                ==>
                self.get_proc(p_ptr).uppertree_seq == old(self).get_proc(p_ptr).uppertree_seq,     
    {
        let pcid = self.proc_man.get_proc(proc_ptr).pcid;
        let (page_ptr, page_perm) = self.proc_man.kill_process_none_root(proc_ptr);
        self.page_alloc.free_page_4k(page_ptr, page_perm);
        self.mem_man.free_page_table(proc_ptr, pcid);
        assert(self.memory_wf()) by {
            assert(self.mem_man.page_closure() + self.proc_man.page_closure()
            == self.page_alloc.allocated_pages_4k());
        assert(self.page_alloc.mapped_pages_2m() =~= Set::empty());
        assert(self.page_alloc.mapped_pages_1g() =~= Set::empty());
        assert(self.page_alloc.allocated_pages_2m() =~= Set::empty());
        assert(self.page_alloc.allocated_pages_1g() =~= Set::empty());
        assert(self.page_alloc.container_map_4k@.dom() =~= self.proc_man.container_dom());
        assert(self.page_alloc.container_map_2m@.dom() =~= self.proc_man.container_dom());
        assert(self.page_alloc.container_map_1g@.dom() =~= self.proc_man.container_dom());
        };
        assert(self.page_mapping_wf()) by {
            assert( self.page_mapping@.dom().subset_of(self.page_alloc.mapped_pages_4k()));
            assert( self.page_io_mapping@.dom().subset_of(self.page_alloc.mapped_pages_4k()));
        assert( forall|page_ptr: PagePtr, p_ptr: ProcPtr, va: VAddr|
            #![trigger self.page_mapping@[page_ptr].contains((p_ptr, va))]
            #![trigger self.page_alloc.page_mappings(page_ptr).contains((self.proc_man.get_proc(p_ptr).pcid, va))]
            self.page_mapping@.dom().contains(page_ptr) && self.page_mapping@[page_ptr].contains(
                (p_ptr, va),
            ) ==> self.page_alloc.page_is_mapped(page_ptr) && self.proc_man.proc_dom().contains(
                p_ptr,
            ) && self.page_alloc.page_mappings(page_ptr).contains(
                (self.proc_man.get_proc(p_ptr).pcid, va),
            ));
        assert( forall|page_ptr: PagePtr, pcid: Pcid, va: VAddr|
            #![trigger self.page_alloc.page_mappings(page_ptr).contains((pcid, va))]
            #![trigger self.page_mapping@[page_ptr].contains((self.mem_man.pcid_to_proc_ptr(pcid), va))]
            self.page_alloc.page_is_mapped(page_ptr) && self.page_alloc.page_mappings(
                page_ptr,
            ).contains((pcid, va)) ==> self.page_mapping@.dom().contains(page_ptr)
                && self.page_mapping@[page_ptr].contains((self.mem_man.pcid_to_proc_ptr(pcid), va)));
        };
        assert(self.mapping_wf());
        assert(self.pcid_ioid_wf());
    }

    pub fn helper_kernel_kill_proc_root(&mut self, proc_ptr:ProcPtr)
        requires
            old(self).wf(),
            old(self).proc_dom().contains(proc_ptr),
            old(self).get_proc(proc_ptr).ioid.is_None(),
            old(self).mem_man.get_pagetable_by_pcid(old(self).get_proc(proc_ptr).pcid).unwrap().is_empty(),
            old(self).get_proc(proc_ptr).owned_threads@ == Seq::<ThreadPtr>::empty(),
            old(self).get_proc(proc_ptr).children@ == Seq::<ProcPtr>::empty(),
            old(self).get_proc(proc_ptr).depth == 0,
        ensures
            self.wf(),
            self.thread_dom() == old(self).thread_dom(),
            threads_unchanged_except(old(self).proc_man, self.proc_man, set![]),
            self.proc_dom() == old(self).proc_dom().remove(proc_ptr),
            processes_fields_unchanged(old(self).proc_man, self.proc_man),
            self.container_dom() == old(self).container_dom(),
            containers_tree_unchanged(old(self).proc_man, self.proc_man),
            forall|p_ptr:ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) 
                ==>
                old(self).mem_man.get_pagetable_by_pcid(old(self).get_proc(p_ptr).pcid)
                    ==
                self.mem_man.get_pagetable_by_pcid(self.get_proc(p_ptr).pcid),
            forall|p_ptr:ProcPtr| #![auto]  self.proc_dom().contains(p_ptr)
                ==>
                self.get_proc(p_ptr).children == old(self).get_proc(p_ptr).children, 
            forall|p_p_ptr:ProcPtr|
                #![trigger self.get_proc(p_p_ptr)]
                old(self).get_proc(proc_ptr).uppertree_seq@.contains(p_p_ptr) 
                ==>
                self.get_proc(p_p_ptr).subtree_set@ =~= 
                    old(self).get_proc(p_p_ptr).subtree_set@.remove(proc_ptr),     
            forall|p_ptr:ProcPtr|  #![auto] self.proc_dom().contains(p_ptr)
                ==>
                self.get_proc(p_ptr).uppertree_seq == old(self).get_proc(p_ptr).uppertree_seq,  
                
    {
        let pcid = self.proc_man.get_proc(proc_ptr).pcid;
        let (page_ptr, page_perm) = self.proc_man.kill_process_root(proc_ptr);
        self.page_alloc.free_page_4k(page_ptr, page_perm);
        self.mem_man.free_page_table(proc_ptr, pcid);
        assert(self.memory_wf()) by {
            assert(self.mem_man.page_closure() + self.proc_man.page_closure()
            == self.page_alloc.allocated_pages_4k());
        assert(self.page_alloc.mapped_pages_2m() =~= Set::empty());
        assert(self.page_alloc.mapped_pages_1g() =~= Set::empty());
        assert(self.page_alloc.allocated_pages_2m() =~= Set::empty());
        assert(self.page_alloc.allocated_pages_1g() =~= Set::empty());
        assert(self.page_alloc.container_map_4k@.dom() =~= self.proc_man.container_dom());
        assert(self.page_alloc.container_map_2m@.dom() =~= self.proc_man.container_dom());
        assert(self.page_alloc.container_map_1g@.dom() =~= self.proc_man.container_dom());
        };
        assert(self.page_mapping_wf()) by {
            assert( self.page_mapping@.dom().subset_of(self.page_alloc.mapped_pages_4k()));
            assert( self.page_io_mapping@.dom().subset_of(self.page_alloc.mapped_pages_4k()));
        assert( forall|page_ptr: PagePtr, p_ptr: ProcPtr, va: VAddr|
            #![trigger self.page_mapping@[page_ptr].contains((p_ptr, va))]
            #![trigger self.page_alloc.page_mappings(page_ptr).contains((self.proc_man.get_proc(p_ptr).pcid, va))]
            self.page_mapping@.dom().contains(page_ptr) && self.page_mapping@[page_ptr].contains(
                (p_ptr, va),
            ) ==> self.page_alloc.page_is_mapped(page_ptr) && self.proc_man.proc_dom().contains(
                p_ptr,
            ) && self.page_alloc.page_mappings(page_ptr).contains(
                (self.proc_man.get_proc(p_ptr).pcid, va),
            ));
        assert( forall|page_ptr: PagePtr, pcid: Pcid, va: VAddr|
            #![trigger self.page_alloc.page_mappings(page_ptr).contains((pcid, va))]
            #![trigger self.page_mapping@[page_ptr].contains((self.mem_man.pcid_to_proc_ptr(pcid), va))]
            self.page_alloc.page_is_mapped(page_ptr) && self.page_alloc.page_mappings(
                page_ptr,
            ).contains((pcid, va)) ==> self.page_mapping@.dom().contains(page_ptr)
                && self.page_mapping@[page_ptr].contains((self.mem_man.pcid_to_proc_ptr(pcid), va)));
        };
        assert(self.mapping_wf());
        assert(self.pcid_ioid_wf());
    }

    // #[verifier::exec_allows_no_decreases_clause]
    pub fn kernel_kill_proc_recursive_non_root(&mut self, proc_ptr:ProcPtr, current_depth: Ghost<int>) -> (ret: Ghost<Set<ProcPtr>>)
        requires
            old(self).wf(),
            old(self).proc_dom().contains(proc_ptr),
            old(self).get_proc(proc_ptr).ioid.is_None(),
            old(self).mem_man.get_pagetable_by_pcid(old(self).get_proc(proc_ptr).pcid).unwrap().is_empty(),
            old(self).get_proc(proc_ptr).owned_threads@ == Seq::<ThreadPtr>::empty(),
            forall|s_p_ptr: ProcPtr|
                #![trigger old(self).get_proc(s_p_ptr)]
                #![trigger old(self).proc_dom().contains(s_p_ptr)]
                old(self).get_proc(proc_ptr).subtree_set@.contains(s_p_ptr) 
                ==>
                old(self).proc_dom().contains(s_p_ptr)
                && old(self).get_proc(s_p_ptr).ioid.is_None()
                && old(self).mem_man.get_pagetable_by_pcid(old(self).get_proc(s_p_ptr).pcid).unwrap().is_empty()
                && old(self).get_proc(s_p_ptr).owned_threads@ == Seq::<ThreadPtr>::empty(),
            current_depth@ == usize::MAX - old(self).get_proc(proc_ptr).depth,
        ensures
            self.wf(),
            ret@ == old(self).get_proc(proc_ptr).subtree_set@.insert(proc_ptr),
            self.proc_dom() =~= old(self).proc_dom().remove(proc_ptr) - old(self).get_proc(proc_ptr).subtree_set@,
            processes_fields_unchanged(old(self).proc_man, self.proc_man),
            old(self).get_proc(proc_ptr).depth != 0 ==> {
                self.get_proc(old(self).get_proc(proc_ptr).parent.unwrap()).children.len() == 
                    old(self).get_proc(old(self).get_proc(proc_ptr).parent.unwrap()).children.len() - 1
            },
            old(self).get_proc(proc_ptr).depth != 0 ==> {
                forall|p_ptr:ProcPtr| #![auto] self.proc_dom().contains(p_ptr) && p_ptr != old(self).get_proc(proc_ptr).parent.unwrap()
                    ==>
                    self.get_proc(p_ptr).children == old(self).get_proc(p_ptr).children
            },
            forall|p_p_ptr:ProcPtr|
                #![trigger self.get_proc(p_p_ptr)]
                old(self).get_proc(proc_ptr).uppertree_seq@.contains(p_p_ptr) 
                ==>
                self.get_proc(p_p_ptr).subtree_set@ =~= 
                    old(self).get_proc(p_p_ptr).subtree_set@ - ret@,
            forall|p_ptr:ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) 
                ==>
                old(self).mem_man.get_pagetable_by_pcid(old(self).get_proc(p_ptr).pcid)
                    ==
                self.mem_man.get_pagetable_by_pcid(self.get_proc(p_ptr).pcid),
            old(self).get_proc(proc_ptr).depth == 0 ==> 
            {
                &&&
                forall|p_ptr:ProcPtr|  #![auto] self.proc_dom().contains(p_ptr)
                ==>
                self.get_proc(p_ptr).children == old(self).get_proc(p_ptr).children
            },
            forall|p_ptr:ProcPtr|  #![auto] self.proc_dom().contains(p_ptr)
                ==>
                self.get_proc(p_ptr).uppertree_seq == old(self).get_proc(p_ptr).uppertree_seq
        // decreases
        //     current_depth@,
    {
        assume(old(self).get_proc(proc_ptr).depth != 0 ==> 
                old(self).get_proc(proc_ptr).parent.is_Some());
        proof{set_add_lemma::<ProcPtr>();}
        let num_children = self.proc_man.get_proc(proc_ptr).children.len();
        assert(self.proc_man.get_proc(proc_ptr).children@.len() == num_children);
        let depth = self.proc_man.get_proc(proc_ptr).depth;
        
        let mut removed_procs = Ghost(Set::<ProcPtr>::empty());

        if num_children != 0 {
            assume(old(self).get_proc(proc_ptr).parent.is_Some());
            assume(old(self).proc_dom().contains(old(self).get_proc(proc_ptr).parent.unwrap()));
            for i in 0..num_children
                invariant
                    0<= i <= num_children,
                    current_depth@ == usize::MAX - old(self).get_proc(proc_ptr).depth,
                    old(self).wf(),
                    old(self).proc_dom().contains(proc_ptr),
                    self.wf(),
                    self.proc_dom().contains(proc_ptr),
                    processes_fields_unchanged(old(self).proc_man, self.proc_man),
                    old(self).get_proc(proc_ptr).uppertree_seq == self.get_proc(proc_ptr).uppertree_seq,
                    old(self).get_proc(proc_ptr).depth == self.get_proc(proc_ptr).depth,
                    old(self).get_proc(proc_ptr).depth != 0 ==> old(self).get_proc(proc_ptr).parent.is_Some(),
                    old(self).get_proc(proc_ptr).parent == self.get_proc(proc_ptr).parent,
                    old(self).get_proc(proc_ptr).depth != 0 ==> old(self).proc_dom().contains(old(self).get_proc(proc_ptr).parent.unwrap()),
                    self.get_proc(proc_ptr).ioid.is_None(),
                    self.mem_man.get_pagetable_by_pcid(self.get_proc(proc_ptr).pcid).unwrap().is_empty(),
                    self.get_proc(proc_ptr).owned_threads@ == Seq::<ThreadPtr>::empty(),
                    self.get_proc(proc_ptr).children.len() == num_children - i,
                    self.get_proc(proc_ptr).subtree_set@.subset_of(old(self).get_proc(proc_ptr).subtree_set@),

                    self.get_proc(proc_ptr).subtree_set@ + removed_procs@ == old(self).get_proc(proc_ptr).subtree_set@,
                    removed_procs@.disjoint(self.get_proc(proc_ptr).subtree_set@),
                    forall|p_p_ptr:ProcPtr|
                        #![trigger self.get_proc(p_p_ptr)]
                        old(self).get_proc(proc_ptr).uppertree_seq@.contains(p_p_ptr) 
                        ==>
                        self.get_proc(p_p_ptr).subtree_set@ =~= 
                            old(self).get_proc(p_p_ptr).subtree_set@ -  removed_procs@,

                    forall|s_p_ptr: ProcPtr|
                        #![trigger self.get_proc(s_p_ptr)]
                        #![trigger self.proc_dom().contains(s_p_ptr)]
                        self.get_proc(proc_ptr).subtree_set@.contains(s_p_ptr) 
                        ==>
                        self.proc_dom().contains(s_p_ptr)
                        && self.get_proc(s_p_ptr).ioid.is_None()
                        && self.mem_man.get_pagetable_by_pcid(self.get_proc(s_p_ptr).pcid).unwrap().is_empty()
                        && self.get_proc(s_p_ptr).owned_threads@ == Seq::<ThreadPtr>::empty(),
                    processes_fields_unchanged(old(self).proc_man, self.proc_man),
                    forall|p_ptr:ProcPtr|
                        #![trigger self.proc_dom().contains(p_ptr)]
                        old(self).proc_dom().contains(p_ptr) && old(self).get_proc(proc_ptr).subtree_set@.contains(p_ptr) == false
                        ==>
                        self.proc_dom().contains(p_ptr),
                    forall|p_ptr:ProcPtr|
                        #![auto]
                        self.proc_dom().contains(p_ptr) ==>
                        old(self).proc_dom().contains(p_ptr)
                        && 
                        (old(self).get_proc(proc_ptr).subtree_set@.contains(p_ptr) == false || 
                            self.get_proc(proc_ptr).subtree_set@.contains(p_ptr)
                        ),
                        forall|p_ptr:ProcPtr|
                            #![trigger self.get_proc(p_ptr)]
                            self.proc_dom().contains(p_ptr) 
                            ==>
                            old(self).mem_man.get_pagetable_by_pcid(old(self).get_proc(p_ptr).pcid)
                                ==
                            self.mem_man.get_pagetable_by_pcid(self.get_proc(p_ptr).pcid),
                        self.get_proc(old(self).get_proc(proc_ptr).parent.unwrap()).children == 
                            old(self).get_proc(old(self).get_proc(proc_ptr).parent.unwrap()).children,
                        forall|p_ptr:ProcPtr|
                            #![auto]
                            self.proc_dom().contains(p_ptr) && p_ptr != proc_ptr
                            ==>
                            self.get_proc(p_ptr).children == 
                                old(self).get_proc(p_ptr).children,
                        forall|p_ptr:ProcPtr|  #![auto] self.proc_dom().contains(p_ptr)
                            ==>
                            self.get_proc(p_ptr).uppertree_seq == old(self).get_proc(p_ptr).uppertree_seq,
            {
                proof{
                    set_add_lemma::<ProcPtr>();
                    seq_push_lemma::<ProcPtr>();
                }
                let child_head = self.proc_man.get_proc(proc_ptr).children.get_head();
                assume(self.get_proc(proc_ptr).subtree_set@.subset_of(self.proc_dom()));
                assume(self.get_proc(proc_ptr).subtree_set@.contains(self.get_proc(proc_ptr).children@[0]));
                assume(self.proc_dom().contains(self.get_proc(proc_ptr).children@[0]));
                assume(self.get_proc(proc_ptr).children@[0] != proc_ptr);
                assume(self.get_proc(child_head).parent == Some(proc_ptr));
                assume(self.get_proc(child_head).depth == old(self).get_proc(proc_ptr).depth + 1);
                assume(self.get_proc(child_head).subtree_set@.subset_of(self.get_proc(proc_ptr).subtree_set@));
                assert(self.get_proc(child_head).subtree_set@.subset_of(old(self).get_proc(proc_ptr).subtree_set@));
                assume(self.get_proc(child_head).uppertree_seq@ == self.get_proc(proc_ptr).uppertree_seq@.push(proc_ptr) );
                assume(                    
                    forall|p_p_ptr:ProcPtr|
                        #![auto]
                        old(self).get_proc(proc_ptr).uppertree_seq@.contains(p_p_ptr) 
                        ==>
                        self.proc_dom().contains(p_p_ptr)
                        &&
                        old(self).get_proc(proc_ptr).subtree_set@.contains(p_p_ptr) == false
                    );
                assert(old(self).get_proc(proc_ptr).subtree_set@.contains(child_head));
                assume(self.get_proc(self.get_proc(proc_ptr).children@[0]).subtree_set@.contains(proc_ptr) == false);
                
                assume(self.get_proc(proc_ptr).parent.is_Some());
                assume(self.proc_dom().contains(self.get_proc(proc_ptr).parent.unwrap()));
                assume(self.get_proc(proc_ptr).parent.unwrap() != proc_ptr);
                assume(self.get_proc(proc_ptr).subtree_set@.contains(self.get_proc(proc_ptr).parent.unwrap()) == false);

                // let snap_shot = Ghost(*self);
                // let snap_shot_seq = Ghost(self.get_proc(child_head).uppertree_seq@);

                let removed = self.kernel_kill_proc_recursive_non_root(child_head, Ghost(current_depth@ - 1));
                proof{removed_procs@ = removed_procs@ + removed@;}
                
                assume(self.proc_dom().contains(proc_ptr));
                assume(self.proc_dom().subset_of(old(self).proc_dom()));
                assume(self.get_proc(proc_ptr).subtree_set@.subset_of(self.proc_dom()));
                assume(forall|p_p_ptr:ProcPtr|
                    #![auto]
                    self.get_proc(proc_ptr).uppertree_seq@.contains(p_p_ptr)
                    ==>
                    self.proc_dom().contains(p_p_ptr));
                assume(self.get_proc(proc_ptr).parent.is_Some());
                assume(self.proc_dom().contains(self.get_proc(proc_ptr).parent.unwrap()));

            }
            assume(self.get_proc(proc_ptr).subtree_set@ == Set::<ProcPtr>::empty());
            assert(self.proc_dom() =~= old(self).proc_dom() - old(self).get_proc(proc_ptr).subtree_set@);
        }else{
            assume(self.get_proc(proc_ptr).subtree_set@ == Set::<ProcPtr>::empty());
            assert(self.proc_dom() =~= old(self).proc_dom() - old(self).get_proc(proc_ptr).subtree_set@);
        }

        if depth == 0{
            assert(self.get_proc(proc_ptr).children.wf()) by {
                broadcast use ProcessManager::reveal_process_manager_wf;
            };
            assert(self.get_proc(proc_ptr).children.len() == 0) by {
                broadcast use ProcessManager::reveal_process_manager_wf;
            };
            assume(0 <= self.get_proc(proc_ptr).children@.len() <= usize::MAX);
            assert(self.get_proc(proc_ptr).children@.len() == 0) by {
                broadcast use ProcessManager::reveal_process_manager_wf;
            };
            proof{lemma_seq_properties::<ProcPtr>();}
            assume(self.get_proc(proc_ptr).parent.is_None());
            assert(old(self).get_proc(proc_ptr).depth == 0);
            assert(removed_procs@ =~= old(self).get_proc(proc_ptr).subtree_set@);
            self.helper_kernel_kill_proc_root(proc_ptr);
            proof{removed_procs@ = removed_procs@.insert(proc_ptr);}
            return removed_procs;
        }else{
            assert(self.get_proc(proc_ptr).children.wf()) by {
                broadcast use ProcessManager::reveal_process_manager_wf;
            };
            assert(self.get_proc(proc_ptr).children.len() == 0) by {
                broadcast use ProcessManager::reveal_process_manager_wf;
            };
            assume(0 <= self.get_proc(proc_ptr).children@.len() <= usize::MAX);
            assert(self.get_proc(proc_ptr).children@.len() == 0) by {
                broadcast use ProcessManager::reveal_process_manager_wf;
            };
            proof{lemma_seq_properties::<ProcPtr>();}
            assume(self.get_proc(proc_ptr).parent.is_Some());
            assume(self.proc_dom().contains(self.get_proc(proc_ptr).parent.unwrap()));
            assume(self.get_proc(proc_ptr).parent.unwrap() != proc_ptr);
            assume(self.get_proc(proc_ptr).subtree_set@.contains(self.get_proc(proc_ptr).parent.unwrap()) == false);
            assert(old(self).get_proc(proc_ptr).depth != 0);
            assert(removed_procs@ =~= old(self).get_proc(proc_ptr).subtree_set@);

            self.helper_kernel_kill_proc_non_root(proc_ptr);
            proof{removed_procs@ = removed_procs@.insert(proc_ptr);}
            return removed_procs;
        }

        // assume(false);
    }
}

}
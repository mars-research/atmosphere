use vstd::prelude::*;
verus! {
    use crate::define::*;
    use crate::slinkedlist::spec_impl_u::*;
    use crate::array_set::*;
    use crate::process_manager::container::Container;
    use vstd::simple_pptr::*;
    use crate::lemma::lemma_u::*;
    use crate::lemma::lemma_t::*;
    use crate::process_manager::container_util_t::*;

    pub struct ContainerTree{
        pub root_container: ContainerPtr,

        pub container_perms: Tracked<Map<ContainerPtr, PointsTo<Container>>>,
    }

    //specs
    impl ContainerTree{
        pub open spec fn container_dom(&self) -> Set<ContainerPtr>
        {
            self.container_perms@.dom()
        }

        pub open spec fn spec_get_container(&self, c_ptr:ContainerPtr) -> &Container
        {
            &self.container_perms@[c_ptr].value()
        }

        #[verifier(when_used_as_spec(spec_get_container))]
        pub fn get_container(&self, container_ptr:ContainerPtr) -> (ret:&Container)
            requires
                self.wf(),
                self.container_dom().contains(container_ptr),
            ensures
                self.get_container(container_ptr) == ret,
        {
            let tracked container_perm = self.container_perms.borrow().tracked_borrow(container_ptr);
            let container : &Container = PPtr::<Container>::from_usize(container_ptr).borrow(Tracked(container_perm));
            container
        }

        pub closed spec fn container_perms_wf(&self) -> bool{
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].is_init()]
                self.container_perms@.dom().contains(c_ptr)
                ==> 
                self.container_perms@[c_ptr].is_init()
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].addr()]
                self.container_perms@.dom().contains(c_ptr)
                ==>        
                self.container_perms@[c_ptr].addr() == c_ptr
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().children.wf()]
                self.container_perms@.dom().contains(c_ptr)
                ==> 
                self.container_perms@[c_ptr].value().children.wf()
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().children.unique()]
                self.container_perms@.dom().contains(c_ptr)
                ==> 
                self.container_perms@[c_ptr].value().children.unique()
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().uppertree_seq@.no_duplicates()]
                self.container_perms@.dom().contains(c_ptr)
                ==> 
                self.container_perms@[c_ptr].value().uppertree_seq@.no_duplicates()
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@.dom().contains(c_ptr), self.container_perms@[c_ptr].value().children@.contains(c_ptr)]
                self.container_perms@.dom().contains(c_ptr)
                ==>
                self.container_perms@[c_ptr].value().children@.contains(c_ptr) == false
                &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().subtree_set@.finite()]
                self.container_perms@.dom().contains(c_ptr)
                ==>
                self.container_perms@[c_ptr].value().subtree_set@.finite()
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().uppertree_seq@.len(), self.container_perms@[c_ptr].value().depth]
                self.container_perms@.dom().contains(c_ptr)
                ==>
                self.container_perms@[c_ptr].value().uppertree_seq@.len() == self.container_perms@[c_ptr].value().depth    
        }
    
        pub closed spec fn container_root_wf(&self) -> bool{
            &&&
            self.container_perms@.dom().contains(self.root_container)
            &&&
            self.container_perms@[self.root_container].value().depth == 0
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@.dom().contains(c_ptr), self.container_perms@[c_ptr].value().depth ]
                self.container_perms@.dom().contains(c_ptr) 
                &&
                c_ptr != self.root_container 
                ==>
                self.container_perms@[c_ptr].value().depth != 0
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().parent.is_Some() ]
                self.container_perms@.dom().contains(c_ptr) 
                &&
                c_ptr != self.root_container 
                ==>
                self.container_perms@[c_ptr].value().parent.is_Some()  
        }
    
        pub closed spec fn container_childern_list_wf(&self) -> bool{
            &&&
            forall|c_ptr:ContainerPtr, child_c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().children@.contains(child_c_ptr), self.container_perms@[child_c_ptr].value().depth, self.container_perms@[c_ptr].value().depth]
                #![trigger self.container_perms@.dom().contains(c_ptr), self.container_perms@[c_ptr].value().children@.contains(child_c_ptr), self.container_perms@.dom().contains(child_c_ptr)]
                #![trigger self.container_perms@[c_ptr].value().children@.contains(child_c_ptr), self.container_perms@[child_c_ptr].value().parent.unwrap()]
               //  #![auto]
                self.container_perms@.dom().contains(c_ptr) 
                && 
                self.container_perms@[c_ptr].value().children@.contains(child_c_ptr)
                ==> self.container_perms@.dom().contains(child_c_ptr)
                    &&
                    self.container_perms@[child_c_ptr].value().parent.unwrap() == c_ptr
                    &&
                    self.container_perms@[child_c_ptr].value().depth == self.container_perms@[c_ptr].value().depth + 1
        }
    
        pub closed spec fn containers_linkedlist_wf(&self) -> bool{  
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@.dom().contains(self.container_perms@[c_ptr].value().parent.unwrap())]
                self.container_perms@.dom().contains(c_ptr) && c_ptr != self.root_container 
                ==> 
                self.container_perms@.dom().contains(self.container_perms@[c_ptr].value().parent.unwrap())
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().parent_rev_ptr.is_Some()]
                #![trigger self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().children@.contains(c_ptr)]
                #![trigger self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().children.node_ref_valid(self.container_perms@[c_ptr].value().parent_rev_ptr.unwrap())]
                #![trigger self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().children.node_ref_resolve(self.container_perms@[c_ptr].value().parent_rev_ptr.unwrap())]
                self.container_perms@.dom().contains(c_ptr) && c_ptr != self.root_container 
                ==> 
                self.container_perms@[c_ptr].value().parent_rev_ptr.is_Some()
                &&
                self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().children@.contains(c_ptr)
                && 
                self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().children.node_ref_valid(self.container_perms@[c_ptr].value().parent_rev_ptr.unwrap())
                && 
                self.container_perms@[self.container_perms@[c_ptr].value().parent.unwrap()].value().children.node_ref_resolve(self.container_perms@[c_ptr].value().parent_rev_ptr.unwrap()) == c_ptr
        }

        pub closed spec fn container_childern_depth_wf(&self) -> bool {
            &&&
            forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth - 1]]
                self.container_perms@.dom().contains(c_ptr) && c_ptr != self.root_container
                ==>
                self.container_perms@[c_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth - 1] == self.container_perms@[c_ptr].value().parent.unwrap()
        }

        pub closed spec fn container_subtree_set_wf(&self) -> bool{
            &&&
            forall|c_ptr:ContainerPtr, sub_c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().subtree_set@.contains(sub_c_ptr), self.container_perms@[sub_c_ptr].value().uppertree_seq@.len(), self.container_perms@[c_ptr].value().depth]
                #![trigger self.container_perms@[c_ptr].value().subtree_set@.contains(sub_c_ptr), self.container_perms@[sub_c_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth as int]]
                #![trigger self.container_perms@.dom().contains(c_ptr), self.container_perms@[c_ptr].value().subtree_set@.contains(sub_c_ptr), self.container_perms@.dom().contains(sub_c_ptr)]
                self.container_perms@.dom().contains(c_ptr) && self.container_perms@[c_ptr].value().subtree_set@.contains(sub_c_ptr)
                ==> 
                self.container_perms@.dom().contains(sub_c_ptr)
                &&
                self.container_perms@[sub_c_ptr].value().uppertree_seq@.len() > self.container_perms@[c_ptr].value().depth
                &&
                self.container_perms@[sub_c_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth as int] == c_ptr
        }

        pub closed spec fn container_uppertree_seq_wf(&self) -> bool{
            &&&
            forall|c_ptr:ContainerPtr, u_ptr:ContainerPtr|
                #![trigger self.container_perms@.dom().contains(c_ptr), self.container_perms@[c_ptr].value().uppertree_seq@.contains(u_ptr), self.container_perms@.dom().contains(u_ptr)]
                #![trigger self.container_perms@[c_ptr].value().uppertree_seq@.subrange(0, self.container_perms@[u_ptr].value().depth as int)]
                #![trigger self.container_perms@[c_ptr].value().uppertree_seq@.index_of(u_ptr)]
                self.container_perms@.dom().contains(c_ptr) && self.container_perms@[c_ptr].value().uppertree_seq@.contains(u_ptr)
                ==>
                self.container_perms@.dom().contains(u_ptr)
                &&
                self.container_perms@[c_ptr].value().uppertree_seq@[self.container_perms@[u_ptr].value().depth as int] == u_ptr
                &&
                self.container_perms@[u_ptr].value().depth == self.container_perms@[c_ptr].value().uppertree_seq@.index_of(u_ptr)
                &&
                self.container_perms@[u_ptr].value().subtree_set@.contains(c_ptr)
                &&
                self.container_perms@[u_ptr].value().uppertree_seq@ =~= self.container_perms@[c_ptr].value().uppertree_seq@.subrange(0, self.container_perms@[u_ptr].value().depth as int)
        }

        pub closed spec fn container_subtree_set_exclusive(&self) -> bool{
            &&&
            forall|c_ptr:ContainerPtr, sub_c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().subtree_set@.contains(sub_c_ptr), self.container_perms@[sub_c_ptr].value().uppertree_seq@.contains(c_ptr)]
                self.container_perms@.dom().contains(c_ptr) 
                && 
                self.container_perms@.dom().contains(sub_c_ptr) 
                ==> 
                (
                    self.container_perms@[c_ptr].value().subtree_set@.contains(sub_c_ptr)
                    ==
                    self.container_perms@[sub_c_ptr].value().uppertree_seq@.contains(c_ptr)
                )
        }

        pub open spec fn tree_wf(&self) -> bool{
            &&&
            self.container_subtree_set_wf()
            &&&
            self.container_uppertree_seq_wf()
        }

        pub open spec fn linked_list_wf(&self) -> bool{
            &&&
            self.container_childern_list_wf()
            &&&
            self.containers_linkedlist_wf()
        }
        
        pub open spec fn rest_specs(&self) -> bool{
            &&&
            self.container_perms_wf()
            &&&
            self.container_root_wf()
            &&&
            self.container_childern_depth_wf()
            &&&
            self.container_subtree_set_exclusive()
        }

        pub open spec fn wf(&self) -> bool{
            &&&
            self.container_perms_wf()
            &&&
            self.container_root_wf()
            &&&
            self.container_childern_list_wf()
            &&&
            self.containers_linkedlist_wf()
            &&&
            self.container_childern_depth_wf()
            &&&
            self.container_subtree_set_wf()
            &&&
            self.container_uppertree_seq_wf()
            &&&
            self.container_subtree_set_exclusive()
        }
    }

    //proof
    impl ContainerTree{

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
        {
        }

        pub proof fn same_or_deeper_depth_imply_none_ancestor(&self, a_ptr:ContainerPtr, child_ptr:ContainerPtr)
            requires
                self.wf(),
                self.container_perms@.dom().contains(a_ptr),
                self.container_perms@.dom().contains(child_ptr),
                self.container_perms@[a_ptr].value().depth >= self.container_perms@[child_ptr].value().depth,
            ensures
                self.container_perms@[a_ptr].value().subtree_set@.contains(child_ptr) == false
        {
            assert(self.container_perms@[a_ptr].value().uppertree_seq@.len() == self.container_perms@[a_ptr].value().depth);
            assert(self.container_perms@[child_ptr].value().uppertree_seq@.len() == self.container_perms@[child_ptr].value().depth);
        }

        pub proof fn no_child_imply_no_subtree(&self, c_ptr:ContainerPtr)
            requires
                self.wf(),
                self.container_perms@.dom().contains(c_ptr),
                self.container_perms@[c_ptr].value().children@ =~= Seq::empty(),
            ensures
                self.container_perms@[c_ptr].value().subtree_set@ =~= Set::empty(),
        {
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[s_ptr].value().uppertree_seq@.contains(c_ptr));
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[s_ptr].value().uppertree_seq@.subrange(0,self.container_perms@[c_ptr].value().depth as int) == self.container_perms@[c_ptr].value().uppertree_seq@);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> s_ptr != self.root_container);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[s_ptr].value().parent.unwrap() != c_ptr);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[s_ptr].value().depth - 1] != c_ptr);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth as int] == c_ptr);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[s_ptr].value().uppertree_seq@.len() > self.container_perms@[c_ptr].value().depth);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[s_ptr].value().uppertree_seq@.len() != self.container_perms@[c_ptr].value().depth + 1);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[s_ptr].value().uppertree_seq@.contains(self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]));
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@.dom().contains(s_ptr));
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@.dom().contains(self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]));
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[s_ptr].value().uppertree_seq@.contains(self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]));
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[s_ptr].value().uppertree_seq@.subrange(0,self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().depth as int) 
                    =~= 
                    self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().uppertree_seq@);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[s_ptr].value().uppertree_seq@.no_duplicates());
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[s_ptr].value().uppertree_seq@.index_of(self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]) == self.container_perms@[c_ptr].value().depth + 1);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().depth == self.container_perms@[c_ptr].value().depth + 1);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth as int] == c_ptr);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().uppertree_seq@[
                    self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().depth - 1] == c_ptr);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().parent.unwrap() == c_ptr);
            assert(forall|s_ptr:ContainerPtr| #![auto] self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr) ==> self.container_perms@[c_ptr].value().children@.contains(self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]));
        }

        pub proof fn in_child_impy_in_subtree(&self, c_ptr:ContainerPtr, child_ptr:ContainerPtr, s_ptr:ContainerPtr)
            requires
                self.wf(),
                self.container_perms@.dom().contains(c_ptr),
                self.container_perms@[c_ptr].value().children@.contains(child_ptr),
                self.container_perms@[child_ptr].value().subtree_set@.contains(s_ptr),
            ensures
                self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr),
        {
            assert(self.container_perms@[child_ptr].value().parent.unwrap() == c_ptr);
            assert(self.container_perms@[child_ptr].value().depth == self.container_perms@[c_ptr].value().depth + 1);
            assert(self.container_perms@[child_ptr].value().uppertree_seq@.len() == self.container_perms@[child_ptr].value().depth);
            assert(self.container_perms@[c_ptr].value().uppertree_seq@.len() == self.container_perms@[c_ptr].value().depth);
            assert(self.container_perms@[child_ptr].value().uppertree_seq@[self.container_perms@[child_ptr].value().depth - 1] == c_ptr);
            assert(self.container_perms@[s_ptr].value().uppertree_seq@.subrange(0, self.container_perms@[child_ptr].value().depth as int) == self.container_perms@[child_ptr].value().uppertree_seq@);
            assert(self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth as int] == c_ptr);
            assert(self.container_perms@[s_ptr].value().uppertree_seq@.contains(c_ptr));
        }

        pub proof fn in_subtree_imply_exist_in_child(&self, c_ptr:ContainerPtr, s_ptr:ContainerPtr)
            requires
                self.wf(),
                self.container_perms@.dom().contains(c_ptr),
                self.container_perms@[c_ptr].value().subtree_set@.contains(s_ptr),
            ensures
                self.container_perms@[c_ptr].value().children@.contains(s_ptr) 
                || 
                (exists|child_ptr:ContainerPtr| 
                    #![auto]
                    self.container_perms@[c_ptr].value().children@.contains(child_ptr) && self.container_perms@[child_ptr].value().subtree_set@.contains(s_ptr)),
        {
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==>
                    self.container_perms@[s_ptr].value().uppertree_seq@.subrange(0,self.container_perms@[c_ptr].value().depth as int) == self.container_perms@[c_ptr].value().uppertree_seq@
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==>
                    s_ptr != self.root_container
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==>
                    self.container_perms@[s_ptr].value().parent.unwrap() != c_ptr
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==>
                    self.container_perms@[s_ptr].value().uppertree_seq@.len() > self.container_perms@[c_ptr].value().depth
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==>
                    self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[s_ptr].value().depth - 1] != c_ptr
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==>
                    self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth as int] == c_ptr
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==>
                    self.container_perms@[s_ptr].value().uppertree_seq@.len() > self.container_perms@[c_ptr].value().depth
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==>
                    self.container_perms@[s_ptr].value().uppertree_seq@.len() != self.container_perms@[c_ptr].value().depth + 1
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==>
                    self.container_perms@[s_ptr].value().uppertree_seq@.len() > self.container_perms@[c_ptr].value().depth + 1
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==> 
                self.container_perms@[s_ptr].value().uppertree_seq@.contains(self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]));
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==> 
                self.container_perms@.dom().contains(self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1])
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==> 
                self.container_perms@[s_ptr].value().uppertree_seq@.subrange(0,self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().depth as int) 
                    =~= self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().uppertree_seq@
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==> 
                self.container_perms@[s_ptr].value().uppertree_seq@.no_duplicates()
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==> 
                self.container_perms@[s_ptr].value().uppertree_seq@.index_of(self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]) == self.container_perms@[c_ptr].value().depth + 1
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==> 
                self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().depth == self.container_perms@[c_ptr].value().depth + 1
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==> 
                self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().uppertree_seq@.len() == self.container_perms@[c_ptr].value().depth + 1
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==> 
                self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth as int] == c_ptr
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==> 
                self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().uppertree_seq@[
                    self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().depth - 1] == c_ptr
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==> 
                self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().parent.unwrap() == c_ptr
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==> 
                self.container_perms@[c_ptr].value().children@.contains(self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1])
            );
            assert(self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==> 
                self.container_perms@[self.container_perms@[s_ptr].value().uppertree_seq@[self.container_perms@[c_ptr].value().depth + 1]].value().subtree_set@.contains(s_ptr)
            );
            assert(                
                self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false ==>
                (exists|child_ptr:ContainerPtr| 
                #![auto]
                self.container_perms@[c_ptr].value().children@.contains(child_ptr) && self.container_perms@[child_ptr].value().subtree_set@.contains(s_ptr)
                )
            );
        }

        pub proof fn not_in_dom_imply_not_in_any_children_set(&self, s_ptr:ContainerPtr)
            requires
                self.wf(),
                self.container_perms@.dom().contains(s_ptr) == false,
        {
            assert(
                forall|c_ptr:ContainerPtr|
                    #![auto]
                    self.container_perms@.dom().contains(c_ptr)
                    ==>
                    self.container_perms@[c_ptr].value().children@.contains(s_ptr) == false
            );
        }
             
        pub proof fn container_tree_inv(&self)
            requires
                self.wf()
            ensures
                forall|c_ptr:ContainerPtr|
                    #![auto]
                    self.container_perms@.dom().contains(c_ptr)
                    ==>
                    self.get_container(c_ptr).children.wf(),
        {}
    }

    //exec
    impl ContainerTree{
        
        pub fn new() -> Self{
            ContainerTree{
                root_container: 0,
            
                container_perms: Tracked(Map::tracked_empty()),
            }
        }

        pub fn check_is_ancestor(&self, a_ptr:ContainerPtr, child_ptr:ContainerPtr) -> (ret:bool)
            requires
                self.wf(),
                self.container_perms@.dom().contains(a_ptr),
                self.container_perms@.dom().contains(child_ptr),
                self.container_perms@[a_ptr].value().depth < self.container_perms@[child_ptr].value().depth,
                child_ptr != self.root_container,
            ensures
                ret == self.container_perms@[child_ptr].value().uppertree_seq@.contains(a_ptr)
        {
            // assert(false);
            proof{
                seq_push_lemma::<ContainerPtr>();
            }
            assert(self.container_perms@[child_ptr].value().parent.is_Some());
            let tracked child_perm = self.container_perms.borrow().tracked_borrow(child_ptr);
            let child : &Container = PPtr::<Container>::from_usize(child_ptr).borrow(Tracked(child_perm));
            let mut current_parent_ptr = child.parent.unwrap();
            let mut depth = child.depth;
            assert(current_parent_ptr == self.container_perms@[child_ptr].value().uppertree_seq@[depth - 1]);

            if current_parent_ptr == a_ptr{
                return true;
            }

            while depth != 1
                invariant
                    1 <= depth <= self.container_perms@[child_ptr].value().depth,
                    self.wf(),
                    self.container_perms@.dom().contains(a_ptr),
                    self.container_perms@.dom().contains(child_ptr),
                    self.container_perms@[a_ptr].value().depth < self.container_perms@[child_ptr].value().depth,
                    child_ptr != self.root_container,
                    current_parent_ptr == self.container_perms@[child_ptr].value().uppertree_seq@[depth - 1],
                    forall|i:int|
                       //  #![auto]
                        depth - 1 <= i < self.container_perms@[child_ptr].value().depth ==> self.container_perms@[child_ptr].value().uppertree_seq@[i] != a_ptr,
                    ensures
                        depth == 1,
                        forall|i:int|
                           //  #![auto]
                            0 <= i < self.container_perms@[child_ptr].value().depth ==> self.container_perms@[child_ptr].value().uppertree_seq@[i] != a_ptr,
            {
                assert(self.container_perms@[child_ptr].value().uppertree_seq@.contains(current_parent_ptr));
                assert(self.container_perms@.dom().contains(current_parent_ptr));
                assert(self.container_perms@[child_ptr].value().uppertree_seq@.no_duplicates());
                assert(self.container_perms@[child_ptr].value().uppertree_seq@.index_of(current_parent_ptr) == depth - 1);
                assert(self.container_perms@[current_parent_ptr].value().depth == depth - 1);
                assert(self.container_perms@[current_parent_ptr].value().parent.is_Some());
                let tracked current_parent_perm = self.container_perms.borrow().tracked_borrow(current_parent_ptr);
                assert(current_parent_perm.addr() == current_parent_ptr);
                let current_parent : &Container = PPtr::<Container>::from_usize(current_parent_ptr).borrow(Tracked(current_parent_perm));
                let current_parent_ptr_tmp = current_parent.parent.unwrap();
                if current_parent_ptr_tmp == a_ptr{
                    assert(self.container_perms@[current_parent_ptr].value().uppertree_seq@[depth - 1 - 1] == current_parent_ptr_tmp);
                    return true;
                }
                assert(self.container_perms@[current_parent_ptr].value().uppertree_seq@[depth - 1 - 1] == current_parent_ptr_tmp);
                current_parent_ptr = current_parent_ptr_tmp;
                depth = depth - 1;
            }
            false
        }

        #[verifier(external_body)]
        pub fn upper_tree_add_container(&mut self, seq:Ghost<Seq<ContainerPtr>>, subchild_ptr:ContainerPtr)
            requires
                forall|c_ptr:ContainerPtr|
                #![trigger seq@.contains(c_ptr)] 
                seq@.contains(c_ptr) ==> old(self).container_perms@.dom().contains(c_ptr)
            ensures
                self.root_container == old(self).root_container,
                old(self).container_perms@.dom() == self.container_perms@.dom(),
                forall|c_ptr:ContainerPtr| 
                    #![trigger self.container_perms@[c_ptr]] 
                    self.container_perms@.dom().contains(c_ptr) && seq@.contains(c_ptr) == false 
                    ==> 
                    self.container_perms@[c_ptr] === old(self).container_perms@[c_ptr],
                forall|c_ptr:ContainerPtr| 
                    #![trigger self.container_perms@[c_ptr].is_init()] 
                    self.container_perms@.dom().contains(c_ptr)
                    ==>
                    self.container_perms@[c_ptr].is_init(),
                forall|c_ptr:ContainerPtr| 
                    #![trigger self.container_perms@[c_ptr].addr()] 
                    self.container_perms@.dom().contains(c_ptr)
                    ==>           
                    self.container_perms@[c_ptr].addr() == old(self).container_perms@[c_ptr].addr(),
                forall|c_ptr:ContainerPtr| 
                    #![trigger self.container_perms@[c_ptr].value().owned_procs] 
                    self.container_perms@.dom().contains(c_ptr)
                    ==>
                    self.container_perms@[c_ptr].value().owned_procs =~= old(self).container_perms@[c_ptr].value().owned_procs,
                forall|c_ptr:ContainerPtr| 
                    #![trigger self.container_perms@[c_ptr].value().parent] 
                    self.container_perms@.dom().contains(c_ptr)
                    ==>
                    self.container_perms@[c_ptr].value().parent =~= old(self).container_perms@[c_ptr].value().parent,
                forall|c_ptr:ContainerPtr| 
                    #![trigger self.container_perms@[c_ptr].value().parent_rev_ptr] 
                    self.container_perms@.dom().contains(c_ptr)
                    ==>
                    self.container_perms@[c_ptr].value().parent_rev_ptr =~= old(self).container_perms@[c_ptr].value().parent_rev_ptr,
                forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@.dom().contains(c_ptr), self.container_perms@[c_ptr].value().children] 
                    self.container_perms@.dom().contains(c_ptr)
                    ==>
                    self.container_perms@[c_ptr].value().children =~= old(self).container_perms@[c_ptr].value().children,
                forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().owned_endpoints] 
                    self.container_perms@.dom().contains(c_ptr)
                    ==>
                    self.container_perms@[c_ptr].value().owned_endpoints =~= old(self).container_perms@[c_ptr].value().owned_endpoints,
                forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().mem_quota] 
                    self.container_perms@.dom().contains(c_ptr)
                    ==>
                    self.container_perms@[c_ptr].value().mem_quota =~= old(self).container_perms@[c_ptr].value().mem_quota,
                forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().mem_used] 
                    self.container_perms@.dom().contains(c_ptr)
                    ==>
                    self.container_perms@[c_ptr].value().mem_used =~= old(self).container_perms@[c_ptr].value().mem_used,
                forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().owned_cpus] 
                    self.container_perms@.dom().contains(c_ptr)
                    ==>
                    self.container_perms@[c_ptr].value().owned_cpus =~= old(self).container_perms@[c_ptr].value().owned_cpus,
                forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@.dom().contains(c_ptr), self.container_perms@[c_ptr].value().scheduler] 
                    self.container_perms@.dom().contains(c_ptr)
                    ==>
                    self.container_perms@[c_ptr].value().scheduler =~= old(self).container_perms@[c_ptr].value().scheduler,
                forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().owned_threads] 
                    self.container_perms@.dom().contains(c_ptr)
                    ==>
                    self.container_perms@[c_ptr].value().owned_threads =~= old(self).container_perms@[c_ptr].value().owned_threads,
                forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().depth] 
                    self.container_perms@.dom().contains(c_ptr)
                    ==>
                    self.container_perms@[c_ptr].value().depth =~= old(self).container_perms@[c_ptr].value().depth,
                forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().uppertree_seq] 
                    self.container_perms@.dom().contains(c_ptr)
                    ==>
                    self.container_perms@[c_ptr].value().uppertree_seq =~= old(self).container_perms@[c_ptr].value().uppertree_seq,
                forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().subtree_set@] 
                    self.container_perms@.dom().contains(c_ptr) && seq@.contains(c_ptr) 
                    ==>
                    self.container_perms@[c_ptr].value().subtree_set@ =~= old(self).container_perms@[c_ptr].value().subtree_set@.insert(subchild_ptr),
                forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@[c_ptr].value().subtree_set] 
                    self.container_perms@.dom().contains(c_ptr) && seq@.contains(c_ptr) == false
                    ==>
                    self.container_perms@[c_ptr].value().subtree_set =~= old(self).container_perms@[c_ptr].value().subtree_set,
        {}

        #[verifier(external_body)]
        pub fn upper_tree_add_container1(&mut self, seq:Ghost<Seq<ContainerPtr>>, subchild_ptr:ContainerPtr)
            requires
                forall|c_ptr:ContainerPtr|
                #![trigger seq@.contains(c_ptr)] 
                seq@.contains(c_ptr) ==> old(self).container_perms@.dom().contains(c_ptr)
            ensures
                self.root_container == old(self).root_container,
                old(self).container_perms@.dom() == self.container_perms@.dom(),
                forall|c_ptr:ContainerPtr| 
                    #![trigger self.container_perms@.dom().contains(c_ptr)] 
                    self.container_perms@.dom().contains(c_ptr) && seq@.contains(c_ptr) == false 
                    ==> 
                    self.container_perms@[c_ptr] =~= old(self).container_perms@[c_ptr],
               
                forall|c_ptr:ContainerPtr| 
                    #![trigger self.container_perms@.dom().contains(c_ptr)]
                    #![trigger self.container_perms@[c_ptr].is_init()]
                    #![trigger self.container_perms@[c_ptr].addr()]
                    #![trigger self.container_perms@[c_ptr].value().owned_procs]
                    #![trigger self.container_perms@[c_ptr].value().owned_procs]
                    #![trigger self.container_perms@[c_ptr].value().parent]
                    #![trigger self.container_perms@[c_ptr].value().parent_rev_ptr]
                    #![trigger self.container_perms@[c_ptr].value().children]
                    #![trigger self.container_perms@[c_ptr].value().owned_endpoints]
                    #![trigger self.container_perms@[c_ptr].value().mem_quota]
                    #![trigger self.container_perms@[c_ptr].value().mem_used]
                    #![trigger self.container_perms@[c_ptr].value().owned_cpus]
                    #![trigger self.container_perms@[c_ptr].value().scheduler]
                    #![trigger self.container_perms@[c_ptr].value().owned_threads]
                    #![trigger self.container_perms@[c_ptr].value().depth]
                    #![trigger self.container_perms@[c_ptr].value().uppertree_seq]
                    self.container_perms@.dom().contains(c_ptr)
                    ==> 
                    self.container_perms@[c_ptr].is_init() == old(self).container_perms@[c_ptr].is_init()
                    &&
                    self.container_perms@[c_ptr].addr() == old(self).container_perms@[c_ptr].addr()
                    &&
                    self.container_perms@[c_ptr].value().owned_procs =~= old(self).container_perms@[c_ptr].value().owned_procs
                    &&                
                    self.container_perms@[c_ptr].value().parent =~= old(self).container_perms@[c_ptr].value().parent
                    &&
                    self.container_perms@[c_ptr].value().parent_rev_ptr =~= old(self).container_perms@[c_ptr].value().parent_rev_ptr
                    &&
                    self.container_perms@[c_ptr].value().children =~= old(self).container_perms@[c_ptr].value().children
                    &&
                    self.container_perms@[c_ptr].value().owned_endpoints =~= old(self).container_perms@[c_ptr].value().owned_endpoints
                    &&
                    self.container_perms@[c_ptr].value().mem_quota =~= old(self).container_perms@[c_ptr].value().mem_quota
                    &&
                    self.container_perms@[c_ptr].value().mem_used =~= old(self).container_perms@[c_ptr].value().mem_used
                    &&
                    self.container_perms@[c_ptr].value().owned_cpus =~= old(self).container_perms@[c_ptr].value().owned_cpus
                    &&
                    self.container_perms@[c_ptr].value().scheduler =~= old(self).container_perms@[c_ptr].value().scheduler
                    &&
                    self.container_perms@[c_ptr].value().owned_threads =~= old(self).container_perms@[c_ptr].value().owned_threads
                    &&
                    self.container_perms@[c_ptr].value().depth =~= old(self).container_perms@[c_ptr].value().depth
                    &&
                    self.container_perms@[c_ptr].value().uppertree_seq =~= old(self).container_perms@[c_ptr].value().uppertree_seq,

                forall|c_ptr:ContainerPtr| 
                    #![trigger self.container_perms@.dom().contains(c_ptr)] 
                    #![trigger self.container_perms@[c_ptr].value().subtree_set] 
                    self.container_perms@.dom().contains(c_ptr) && seq@.contains(c_ptr) 
                    ==>
                    self.container_perms@[c_ptr].value().subtree_set@ =~= old(self).container_perms@[c_ptr].value().subtree_set@.insert(subchild_ptr),
                forall|c_ptr:ContainerPtr| 
                    #![trigger self.container_perms@.dom().contains(c_ptr)] 
                    #![trigger self.container_perms@[c_ptr].value().subtree_set] 
                    self.container_perms@.dom().contains(c_ptr) && seq@.contains(c_ptr) == false
                    ==>
                    self.container_perms@[c_ptr].value().subtree_set =~= old(self).container_perms@[c_ptr].value().subtree_set,
        {}

        pub fn new_container(&mut self, container_ptr:ContainerPtr, init_quota:usize, page_ptr_1: PagePtr, page_perm_1: Tracked<PagePerm4k>)
            requires
                old(self).wf(),
                old(self).container_perms@.dom().contains(container_ptr),
                old(self).container_perms@.dom().contains(page_ptr_1) == false,
                old(self).container_perms@[container_ptr].value().children.len() < CONTAINER_CHILD_LIST_LEN,
                old(self).container_perms@[container_ptr].value().depth < usize::MAX,
                old(self).container_perms@[container_ptr].value().mem_quota >= init_quota + 3,
                page_perm_1@.is_init(),
                page_perm_1@.addr() == page_ptr_1,
            ensures
                self.wf(),  
                self.container_dom() =~= old(self).container_dom().insert(page_ptr_1),
                self.get_container(page_ptr_1).uppertree_seq@ =~= old(self).get_container(container_ptr).uppertree_seq@.push(container_ptr),
                forall|c_ptr:ContainerPtr| 
                    #![trigger self.container_perms@.dom().contains(c_ptr)]
                    #![trigger self.container_perms@[c_ptr].is_init()]
                    #![trigger self.container_perms@[c_ptr].addr()]
                    #![trigger self.container_perms@[c_ptr].value().owned_procs]
                    #![trigger self.container_perms@[c_ptr].value().parent]
                    #![trigger self.container_perms@[c_ptr].value().parent_rev_ptr]
                    #![trigger self.container_perms@[c_ptr].value().children]
                    #![trigger self.container_perms@[c_ptr].value().owned_endpoints]
                    #![trigger self.container_perms@[c_ptr].value().mem_quota]
                    #![trigger self.container_perms@[c_ptr].value().mem_used]
                    #![trigger self.container_perms@[c_ptr].value().owned_cpus]
                    #![trigger self.container_perms@[c_ptr].value().scheduler]
                    #![trigger self.container_perms@[c_ptr].value().owned_threads]
                    #![trigger self.container_perms@[c_ptr].value().depth]
                    #![trigger self.container_perms@[c_ptr].value().uppertree_seq]
                    old(self).container_perms@.dom().contains(c_ptr) && c_ptr != container_ptr
                    ==> 
                    self.container_perms@[c_ptr].value().owned_procs =~= old(self).container_perms@[c_ptr].value().owned_procs
                    &&                
                    self.container_perms@[c_ptr].value().parent =~= old(self).container_perms@[c_ptr].value().parent
                    &&                
                    self.container_perms@[c_ptr].value().parent_rev_ptr =~= old(self).container_perms@[c_ptr].value().parent_rev_ptr
                    &&
                    self.container_perms@[c_ptr].value().children =~= old(self).container_perms@[c_ptr].value().children
                    &&
                    self.container_perms@[c_ptr].value().owned_endpoints =~= old(self).container_perms@[c_ptr].value().owned_endpoints
                    &&
                    self.container_perms@[c_ptr].value().mem_quota =~= old(self).container_perms@[c_ptr].value().mem_quota
                    &&
                    self.container_perms@[c_ptr].value().mem_used =~= old(self).container_perms@[c_ptr].value().mem_used
                    &&
                    self.container_perms@[c_ptr].value().owned_cpus =~= old(self).container_perms@[c_ptr].value().owned_cpus
                    &&
                    self.container_perms@[c_ptr].value().scheduler =~= old(self).container_perms@[c_ptr].value().scheduler
                    &&
                    self.container_perms@[c_ptr].value().owned_threads =~= old(self).container_perms@[c_ptr].value().owned_threads
                    &&
                    self.container_perms@[c_ptr].value().depth =~= old(self).container_perms@[c_ptr].value().depth
                    &&
                    self.container_perms@[c_ptr].value().uppertree_seq =~= old(self).container_perms@[c_ptr].value().uppertree_seq,
                forall|c_ptr:ContainerPtr| 
                    #![trigger self.container_perms@.dom().contains(c_ptr)] 
                    #![trigger self.container_perms@[c_ptr].value().subtree_set] 
                    self.container_perms@.dom().contains(c_ptr) && self.get_container(page_ptr_1).uppertree_seq@.contains(c_ptr)
                    ==>
                    self.container_perms@[c_ptr].value().subtree_set@ =~= old(self).container_perms@[c_ptr].value().subtree_set@.insert(page_ptr_1),
                forall|c_ptr:ContainerPtr| 
                    #![trigger self.container_perms@.dom().contains(c_ptr)] 
                    #![trigger self.container_perms@[c_ptr].value().subtree_set] 
                    old(self).container_perms@.dom().contains(c_ptr) && self.get_container(page_ptr_1).uppertree_seq@.contains(c_ptr) == false
                    ==>
                    self.container_perms@[c_ptr].value().subtree_set =~= old(self).container_perms@[c_ptr].value().subtree_set,

                self.container_perms@[container_ptr].value().owned_procs =~= old(self).container_perms@[container_ptr].value().owned_procs,
                self.container_perms@[container_ptr].value().parent =~= old(self).container_perms@[container_ptr].value().parent,
                self.container_perms@[container_ptr].value().children@ =~= old(self).container_perms@[container_ptr].value().children@.push(page_ptr_1),
                self.container_perms@[container_ptr].value().owned_endpoints =~= old(self).container_perms@[container_ptr].value().owned_endpoints,
                self.container_perms@[container_ptr].value().mem_quota as int =~= old(self).container_perms@[container_ptr].value().mem_quota - init_quota - 3,
                self.container_perms@[container_ptr].value().mem_used =~= old(self).container_perms@[container_ptr].value().mem_used,
                self.container_perms@[container_ptr].value().owned_cpus =~= old(self).container_perms@[container_ptr].value().owned_cpus,
                self.container_perms@[container_ptr].value().scheduler =~= old(self).container_perms@[container_ptr].value().scheduler,
                self.container_perms@[container_ptr].value().owned_threads =~= old(self).container_perms@[container_ptr].value().owned_threads,
                self.container_perms@[container_ptr].value().depth =~= old(self).container_perms@[container_ptr].value().depth,
                self.container_perms@[container_ptr].value().uppertree_seq =~= old(self).container_perms@[container_ptr].value().uppertree_seq,
                self.container_perms@[container_ptr].value().subtree_set@ =~= old(self).container_perms@[container_ptr].value().subtree_set@.insert(page_ptr_1),
                
                self.container_perms@[page_ptr_1].value().owned_procs@ =~= Seq::<ProcPtr>::empty(),
                self.container_perms@[page_ptr_1].value().parent =~= Some(container_ptr),
                self.container_perms@[page_ptr_1].value().children@ =~= Seq::<ContainerPtr>::empty(),
                self.container_perms@[page_ptr_1].value().owned_endpoints.wf(),
                self.container_perms@[page_ptr_1].value().owned_endpoints@ =~= Seq::<EndpointPtr>::empty(),
                self.container_perms@[page_ptr_1].value().mem_quota =~= init_quota,
                self.container_perms@[page_ptr_1].value().mem_used =~= 0,
                self.container_perms@[page_ptr_1].value().owned_cpus.wf(),
                self.container_perms@[page_ptr_1].value().owned_cpus@ =~= Set::<CpuId>::empty(),
                self.container_perms@[page_ptr_1].value().scheduler.wf(),
                self.container_perms@[page_ptr_1].value().scheduler@ =~= Seq::<ThreadPtr>::empty(),
                self.container_perms@[page_ptr_1].value().owned_threads@.finite(),
                self.container_perms@[page_ptr_1].value().owned_threads@ =~= Set::<ThreadPtr>::empty(),
                self.container_perms@[page_ptr_1].value().depth as int =~= old(self).container_perms@[container_ptr].value().depth + 1,
                self.container_perms@[page_ptr_1].value().uppertree_seq@ =~= old(self).container_perms@[container_ptr].value().uppertree_seq@.push(container_ptr),
                self.container_perms@[page_ptr_1].value().subtree_set@ =~= Set::<ContainerPtr>::empty(),

                self.container_perms@[page_ptr_1].value().owned_procs.wf(),        
                self.container_perms@[page_ptr_1].value().scheduler.wf(),        
        {
            let tracked container_perm = self.container_perms.borrow().tracked_borrow(container_ptr);
            let container : &Container = PPtr::<Container>::from_usize(container_ptr).borrow(Tracked(container_perm));
            let quota = container.mem_quota;
            let depth = container.depth;
            let uppertree_seq = container.uppertree_seq;

            let mut container_perm = Tracked(self.container_perms.borrow_mut().tracked_remove(container_ptr));
            container_set_mem_quota(container_ptr,&mut container_perm, quota - init_quota - 3);
            let child_list_node_ref = container_push_child(container_ptr,&mut container_perm, page_ptr_1);
            proof {
                self.container_perms.borrow_mut().tracked_insert(container_ptr, container_perm.get());
            }

            let new_upper_tree_ghost = Ghost(uppertree_seq@.push(container_ptr));
            let (new_container_ptr, container_perm) = 
                page_to_container_tree_version_1(page_ptr_1, page_perm_1, container_ptr, child_list_node_ref, init_quota, ArraySet::<NUM_CPUS>::new(),
                    depth + 1, Ghost(Set::<ContainerPtr>::empty()), new_upper_tree_ghost
                    // depth + 1, Ghost(Set::<ContainerPtr>::empty()), uppertree_seq
                    );
            proof {
                self.container_perms.borrow_mut().tracked_insert(new_container_ptr, container_perm.get());
            }

            assert(
                forall|u_ptr:ContainerPtr|
                #![trigger self.container_perms@[container_ptr].value().uppertree_seq@.contains(u_ptr)]
                self.container_perms@[container_ptr].value().uppertree_seq@.push(container_ptr).contains(u_ptr)
                ==>
                self.container_perms@.dom().contains(u_ptr)
            ) by {
                seq_push_lemma::<ContainerPtr>();
            };
            assert(new_upper_tree_ghost@ =~= self.container_perms@[container_ptr].value().uppertree_seq@.push(container_ptr));
            assert(
                forall|u_ptr:ContainerPtr|
                #![trigger uppertree_seq@.push(container_ptr).contains(u_ptr)]
                uppertree_seq@.push(container_ptr).contains(u_ptr)
                ==>
                self.container_perms@.dom().contains(u_ptr)
            ) by {
                seq_push_lemma::<ContainerPtr>();
            };


            self.upper_tree_add_container1(new_upper_tree_ghost, new_container_ptr);
            // self.upper_tree_add_container(uppertree_seq, new_container_ptr);
            
                assert(uppertree_seq@.contains(container_ptr) == false);
                assert(uppertree_seq@.contains(new_container_ptr) == false);
                assert(uppertree_seq@.push(container_ptr).contains(container_ptr)) by {
                    seq_push_lemma::<ContainerPtr>();
                }
                assert(uppertree_seq@.push(container_ptr).contains(new_container_ptr) == false) by {
                    seq_push_lemma::<ContainerPtr>();
                }
                assert(uppertree_seq@.push(container_ptr).no_duplicates()) by {
                    seq_push_lemma::<ContainerPtr>();
                    seq_push_unique_lemma::<ContainerPtr>();
                }

            assert(self.rest_specs()) by {
                assert(self.container_perms_wf()) by {
                    seq_push_unique_lemma::<ContainerPtr>();
                    seq_push_lemma::<ContainerPtr>();
                    assert(forall|c_ptr:ContainerPtr| 
                        #![trigger self.container_perms@[c_ptr].value().uppertree_seq]
                        self.container_perms@.dom().contains(c_ptr) && c_ptr != new_container_ptr
                        ==> 
                        self.container_perms@[c_ptr].value().uppertree_seq@ =~= old(self).container_perms@[c_ptr].value().uppertree_seq@);
                        assert(forall|c_ptr:ContainerPtr| 
                            #![trigger self.container_perms@.dom().contains(c_ptr)]
                            self.container_perms@.dom().contains(c_ptr) && c_ptr != new_container_ptr
                            ==> 
                            self.container_perms@[c_ptr].value().owned_procs =~= old(self).container_perms@[c_ptr].value().owned_procs
                            &&                
                            self.container_perms@[c_ptr].value().parent =~= old(self).container_perms@[c_ptr].value().parent
                            &&
                            self.container_perms@[c_ptr].value().parent_rev_ptr =~= old(self).container_perms@[c_ptr].value().parent_rev_ptr
                            &&
                            self.container_perms@[c_ptr].value().owned_endpoints =~= old(self).container_perms@[c_ptr].value().owned_endpoints
                            &&
                            self.container_perms@[c_ptr].value().mem_used =~= old(self).container_perms@[c_ptr].value().mem_used
                            &&
                            self.container_perms@[c_ptr].value().owned_cpus =~= old(self).container_perms@[c_ptr].value().owned_cpus
                            &&
                            self.container_perms@[c_ptr].value().scheduler =~= old(self).container_perms@[c_ptr].value().scheduler
                            &&
                            self.container_perms@[c_ptr].value().owned_threads =~= old(self).container_perms@[c_ptr].value().owned_threads
                            &&
                            self.container_perms@[c_ptr].value().depth =~= old(self).container_perms@[c_ptr].value().depth
                            &&
                            self.container_perms@[c_ptr].value().uppertree_seq =~= old(self).container_perms@[c_ptr].value().uppertree_seq
                        );
                        assert(self.container_perms@[new_container_ptr].is_init());
                        assert(self.container_perms@[new_container_ptr].addr() == new_container_ptr);
                        assert(self.container_perms@[new_container_ptr].value().children.wf());
                        assert(self.container_perms@[new_container_ptr].value().children.unique());
                        assert(self.container_perms@[new_container_ptr].value().owned_cpus.wf());
                        assert(self.container_perms@[new_container_ptr].value().scheduler.wf());
                        assert(self.container_perms@[new_container_ptr].value().scheduler.unique());
                        assert(self.container_perms@[new_container_ptr].value().owned_procs.wf());
                        assert(self.container_perms@[new_container_ptr].value().owned_procs.unique());
                        assert(self.container_perms@[new_container_ptr].value().uppertree_seq@.no_duplicates());
                        assert(self.container_perms@[new_container_ptr].value().subtree_set@.finite());
                        assert(self.container_perms@[new_container_ptr].value().uppertree_seq@.len() == self.container_perms@[new_container_ptr].value().depth);
                        assert(forall|c_ptr:ContainerPtr| 
                            #![trigger self.container_perms@[c_ptr].is_init()]
                            self.container_perms@.dom().contains(c_ptr)
                            ==> 
                            self.container_perms@[c_ptr].is_init());
                        assert(forall|c_ptr:ContainerPtr| 
                            #![trigger self.container_perms@[c_ptr].addr()]
                            self.container_perms@.dom().contains(c_ptr)
                            ==>        
                            self.container_perms@[c_ptr].addr() == c_ptr);
                        assert(forall|c_ptr:ContainerPtr| 
                            #![trigger self.container_perms@[c_ptr].value().children.wf()]
                            self.container_perms@.dom().contains(c_ptr)
                            ==> 
                            self.container_perms@[c_ptr].value().children.wf());
                        assert(forall|c_ptr:ContainerPtr| 
                            #![trigger self.container_perms@[c_ptr].value().children.unique()]
                            self.container_perms@.dom().contains(c_ptr)
                            ==> 
                            self.container_perms@[c_ptr].value().children.unique());
                        assert(forall|c_ptr:ContainerPtr| 
                            #![trigger self.container_perms@[c_ptr].value().uppertree_seq@.no_duplicates()]
                            self.container_perms@.dom().contains(c_ptr)
                            ==> 
                            self.container_perms@[c_ptr].value().uppertree_seq@.no_duplicates());
                        assert(forall|c_ptr:ContainerPtr| 
                            #![trigger self.container_perms@.dom().contains(c_ptr), self.container_perms@[c_ptr].value().children@.contains(c_ptr)]
                            self.container_perms@.dom().contains(c_ptr)
                            ==>
                            self.container_perms@[c_ptr].value().children@.contains(c_ptr) == false);
                        assert(forall|c_ptr:ContainerPtr| 
                            #![trigger self.container_perms@[c_ptr].value().subtree_set@.finite()]
                            self.container_perms@.dom().contains(c_ptr)
                            ==>
                            self.container_perms@[c_ptr].value().subtree_set@.finite());
                        assert(forall|c_ptr:ContainerPtr| 
                            #![trigger self.container_perms@[c_ptr].value().uppertree_seq@.len(), self.container_perms@[c_ptr].value().depth]
                            self.container_perms@.dom().contains(c_ptr)
                            ==>
                            self.container_perms@[c_ptr].value().uppertree_seq@.len() == self.container_perms@[c_ptr].value().depth);
                };
                assert(self.container_root_wf()) by {
                };
                assert(self.container_childern_depth_wf()) by {
                    seq_push_lemma::<ContainerPtr>();
                    
                    assert(forall|c_ptr:ContainerPtr| 
                        #![trigger self.container_perms@[c_ptr].value().uppertree_seq@]
                        #![trigger self.container_perms@[c_ptr].value().parent]
                        #![trigger self.container_perms@[c_ptr].value().depth]
                        self.container_perms@.dom().contains(c_ptr) && c_ptr != self.root_container && c_ptr != new_container_ptr
                        ==>
                        self.container_perms@[c_ptr].value().uppertree_seq@ =~= old(self).container_perms@[c_ptr].value().uppertree_seq@
                        &&
                        self.container_perms@[c_ptr].value().parent == old(self).container_perms@[c_ptr].value().parent
                        &&
                        self.container_perms@[c_ptr].value().depth == old(self).container_perms@[c_ptr].value().depth
                    );
                };
                assert(self.container_subtree_set_exclusive())by {
                    seq_push_lemma::<ContainerPtr>();
                    seq_push_unique_lemma::<ContainerPtr>();
                };
            }
            assert(self.tree_wf()) by {
                assert(self.container_subtree_set_wf()) by {
                    seq_push_lemma::<ContainerPtr>();
                    seq_push_unique_lemma::<ContainerPtr>();
                };
                assert(self.container_uppertree_seq_wf()) by {
                    seq_push_lemma::<ContainerPtr>();
                    seq_push_unique_lemma::<ContainerPtr>();
                };
            }

            assert(self.linked_list_wf()) by {
                assert(self.container_childern_list_wf()) by {
                    seq_push_lemma::<ContainerPtr>();
                };
                assert(self.containers_linkedlist_wf()) by {
                    seq_push_lemma::<ContainerPtr>();
                };
            }
        }

        pub fn container_tree_scheduler_pop_head(&mut self, container_ptr:ContainerPtr) -> (ret:(ThreadPtr,SLLIndex))
            requires
                old(self).wf(),
                old(self).container_dom().contains(container_ptr),
                old(self).get_container(container_ptr).scheduler.wf(),
                old(self).get_container(container_ptr).scheduler.unique(),
                old(self).get_container(container_ptr).scheduler.len() != 0,
            ensures
                self.wf(),
                self.container_dom() == old(self).container_dom(),
                forall|c_ptr:ContainerPtr|
                    #![trigger self.get_container(c_ptr)]
                    self.container_dom().contains(c_ptr) && c_ptr != container_ptr
                    ==>
                    self.get_container(c_ptr) == old(self).get_container(c_ptr),
                self.get_container(container_ptr).owned_procs =~= old(self).get_container(container_ptr).owned_procs,
                self.get_container(container_ptr).parent =~= old(self).get_container(container_ptr).parent,
                self.get_container(container_ptr).parent_rev_ptr =~= old(self).get_container(container_ptr).parent_rev_ptr,
                self.get_container(container_ptr).children =~= old(self).get_container(container_ptr).children,
                self.get_container(container_ptr).owned_endpoints =~= old(self).get_container(container_ptr).owned_endpoints,
                self.get_container(container_ptr).mem_quota =~= old(self).get_container(container_ptr).mem_quota,
                self.get_container(container_ptr).mem_used =~= old(self).get_container(container_ptr).mem_used,
                self.get_container(container_ptr).owned_cpus =~= old(self).get_container(container_ptr).owned_cpus,
                // self.get_container(container_ptr).scheduler =~= old(self).get_container(container_ptr).scheduler,
                self.get_container(container_ptr).owned_threads =~= old(self).get_container(container_ptr).owned_threads,
                self.get_container(container_ptr).depth =~= old(self).get_container(container_ptr).depth,
                self.get_container(container_ptr).uppertree_seq =~= old(self).get_container(container_ptr).uppertree_seq,
                self.get_container(container_ptr).subtree_set =~= old(self).get_container(container_ptr).subtree_set,
                
                self.get_container(container_ptr).scheduler.wf(),
                self.get_container(container_ptr).scheduler.unique(),
                self.get_container(container_ptr).scheduler.len() == old(self).get_container(container_ptr).scheduler.len() - 1,
                self.get_container(container_ptr).scheduler@ == old(self).get_container(container_ptr).scheduler@.skip(1),
                ret.0 == old(self).get_container(container_ptr).scheduler@[0],
                old(self).get_container(container_ptr).scheduler.value_list@[0] == ret.1,
                old(self).get_container(container_ptr).scheduler.node_ref_valid(ret.1),
                old(self).get_container(container_ptr).scheduler.node_ref_resolve(ret.1) == ret.0,
                forall|index:SLLIndex|
                    #![trigger old(self).get_container(container_ptr).scheduler.node_ref_valid(index)]
                    #![trigger self.get_container(container_ptr).scheduler.node_ref_valid(index)]
                    old(self).get_container(container_ptr).scheduler.node_ref_valid(index) && index != ret.1 ==> self.get_container(container_ptr).scheduler.node_ref_valid(index),
                forall|index:SLLIndex| 
                    #![trigger old(self).get_container(container_ptr).scheduler.node_ref_valid(index)]
                    #![trigger self.get_container(container_ptr).scheduler.node_ref_resolve(index)]
                    #![trigger old(self).get_container(container_ptr).scheduler.node_ref_resolve(index)]
                    old(self).get_container(container_ptr).scheduler.node_ref_valid(index) && index != ret.1 ==> self.get_container(container_ptr).scheduler.node_ref_resolve(index) == old(self).get_container(container_ptr).scheduler.node_ref_resolve(index),
                forall|index:SLLIndex|
                    #![trigger old(self).get_container(container_ptr).scheduler.node_ref_valid(index)]
                    #![trigger self.get_container(container_ptr).scheduler.node_ref_valid(index)]
                    #![trigger old(self).get_container(container_ptr).scheduler.node_ref_resolve(index)]
                    #![trigger self.get_container(container_ptr).scheduler.node_ref_resolve(index)]
                    old(self).get_container(container_ptr).scheduler.node_ref_valid(index) && old(self).get_container(container_ptr).scheduler.node_ref_resolve(index) != ret.0 
                    ==> 
                    self.get_container(container_ptr).scheduler.node_ref_valid(index)
                    &&
                    self.get_container(container_ptr).scheduler.node_ref_resolve(index) == old(self).get_container(container_ptr).scheduler.node_ref_resolve(index),
        {
            let mut container_perm = Tracked(self.container_perms.borrow_mut().tracked_remove(container_ptr));
            let (ret_thread_ptr, sll) = scheduler_pop_head(container_ptr,&mut container_perm);
            proof {
                self.container_perms.borrow_mut().tracked_insert(container_ptr, container_perm.get());
            }

            assert(self.container_dom() == old(self).container_dom());
            assert(
                forall|c_ptr:ContainerPtr|
                    #![trigger self.get_container(c_ptr)]
                    self.container_dom().contains(c_ptr) && c_ptr != container_ptr
                    ==>
                    self.get_container(c_ptr) == old(self).get_container(c_ptr) 
            );

            assert(forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@.dom().contains(c_ptr)]
                self.container_perms@.dom().contains(c_ptr) && c_ptr != container_ptr
                ==> 
                self.container_perms@[c_ptr].value().owned_procs =~= old(self).container_perms@[c_ptr].value().owned_procs
                &&                
                self.container_perms@[c_ptr].value().parent =~= old(self).container_perms@[c_ptr].value().parent
                &&
                self.container_perms@[c_ptr].value().parent_rev_ptr =~= old(self).container_perms@[c_ptr].value().parent_rev_ptr
                &&
                self.container_perms@[c_ptr].value().children =~= old(self).container_perms@[c_ptr].value().children
                &&
                self.container_perms@[c_ptr].value().owned_endpoints =~= old(self).container_perms@[c_ptr].value().owned_endpoints
                &&
                self.container_perms@[c_ptr].value().mem_used =~= old(self).container_perms@[c_ptr].value().mem_used
                &&
                self.container_perms@[c_ptr].value().owned_cpus =~= old(self).container_perms@[c_ptr].value().owned_cpus
                &&
                self.container_perms@[c_ptr].value().scheduler =~= old(self).container_perms@[c_ptr].value().scheduler
                &&
                self.container_perms@[c_ptr].value().owned_threads =~= old(self).container_perms@[c_ptr].value().owned_threads
                &&
                self.container_perms@[c_ptr].value().depth =~= old(self).container_perms@[c_ptr].value().depth
                &&
                self.container_perms@[c_ptr].value().uppertree_seq =~= old(self).container_perms@[c_ptr].value().uppertree_seq
            );

            assert(self.rest_specs()) by {
                assert(self.container_perms_wf()) by {
                };
                assert(self.container_root_wf()) by {
                };
                assert(self.container_childern_depth_wf()) by {
                };
                assert(self.container_subtree_set_exclusive())by {
                };
            }
            assert(self.tree_wf()) by {
                assert(self.container_subtree_set_wf()) by {
                };
                assert(self.container_uppertree_seq_wf()) by {
                };
            }

            assert(self.linked_list_wf()) by {
                assert(self.container_childern_list_wf()) by {
                };
                assert(self.containers_linkedlist_wf()) by {
                };
            }

            (ret_thread_ptr, sll) 
        }

        pub fn container_tree_set_quota(&mut self, container_ptr:ContainerPtr, new_quota:usize)
            requires
                old(self).wf(),
                old(self).container_dom().contains(container_ptr),
            ensures
                self.wf(),
                old(self).container_dom() =~= self.container_dom(),
                forall|c_ptr:ContainerPtr|
                    #![trigger self.get_container(c_ptr)]
                    self.container_dom().contains(c_ptr) && c_ptr != container_ptr
                    ==>
                    self.get_container(c_ptr) == old(self).get_container(c_ptr),
                self.get_container(container_ptr).owned_procs =~= old(self).get_container(container_ptr).owned_procs,
                self.get_container(container_ptr).parent =~= old(self).get_container(container_ptr).parent,
                self.get_container(container_ptr).parent_rev_ptr =~= old(self).get_container(container_ptr).parent_rev_ptr,
                self.get_container(container_ptr).children =~= old(self).get_container(container_ptr).children,
                self.get_container(container_ptr).owned_endpoints =~= old(self).get_container(container_ptr).owned_endpoints,
                // self.get_container(container_ptr).mem_quota =~= old(self).get_container(container_ptr).mem_quota,
                self.get_container(container_ptr).mem_used =~= old(self).get_container(container_ptr).mem_used,
                self.get_container(container_ptr).owned_cpus =~= old(self).get_container(container_ptr).owned_cpus,
                self.get_container(container_ptr).scheduler =~= old(self).get_container(container_ptr).scheduler,
                self.get_container(container_ptr).owned_threads =~= old(self).get_container(container_ptr).owned_threads,
                self.get_container(container_ptr).depth =~= old(self).get_container(container_ptr).depth,
                self.get_container(container_ptr).uppertree_seq =~= old(self).get_container(container_ptr).uppertree_seq,
                self.get_container(container_ptr).subtree_set =~= old(self).get_container(container_ptr).subtree_set,
                self.get_container(container_ptr).mem_quota =~= new_quota,
        {
            let mut container_perm = Tracked(self.container_perms.borrow_mut().tracked_remove(container_ptr));
            container_set_mem_quota(container_ptr,&mut container_perm, new_quota);
            proof {
                self.container_perms.borrow_mut().tracked_insert(container_ptr, container_perm.get());
            }

            assert(self.container_dom() == old(self).container_dom());
            assert(
                forall|c_ptr:ContainerPtr|
                    #![trigger self.get_container(c_ptr)]
                    self.container_dom().contains(c_ptr) && c_ptr != container_ptr
                    ==>
                    self.get_container(c_ptr) == old(self).get_container(c_ptr) 
            );

            assert(forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@.dom().contains(c_ptr)]
                self.container_perms@.dom().contains(c_ptr) && c_ptr != container_ptr
                ==> 
                self.container_perms@[c_ptr].value().owned_procs =~= old(self).container_perms@[c_ptr].value().owned_procs
                &&                
                self.container_perms@[c_ptr].value().parent =~= old(self).container_perms@[c_ptr].value().parent
                &&
                self.container_perms@[c_ptr].value().parent_rev_ptr =~= old(self).container_perms@[c_ptr].value().parent_rev_ptr
                &&
                self.container_perms@[c_ptr].value().children =~= old(self).container_perms@[c_ptr].value().children
                &&
                self.container_perms@[c_ptr].value().owned_endpoints =~= old(self).container_perms@[c_ptr].value().owned_endpoints
                &&
                self.container_perms@[c_ptr].value().mem_used =~= old(self).container_perms@[c_ptr].value().mem_used
                &&
                self.container_perms@[c_ptr].value().owned_cpus =~= old(self).container_perms@[c_ptr].value().owned_cpus
                &&
                self.container_perms@[c_ptr].value().scheduler =~= old(self).container_perms@[c_ptr].value().scheduler
                &&
                self.container_perms@[c_ptr].value().owned_threads =~= old(self).container_perms@[c_ptr].value().owned_threads
                &&
                self.container_perms@[c_ptr].value().depth =~= old(self).container_perms@[c_ptr].value().depth
                &&
                self.container_perms@[c_ptr].value().uppertree_seq =~= old(self).container_perms@[c_ptr].value().uppertree_seq
            );

            assert(self.rest_specs()) by {
                assert(self.container_perms_wf()) by {
                };
                assert(self.container_root_wf()) by {
                };
                assert(self.container_childern_depth_wf()) by {
                };
                assert(self.container_subtree_set_exclusive())by {
                };
            }
            assert(self.tree_wf()) by {
                assert(self.container_subtree_set_wf()) by {
                };
                assert(self.container_uppertree_seq_wf()) by {
                };
            }

            assert(self.linked_list_wf()) by {
                assert(self.container_childern_list_wf()) by {
                };
                assert(self.containers_linkedlist_wf()) by {
                };
            }
        }

        pub fn container_tree_scheduler_push_thread(&mut self, container_ptr:ContainerPtr, thread_ptr:ThreadPtr) -> (ret:SLLIndex)
            requires
                old(self).wf(),
                old(self).container_dom().contains(container_ptr),
                old(self).get_container(container_ptr).scheduler.wf(),
                old(self).get_container(container_ptr).scheduler.unique(),
                old(self).get_container(container_ptr).scheduler.len() < MAX_CONTAINER_SCHEDULER_LEN,
                old(self).get_container(container_ptr).scheduler@.contains(thread_ptr) == false,
            ensures
                self.wf(),
                old(self).container_dom() =~= self.container_dom(),
                forall|c_ptr:ContainerPtr|
                    #![trigger self.get_container(c_ptr)]
                    self.container_dom().contains(c_ptr) && c_ptr != container_ptr
                    ==>
                    self.get_container(c_ptr) == old(self).get_container(c_ptr),
                self.get_container(container_ptr).owned_procs =~= old(self).get_container(container_ptr).owned_procs,
                self.get_container(container_ptr).parent =~= old(self).get_container(container_ptr).parent,
                self.get_container(container_ptr).parent_rev_ptr =~= old(self).get_container(container_ptr).parent_rev_ptr,
                self.get_container(container_ptr).children =~= old(self).get_container(container_ptr).children,
                self.get_container(container_ptr).owned_endpoints =~= old(self).get_container(container_ptr).owned_endpoints,
                self.get_container(container_ptr).mem_quota =~= old(self).get_container(container_ptr).mem_quota,
                self.get_container(container_ptr).mem_used =~= old(self).get_container(container_ptr).mem_used,
                self.get_container(container_ptr).owned_cpus =~= old(self).get_container(container_ptr).owned_cpus,
                // self.get_container(container_ptr).scheduler =~= old(self).get_container(container_ptr).scheduler,
                self.get_container(container_ptr).owned_threads =~= old(self).get_container(container_ptr).owned_threads,
                self.get_container(container_ptr).depth =~= old(self).get_container(container_ptr).depth,
                self.get_container(container_ptr).uppertree_seq =~= old(self).get_container(container_ptr).uppertree_seq,
                self.get_container(container_ptr).subtree_set =~= old(self).get_container(container_ptr).subtree_set,

                self.get_container(container_ptr).scheduler.wf(),
                self.get_container(container_ptr).scheduler@ == old(self).get_container(container_ptr).scheduler@.push(thread_ptr),
                self.get_container(container_ptr).scheduler.len() == old(self).get_container(container_ptr).scheduler.len() + 1,
                forall|index:SLLIndex|
                    #![trigger old(self).get_container(container_ptr).scheduler.node_ref_valid(index)]
                    #![trigger self.get_container(container_ptr).scheduler.node_ref_valid(index)]
                    old(self).get_container(container_ptr).scheduler.node_ref_valid(index) ==> self.get_container(container_ptr).scheduler.node_ref_valid(index),
                forall|index:SLLIndex| 
                    #![trigger old(self).get_container(container_ptr).scheduler.node_ref_valid(index)]
                    old(self).get_container(container_ptr).scheduler.node_ref_valid(index) ==> index != ret,
                forall|index:SLLIndex| 
                    #![trigger old(self).get_container(container_ptr).scheduler.node_ref_valid(index)]
                    #![trigger self.get_container(container_ptr).scheduler.node_ref_resolve(index)]
                    #![trigger old(self).get_container(container_ptr).scheduler.node_ref_resolve(index)]
                    old(self).get_container(container_ptr).scheduler.node_ref_valid(index) ==> self.get_container(container_ptr).scheduler.node_ref_resolve(index) == old(self).get_container(container_ptr).scheduler.node_ref_resolve(index),
                self.get_container(container_ptr).scheduler.node_ref_valid(ret),
                self.get_container(container_ptr).scheduler.node_ref_resolve(ret) == thread_ptr,
                self.get_container(container_ptr).scheduler.unique(),
        {
            let mut container_perm = Tracked(self.container_perms.borrow_mut().tracked_remove(container_ptr));
            let sll = scheduler_push_thread(container_ptr,&mut container_perm, &thread_ptr);
            proof {
                self.container_perms.borrow_mut().tracked_insert(container_ptr, container_perm.get());
            }

            assert(self.container_dom() == old(self).container_dom());
            assert(
                forall|c_ptr:ContainerPtr|
                    #![trigger self.get_container(c_ptr)]
                    self.container_dom().contains(c_ptr) && c_ptr != container_ptr
                    ==>
                    self.get_container(c_ptr) == old(self).get_container(c_ptr) 
            );

            assert(forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@.dom().contains(c_ptr)]
                self.container_perms@.dom().contains(c_ptr) && c_ptr != container_ptr
                ==> 
                self.container_perms@[c_ptr].value().owned_procs =~= old(self).container_perms@[c_ptr].value().owned_procs
                &&                
                self.container_perms@[c_ptr].value().parent =~= old(self).container_perms@[c_ptr].value().parent
                &&
                self.container_perms@[c_ptr].value().parent_rev_ptr =~= old(self).container_perms@[c_ptr].value().parent_rev_ptr
                &&
                self.container_perms@[c_ptr].value().children =~= old(self).container_perms@[c_ptr].value().children
                &&
                self.container_perms@[c_ptr].value().owned_endpoints =~= old(self).container_perms@[c_ptr].value().owned_endpoints
                &&
                self.container_perms@[c_ptr].value().mem_used =~= old(self).container_perms@[c_ptr].value().mem_used
                &&
                self.container_perms@[c_ptr].value().owned_cpus =~= old(self).container_perms@[c_ptr].value().owned_cpus
                &&
                self.container_perms@[c_ptr].value().scheduler =~= old(self).container_perms@[c_ptr].value().scheduler
                &&
                self.container_perms@[c_ptr].value().owned_threads =~= old(self).container_perms@[c_ptr].value().owned_threads
                &&
                self.container_perms@[c_ptr].value().depth =~= old(self).container_perms@[c_ptr].value().depth
                &&
                self.container_perms@[c_ptr].value().uppertree_seq =~= old(self).container_perms@[c_ptr].value().uppertree_seq
            );

            assert(self.rest_specs()) by {
                assert(self.container_perms_wf()) by {
                };
                assert(self.container_root_wf()) by {
                };
                assert(self.container_childern_depth_wf()) by {
                };
                assert(self.container_subtree_set_exclusive())by {
                };
            }
            assert(self.tree_wf()) by {
                assert(self.container_subtree_set_wf()) by {
                };
                assert(self.container_uppertree_seq_wf()) by {
                };
            }

            assert(self.linked_list_wf()) by {
                assert(self.container_childern_list_wf()) by {
                };
                assert(self.containers_linkedlist_wf()) by {
                };
            }

            sll
        }

        pub fn container_tree_set_owned_threads(&mut self, container_ptr:ContainerPtr, new_owned_threads:Ghost<Set<ThreadPtr>>)
            requires
                old(self).wf(),
                old(self).container_dom().contains(container_ptr),
            ensures
                self.wf(),
                old(self).container_dom() =~= self.container_dom(),
                forall|c_ptr:ContainerPtr|
                    #![trigger self.get_container(c_ptr)]
                    self.container_dom().contains(c_ptr) && c_ptr != container_ptr
                    ==>
                    self.get_container(c_ptr) == old(self).get_container(c_ptr),
                self.get_container(container_ptr).owned_procs =~= old(self).get_container(container_ptr).owned_procs,
                self.get_container(container_ptr).parent =~= old(self).get_container(container_ptr).parent,
                self.get_container(container_ptr).parent_rev_ptr =~= old(self).get_container(container_ptr).parent_rev_ptr,
                self.get_container(container_ptr).children =~= old(self).get_container(container_ptr).children,
                self.get_container(container_ptr).owned_endpoints =~= old(self).get_container(container_ptr).owned_endpoints,
                self.get_container(container_ptr).mem_quota =~= old(self).get_container(container_ptr).mem_quota,
                self.get_container(container_ptr).mem_used =~= old(self).get_container(container_ptr).mem_used,
                self.get_container(container_ptr).owned_cpus =~= old(self).get_container(container_ptr).owned_cpus,
                self.get_container(container_ptr).scheduler =~= old(self).get_container(container_ptr).scheduler,
                // self.get_container(container_ptr).owned_threads =~= old(self).get_container(container_ptr).owned_threads,
                self.get_container(container_ptr).depth =~= old(self).get_container(container_ptr).depth,
                self.get_container(container_ptr).uppertree_seq =~= old(self).get_container(container_ptr).uppertree_seq,
                self.get_container(container_ptr).subtree_set =~= old(self).get_container(container_ptr).subtree_set,
                self.get_container(container_ptr).owned_threads =~= new_owned_threads,
        {
            let mut container_perm = Tracked(self.container_perms.borrow_mut().tracked_remove(container_ptr));
            container_set_owned_threads(container_ptr,&mut container_perm, new_owned_threads);
            proof {
                self.container_perms.borrow_mut().tracked_insert(container_ptr, container_perm.get());
            }

            assert(self.container_dom() == old(self).container_dom());
            assert(
                forall|c_ptr:ContainerPtr|
                    #![trigger self.get_container(c_ptr)]
                    self.container_dom().contains(c_ptr) && c_ptr != container_ptr
                    ==>
                    self.get_container(c_ptr) == old(self).get_container(c_ptr) 
            );

            assert(forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@.dom().contains(c_ptr)]
                self.container_perms@.dom().contains(c_ptr) && c_ptr != container_ptr
                ==> 
                self.container_perms@[c_ptr].value().owned_procs =~= old(self).container_perms@[c_ptr].value().owned_procs
                &&                
                self.container_perms@[c_ptr].value().parent =~= old(self).container_perms@[c_ptr].value().parent
                &&
                self.container_perms@[c_ptr].value().parent_rev_ptr =~= old(self).container_perms@[c_ptr].value().parent_rev_ptr
                &&
                self.container_perms@[c_ptr].value().children =~= old(self).container_perms@[c_ptr].value().children
                &&
                self.container_perms@[c_ptr].value().owned_endpoints =~= old(self).container_perms@[c_ptr].value().owned_endpoints
                &&
                self.container_perms@[c_ptr].value().mem_used =~= old(self).container_perms@[c_ptr].value().mem_used
                &&
                self.container_perms@[c_ptr].value().owned_cpus =~= old(self).container_perms@[c_ptr].value().owned_cpus
                &&
                self.container_perms@[c_ptr].value().scheduler =~= old(self).container_perms@[c_ptr].value().scheduler
                &&
                self.container_perms@[c_ptr].value().owned_threads =~= old(self).container_perms@[c_ptr].value().owned_threads
                &&
                self.container_perms@[c_ptr].value().depth =~= old(self).container_perms@[c_ptr].value().depth
                &&
                self.container_perms@[c_ptr].value().uppertree_seq =~= old(self).container_perms@[c_ptr].value().uppertree_seq
            );

            assert(self.rest_specs()) by {
                assert(self.container_perms_wf()) by {
                };
                assert(self.container_root_wf()) by {
                };
                assert(self.container_childern_depth_wf()) by {
                };
                assert(self.container_subtree_set_exclusive())by {
                };
            }
            assert(self.tree_wf()) by {
                assert(self.container_subtree_set_wf()) by {
                };
                assert(self.container_uppertree_seq_wf()) by {
                };
            }

            assert(self.linked_list_wf()) by {
                assert(self.container_childern_list_wf()) by {
                };
                assert(self.containers_linkedlist_wf()) by {
                };
            }
        }

        pub fn container_tree_push_proc(&mut self, container_ptr:ContainerPtr, proc_ptr:ProcPtr) -> (ret:SLLIndex)
            requires
                old(self).wf(),
                old(self).container_dom().contains(container_ptr),
                old(self).get_container(container_ptr).owned_procs.wf(),
                old(self).get_container(container_ptr).owned_procs.unique(),
                old(self).get_container(container_ptr).owned_procs.len() < CONTAINER_PROC_LIST_LEN,
                old(self).get_container(container_ptr).owned_procs@.contains(proc_ptr) == false,
            ensures
                self.wf(),
                old(self).container_dom() =~= self.container_dom(),
                forall|c_ptr:ContainerPtr|
                    #![trigger self.get_container(c_ptr)]
                    self.container_dom().contains(c_ptr) && c_ptr != container_ptr
                    ==>
                    self.get_container(c_ptr) == old(self).get_container(c_ptr),
                // self.get_container(container_ptr).owned_procs =~= old(self).get_container(container_ptr).owned_procs,
                self.get_container(container_ptr).parent =~= old(self).get_container(container_ptr).parent,
                self.get_container(container_ptr).parent_rev_ptr =~= old(self).get_container(container_ptr).parent_rev_ptr,
                self.get_container(container_ptr).children =~= old(self).get_container(container_ptr).children,
                self.get_container(container_ptr).owned_endpoints =~= old(self).get_container(container_ptr).owned_endpoints,
                self.get_container(container_ptr).mem_quota =~= old(self).get_container(container_ptr).mem_quota,
                self.get_container(container_ptr).mem_used =~= old(self).get_container(container_ptr).mem_used,
                self.get_container(container_ptr).owned_cpus =~= old(self).get_container(container_ptr).owned_cpus,
                self.get_container(container_ptr).scheduler =~= old(self).get_container(container_ptr).scheduler,
                self.get_container(container_ptr).owned_threads =~= old(self).get_container(container_ptr).owned_threads,
                self.get_container(container_ptr).depth =~= old(self).get_container(container_ptr).depth,
                self.get_container(container_ptr).uppertree_seq =~= old(self).get_container(container_ptr).uppertree_seq,
                self.get_container(container_ptr).subtree_set =~= old(self).get_container(container_ptr).subtree_set,

                self.get_container(container_ptr).owned_procs.wf(),
                self.get_container(container_ptr).owned_procs@ == old(self).get_container(container_ptr).owned_procs@.push(proc_ptr),
                self.get_container(container_ptr).owned_procs.len() == old(self).get_container(container_ptr).owned_procs.len() + 1,
                forall|index:SLLIndex|
                    #![trigger old(self).get_container(container_ptr).owned_procs.node_ref_valid(index)]
                    #![trigger self.get_container(container_ptr).owned_procs.node_ref_valid(index)]
                    old(self).get_container(container_ptr).owned_procs.node_ref_valid(index) ==> self.get_container(container_ptr).owned_procs.node_ref_valid(index),
                forall|index:SLLIndex| 
                    #![trigger old(self).get_container(container_ptr).owned_procs.node_ref_valid(index)]
                    old(self).get_container(container_ptr).owned_procs.node_ref_valid(index) ==> index != ret,
                forall|index:SLLIndex| 
                    #![trigger old(self).get_container(container_ptr).owned_procs.node_ref_valid(index)]
                    #![trigger self.get_container(container_ptr).owned_procs.node_ref_resolve(index)]
                    #![trigger old(self).get_container(container_ptr).owned_procs.node_ref_resolve(index)]
                    old(self).get_container(container_ptr).owned_procs.node_ref_valid(index) ==> self.get_container(container_ptr).owned_procs.node_ref_resolve(index) == old(self).get_container(container_ptr).owned_procs.node_ref_resolve(index),
                self.get_container(container_ptr).owned_procs.node_ref_valid(ret),
                self.get_container(container_ptr).owned_procs.node_ref_resolve(ret) == proc_ptr,
                self.get_container(container_ptr).owned_procs.unique(),
        {
            let mut container_perm = Tracked(self.container_perms.borrow_mut().tracked_remove(container_ptr));
            let sll = container_push_proc(container_ptr,&mut container_perm, proc_ptr);
            proof {
                self.container_perms.borrow_mut().tracked_insert(container_ptr, container_perm.get());
            }

            assert(self.container_dom() == old(self).container_dom());
            assert(
                forall|c_ptr:ContainerPtr|
                    #![trigger self.get_container(c_ptr)]
                    self.container_dom().contains(c_ptr) && c_ptr != container_ptr
                    ==>
                    self.get_container(c_ptr) == old(self).get_container(c_ptr) 
            );

            assert(forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@.dom().contains(c_ptr)]
                self.container_perms@.dom().contains(c_ptr) && c_ptr != container_ptr
                ==> 
                self.container_perms@[c_ptr].value().owned_procs =~= old(self).container_perms@[c_ptr].value().owned_procs
                &&                
                self.container_perms@[c_ptr].value().parent =~= old(self).container_perms@[c_ptr].value().parent
                &&
                self.container_perms@[c_ptr].value().parent_rev_ptr =~= old(self).container_perms@[c_ptr].value().parent_rev_ptr
                &&
                self.container_perms@[c_ptr].value().children =~= old(self).container_perms@[c_ptr].value().children
                &&
                self.container_perms@[c_ptr].value().owned_endpoints =~= old(self).container_perms@[c_ptr].value().owned_endpoints
                &&
                self.container_perms@[c_ptr].value().mem_used =~= old(self).container_perms@[c_ptr].value().mem_used
                &&
                self.container_perms@[c_ptr].value().owned_cpus =~= old(self).container_perms@[c_ptr].value().owned_cpus
                &&
                self.container_perms@[c_ptr].value().scheduler =~= old(self).container_perms@[c_ptr].value().scheduler
                &&
                self.container_perms@[c_ptr].value().owned_threads =~= old(self).container_perms@[c_ptr].value().owned_threads
                &&
                self.container_perms@[c_ptr].value().depth =~= old(self).container_perms@[c_ptr].value().depth
                &&
                self.container_perms@[c_ptr].value().uppertree_seq =~= old(self).container_perms@[c_ptr].value().uppertree_seq
            );

            assert(self.rest_specs()) by {
                assert(self.container_perms_wf()) by {
                };
                assert(self.container_root_wf()) by {
                };
                assert(self.container_childern_depth_wf()) by {
                };
                assert(self.container_subtree_set_exclusive())by {
                };
            }
            assert(self.tree_wf()) by {
                assert(self.container_subtree_set_wf()) by {
                };
                assert(self.container_uppertree_seq_wf()) by {
                };
            }

            assert(self.linked_list_wf()) by {
                assert(self.container_childern_list_wf()) by {
                };
                assert(self.containers_linkedlist_wf()) by {
                };
            }

            sll
        }

        pub fn container_tree_push_endpoint(&mut self, container_ptr:ContainerPtr, endpoint_ptr:EndpointPtr) -> (ret:SLLIndex)
            requires
                old(self).wf(),
                old(self).container_dom().contains(container_ptr),
                old(self).get_container(container_ptr).owned_endpoints.wf(),
                old(self).get_container(container_ptr).owned_endpoints.unique(),
                old(self).get_container(container_ptr).owned_endpoints.len() < CONTAINER_ENDPOINT_LIST_LEN,
                old(self).get_container(container_ptr).owned_endpoints@.contains(endpoint_ptr) == false,
            ensures
                self.wf(),
                old(self).container_dom() =~= self.container_dom(),
                forall|c_ptr:ContainerPtr|
                    #![trigger self.get_container(c_ptr)]
                    self.container_dom().contains(c_ptr) && c_ptr != container_ptr
                    ==>
                    self.get_container(c_ptr) == old(self).get_container(c_ptr),
                self.get_container(container_ptr).owned_procs =~= old(self).get_container(container_ptr).owned_procs,
                self.get_container(container_ptr).parent =~= old(self).get_container(container_ptr).parent,
                self.get_container(container_ptr).parent_rev_ptr =~= old(self).get_container(container_ptr).parent_rev_ptr,
                self.get_container(container_ptr).children =~= old(self).get_container(container_ptr).children,
                // self.get_container(container_ptr).owned_endpoints =~= old(self).get_container(container_ptr).owned_endpoints,
                self.get_container(container_ptr).mem_quota =~= old(self).get_container(container_ptr).mem_quota,
                self.get_container(container_ptr).mem_used =~= old(self).get_container(container_ptr).mem_used,
                self.get_container(container_ptr).owned_cpus =~= old(self).get_container(container_ptr).owned_cpus,
                self.get_container(container_ptr).scheduler =~= old(self).get_container(container_ptr).scheduler,
                self.get_container(container_ptr).owned_threads =~= old(self).get_container(container_ptr).owned_threads,
                self.get_container(container_ptr).depth =~= old(self).get_container(container_ptr).depth,
                self.get_container(container_ptr).uppertree_seq =~= old(self).get_container(container_ptr).uppertree_seq,
                self.get_container(container_ptr).subtree_set =~= old(self).get_container(container_ptr).subtree_set,

                self.get_container(container_ptr).owned_endpoints.wf(),
                self.get_container(container_ptr).owned_endpoints@ == old(self).get_container(container_ptr).owned_endpoints@.push(endpoint_ptr),
                self.get_container(container_ptr).owned_endpoints.len() == old(self).get_container(container_ptr).owned_endpoints.len() + 1,
                forall|index:SLLIndex|
                    #![trigger old(self).get_container(container_ptr).owned_endpoints.node_ref_valid(index)]
                    #![trigger self.get_container(container_ptr).owned_endpoints.node_ref_valid(index)]
                    old(self).get_container(container_ptr).owned_endpoints.node_ref_valid(index) ==> self.get_container(container_ptr).owned_endpoints.node_ref_valid(index),
                forall|index:SLLIndex| 
                    #![trigger old(self).get_container(container_ptr).owned_endpoints.node_ref_valid(index)]
                    old(self).get_container(container_ptr).owned_endpoints.node_ref_valid(index) ==> index != ret,
                forall|index:SLLIndex| 
                    #![trigger old(self).get_container(container_ptr).owned_endpoints.node_ref_valid(index)]
                    #![trigger self.get_container(container_ptr).owned_endpoints.node_ref_resolve(index)]
                    #![trigger old(self).get_container(container_ptr).owned_endpoints.node_ref_resolve(index)]
                    old(self).get_container(container_ptr).owned_endpoints.node_ref_valid(index) ==> self.get_container(container_ptr).owned_endpoints.node_ref_resolve(index) == old(self).get_container(container_ptr).owned_endpoints.node_ref_resolve(index),
                self.get_container(container_ptr).owned_endpoints.node_ref_valid(ret),
                self.get_container(container_ptr).owned_endpoints.node_ref_resolve(ret) == endpoint_ptr,
                self.get_container(container_ptr).owned_endpoints.unique(),
        {
            let mut container_perm = Tracked(self.container_perms.borrow_mut().tracked_remove(container_ptr));
            let sll = container_push_endpoint(container_ptr,&mut container_perm, endpoint_ptr);
            proof {
                self.container_perms.borrow_mut().tracked_insert(container_ptr, container_perm.get());
            }

            assert(self.container_dom() == old(self).container_dom());
            assert(
                forall|c_ptr:ContainerPtr|
                    #![trigger self.get_container(c_ptr)]
                    self.container_dom().contains(c_ptr) && c_ptr != container_ptr
                    ==>
                    self.get_container(c_ptr) == old(self).get_container(c_ptr) 
            );

            assert(forall|c_ptr:ContainerPtr| 
                #![trigger self.container_perms@.dom().contains(c_ptr)]
                self.container_perms@.dom().contains(c_ptr) && c_ptr != container_ptr
                ==> 
                self.container_perms@[c_ptr].value().owned_procs =~= old(self).container_perms@[c_ptr].value().owned_procs
                &&                
                self.container_perms@[c_ptr].value().parent =~= old(self).container_perms@[c_ptr].value().parent
                &&
                self.container_perms@[c_ptr].value().parent_rev_ptr =~= old(self).container_perms@[c_ptr].value().parent_rev_ptr
                &&
                self.container_perms@[c_ptr].value().children =~= old(self).container_perms@[c_ptr].value().children
                &&
                self.container_perms@[c_ptr].value().owned_endpoints =~= old(self).container_perms@[c_ptr].value().owned_endpoints
                &&
                self.container_perms@[c_ptr].value().mem_used =~= old(self).container_perms@[c_ptr].value().mem_used
                &&
                self.container_perms@[c_ptr].value().owned_cpus =~= old(self).container_perms@[c_ptr].value().owned_cpus
                &&
                self.container_perms@[c_ptr].value().scheduler =~= old(self).container_perms@[c_ptr].value().scheduler
                &&
                self.container_perms@[c_ptr].value().owned_threads =~= old(self).container_perms@[c_ptr].value().owned_threads
                &&
                self.container_perms@[c_ptr].value().depth =~= old(self).container_perms@[c_ptr].value().depth
                &&
                self.container_perms@[c_ptr].value().uppertree_seq =~= old(self).container_perms@[c_ptr].value().uppertree_seq
            );

            assert(self.rest_specs()) by {
                assert(self.container_perms_wf()) by {
                };
                assert(self.container_root_wf()) by {
                };
                assert(self.container_childern_depth_wf()) by {
                };
                assert(self.container_subtree_set_exclusive())by {
                };
            }
            assert(self.tree_wf()) by {
                assert(self.container_subtree_set_wf()) by {
                };
                assert(self.container_uppertree_seq_wf()) by {
                };
            }

            assert(self.linked_list_wf()) by {
                assert(self.container_childern_list_wf()) by {
                };
                assert(self.containers_linkedlist_wf()) by {
                };
            }

            sll
        }
    }
}

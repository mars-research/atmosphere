use vstd::prelude::*;

verus!{


use crate::define::*;
use crate::page_arena::{PageArena, PageElementPtr, PageMetadataPtr};

type Arena<T> = PageArena<Node<T>, PageNode>;
type NodePtr<T> = PageElementPtr<Node<T>>;
type PageNodePtr = PageMetadataPtr<PageNode>;


/// A reference to a node in a linked list.
pub struct NodeRef<T>(NodePtr<T>);

/// A node in the value/free list.
struct Node<T> {
    value: T,
    prev: Option<NodePtr<T>>,
    next: Option<NodePtr<T>>,
}

/// A node in the page list.
///
/// This is stored as the per-page metadata in PageArena.
struct PageNode {
    next: Option<PageNodePtr>,
}

/// A doubly linked list holding sized values.
pub struct LinkedList<T: Default> {
    ptrs: Ghost<Seq<NodePtr<T>>>,
    head: Option<NodePtr<T>>,
    tail: Option<NodePtr<T>>,

    free_ptrs: Ghost<Seq<NodePtr<T>>>,
    free_head: Option<NodePtr<T>>,

    page_ptrs: Ghost<Seq<PageNodePtr>>,
    page_head: Option<PageNodePtr>,

    perms: Tracked<Map<int, Arena<T>>>,
}

impl<T: Default> LinkedList<T> {

    //start of tmp
    pub closed spec fn view(&self) -> Seq<T>
        recommends self.wf()
    {
        Seq::new(self.ptrs@.len(), |i: int| {
            let ptr = self.ptrs@[i];
            let arena: &Arena<T> = &self.perms@[ptr.page_pptr().id()];
            arena.value_at(ptr.index()).value
        })
    }

    pub closed spec fn unique(&self) -> bool
    {
        forall|i:int, j:int| i != j && 0<=i<self@.len() && 0<=j<self@.len() ==> self@[i] != self@[j]
    }

    pub closed spec fn len(&self) -> nat
    {
        self.ptrs@.len()
    }

    pub closed spec fn page_closure(&self) -> Set<PagePtr>
    {
        Set::empty()
    }

    pub closed spec fn node_ref_valid(&self, nr: &NodeRef<T>) -> bool
    {
        arbitrary()
    }

    pub closed spec fn node_ref_resolve(&self, nr: &NodeRef<T>) -> &T
    {
        arbitrary()
    }

    pub closed spec fn capacity(&self) -> nat {
        self.free_ptrs@.len()
    }

    //end of tmp
    //@Lukas: just change to whatever you want

    // *********************
    // API *****************
    // *********************

    pub fn new() -> (ret: Self)
        ensures ret.wf()
    {
        Self {
            ptrs: Ghost(Seq::empty()),
            head: None,
            tail: None,

            free_ptrs: Ghost(Seq::empty()),
            free_head: None,

            page_ptrs: Ghost(Seq::empty()),
            page_head: None,

            perms: Tracked(Map::tracked_empty()),
        }
    }

    fn pop_free(&mut self) -> (res: NodePtr<T>)
        requires
            old(self).wf(),
            old(self).capacity() > 0,
        ensures
            self.wf(),
            self.capacity() == old(self).capacity() - 1,
            self.len() == old(self).len(),
            self.perms@.dom().contains(res.page_base()),
    {
        proof {
            // Assert that free list is well formed
            assert(Self::wf_free_head(self.free_head, self.free_ptrs@));
            assert(Self::wf_free_ptrs(self.free_ptrs@, self.perms@));

            assert(Self::node_ptrs_eq(self.free_head, Some(self.free_ptrs@[0])));
            assert(Self::wf_free_ptr(self.free_ptrs@, 0, self.perms@));

            let index = self.free_ptrs@[0].index();
            let base = self.free_ptrs@[0].page_base();

            assert(self.perms@.dom().contains(base));
            assert(Self::node_ptrs_eq(self.perms@[base].value_at(index).next, Self::node_next_of(self.free_ptrs@, 0)));
            assert(Self::wf_free_head(Self::node_next_of(self.free_ptrs@, 0), self.free_ptrs@.skip(1)));
        }

        // Retrieve current free_head
        let ptr = self.free_head.as_ref().unwrap().clone();

        {
            let ptr_ref: &NodePtr<T> = self.free_head.as_ref().unwrap();

            assert(ptr.same_ptr(ptr_ref));

            assert(ptr_ref.same_ptr(&self.free_ptrs@[0]));
            assert(ptr_ref.page_base() == self.free_ptrs@[0].page_base());

            assert(self.perms@.dom().contains(self.free_ptrs@[0].page_base()));
            assert(self.perms@.dom().contains(ptr_ref.page_base()));
        }

        assert(self.perms@.dom().contains(ptr.page_base()));

        // Use lemma to show that after removing the permission, the map is still well formed
        proof {
            Self::lemma_remove_wf_perms(self.perms@, ptr.page_base());
        }

        // Get permission
        // let tracked mut perm: Arena<T> = (self.perms.borrow_mut()).tracked_remove(ptr.page_base());
        let tracked perm: &Arena<T> = self.perms.borrow().tracked_borrow(ptr.page_base());

        assert(Self::wf_perms(self.perms@));
        assert(forall|i: int| self.perms@.dom().contains(i) ==> #[trigger] Self::wf_perm(i, self.perms@.index(i)));
        assert(Self::wf_perm(ptr.page_base(), *perm));
        assert(perm.wf());
        assert(perm.page_base() == ptr.page_base());
        assert(perm.has_element(&ptr));

        // Node
        let node: &Node<T> = ptr.borrow::<PageNode>(Tracked(&perm));
        assert(Self::node_ptrs_eq(node.next, Self::node_next_of(self.free_ptrs@, 0)));

        match &node.next {
            Some(p) => self.free_head = Some(p.clone()),
            None => self.free_head = None,
        }

        assert(Self::node_ptrs_eq(self.free_head, Self::node_next_of(self.free_ptrs@, 0)));

        proof {
            // self.perms.borrow_mut().tracked_insert(ptr.page_base(), perm);
        }

        assert(Self::wf_free_head(self.free_head, self.free_ptrs@.skip(1)));
        assert(Self::wf_free_ptrs(self.free_ptrs@, self.perms@));

        // Remove first element of free pointer map
        proof {
            Self::lemma_remove_wf_free_ptrs(self.free_ptrs@, self.perms@);
            self.free_ptrs@ = self.free_ptrs@.skip(1);
            assert(Self::wf_free_ptrs(self.free_ptrs@, self.perms@));
            assert(Self::wf_free_head(self.free_head, self.free_ptrs@));
        }

        return ptr;
    }

    // fn push_back(&mut self, v: T) 
    //     requires
    //         old(self).wf(),
    //         old(self).capacity() > 0,
    //     ensures
    //         // self.wf(),
    //         self.capacity() == old(self).capacity() - 1,
    //         self.len() == old(self).len() + 1,
    //         v == self.perms@[self.ptrs@.last().page_base()].value_at(self.ptrs@.last().index()).value
    // {
    //     proof {
    //         // Assert that free list is well formed
    //         assert(Self::wf_free_head(self.free_head, self.free_ptrs@));
    //         assert(Self::wf_free_ptrs(self.free_ptrs@, self.perms@));

    //         assert(self.free_head == Some(self.free_ptrs@[0]));
    //         assert(Self::wf_free_ptr(self.free_ptrs@, 0, self.perms@));

    //         let index = self.free_ptrs@[0].index();
    //         let base = self.free_ptrs@[0].page_base();

    //         assert(self.perms@.dom().contains(base));
    //         assert(self.perms@[base].value_at(index).next == Self::node_next_of(self.free_ptrs@, 0));

    //         assert(Self::wf_free_head(Self::node_next_of(self.free_ptrs@, 0), self.free_ptrs@.skip(1)));
    //     }
        
    //     // Retrieve current free_head
    //     let ptr = self.free_head.as_ref().unwrap().clone();

    //     {
    //         let ptr_ref: &NodePtr<T> = self.free_head.as_ref().unwrap();

    //         assert(ptr.same_ptr(ptr_ref));

    //         assert(ptr_ref.same_ptr(&self.free_ptrs@[0]));
    //         assert(ptr_ref.page_base() == self.free_ptrs@[0].page_base());

    //         assert(self.perms@.dom().contains(self.free_ptrs@[0].page_base()));
    //         assert(self.perms@.dom().contains(ptr_ref.page_base()));
    //     }

    //     assert(self.perms@.dom().contains(ptr.page_base()));

    //     // Remove first element of free pointer map
    //     proof {
    //         Self::lemma_remove_wf_free_ptrs(self.free_ptrs@, self.perms@);
    //         self.free_ptrs@ = self.free_ptrs@.skip(1);
    //         assert(Self::wf_free_ptrs(self.free_ptrs@, self.perms@));
    //     }

    //     // Update 

        
        
    //     // Assert that the current perms map is wf
    //     assert(Self::wf_perms(self.perms@));
    //     // So ptr.page_base() is wf
    //     assert(Self::wf_perm(ptr.page_base(), self.perms@[ptr.page_base()]));
        
    //     // Use lemma to show that after removing the permission, the map is still well formed
    //     proof {
    //         Self::lemma_remove_wf_perms(self.perms@, ptr.page_base());
    //     }

    //     // Get permission
    //     let tracked mut perm: Arena<T> = (self.perms.borrow_mut()).tracked_remove(ptr.page_base());

    //     assert(Self::wf_perms(self.perms@));
    //     assert(perm.wf());
    //     assert(perm.page_base() == ptr.page_base());
    //     assert(perm.has_element(&ptr));
        
    //     // Update free ptrs linked list and model sequence
    //     let node: &Node<T> = ptr.borrow::<PageNode>(Tracked(&perm));

    //     match &node.next {
    //         Some(p) => self.free_head = Some(p.clone()),
    //         None => self.free_head = None,
    //     }

    //     assert(self.free_head.is_Some() ==> self.free_ptrs@.len() > 0);
    //     assert(self.free_head.is_None() ==> self.free_ptrs@.len() == 0);

    //     // assert(self.free_head.is_Some() ==> self.free_ptrs@[0] == self.free_head.unwrap());


    //     // assert(Self::wf_free_head(self.free_head, self.free_ptrs@));


    //     // Update contents of this ptr
    //     let tail = match &self.tail {
    //         Some(p) => Some(p.clone()),
    //         None => None,
    //     };

    //     ptr.put::<PageNode>(Tracked(&mut perm), Node { value: v, prev: tail, next: None });

    //     assert(Self::wf_perm(ptr.page_base(), perm));

    //     proof {
    //         Self::lemma_insert_wf_perms(self.perms@, ptr.page_base(), perm);
    //         (self.perms.borrow_mut()).tracked_insert(ptr.page_base(), perm);
    //     }

    //     assert(Self::wf_perms(self.perms@));

    //     // Update ptrs linked list and model sequence
    //     if self.tail.is_none() {
    //         self.head = Some(ptr.clone());
    //     }
    //     self.tail = Some(ptr.clone());

    //     let cloned_ptr = ptr.clone();

    //     proof {
    //         self.ptrs@ = self.ptrs@.push(cloned_ptr);
    //     }
    // }

    // ********************
    // Spec helpers *******
    // ********************

    spec fn page_next_of(ptrs: Seq<PageNodePtr>, i: int) -> Option<PageNodePtr> {
        if i + 1 == ptrs.len() {
            None::<PageNodePtr>
        } else {
            Some(ptrs[i + 1])
        }
    }

    spec fn node_next_of(ptrs: Seq<NodePtr<T>>, i: int) -> Option<NodePtr<T>> {
        if i + 1 == ptrs.len() {
            None::<NodePtr<T>>
        } else {
            Some(ptrs[i + 1int])
        }
    }

    spec fn node_prev_of(ptrs: Seq<NodePtr<T>>, i: int) -> Option<NodePtr<T>> {
        if i == 0 {
            None::<NodePtr<T>>
        } else {
            Some(ptrs[i - 1])
        }
    }

    // ********************
    // Lemmas *************
    // ********************

    proof fn lemma_remove_wf_perms(perms: Map<int, Arena<T>>, key: int) 
        requires 
            Self::wf_perms(perms)
        ensures
            Self::wf_perms(perms.remove(key))
    {
    }

    proof fn lemma_insert_wf_perms(perms: Map<int, Arena<T>>, key: int, perm: Arena<T>) 
        requires 
            Self::wf_perms(perms),
            Self::wf_perm(key, perm),
        ensures
            Self::wf_perms(perms.insert(key, perm))
    {
    }

    // *************************
    // Permission Map

    // Ensures the perm map is valid at all times
    spec fn wf_perms(perms: Map<int, Arena<T>>) -> bool {
        &&& forall|i: int| perms.dom().contains(i) ==> #[trigger] Self::wf_perm(i, perms[i])
    }

    // Checks that for a given pointer, there is a permission corresponding to that page, and that the permission is well formed
    spec fn wf_perm(ptr: int, perm: Arena<T>) -> bool {
        // Key matches arena pointed to
        &&& ptr == perm.page_base()
        &&& perm.wf()
    }

    // *************************
    // Free Ptrs

    spec fn wf_free_ptrs(ptrs: Seq<NodePtr<T>>, perms: Map<int, Arena<T>>) -> bool {
        forall|i: int| 0 <= i < ptrs.len() ==> #[trigger] Self::wf_free_ptr(ptrs, i, perms)
    }

    spec fn wf_free_ptr(ptrs: Seq<NodePtr<T>>, i: int, perms: Map<int, Arena<T>>) -> bool {
        let ptr: NodePtr<T> = ptrs[i];
        let base = ptr.page_base();

        perms.dom().contains(base)
        && perms[base].has_element(&ptr)
        && Self::node_ptrs_eq((perms[base].value_at(ptr.index()).next), Self::node_next_of(ptrs, i))
    }

    proof fn lemma_remove_wf_free_ptrs(ptrs: Seq<NodePtr<T>>, perms: Map<int, Arena<T>>)
        requires
            ptrs.len() > 0,
            Self::wf_perms(perms),
            Self::wf_free_ptrs(ptrs, perms),
        ensures
            Self::wf_free_ptrs(ptrs.skip(1), perms),
    {
        assert(forall|i: int| 0 <= i < ptrs.len() ==> #[trigger] Self::wf_free_ptr(ptrs, i, perms));

        assert forall|i: int| 1 <= i < ptrs.len() implies #[trigger] Self::wf_free_ptr(ptrs.skip(1), i - 1, perms) by {
            assert(Self::wf_free_ptr(ptrs, i, perms));

            Self::lemma_wf_free_ptr_chain(ptrs, i, perms);
        }

        assert(ptrs.skip(1).len() == ptrs.len() - 1);

        assert forall|i: int| 0 <= i < ptrs.skip(1).len() implies #[trigger] Self::wf_free_ptr(ptrs.skip(1), i, perms) by {
            let j = i + 1;

            assert(1 <= j < ptrs.len());
            assert(Self::wf_free_ptr(ptrs.skip(1), j - 1, perms));
            assert(Self::wf_free_ptr(ptrs.skip(1), i, perms));
        }

        // assert(forall|i: int| 0 <= i < ptrs.skip(1).len() ==> #[trigger] Self::wf_free_ptr(ptrs.skip(1), i, perms))
    }

    proof fn lemma_wf_free_ptr_chain(ptrs: Seq<NodePtr<T>>, i: int, perms: Map<int, Arena<T>>) 
        requires 
            1 <= i < ptrs.len(),
            Self::wf_perms(perms),
            Self::wf_free_ptr(ptrs, i, perms),
        ensures
            Self::wf_free_ptr(ptrs.skip(1), i - 1, perms)
    {
        vstd::seq::axiom_seq_subrange_index(ptrs, 1, ptrs.len() as int, i - 1);
        assert(ptrs[i] == ptrs.skip(1)[i - 1]);
        assert(ptrs[i].index() == ptrs.skip(1)[i - 1].index());
        assert(Self::node_ptrs_eq(Self::node_next_of(ptrs, i), Self::node_next_of(ptrs.skip(1), i - 1)));
    }

    spec fn wf_free_head(head: Option<NodePtr<T>>, ptrs: Seq<NodePtr<T>>) -> bool {
        if ptrs.len() == 0 {
            head == None::<NodePtr<T>>
        } else {
            Self::node_ptrs_eq(head, Some(ptrs[0]))
        }
    }

    proof fn lemma_remove_wf_free_head_trivial(ptrs: Seq<NodePtr<T>>) 
        requires
            ptrs.len() == 1,
        ensures
            Self::wf_free_head(None, ptrs.skip(1))
    {
    }

    proof fn lemma_remove_wf_free_head(ptrs: Seq<NodePtr<T>>) 
        requires
            ptrs.len() > 1,
        ensures
            Self::wf_free_head(Some(ptrs.skip(1)[0]), ptrs.skip(1))
    {
    }

    // ********************
    // Well Formed Spec ***
    // ********************

    pub closed spec fn wf(&self) -> bool {
        &&& Self::wf_perms(self.perms@) 
        &&& Self::wf_free_head(self.free_head, self.free_ptrs@)
        &&& Self::wf_free_ptrs(self.free_ptrs@, self.perms@)
    }

    spec fn node_ptrs_eq(a: Option<NodePtr<T>>, b: Option<NodePtr<T>>) -> bool {
        if a.is_none() && b.is_none() {
            true
        } else if (a.is_none() && b.is_some()) || (a.is_some() && b.is_none()) {
            false
        } else {
            a.unwrap().same_ptr(&b.unwrap())
        }
    }

    // // Ensures each ptr is valid
    // spec fn wf_ptrs(&self) -> bool {
    //     self.wf_head() && self.wf_tail() && forall|i: nat| 0 <= i < self.ptrs@.len() ==> #[trigger] self.wf_ptr(i)
    // }

    // spec fn wf_ptr(&self, i: nat) -> bool {
    //     let ptr: &NodePtr<T> = &self.ptrs@[i as int];
    //     let arena: &Arena<T> = &self.perms@[ptr.page_base()];
    //     let node = arena.value_at(ptr.index());
    //     node.prev == self.prev_of(i) && node.next == self.next_of(i)  
    // }

    // spec fn wf_head(&self) -> bool {
    //     if self.ptrs@.len() == 0 {
    //         self.head == None::<NodePtr<T>>
    //     } else {
    //         self.head == Some(self.ptrs@[0])
    //     }
    // }

    // spec fn wf_tail(&self) -> bool {
    //     if self.ptrs@.len() == 0 {
    //         self.tail == None::<NodePtr<T>>
    //     } else {
    //         self.tail == Some(self.ptrs@[self.ptrs@.len() - 1])
    //     }
    // }

    // spec fn wf_page_ptrs(&self) -> bool {
    //     self.wf_page_head() && forall |i: nat| 0 <= i < self.page_ptrs@.len() ==> #[trigger] self.wf_page_ptr(i)
    // }

    // spec fn wf_page_ptr(&self, i: nat) -> bool {
    //     let ptr: &PageNodePtr = &self.page_ptrs@[i as int];
    //     let arena: &Arena<T> = &self.perms@[ptr.page_base()];
    //     arena.metadata().next == self.page_next_of(i)     
    // }

    // spec fn wf_page_head(&self) -> bool {
    //     if self.page_ptrs@.len() == 0 {
    //         self.page_head == None::<PageNodePtr>
    //     } else {
    //         self.page_head == Some(self.page_ptrs@[0])
    //     }
    // }
}

}
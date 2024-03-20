use vstd::prelude::*;

verus!{


use crate::define::*;
use crate::page_arena::{PageArena, PageElementPtr, PageMetadataPtr};

pub type Arena<T> = PageArena<Node<T>, PageNode>;
pub type NodePtr<T> = PageElementPtr<Node<T>>;
pub type PageNodePtr = PageMetadataPtr<PageNode>;


/// Checks if two optional points are the same.
spec fn same_ptr_opt<T>(a: Option<NodePtr<T>>, b: Option<NodePtr<T>>) -> bool 
{
    if a.is_none() != b.is_none() {
        false
    } else if a.is_none() && b.is_none() {
        true
    } else {
        a.unwrap().same_ptr(&b.unwrap())
    }
}

/// A reference to a node in a linked list.
pub struct NodeRef<T>(NodePtr<T>);

/// A node in the value/free list.
pub struct Node<T> {
    value: T,
    prev: Option<NodePtr<T>>,
    next: Option<NodePtr<T>>,
}

/// A node in the page list.
///
/// This is stored as the per-page metadata in PageArena.
pub struct PageNode {
    next: Option<PageNodePtr>,
}

pub struct Permissions<T> {
    perms: Tracked<Map<int, Arena<T>>>,
    // closure: Ghost<Set<NodePtr<T>>>,
}

impl<T> Permissions<T> {
    /// Constructs a new permissions map
    pub fn new() -> (res: Self) 
        ensures
            res.wf()

    {
        Self { perms: Tracked(Map::tracked_empty()) }
    }

    // ****************************
    // Well formed

    // Ensures the perm map is valid at all times
    pub closed spec fn wf(&self) -> bool {
        &&& forall|i: int| self.perms@.dom().contains(i) ==> #[trigger] Self::wf_perm(i, self.perms@[i])
    }

    // Checks that for a given pointer, there is a permission corresponding to that page, and that the permission is well formed
    spec fn wf_perm(ptr: int, perm: Arena<T>) -> bool {
        // Key matches arena pointed to
        &&& ptr == perm.page_base()
        &&& perm.wf()
    }

    // ****************************
    // Spec

    /// The given node pointer is owned by this map.
    pub closed spec fn owns(&self, ptr: NodePtr<T>) -> bool {
        &&& self.perms@.dom().contains(ptr.page_base())
        &&& self.perms@[ptr.page_base()].has_element(&ptr)
    }

    /// All node pointers in the sequence are owned by this map.
    pub closed spec fn owns_seq(&self, ptrs: Seq<NodePtr<T>>) -> bool {
        forall|i: int| 0 <= i < ptrs.len() ==> #[trigger] self.owns(ptrs[i]) 
    }

    /// Retrieves the model node at the given ptr.
    pub closed spec fn node(&self, ptr: NodePtr<T>) -> Node<T>
        recommends
            self.owns(ptr)
    {
        *self.perms@[ptr.page_base()].value_at(ptr.index())
    }

    /// Gets the value of a node from a pointer.
    fn value(&self, ptr: &NodePtr<T>) -> (res: &T) 
        requires
            self.wf(),
            self.owns(*ptr),
        ensures
            self.node(*ptr).value == *res,
    {
        let tracked perm: &Arena<T> = self.perms.borrow().tracked_borrow(ptr.page_base());

        assert(self.wf());
        assert(Self::wf_perm(ptr.page_base(), *perm));
        assert(perm.wf());

        // Get Node
        &ptr.borrow::<PageNode>(Tracked(&perm)).value
    }

    /// Stores a value at the given pointer.
    /// 
    /// This has to be a trusted function until we figure out an API for `put`ing individual fields.
    #[verifier(external_body)]
    fn put_value(&mut self, ptr: &NodePtr<T>, value: T) 
        requires
            old(self).wf(),
            old(self).owns(*ptr),
        ensures
            self.wf(),
            self.owns(*ptr),
            self.node(*ptr).value == value,
            same_ptr_opt(self.node(*ptr).next, old(self).node(*ptr).next),
            same_ptr_opt(self.node(*ptr).prev, old(self).node(*ptr).prev),
    {
        unsafe {
            let slice = core::slice::from_raw_parts_mut(ptr.page_pptr_concrete().to_usize() as *mut Node<T>, Arena::<T>::capacity());
            slice[ptr.index_concrete()].value = value;
        }
    }

    fn next(&self, ptr: &NodePtr<T>) -> (res: Option<NodePtr<T>>)
        requires 
            self.wf(),
            self.owns(*ptr),
        ensures
            same_ptr_opt(self.node(*ptr).next, res)
    {
        let tracked perm: &Arena<T> = self.perms.borrow().tracked_borrow(ptr.page_base());

        assert(self.wf());
        assert(Self::wf_perm(ptr.page_base(), *perm));
        assert(perm.wf());

        let next = ptr.borrow::<PageNode>(Tracked(&perm)).next.as_ref();

        match next {
            Some(ptr) => Some(ptr.clone()),
            None => None
        }
    }

    /// This has to be a trusted function until we figure out an API for `put`ing individual fields.
    #[verifier(external_body)]
    fn put_next(&mut self, ptr: &NodePtr<T>, next: Option<NodePtr<T>>) 
        requires
            old(self).wf(),
            old(self).owns(*ptr),
        ensures
            self.wf(),
            self.owns(*ptr),
            self.node(*ptr).value == old(self).node(*ptr).value,
            same_ptr_opt(self.node(*ptr).next, next),
            same_ptr_opt(self.node(*ptr).prev, old(self).node(*ptr).prev),
    {
        unsafe {
            let slice = core::slice::from_raw_parts_mut(ptr.page_pptr_concrete().to_usize() as *mut Node<T>, Arena::<T>::capacity());
            slice[ptr.index_concrete()].next = next;
        }
    }

    fn prev(&self, ptr: &NodePtr<T>) -> (res: Option<NodePtr<T>>)
        requires 
            self.wf(),
            self.owns(*ptr),
        ensures
            same_ptr_opt(self.node(*ptr).prev, res)
    {
        let tracked perm: &Arena<T> = self.perms.borrow().tracked_borrow(ptr.page_base());

        assert(self.wf());
        assert(Self::wf_perm(ptr.page_base(), *perm));
        assert(perm.wf());

        let prev = ptr.borrow::<PageNode>(Tracked(&perm)).prev.as_ref();

        match prev {
            Some(ptr) => Some(ptr.clone()),
            None => None
        }
    }

    /// This has to be a trusted function until we figure out an API for `put`ing individual fields.
    #[verifier(external_body)]
    fn put_prev(&mut self, ptr: &NodePtr<T>, prev: Option<NodePtr<T>>) 
        requires
            old(self).wf(),
            old(self).owns(*ptr),
        ensures
            self.wf(),
            self.owns(*ptr),
            self.node(*ptr).value == old(self).node(*ptr).value,
            same_ptr_opt(self.node(*ptr).next, old(self).node(*ptr).next),
            same_ptr_opt(self.node(*ptr).prev, prev),
    {
        unsafe {
            let slice = core::slice::from_raw_parts_mut(ptr.page_pptr_concrete().to_usize() as *mut Node<T>, Arena::<T>::capacity());
            slice[ptr.index_concrete()].prev = prev;
        }
    }

    proof fn lemma_owns_same_ptr(&self, a: &NodePtr<T>, b: &NodePtr<T>) 
        requires
            self.wf(),
            a.same_ptr(b),
            self.owns(*a),
        ensures
            self.owns(*b),
    {
    }
}

pub struct LinkedList2<T: Default> {
    free_head: Option<NodePtr<T>>,
    free_ptrs: Ghost<Seq<NodePtr<T>>>,

    permissions: Permissions<T>,
}

impl<T: Default> LinkedList2<T> {

    // **********************
    // Well formed

    pub closed spec fn wf(&self) -> bool {
        &&& self.wf_permissions()
        &&& Self::wf_free_head(self.free_head, self.free_ptrs@)
        &&& Self::wf_free_ptrs(self.free_ptrs@, self.permissions)
    }

    spec fn wf_permissions(&self) -> bool {
        &&& self.permissions.wf()
        &&& self.permissions.owns_seq(self.free_ptrs@)
    }

    spec fn wf_free_head(free_head: Option<NodePtr<T>>, free_ptrs: Seq<NodePtr<T>>) -> bool {
        let head = if free_ptrs.len() == 0 { None::<NodePtr<T>> } else { Some(free_ptrs[0]) };
        same_ptr_opt(free_head, head)
    }

    spec fn wf_free_ptrs(free_ptrs: Seq<NodePtr<T>>, permissions: Permissions<T>) -> bool
        recommends
            permissions.owns_seq(free_ptrs)
    {
        forall|i: int| 0 <= i < free_ptrs.len() ==> #[trigger] Self::wf_free_ptr(free_ptrs, permissions, i)
    }

    spec fn wf_free_ptr(free_ptrs: Seq<NodePtr<T>>, permissions: Permissions<T>, i: int) -> bool
        recommends
            permissions.owns_seq(free_ptrs),
            0 <= i < free_ptrs.len()
    {
        same_ptr_opt(permissions.node(free_ptrs[i]).next, Self::node_next_of(free_ptrs, i))
    }

    // **********************
    // Specs

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

    // ***************************
    // API

    pub fn new() -> (res: Self)
        ensures
            res.wf()
    {
        Self {
            free_head: None::<NodePtr::<T>>,
            free_ptrs: Ghost(Seq::empty()),

            permissions: Permissions::<T>::new(),
        }
    }

    pub closed spec fn len_free(&self) -> nat
    {
        self.free_ptrs@.len()
    }

    pub fn pop_free(&mut self) -> (res: NodePtr<T>) 
        requires
            old(self).len_free() > 0,
            old(self).wf(),
        ensures
            self.wf(),
    {
        assert(same_ptr_opt(self.free_head, Some(self.free_ptrs@[0])));

        let free_head_ref = self.free_head.as_ref().unwrap();
        assert(free_head_ref.same_ptr(&self.free_ptrs@[0]));

        let ptr = free_head_ref.clone();
        assert(ptr.same_ptr(&self.free_ptrs@[0]));

        proof {
            self.permissions.lemma_owns_same_ptr(&self.free_ptrs@[0], &ptr)
        }

        let next = self.permissions.next(&ptr);

        assert(Self::wf_free_head(self.free_head, self.free_ptrs@));
        assert(Self::wf_free_ptrs(self.free_ptrs@, self.permissions));
        assert(Self::wf_free_ptr(self.free_ptrs@, self.permissions, 0));
        assert(same_ptr_opt(next, Self::node_next_of(self.free_ptrs@, 0)));

        self.free_head = next;

        proof {
            self.lemma_pop_wf_free_ptrs();
            self.free_ptrs@ = self.free_ptrs@.skip(1);
        }

        // assert(Self::wf_free_head(self.free_head, self.free_ptrs@))
        assert(self.wf_permissions());
        assert(Self::wf_free_head(self.free_head, self.free_ptrs@));
        assert(Self::wf_free_ptrs(self.free_ptrs@, self.permissions));

        ptr
    }

    proof fn lemma_pop_wf_free_ptrs(&self)
        requires
            self.len_free() > 0,
            self.wf_permissions(),
            Self::wf_free_ptrs(self.free_ptrs@, self.permissions)
        ensures
            Self::wf_free_ptrs(self.free_ptrs@.skip(1), self.permissions)
    {
        assert(forall|i: int| 0 <= i < self.len_free() ==> #[trigger] Self::wf_free_ptr(self.free_ptrs@, self.permissions, i));

        assert forall|i: int| 1 <= i < self.len_free() implies #[trigger]  Self::wf_free_ptr(self.free_ptrs@.skip(1), self.permissions, i - 1) by {
            assert(Self::wf_free_ptr(self.free_ptrs@, self.permissions, i));
            self.lemma_chain_wf_free_ptr(i)
        }

        assert(self.free_ptrs@.skip(1).len() == self.free_ptrs@.len() - 1);

        assert forall|i: int| 0 <= i < self.free_ptrs@.skip(1).len() implies #[trigger] Self::wf_free_ptr(self.free_ptrs@.skip(1), self.permissions, i) by {
            let j = i + 1;

            assert(1 <= j < self.free_ptrs@.len());
            assert(Self::wf_free_ptr(self.free_ptrs@.skip(1), self.permissions, j - 1));
            assert(Self::wf_free_ptr(self.free_ptrs@.skip(1), self.permissions, i));
        }

        // assert(forall|i: int| 0 <= i < ptrs.skip(1).len() ==> #[trigger] Self::wf_free_ptr(ptrs.skip(1), i, perms))
    }

    proof fn lemma_chain_wf_free_ptr(&self, i: int) 
        requires
            1 <= i < self.len_free(),
            self.wf_permissions(),
            Self::wf_free_ptr(self.free_ptrs@, self.permissions, i)
        ensures
            Self::wf_free_ptr(self.free_ptrs@.skip(1), self.permissions, i - 1)
    {
        vstd::seq::axiom_seq_subrange_index(self.free_ptrs@, 1, self.free_ptrs@.len() as int, i - 1);
        assert(self.free_ptrs@[i] == self.free_ptrs@.skip(1)[i - 1]);
        assert(self.free_ptrs@[i].index() == self.free_ptrs@.skip(1)[i - 1].index());
        assert(same_ptr_opt(Self::node_next_of(self.free_ptrs@, i), Self::node_next_of(self.free_ptrs@.skip(1), i - 1)));
    }
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

    // ********************************
    // Public Spec ********************
    // ********************************

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

    pub closed spec fn owns(&self, ptr: NodePtr<T>) -> bool {
        self.perms@.dom().contains(ptr.page_base())
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

    pub closed spec fn len(&self) -> nat
    {
        self.ptrs@.len()
    }

    // ******************************
    // Private spec helpers
    // ******************************

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

    spec fn node_ptrs_eq(a: Option<NodePtr<T>>, b: Option<NodePtr<T>>) -> bool {
        if a.is_none() && b.is_none() {
            true
        } else if (a.is_none() && b.is_some()) || (a.is_some() && b.is_none()) {
            false
        } else {
            a.unwrap().same_ptr(&b.unwrap())
        }
    }

    // *************************
    // Well formed

    pub closed spec fn wf(&self) -> bool {
        &&& Self::wf_perms(self.perms@) 
        &&& Self::wf_free_head(self.free_head, self.free_ptrs@)
        &&& Self::wf_free_ptrs(self.free_ptrs@, self.perms@)
    }

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

    // *********************************
    // Lemmas **************************
    // *********************************

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

    pub fn push_back(&mut self, v: T)
        requires
            old(self).wf(),
            old(self).capacity() > 0,
        ensures
            self.wf(),
            self.capacity() == old(self).capacity() - 1,
    {
        let free = self.pop_free();
    }

    fn pop_free(&mut self) -> (res: NodePtr<T>)
        requires
            old(self).wf(),
            old(self).capacity() > 0,
        ensures
            self.wf(),
            self.capacity() == old(self).capacity() - 1,
            self.len() == old(self).len(),
            self.owns(res),
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

        // assert(self.perms@.dom().contains(ptr.page_base()));
        assert(self.owns(ptr));

        // Use lemma to show that after removing the permission, the map is still well formed
        proof {
            Self::lemma_remove_wf_perms(self.perms@, ptr.page_base());
        }

        // Get permission
        // let tracked mut perm: Arena<T> = (self.perms.borrow_mut()).tracked_remove(ptr.page_base());
        let tracked perm: &Arena<T> = self.perms.borrow().tracked_borrow(ptr.page_base());

        assert(Self::wf_perms(self.perms@));
        assert(Self::wf_perm(ptr.page_base(), *perm));
        assert(perm.wf());

        // Node
        let node: &Node<T> = ptr.borrow::<PageNode>(Tracked(&perm));
        assert(Self::node_ptrs_eq(node.next, Self::node_next_of(self.free_ptrs@, 0)));

        match &node.next {
            Some(p) => self.free_head = Some(p.clone()),
            None => self.free_head = None,
        }

        assert(Self::node_ptrs_eq(self.free_head, Self::node_next_of(self.free_ptrs@, 0)));


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

    // fn get_page_next(&self, ptr: &NodePtr<T>) -> (res: Option<NodePtr<T>>)
    //     requires
    //         self.wf(),
    //         self.owns(*ptr),
    //     ensures
    //         Self::node_ptrs_eq(ptr)
    // {

    // }

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
    
    

    // ********************
    // Well Formed Spec ***
    // ********************

    

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
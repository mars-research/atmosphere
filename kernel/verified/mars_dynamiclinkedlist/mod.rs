use vstd::prelude::*;
verus! {
use vstd::seq_lib::*;
use vstd::set_lib::*;
use crate::page_alloc::*;
use vstd::ptr::*;
use crate::define::*;

pub mod dyn_array_util;
pub use dyn_array_util::*;

pub const DYN_ARRAY_LEN:usize = 128;

#[verifier(external_body)]
pub proof fn usize_dyn_index_lemma()
    ensures
        forall|u:usize| #![auto] dyn_index_to_usize(&usize_to_dyn_index(u)) == u,
        forall|u:usize,v:usize| #![auto] v != u ==> usize_to_dyn_index(u) =~= usize_to_dyn_index(v) == false,
        forall|i:DynIndex| #![auto] usize_to_dyn_index(dyn_index_to_usize(&i)) == i,
        forall|i:DynIndex,j:DynIndex| #![auto] i =~= j == false ==> dyn_index_to_usize(&i) != dyn_index_to_usize(&j),
{
}

pub open spec fn spec_dyn_index_valid(i:usize) -> bool{
    0<=i<DYN_ARRAY_LEN
}

#[verifier(when_used_as_spec(spec_dyn_index_valid))]
pub fn dyn_index_valid(i:usize) -> (ret:bool)
    ensures
        ret == spec_dyn_index_valid(i),
{
    0<=i && i<DYN_ARRAY_LEN
}

pub open spec fn spec_usize_to_dyn_index(u:usize) -> DynIndex {
    DynIndex{
        ptr: u & (0xFFFF_FFFF_FFFF_F000u64 as usize),
        index: u & (0xFFFu64 as usize),
    }
}

#[verifier(when_used_as_spec(spec_usize_to_dyn_index))]
pub fn usize_to_dyn_index(u:usize) -> (ret : DynIndex) 
    ensures
        ret.ptr == spec_usize_to_dyn_index(u).ptr,
        ret.index == spec_usize_to_dyn_index(u).index,
{
    DynIndex{
        ptr: u & (0xFFFF_FFFF_FFFF_F000u64 as usize),
        index: u & (0xFFFu64 as usize),
    }
}

pub open spec fn spec_dyn_index_to_usize(u:&DynIndex) -> usize 
    recommends 
        page_ptr_valid(u.ptr),
        dyn_index_valid(u.index),
{
    u.ptr | u.index
}

#[verifier(when_used_as_spec(spec_dyn_index_to_usize))]
pub fn dyn_index_to_usize(u:&DynIndex) -> (ret:usize) 
    requires 
        page_ptr_valid(u.ptr),
        dyn_index_valid(u.index),
    ensures
        ret == spec_dyn_index_to_usize(u),
{
    u.ptr | u.index
}

pub fn dyn_ptr_index_to_usize(ptr: usize, index: usize) -> (ret:usize) 
    requires 
        page_ptr_valid(ptr),
        dyn_index_valid(index),
    ensures
        ret == spec_dyn_index_to_usize(&DynIndex{ptr:ptr, index:index}),
{
    ptr | index
}

pub open spec fn spec_dyn_node_to_dny_resolve(node :&DynNode) -> DynNodeResolve
{
    DynNodeResolve{
        value: node.value,
        next: usize_to_dyn_index(node.next),
        prev: usize_to_dyn_index(node.prev),
    }
}


#[verifier(when_used_as_spec(spec_dyn_node_to_dny_resolve))]
pub fn dyn_node_to_dny_resolve(node :&DynNode) -> (ret: DynNodeResolve)
    ensures
        ret =~= spec_dyn_node_to_dny_resolve(node),
{
    DynNodeResolve{
        value: node.value,
        next: usize_to_dyn_index(node.next),
        prev: usize_to_dyn_index(node.prev),
    }
}


pub struct DynIndex{
    pub ptr: DynArrayPtr,
    pub index: usize,
}

pub struct DynNode{
    pub value: usize,
    pub next: usize,
    pub prev: usize,
}

pub struct DynNodeResolve{
    pub value: usize,
    pub next: DynIndex,
    pub prev: DynIndex,
}

pub struct DynArray{
    pub free_count: usize,
    pub ar: [DynNode;DYN_ARRAY_LEN],
    pub seq: Ghost<Seq<DynNodeResolve>>,

    pub free_set: Ghost<Set<usize>>,
    pub value_set: Ghost<Set<usize>>,
}

impl DynArray{
    pub open spec fn wf(&self) -> bool{
        self.seq@.len() == DYN_ARRAY_LEN
        &&
        self.free_set@.finite()
        &&
        self.value_set@.finite()
        &&
        self.free_set@.disjoint(self.value_set@)
        &&
        self.free_set@ + self.value_set@ =~= Set::new(|index: usize| {
            0<=index<DYN_ARRAY_LEN
        })
        &&
        self.free_count == self.free_set@.len()
    }
    pub open spec fn view(&self) -> Seq<DynNodeResolve>
        recommends self.wf()
    {
        self.seq@
    }

    #[verifier(external_body)]
    pub fn get_prev(&self, i:usize) -> (ret:DynIndex)
        requires
            self.wf(),
            dyn_index_valid(i),
        ensures
            ret =~= self@[i as int].prev
    {
        usize_to_dyn_index(self.ar[i].prev)
    }

    #[verifier(external_body)]
    pub fn get_prev_ptr_index(&self, i:usize) -> (ret:(DynArrayPtr, usize))
        requires
            self.wf(),
            dyn_index_valid(i),
        ensures
            (DynIndex{ptr:ret.0,index:ret.1}) =~= self@[i as int].prev
    {
        (self.ar[i].prev & (0xFFFF_FFFF_FFFF_F000u64 as usize), self.ar[i].prev & (0xFFFu64 as usize))
    }

    #[verifier(external_body)]
    pub fn get_next_ptr_index(&self, i:usize) -> (ret:(DynArrayPtr, usize))
        requires
            self.wf(),
            dyn_index_valid(i),
        ensures
            (DynIndex{ptr:ret.0,index:ret.1}) =~= self@[i as int].next
    {
        (self.ar[i].next & (0xFFFF_FFFF_FFFF_F000u64 as usize), self.ar[i].next & (0xFFFu64 as usize))
    }

    #[verifier(external_body)]
    pub fn get_value(&self, i:usize) -> (ret:usize)
        requires
            self.wf(),
            dyn_index_valid(i),
        ensures
            ret =~= self@[i as int].value
    {
        self.ar[i].value
    }

}

pub struct DynLinkedlist{
    pub free_head: DynIndex,
    pub free_tail: DynIndex,

    pub value_head: DynIndex,
    pub value_tail: DynIndex,

    pub array_ptrs : Ghost<Set<DynArrayPtr>>,
    pub array_perms : Tracked<Map<DynArrayPtr, PointsTo<DynArray>>>,

    pub size: usize,
    pub len: usize,

    pub value_list: Ghost<Seq<DynIndex>>,
    pub free_list: Ghost<Seq<DynIndex>>,
    pub spec_seq: Ghost<Seq<usize>>,
}

impl DynLinkedlist{
    pub open spec fn spec_size(&self) -> usize{
        self.size
    }

    #[verifier(external_body)]
    #[verifier(when_used_as_spec(spec_size))]
    pub fn size(&self) -> (s: usize)
        ensures
            s == self.size,
    {
        self.size
    }

    pub open spec fn spec_len(&self) -> usize{
        self.len
    }

    #[verifier(external_body)]
    #[verifier(when_used_as_spec(spec_len))]
    pub fn len(&self) -> (l: usize)
        ensures
            l == self.len,
    {
        self.len
    }

    pub closed spec fn node_ref_valid(&self, rf: usize) -> bool{
        self.value_list@.contains(usize_to_dyn_index(rf))
    }

    pub closed spec fn node_ref_resolve(&self, rf: usize) -> usize
        recommends self.node_ref_valid(rf)
    {
        self.get_node_by_dyn_index(usize_to_dyn_index(rf)).value
    }

    pub open spec fn unique(&self) -> bool {
        forall|i:int, j:int| #![auto] i != j && 0 <= i < self.spec_seq@.len() && 0 <= j < self.spec_seq@.len()
            ==> self.spec_seq@[i] != self.spec_seq@[j]
    }

    pub open spec fn wf_free_head(&self) -> bool {
        if self.free_list@.len() == 0 {
            self.free_head.ptr == 0
        } else {
            self.free_head =~= self.free_list@[0]
        }
    }

    pub open spec fn wf_free_tail(&self) -> bool {
        if self.free_list@.len() == 0 {
            self.free_tail.ptr == 0
        } else {
            self.free_tail  =~= self.free_list@[self.free_list@.len() - 1]
        }
    }

    pub open spec fn prev_free_node_of(&self, i: int) -> DynIndex
        recommends i < self.free_list@.len()
    {
        if i == 0{
            DynIndex{
                ptr:0,
                index: 0,
            }
        } else {
            self.free_list@[i - 1int]
        }
    }

    pub open spec fn next_free_node_of(&self, i: int) -> DynIndex
        recommends i < self.free_list@.len()
    {
        if i + 1 == self.free_list@.len() {
            DynIndex{
                ptr:0,
                index: 0,
            }
        } else {
            self.free_list@[i + 1int]
        }
    }

    pub open spec fn wf_value_head(&self) -> bool {
        if self.value_list@.len() == 0 {
            self.value_head.ptr == 0
            &&
            self.value_head.index == 0
        } else {
            self.value_head =~= self.value_list@[0]
        }
    }

    pub open spec fn wf_value_tail(&self) -> bool {
        if self.value_list@.len() == 0 {
            self.value_tail.ptr == 0
            &&
            self.value_tail.index == 0
        } else {
            self.value_tail  =~= self.value_list@[self.value_list@.len() - 1]
        }
    }

    pub open spec fn prev_value_node_of(&self, i: int) -> DynIndex
        recommends i < self.value_list@.len()
    {
        if i == 0{
            DynIndex{
                ptr:0,
                index: 0,
            }
        } else {
            self.value_list@[i - 1int]
        }
    }

    pub open spec fn next_value_node_of(&self, i: int) -> DynIndex
        recommends i < self.value_list@.len()
    {
        if i + 1 == self.value_list@.len() {
            DynIndex{
                ptr:0,
                index: 0,
            }
        } else {
            self.value_list@[i + 1int]
        }
    }

    #[verifier(inline)]
    pub open spec fn get_node_by_dyn_index(&self, dyn_index: DynIndex) -> DynNodeResolve
        recommends
            page_ptr_valid(dyn_index.ptr),
            dyn_index_valid(dyn_index.index),
            self.array_ptrs@.contains(dyn_index.ptr),
    {
        self.array_perms@[dyn_index.ptr]@.value.get_Some_0()@[dyn_index.index as int]
    }

    pub open spec fn value_list_wf(&self) -> bool{
        (forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> page_ptr_valid(self.value_list@[i as int].ptr))
        &&
        (forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.array_ptrs@.contains(self.value_list@[i as int].ptr))
        &&
        (forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> dyn_index_valid(self.value_list@[i as int].index))
        &&
        (forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.get_node_by_dyn_index(self.value_list@[i as int]).next == self.next_value_node_of(i))
        &&
        (forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.get_node_by_dyn_index(self.value_list@[i as int]).prev == self.prev_value_node_of(i))
        &&
        (forall|i: int, j:int|  #![auto] i != j && 0 <= i < self.value_list@.len() && 0 <= j < self.value_list@.len() ==> (self.value_list@[i as int] =~= self.value_list@[j as int]) == false)
        &&
        self.wf_value_head()
        &&
        self.wf_value_tail()
        &&
        self.len == self.value_list@.len()
        &&
        forall|i:int| #![auto] 0 <= i < self.value_list@.len() ==> self.free_list@.contains(self.value_list@[i]) == false 
        &&
        (
            self.value_list@.len() != 0 ==> (
                (self.array_ptrs@.contains(self.value_head.ptr))
                &&
                (dyn_index_valid(self.value_head.index))
                &&
                (self.array_ptrs@.contains(self.value_tail.ptr))
                &&
                (dyn_index_valid(self.value_tail.index))
            )
        )
    }

    pub open spec fn free_list_wf(&self) -> bool{
        (forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> page_ptr_valid(self.free_list@[i as int].ptr))
        &&
        (forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.array_ptrs@.contains(self.free_list@[i as int].ptr))
        &&
        (forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> dyn_index_valid(self.free_list@[i as int].index))
        &&
        (forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.get_node_by_dyn_index(self.free_list@[i as int]).next == self.next_free_node_of(i))
        &&
        (forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.get_node_by_dyn_index(self.free_list@[i as int]).prev == self.prev_free_node_of(i))
        &&
        (forall|i: int, j:int|  #![auto] i != j && 0 <= i < self.free_list@.len() && 0 <= j < self.free_list@.len() ==> (self.free_list@[i as int] =~= self.free_list@[j as int]) == false)
        &&
        (self.wf_free_head())
        &&
        (self.wf_free_tail())
        &&
        (self.size - self.len == self.free_list@.len())
        &&
        (forall|i:int| #![auto] 0 <= i < self.free_list@.len() ==> self.value_list@.contains(self.free_list@[i]) == false)
        &&
        (
            self.free_list@.len() != 0 ==> (
                (self.array_ptrs@.contains(self.free_head.ptr))
                &&
                (dyn_index_valid(self.free_head.index))
                &&
                (self.array_ptrs@.contains(self.free_tail.ptr))
                &&
                (dyn_index_valid(self.free_tail.index))
            )
        )
    }

    pub open spec fn array_perms_wf(&self) -> bool{
        self.array_ptrs@.finite()
        &&
        self.array_ptrs@.contains(0) == false
        &&
        self.array_ptrs@ =~= self.array_perms@.dom()
        &&
        self.size == self.array_ptrs@.len() * DYN_ARRAY_LEN
        &&
        (forall|array_ptr:DynArrayPtr| #![auto] self.array_ptrs@.contains(array_ptr) ==> page_ptr_valid(array_ptr))
        &&
        (forall|array_ptr:DynArrayPtr| #![auto] self.array_perms@.dom().contains(array_ptr) ==> self.array_perms@[array_ptr]@.pptr == array_ptr)
        &&
        (forall|array_ptr:DynArrayPtr| #![auto] self.array_perms@.dom().contains(array_ptr) ==> self.array_perms@[array_ptr]@.value.is_Some())
        &&
        (forall|array_ptr:DynArrayPtr| #![auto] self.array_perms@.dom().contains(array_ptr) ==> self.array_perms@[array_ptr]@.value.get_Some_0().wf())
    }

    pub open spec fn array_sets_wf(&self) -> bool{
        (forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.array_perms@[self.free_list@[i].ptr]@.value.get_Some_0().free_set@.contains(self.free_list@[i].index))
        &&
        (forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.array_perms@[self.value_list@[i].ptr]@.value.get_Some_0().value_set@.contains(self.value_list@[i].index))
        &&
        (forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index) ==> 
            self.free_list@.contains(DynIndex{ptr:array_ptr,index:index})
        )
        &&
        (forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index) ==> 
            self.value_list@.contains(DynIndex{ptr:array_ptr,index:index})
        )
    }

    pub open spec fn spec_seq_wf(&self) -> bool{
        self.spec_seq@.len() == self.len()
        &&
        (forall|i: int| #![auto] 0 <= i < self.len() ==> self.spec_seq@[i] =~= self.get_node_by_dyn_index(self.value_list@[i]).value)
        &&
        (forall|i: int, j:int|  #![auto] i != j && 0 <= i < self.len() && 0 <= j < self.len() ==> (self.spec_seq@[i as int] =~= self.spec_seq@[j as int]) == false)
    }


    pub fn remove(&mut self, rf:usize)
        requires
            old(self).wf(),
            old(self).node_ref_valid(rf),
    {
        proof{
            lemma_seq_properties::<DynIndex>();
            lemma_set_properties::<DynIndex>();
            usize_dyn_index_lemma();
        }
        assert(self.value_list@.len() > 0);
        let rf_ptr = usize_to_dyn_index(rf).ptr;
        let rf_index = usize_to_dyn_index(rf).index;

        let rf_value_list_index = Ghost(self.value_list@.index_of(DynIndex{ptr:rf_ptr,index:rf_index}));

        if rf_ptr == self.value_head.ptr && rf_index == self.value_head.index{

        }else if rf_ptr == self.value_tail.ptr && rf_index == self.value_tail.index{

        }else if self.len() == self.size(){

            assert(self.value_list@.len() > 1);
            assert(self.free_list@.len() == 0);
            let tracked value_head_array_perm = self.array_perms.borrow().tracked_borrow(rf_ptr);
            let value_head_array : &DynArray = PPtr::<DynArray>::from_usize(rf_ptr).borrow(Tracked(value_head_array_perm));
            let (next_value_ptr,next_value_index) = value_head_array.get_next_ptr_index(rf_index);
            let (prev_value_ptr,prev_value_index) = value_head_array.get_prev_ptr_index(rf_index);

            assert(self.value_list@[rf_value_list_index@] =~= DynIndex{ptr:rf_ptr,index:rf_index});
            assert(self.get_node_by_dyn_index(DynIndex{ptr:rf_ptr,index:rf_index}).next.ptr == next_value_ptr && self.get_node_by_dyn_index(DynIndex{ptr:rf_ptr,index:rf_index}).next.index == next_value_index);
            assert(self.get_node_by_dyn_index(DynIndex{ptr:rf_ptr,index:rf_index}).next.ptr == self.next_value_node_of(rf_value_list_index@).ptr && self.get_node_by_dyn_index(DynIndex{ptr:rf_ptr,index:rf_index}).next.index == self.next_value_node_of(rf_value_list_index@).index);
            assert(self.get_node_by_dyn_index(DynIndex{ptr:rf_ptr,index:rf_index}).next.ptr == self.value_list@[rf_value_list_index@ + 1].ptr && self.get_node_by_dyn_index(DynIndex{ptr:rf_ptr,index:rf_index}).next.index == self.value_list@[rf_value_list_index@ + 1].index);
            assert(self.value_list@[rf_value_list_index@ + 1].ptr == next_value_ptr && self.value_list@[rf_value_list_index@ + 1].index == next_value_index);

            assert(self.value_list@[rf_value_list_index@] =~= DynIndex{ptr:rf_ptr,index:rf_index});
            assert(self.get_node_by_dyn_index(DynIndex{ptr:rf_ptr,index:rf_index}).prev.ptr == prev_value_ptr && self.get_node_by_dyn_index(DynIndex{ptr:rf_ptr,index:rf_index}).prev.index == prev_value_index);
            assert(self.get_node_by_dyn_index(DynIndex{ptr:rf_ptr,index:rf_index}).prev.ptr == self.prev_value_node_of(rf_value_list_index@).ptr && self.get_node_by_dyn_index(DynIndex{ptr:rf_ptr,index:rf_index}).prev.index == self.prev_value_node_of(rf_value_list_index@).index);
            assert(self.get_node_by_dyn_index(DynIndex{ptr:rf_ptr,index:rf_index}).prev.ptr == self.value_list@[rf_value_list_index@ - 1].ptr && self.get_node_by_dyn_index(DynIndex{ptr:rf_ptr,index:rf_index}).prev.index == self.value_list@[rf_value_list_index@ - 1].index);
            assert(self.value_list@[rf_value_list_index@ - 1].ptr == prev_value_ptr && self.value_list@[rf_value_list_index@ - 1].index == prev_value_index);

            let mut next_value_array_perm =
                Tracked((self.array_perms.borrow_mut()).tracked_remove(next_value_ptr));
            assert(next_value_array_perm@@.value.is_Some());
            dyn_array_set_prev(&PPtr::<DynArray>::from_usize(next_value_ptr), &mut next_value_array_perm, prev_value_ptr,prev_value_index,next_value_index);
            proof{
                (self.array_perms.borrow_mut())
                    .tracked_insert(next_value_ptr, next_value_array_perm.get());
            }

            let mut prev_value_array_perm =
                Tracked((self.array_perms.borrow_mut()).tracked_remove(prev_value_ptr));
            assert(prev_value_array_perm@@.value.is_Some());
            dyn_array_set_next(&PPtr::<DynArray>::from_usize(prev_value_ptr), &mut prev_value_array_perm, next_value_ptr,next_value_index,prev_value_index);
            proof{
                (self.array_perms.borrow_mut())
                    .tracked_insert(prev_value_ptr, prev_value_array_perm.get());
            }

            let mut value_head_array_perm =
                Tracked((self.array_perms.borrow_mut()).tracked_remove(rf_ptr));
            assert(value_head_array_perm@@.value.is_Some());
            dyn_array_set_prev(&PPtr::<DynArray>::from_usize(rf_ptr), &mut value_head_array_perm, 0,0,rf_index);
            dyn_array_set_next(&PPtr::<DynArray>::from_usize(rf_ptr), &mut value_head_array_perm, 0,0,rf_index);
            dyn_array_pop_value_to_free(&PPtr::<DynArray>::from_usize(rf_ptr), &mut value_head_array_perm,rf_index);
            proof{
                (self.array_perms.borrow_mut())
                    .tracked_insert(rf_ptr, value_head_array_perm.get());
            }

            proof{
                self.value_list@ = self.value_list@.subrange(0, rf_value_list_index@) + self.value_list@.subrange(rf_value_list_index@ + 1, self.value_list@.len() as int);
                self.spec_seq@ = self.spec_seq@.subrange(0, rf_value_list_index@) + self.spec_seq@.subrange(rf_value_list_index@ + 1, self.spec_seq@.len() as int);
            }

            self.free_head.ptr = rf_ptr;
            self.free_head.index = rf_index;
            self.free_tail.ptr = rf_ptr;
            self.free_tail.index = rf_index;

            proof{
                self.free_list@ = self.free_list@.push(DynIndex{ptr:rf_ptr,index:rf_index});
            }

            self.len = self.len - 1;

            assert(self.array_perms_wf());
            assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.array_perms@[self.free_list@[i].ptr]@.value.get_Some_0().free_set@.contains(self.free_list@[i].index));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.array_perms@[self.value_list@[i].ptr]@.value.get_Some_0().value_set@.contains(self.value_list@[i].index));
            assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old(self).array_perms@.dom().contains(array_ptr) && old(self).array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index) ==> (self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index)));
            assert(old(self).free_list@ =~= self.free_list@.subrange(0, self.free_list@.len() - 1));
            assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old(self).free_list@.contains(DynIndex{ptr:array_ptr,index:index}) ==> self.free_list@.contains(DynIndex{ptr:array_ptr,index:index}));
            assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index) ==> self.free_list@.contains(DynIndex{ptr:array_ptr,index:index}));
            assert(self.value_list@ =~= old(self).value_list@.subrange(0, rf_value_list_index@) + old(self).value_list@.subrange(rf_value_list_index@ + 1, old(self).value_list@.len() as int));
            assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index) && array_ptr != rf_ptr ==> (old(self).array_perms@.dom().contains(array_ptr) && old(self).array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index)));
            assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old(self).value_list@.contains(DynIndex{ptr:array_ptr,index:index}) && (DynIndex{ptr:array_ptr,index:index} =~= DynIndex{ptr:rf_ptr,index:rf_index} == false) ==> self.value_list@.contains(DynIndex{ptr:array_ptr,index:index}));
            assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index) ==> self.value_list@.contains(DynIndex{ptr:array_ptr,index:index}));
            assert(self.array_sets_wf());
            assert(self.spec_seq_wf());
            assert(self.free_list_wf());
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> page_ptr_valid(self.value_list@[i as int].ptr));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.array_ptrs@.contains(self.value_list@[i as int].ptr));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> dyn_index_valid(self.value_list@[i as int].index));


            assert(forall|i: int| #![auto] 0 <= i < rf_value_list_index@ - 1  ==> self.get_node_by_dyn_index(self.value_list@[i as int]).next == old(self).get_node_by_dyn_index(self.value_list@[i as int]).next);
            assert(forall|i: int| #![auto] rf_value_list_index@ <= i < self.value_list@.len()  ==> self.value_list@[i] == old(self).value_list@[i + 1]);
            assert(forall|i: int| #![auto] rf_value_list_index@ <= i < self.value_list@.len()  ==> self.get_node_by_dyn_index(self.value_list@[i]).next == old(self).get_node_by_dyn_index(old(self).value_list@[i + 1]).next);
            assert(forall|i: int| #![auto] 0 <= i < rf_value_list_index@ - 1  ==> self.next_value_node_of(i) == old(self).next_value_node_of(i));
            assert(forall|i: int| rf_value_list_index@ <= i < self.value_list@.len() ==> #[trigger] self.next_value_node_of(i) =~= old(self).next_value_node_of(i + 1));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.get_node_by_dyn_index(self.value_list@[i as int]).next == self.next_value_node_of(i));
            
            assert(forall|i: int| #![auto] 0 <= i < rf_value_list_index@  ==> self.get_node_by_dyn_index(self.value_list@[i as int]).prev == old(self).get_node_by_dyn_index(self.value_list@[i as int]).prev);
            assert(forall|i: int| #![auto] rf_value_list_index@ <= i < self.value_list@.len()  ==> self.value_list@[i] == old(self).value_list@[i + 1]);
            assert(forall|i: int| #![auto] rf_value_list_index@ + 1 <= i < self.value_list@.len()  ==> self.get_node_by_dyn_index(self.value_list@[i]).prev == old(self).get_node_by_dyn_index(old(self).value_list@[i + 1]).prev);
            assert(forall|i: int| #![auto] 0 <= i < rf_value_list_index@  ==> self.prev_value_node_of(i) == old(self).prev_value_node_of(i));
            assert(forall|i: int| rf_value_list_index@ + 1 <= i < self.value_list@.len() ==> #[trigger] self.prev_value_node_of(i) =~= old(self).prev_value_node_of(i + 1));

            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.get_node_by_dyn_index(self.value_list@[i as int]).prev == self.prev_value_node_of(i));
            assert(forall|i: int, j:int|  #![auto] i != j && 0 <= i < self.value_list@.len() && 0 <= j < self.value_list@.len() ==> (self.value_list@[i as int] =~= self.value_list@[j as int]) == false);
            assert(self.wf_value_head());
            assert(self.wf_value_tail());
            assert(self.len == self.value_list@.len());
            assert(forall|i:int| #![auto] 0 <= i < self.value_list@.len() ==> self.free_list@.contains(self.value_list@[i]) == false );
            assert(self.value_list_wf());
            assert(self.wf());

        }else{
            assert(self.value_list@.len() > 1);
            assert(self.free_list@.len() > 0);
            let tracked value_head_array_perm = self.array_perms.borrow().tracked_borrow(rf_ptr);
            let value_head_array : &DynArray = PPtr::<DynArray>::from_usize(rf_ptr).borrow(Tracked(value_head_array_perm));
            let (next_value_ptr,next_value_index) = value_head_array.get_next_ptr_index(rf_index);
            let (prev_value_ptr,prev_value_index) = value_head_array.get_prev_ptr_index(rf_index);

            let free_tail_ptr = self.free_tail.ptr;
            let free_tail_index = self.free_tail.index; 

            assert(self.value_list@[rf_value_list_index@] =~= DynIndex{ptr:rf_ptr,index:rf_index});
            assert(self.get_node_by_dyn_index(DynIndex{ptr:rf_ptr,index:rf_index}).next.ptr == next_value_ptr && self.get_node_by_dyn_index(DynIndex{ptr:rf_ptr,index:rf_index}).next.index == next_value_index);
            assert(self.get_node_by_dyn_index(DynIndex{ptr:rf_ptr,index:rf_index}).next.ptr == self.next_value_node_of(rf_value_list_index@).ptr && self.get_node_by_dyn_index(DynIndex{ptr:rf_ptr,index:rf_index}).next.index == self.next_value_node_of(rf_value_list_index@).index);
            assert(self.get_node_by_dyn_index(DynIndex{ptr:rf_ptr,index:rf_index}).next.ptr == self.value_list@[rf_value_list_index@ + 1].ptr && self.get_node_by_dyn_index(DynIndex{ptr:rf_ptr,index:rf_index}).next.index == self.value_list@[rf_value_list_index@ + 1].index);
            assert(self.value_list@[rf_value_list_index@ + 1].ptr == next_value_ptr && self.value_list@[rf_value_list_index@ + 1].index == next_value_index);

            assert(self.value_list@[rf_value_list_index@] =~= DynIndex{ptr:rf_ptr,index:rf_index});
            assert(self.get_node_by_dyn_index(DynIndex{ptr:rf_ptr,index:rf_index}).prev.ptr == prev_value_ptr && self.get_node_by_dyn_index(DynIndex{ptr:rf_ptr,index:rf_index}).prev.index == prev_value_index);
            assert(self.get_node_by_dyn_index(DynIndex{ptr:rf_ptr,index:rf_index}).prev.ptr == self.prev_value_node_of(rf_value_list_index@).ptr && self.get_node_by_dyn_index(DynIndex{ptr:rf_ptr,index:rf_index}).prev.index == self.prev_value_node_of(rf_value_list_index@).index);
            assert(self.get_node_by_dyn_index(DynIndex{ptr:rf_ptr,index:rf_index}).prev.ptr == self.value_list@[rf_value_list_index@ - 1].ptr && self.get_node_by_dyn_index(DynIndex{ptr:rf_ptr,index:rf_index}).prev.index == self.value_list@[rf_value_list_index@ - 1].index);
            assert(self.value_list@[rf_value_list_index@ - 1].ptr == prev_value_ptr && self.value_list@[rf_value_list_index@ - 1].index == prev_value_index);

            let mut next_value_array_perm =
                Tracked((self.array_perms.borrow_mut()).tracked_remove(next_value_ptr));
            assert(next_value_array_perm@@.value.is_Some());
            dyn_array_set_prev(&PPtr::<DynArray>::from_usize(next_value_ptr), &mut next_value_array_perm, prev_value_ptr,prev_value_index,next_value_index);
            proof{
                (self.array_perms.borrow_mut())
                    .tracked_insert(next_value_ptr, next_value_array_perm.get());
            }

            let mut prev_value_array_perm =
                Tracked((self.array_perms.borrow_mut()).tracked_remove(prev_value_ptr));
            assert(prev_value_array_perm@@.value.is_Some());
            dyn_array_set_next(&PPtr::<DynArray>::from_usize(prev_value_ptr), &mut prev_value_array_perm, next_value_ptr,next_value_index,prev_value_index);
            proof{
                (self.array_perms.borrow_mut())
                    .tracked_insert(prev_value_ptr, prev_value_array_perm.get());
            }

            let mut value_head_array_perm =
                Tracked((self.array_perms.borrow_mut()).tracked_remove(rf_ptr));
            assert(value_head_array_perm@@.value.is_Some());
            dyn_array_set_prev(&PPtr::<DynArray>::from_usize(rf_ptr), &mut value_head_array_perm, free_tail_ptr,free_tail_index,rf_index);
            dyn_array_set_next(&PPtr::<DynArray>::from_usize(rf_ptr), &mut value_head_array_perm, 0,0,rf_index);
            dyn_array_pop_value_to_free(&PPtr::<DynArray>::from_usize(rf_ptr), &mut value_head_array_perm,rf_index);            
            proof{
                (self.array_perms.borrow_mut())
                    .tracked_insert(rf_ptr, value_head_array_perm.get());
            }

            let mut free_tail_array_perm =
                Tracked((self.array_perms.borrow_mut()).tracked_remove(free_tail_ptr));
            assert(free_tail_array_perm@@.value.is_Some());
            dyn_array_set_next(&PPtr::<DynArray>::from_usize(free_tail_ptr), &mut free_tail_array_perm, rf_ptr,rf_index,free_tail_index);
            proof{
                (self.array_perms.borrow_mut())
                    .tracked_insert(free_tail_ptr, free_tail_array_perm.get());
            }

            proof{
                self.value_list@ = self.value_list@.subrange(0, rf_value_list_index@) + self.value_list@.subrange(rf_value_list_index@ + 1, self.value_list@.len() as int);
                self.spec_seq@ = self.spec_seq@.subrange(0, rf_value_list_index@) + self.spec_seq@.subrange(rf_value_list_index@ + 1, self.spec_seq@.len() as int);
            }


            self.free_tail.ptr = rf_ptr;
            self.free_tail.index = rf_index;

            proof{
                self.free_list@ = self.free_list@.push(DynIndex{ptr:rf_ptr,index:rf_index});
            }

            self.len = self.len - 1;

            assert(self.array_perms_wf());
            assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.array_perms@[self.free_list@[i].ptr]@.value.get_Some_0().free_set@.contains(self.free_list@[i].index));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.array_perms@[self.value_list@[i].ptr]@.value.get_Some_0().value_set@.contains(self.value_list@[i].index));
            assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old(self).array_perms@.dom().contains(array_ptr) && old(self).array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index) ==> (self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index)));
            assert(old(self).free_list@ =~= self.free_list@.subrange(0, self.free_list@.len() - 1));
            assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old(self).free_list@.contains(DynIndex{ptr:array_ptr,index:index}) ==> self.free_list@.contains(DynIndex{ptr:array_ptr,index:index}));
            assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index) ==> self.free_list@.contains(DynIndex{ptr:array_ptr,index:index}));
            assert(self.value_list@ =~= old(self).value_list@.subrange(0, rf_value_list_index@) + old(self).value_list@.subrange(rf_value_list_index@ + 1, old(self).value_list@.len() as int));
            assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index) && array_ptr != rf_ptr ==> (old(self).array_perms@.dom().contains(array_ptr) && old(self).array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index)));
            assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old(self).value_list@.contains(DynIndex{ptr:array_ptr,index:index}) && (DynIndex{ptr:array_ptr,index:index} =~= DynIndex{ptr:rf_ptr,index:rf_index} == false) ==> self.value_list@.contains(DynIndex{ptr:array_ptr,index:index}));
            assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index) ==> self.value_list@.contains(DynIndex{ptr:array_ptr,index:index}));
            assert(self.array_sets_wf());
            assert(self.spec_seq_wf());
            assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> page_ptr_valid(self.free_list@[i as int].ptr));
            assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.array_ptrs@.contains(self.free_list@[i as int].ptr));
            assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> dyn_index_valid(self.free_list@[i as int].index));

            assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() - 2 ==> self.get_node_by_dyn_index(self.free_list@[i as int]).next == old(self).get_node_by_dyn_index(self.free_list@[i as int]).next);
            assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() - 2 ==> self.next_free_node_of(i) == old(self).next_free_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.get_node_by_dyn_index(self.free_list@[i as int]).next == self.next_free_node_of(i));

            assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() - 1 ==> self.get_node_by_dyn_index(self.free_list@[i as int]).prev == old(self).get_node_by_dyn_index(self.free_list@[i as int]).prev);
            assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() - 1 ==> self.prev_free_node_of(i) == old(self).prev_free_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.get_node_by_dyn_index(self.free_list@[i as int]).prev == self.prev_free_node_of(i));
            assert(forall|i: int, j:int|  #![auto] i != j && 0 <= i < self.free_list@.len() && 0 <= j < self.free_list@.len() ==> (self.free_list@[i as int] =~= self.free_list@[j as int]) == false);
            assert(self.wf_free_head());
            assert(self.wf_free_tail());
            assert(self.size - self.len == self.free_list@.len());
            assert(forall|i:int| #![auto] 0 <= i < self.free_list@.len() ==> self.value_list@.contains(self.free_list@[i]) == false);
            assert(self.free_list_wf());
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> page_ptr_valid(self.value_list@[i as int].ptr));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.array_ptrs@.contains(self.value_list@[i as int].ptr));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> dyn_index_valid(self.value_list@[i as int].index));


            assert(forall|i: int| #![auto] 0 <= i < rf_value_list_index@ - 1  ==> self.get_node_by_dyn_index(self.value_list@[i as int]).next == old(self).get_node_by_dyn_index(self.value_list@[i as int]).next);
            assert(forall|i: int| #![auto] rf_value_list_index@ <= i < self.value_list@.len()  ==> self.value_list@[i] == old(self).value_list@[i + 1]);
            assert(forall|i: int| #![auto] rf_value_list_index@ <= i < self.value_list@.len()  ==> self.get_node_by_dyn_index(self.value_list@[i]).next == old(self).get_node_by_dyn_index(old(self).value_list@[i + 1]).next);
            assert(forall|i: int| #![auto] 0 <= i < rf_value_list_index@ - 1  ==> self.next_value_node_of(i) == old(self).next_value_node_of(i));
            assert(forall|i: int| rf_value_list_index@ <= i < self.value_list@.len() ==> #[trigger] self.next_value_node_of(i) =~= old(self).next_value_node_of(i + 1));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.get_node_by_dyn_index(self.value_list@[i as int]).next == self.next_value_node_of(i));
            
            assert(forall|i: int| #![auto] 0 <= i < rf_value_list_index@  ==> self.get_node_by_dyn_index(self.value_list@[i as int]).prev == old(self).get_node_by_dyn_index(self.value_list@[i as int]).prev);
            assert(forall|i: int| #![auto] rf_value_list_index@ <= i < self.value_list@.len()  ==> self.value_list@[i] == old(self).value_list@[i + 1]);
            assert(forall|i: int| #![auto] rf_value_list_index@ + 1 <= i < self.value_list@.len()  ==> self.get_node_by_dyn_index(self.value_list@[i]).prev == old(self).get_node_by_dyn_index(old(self).value_list@[i + 1]).prev);
            assert(forall|i: int| #![auto] 0 <= i < rf_value_list_index@  ==> self.prev_value_node_of(i) == old(self).prev_value_node_of(i));
            assert(forall|i: int| rf_value_list_index@ + 1 <= i < self.value_list@.len() ==> #[trigger] self.prev_value_node_of(i) =~= old(self).prev_value_node_of(i + 1));

            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.get_node_by_dyn_index(self.value_list@[i as int]).prev == self.prev_value_node_of(i));
            assert(forall|i: int, j:int|  #![auto] i != j && 0 <= i < self.value_list@.len() && 0 <= j < self.value_list@.len() ==> (self.value_list@[i as int] =~= self.value_list@[j as int]) == false);
            assert(self.wf_value_head());
            assert(self.wf_value_tail());
            assert(self.len == self.value_list@.len());
            assert(forall|i:int| #![auto] 0 <= i < self.value_list@.len() ==> self.free_list@.contains(self.value_list@[i]) == false );
            assert(self.value_list_wf());
            assert(self.wf());

        }
    }

    // pub fn pop(&mut self) -> (ret:usize)
    //     requires
    //         old(self).wf(),
    //         old(self).len() > 0,
    //     ensures
    //         self.wf(),
    //         ret =~= old(self)@[0],
    //         self@ =~= old(self)@.subrange(1,old(self)@.len() as int),
    //         self.size() == old(self).size(),
    //         self.len() == old(self).len() - 1,
    //         forall|rf:usize| old(self).node_ref_valid(rf) && self.node_ref_resolve(rf) != ret ==> self.node_ref_valid(rf),
    //         forall|rf:usize| old(self).node_ref_valid(rf) && self.node_ref_resolve(rf) != ret ==> self.node_ref_resolve(rf) == old(self).node_ref_resolve(rf),
    // {
    //     proof{
    //         lemma_seq_properties::<DynIndex>();
    //         lemma_set_properties::<DynIndex>();
    //         usize_dyn_index_lemma();
    //     }
    //     if self.len() == self.size() {
    //         assert(self.free_list@.len() == 0);
    //         assert(self.size() >= DYN_ARRAY_LEN);
    //         assert(self.len() > 1);

    //         let value_head_ptr = self.value_head.ptr;
    //         let value_head_index = self.value_head.index;

    //         assert(self.value_list@[0] == self.value_head);
    //         assert(self.prev_value_node_of(0).ptr == 0 && self.prev_value_node_of(0).index == 0);
    //         assert(self.get_node_by_dyn_index(self.value_head).prev.ptr == 0 && self.get_node_by_dyn_index(self.value_head).prev.index == 0);

    //         let tracked value_head_array_perm = self.array_perms.borrow().tracked_borrow(value_head_ptr);
    //         let value_head_array : &DynArray = PPtr::<DynArray>::from_usize(value_head_ptr).borrow(Tracked(value_head_array_perm));
    //         let (next_value_ptr,next_value_index) = value_head_array.get_next_ptr_index(value_head_index);
    //         let ret = value_head_array.get_value(value_head_index);

    //         assert(self.value_list@[0] =~= self.value_head);
    //         assert(self.get_node_by_dyn_index(self.value_head).next.ptr == next_value_ptr && self.get_node_by_dyn_index(self.value_head).next.index == next_value_index);
    //         assert(self.get_node_by_dyn_index(self.value_head).next.ptr == self.next_value_node_of(0).ptr && self.get_node_by_dyn_index(self.value_head).next.index == self.next_value_node_of(0).index);
    //         assert(self.get_node_by_dyn_index(self.value_head).next.ptr == self.value_list@[1].ptr && self.get_node_by_dyn_index(self.value_head).next.index == self.value_list@[1].index);
    //         assert(self.value_list@[1].ptr == next_value_ptr && self.value_list@[1].index == next_value_index);


    //         let mut next_value_array_perm =
    //             Tracked((self.array_perms.borrow_mut()).tracked_remove(next_value_ptr));
    //         assert(next_value_array_perm@@.value.is_Some());
    //         dyn_array_set_prev(&PPtr::<DynArray>::from_usize(next_value_ptr), &mut next_value_array_perm, 0,0,next_value_index);
    //         proof{
    //             (self.array_perms.borrow_mut())
    //                 .tracked_insert(next_value_ptr, next_value_array_perm.get());
    //         }

    //         let mut value_head_array_perm =
    //             Tracked((self.array_perms.borrow_mut()).tracked_remove(value_head_ptr));
    //         assert(value_head_array_perm@@.value.is_Some());
    //         // dyn_array_set_prev(&PPtr::<DynArray>::from_usize(value_head_ptr), &mut value_head_array_perm, 0,0,value_head_index);
    //         dyn_array_set_next(&PPtr::<DynArray>::from_usize(value_head_ptr), &mut value_head_array_perm, 0,0,value_head_index);
    //         dyn_array_pop_value_to_free(&PPtr::<DynArray>::from_usize(value_head_ptr), &mut value_head_array_perm,value_head_index);
    //         proof{
    //             (self.array_perms.borrow_mut())
    //                 .tracked_insert(value_head_ptr, value_head_array_perm.get());
    //         }

    //         self.value_head.ptr = next_value_ptr;
    //         self.value_head.index = next_value_index;
    //         proof{
    //             self.value_list@ = self.value_list@.subrange(1,self.value_list@.len() as int);
    //             self.spec_seq@ = self.spec_seq@.subrange(1,self.spec_seq@.len() as int);
    //         }

    //         self.free_head.ptr = value_head_ptr;
    //         self.free_head.index = value_head_index;
    //         self.free_tail.ptr = value_head_ptr;
    //         self.free_tail.index = value_head_index;

    //         proof{
    //             self.free_list@ = self.free_list@.push(DynIndex{ptr:value_head_ptr, index:value_head_index});
    //         }

    //         self.len = self.len - 1;

    //         assert(self.array_perms_wf());
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.array_perms@[self.free_list@[i].ptr]@.value.get_Some_0().free_set@.contains(self.free_list@[i].index));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.array_perms@[self.value_list@[i].ptr]@.value.get_Some_0().value_set@.contains(self.value_list@[i].index));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old(self).array_perms@.dom().contains(array_ptr) && old(self).array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index) ==> (self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index)));
    //         assert(old(self).free_list@ =~= self.free_list@.subrange(0, self.free_list@.len() - 1));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old(self).free_list@.contains(DynIndex{ptr:array_ptr,index:index}) ==> self.free_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index) ==> self.free_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //         assert(self.value_list@ =~= old(self).value_list@.subrange(1, old(self).value_list@.len() as int));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index) && array_ptr != value_head_ptr ==> (old(self).array_perms@.dom().contains(array_ptr) && old(self).array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index)));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old(self).value_list@.contains(DynIndex{ptr:array_ptr,index:index}) && (DynIndex{ptr:array_ptr,index:index} =~= old(self).value_head == false) ==> self.value_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index) ==> self.value_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //         assert(self.array_sets_wf());
    //         assert(self.spec_seq_wf());
    //         assert(self.free_list_wf());
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> page_ptr_valid(self.value_list@[i as int].ptr));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.array_ptrs@.contains(self.value_list@[i as int].ptr));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> dyn_index_valid(self.value_list@[i as int].index));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.get_node_by_dyn_index(self.value_list@[i as int]).next == old(self).get_node_by_dyn_index(old(self).value_list@[(i as int) + 1]).next);
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.next_value_node_of(i) == old(self).next_value_node_of(i + 1));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.get_node_by_dyn_index(self.value_list@[i as int]).next == self.next_value_node_of(i));
            
    //         assert(forall|i: int| #![auto] 1 <= i < self.value_list@.len() ==> self.get_node_by_dyn_index(self.value_list@[i as int]).prev == old(self).get_node_by_dyn_index(old(self).value_list@[(i as int) + 1]).prev);
    //         assert(forall|i: int| #![auto] 1 <= i < self.value_list@.len() ==>  self.prev_value_node_of(i) == old(self).prev_value_node_of(i + 1));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.get_node_by_dyn_index(self.value_list@[i as int]).prev == self.prev_value_node_of(i));
    //         assert(forall|i: int, j:int|  #![auto] i != j && 0 <= i < self.value_list@.len() && 0 <= j < self.value_list@.len() ==> (self.value_list@[i as int] =~= self.value_list@[j as int]) == false);
    //         assert(self.wf_value_head());
    //         assert(self.wf_value_tail());
    //         assert(self.len == self.value_list@.len());
    //         assert(forall|i:int| #![auto] 0 <= i < self.value_list@.len() ==> self.free_list@.contains(self.value_list@[i]) == false );
    //         assert(self.value_list_wf());

    //         return ret;
    //     }else if self.len() == 1{
    //         assert(self.free_list@.len() > 1);
    //         assert(self.value_head =~= self.value_tail);
    //         let value_head_ptr = self.value_head.ptr;
    //         let value_head_index = self.value_head.index;
    //         let free_tail_ptr = self.free_tail.ptr;
    //         let free_tail_index = self.free_tail.index;

    //         assert(self.value_list@[0] == self.value_head);
    //         assert(self.prev_value_node_of(0).ptr == 0 && self.prev_value_node_of(0).index == 0);
    //         assert(self.get_node_by_dyn_index(self.value_head).prev.ptr == 0 && self.get_node_by_dyn_index(self.value_head).prev.index == 0);
    //         assert(self.value_list@[self.value_list@.len() - 1] == self.value_head);
    //         assert(self.next_value_node_of(0).ptr == 0 && self.next_value_node_of(0).index == 0);
    //         assert(self.get_node_by_dyn_index(self.value_head).next.ptr == 0 && self.get_node_by_dyn_index(self.value_head).next.index == 0);

    //         let tracked value_head_array_perm = self.array_perms.borrow().tracked_borrow(value_head_ptr);
    //         let value_head_array : &DynArray = PPtr::<DynArray>::from_usize(value_head_ptr).borrow(Tracked(value_head_array_perm));
    //         let ret = value_head_array.get_value(value_head_index);

    //         let mut value_head_array_perm =
    //             Tracked((self.array_perms.borrow_mut()).tracked_remove(value_head_ptr));
    //         assert(value_head_array_perm@@.value.is_Some());
    //         dyn_array_set_prev(&PPtr::<DynArray>::from_usize(value_head_ptr), &mut value_head_array_perm, free_tail_ptr,free_tail_index,value_head_index);
    //         dyn_array_set_next(&PPtr::<DynArray>::from_usize(value_head_ptr), &mut value_head_array_perm, 0,0,value_head_index);
    //         dyn_array_pop_value_to_free(&PPtr::<DynArray>::from_usize(value_head_ptr), &mut value_head_array_perm,value_head_index);
    //         proof{
    //             (self.array_perms.borrow_mut())
    //                 .tracked_insert(value_head_ptr, value_head_array_perm.get());
    //         }

    //         let mut free_tail_array_perm =
    //             Tracked((self.array_perms.borrow_mut()).tracked_remove(free_tail_ptr));
    //         assert(free_tail_array_perm@@.value.is_Some());
    //         dyn_array_set_next(&PPtr::<DynArray>::from_usize(free_tail_ptr), &mut free_tail_array_perm, value_head_ptr,value_head_index,free_tail_index);
    //         proof{
    //             (self.array_perms.borrow_mut())
    //                 .tracked_insert(free_tail_ptr, free_tail_array_perm.get());
    //         }

    //         self.value_head.ptr = 0;
    //         self.value_head.index = 0;
    //         self.value_tail.ptr = 0;
    //         self.value_tail.index = 0;
    //         proof{
    //             self.value_list@ = self.value_list@.subrange(1,self.value_list@.len() as int);
    //             self.spec_seq@ = self.spec_seq@.subrange(1,self.spec_seq@.len() as int);
    //         }

    //         self.free_tail.ptr = value_head_ptr;
    //         self.free_tail.index = value_head_index;

    //         proof{
    //             self.free_list@ = self.free_list@.push(DynIndex{ptr:value_head_ptr, index:value_head_index});
    //         }

    //         self.len = self.len - 1;

    //         assert(self.array_perms_wf());
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.array_perms@[self.free_list@[i].ptr]@.value.get_Some_0().free_set@.contains(self.free_list@[i].index));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.array_perms@[self.value_list@[i].ptr]@.value.get_Some_0().value_set@.contains(self.value_list@[i].index));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old(self).array_perms@.dom().contains(array_ptr) && old(self).array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index) ==> (self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index)));
    //         assert(old(self).free_list@ =~= self.free_list@.subrange(0, self.free_list@.len() - 1));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old(self).free_list@.contains(DynIndex{ptr:array_ptr,index:index}) ==> self.free_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index) ==> self.free_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //         assert(self.value_list@ =~= old(self).value_list@.subrange(1, old(self).value_list@.len() as int));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index) && array_ptr != value_head_ptr ==> (old(self).array_perms@.dom().contains(array_ptr) && old(self).array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index)));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old(self).value_list@.contains(DynIndex{ptr:array_ptr,index:index}) && (DynIndex{ptr:array_ptr,index:index} =~= old(self).value_head == false) ==> self.value_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index) ==> self.value_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //         assert(self.array_sets_wf());
    //         assert(self.spec_seq_wf());

    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> page_ptr_valid(self.free_list@[i as int].ptr));
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.array_ptrs@.contains(self.free_list@[i as int].ptr));
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> dyn_index_valid(self.free_list@[i as int].index));
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() - 2 ==> self.get_node_by_dyn_index(self.free_list@[i as int]).next == old(self).get_node_by_dyn_index(self.free_list@[i as int]).next);
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() - 2 ==> self.next_free_node_of(i) == old(self).next_free_node_of(i));
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.get_node_by_dyn_index(self.free_list@[i as int]).next == self.next_free_node_of(i));
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() - 1 ==> self.get_node_by_dyn_index(self.free_list@[i as int]).prev == old(self).get_node_by_dyn_index(self.free_list@[i as int]).prev);
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() - 1 ==> self.prev_free_node_of(i) == old(self).prev_free_node_of(i));
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.get_node_by_dyn_index(self.free_list@[i as int]).prev == self.prev_free_node_of(i));
    //         assert(forall|i: int, j:int|  #![auto] i != j && 0 <= i < self.free_list@.len() && 0 <= j < self.free_list@.len() ==> (self.free_list@[i as int] =~= self.free_list@[j as int]) == false);
    //         assert(self.wf_free_head());
    //         assert(self.wf_free_tail());
    //         assert(self.size - self.len == self.free_list@.len());
    //         assert(forall|i:int| #![auto] 0 <= i < self.free_list@.len() ==> self.value_list@.contains(self.free_list@[i]) == false);
    //         assert(self.free_list_wf());
    //         assert(self.value_list_wf());

    //         return ret;
    //     }else{
    //         assert(self.free_list@.len() > 0);
    //         assert(self.value_list@.len() > 1);

    //         let value_head_ptr = self.value_head.ptr;
    //         let value_head_index = self.value_head.index;
    //         let free_tail_ptr = self.free_tail.ptr;
    //         let free_tail_index = self.free_tail.index;

    //         assert(self.value_list@[0] == self.value_head);
    //         assert(self.prev_value_node_of(0).ptr == 0 && self.prev_value_node_of(0).index == 0);
    //         assert(self.get_node_by_dyn_index(self.value_head).prev.ptr == 0 && self.get_node_by_dyn_index(self.value_head).prev.index == 0);

    //         let tracked value_head_array_perm = self.array_perms.borrow().tracked_borrow(value_head_ptr);
    //         let value_head_array : &DynArray = PPtr::<DynArray>::from_usize(value_head_ptr).borrow(Tracked(value_head_array_perm));
    //         let (next_value_ptr,next_value_index) = value_head_array.get_next_ptr_index(value_head_index);
    //         let ret = value_head_array.get_value(value_head_index);

    //         assert(self.value_list@[0] =~= self.value_head);
    //         assert(self.get_node_by_dyn_index(self.value_head).next.ptr == next_value_ptr && self.get_node_by_dyn_index(self.value_head).next.index == next_value_index);
    //         assert(self.get_node_by_dyn_index(self.value_head).next.ptr == self.next_value_node_of(0).ptr && self.get_node_by_dyn_index(self.value_head).next.index == self.next_value_node_of(0).index);
    //         assert(self.get_node_by_dyn_index(self.value_head).next.ptr == self.value_list@[1].ptr && self.get_node_by_dyn_index(self.value_head).next.index == self.value_list@[1].index);
    //         assert(self.value_list@[1].ptr == next_value_ptr && self.value_list@[1].index == next_value_index);

    //         let mut next_value_array_perm =
    //             Tracked((self.array_perms.borrow_mut()).tracked_remove(next_value_ptr));
    //         assert(next_value_array_perm@@.value.is_Some());
    //         dyn_array_set_prev(&PPtr::<DynArray>::from_usize(next_value_ptr), &mut next_value_array_perm, 0,0,next_value_index);
    //         proof{
    //             (self.array_perms.borrow_mut())
    //                 .tracked_insert(next_value_ptr, next_value_array_perm.get());
    //         }

    //         let mut value_head_array_perm =
    //             Tracked((self.array_perms.borrow_mut()).tracked_remove(value_head_ptr));
    //         assert(value_head_array_perm@@.value.is_Some());
    //         dyn_array_set_prev(&PPtr::<DynArray>::from_usize(value_head_ptr), &mut value_head_array_perm, free_tail_ptr,free_tail_index,value_head_index);
    //         dyn_array_set_next(&PPtr::<DynArray>::from_usize(value_head_ptr), &mut value_head_array_perm, 0,0,value_head_index);
    //         dyn_array_pop_value_to_free(&PPtr::<DynArray>::from_usize(value_head_ptr), &mut value_head_array_perm,value_head_index);
    //         proof{
    //             (self.array_perms.borrow_mut())
    //                 .tracked_insert(value_head_ptr, value_head_array_perm.get());
    //         }

    //         self.value_head.ptr = next_value_ptr;
    //         self.value_head.index = next_value_index;
    //         proof{
    //             self.value_list@ = self.value_list@.subrange(1,self.value_list@.len() as int);
    //             self.spec_seq@ = self.spec_seq@.subrange(1,self.spec_seq@.len() as int);
    //         }


    //         let mut free_tail_array_perm =
    //             Tracked((self.array_perms.borrow_mut()).tracked_remove(free_tail_ptr));
    //         assert(free_tail_array_perm@@.value.is_Some());
    //         dyn_array_set_next(&PPtr::<DynArray>::from_usize(free_tail_ptr), &mut free_tail_array_perm, value_head_ptr,value_head_index,free_tail_index);
    //         proof{
    //             (self.array_perms.borrow_mut())
    //                 .tracked_insert(free_tail_ptr, free_tail_array_perm.get());
    //         }

    //         self.free_tail.ptr = value_head_ptr;
    //         self.free_tail.index = value_head_index;

    //         proof{
    //             self.free_list@ = self.free_list@.push(DynIndex{ptr:value_head_ptr,index:value_head_index});
    //         }

    //         self.len = self.len - 1;

    //         assert(self.array_perms_wf());
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.array_perms@[self.free_list@[i].ptr]@.value.get_Some_0().free_set@.contains(self.free_list@[i].index));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.array_perms@[self.value_list@[i].ptr]@.value.get_Some_0().value_set@.contains(self.value_list@[i].index));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old(self).array_perms@.dom().contains(array_ptr) && old(self).array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index) ==> (self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index)));
    //         assert(old(self).free_list@ =~= self.free_list@.subrange(0, self.free_list@.len() - 1));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old(self).free_list@.contains(DynIndex{ptr:array_ptr,index:index}) ==> self.free_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index) ==> self.free_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //         assert(self.value_list@ =~= old(self).value_list@.subrange(1, old(self).value_list@.len() as int));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index) && array_ptr != value_head_ptr ==> (old(self).array_perms@.dom().contains(array_ptr) && old(self).array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index)));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old(self).value_list@.contains(DynIndex{ptr:array_ptr,index:index}) && (DynIndex{ptr:array_ptr,index:index} =~= old(self).value_head == false) ==> self.value_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index) ==> self.value_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //         assert(self.array_sets_wf());
    //         assert(self.spec_seq_wf());

    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> page_ptr_valid(self.free_list@[i as int].ptr));
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.array_ptrs@.contains(self.free_list@[i as int].ptr));
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> dyn_index_valid(self.free_list@[i as int].index));

    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() - 2 ==> self.get_node_by_dyn_index(self.free_list@[i as int]).next == old(self).get_node_by_dyn_index(self.free_list@[i]).next);
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() - 2 ==> self.next_free_node_of(i) == old(self).next_free_node_of(i));
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() - 2 ==> self.get_node_by_dyn_index(self.free_list@[i as int]).next == self.next_free_node_of(i));
    //         // assert(self.free_list@[0 as int] =~= DynIndex{ptr:value_head_ptr, index:value_head_index});
    //         // assert(self.free_list@[1 as int] =~= DynIndex{ptr:free_head_ptr, index:free_head_index});
    //         // assert(self.get_node_by_dyn_index(self.free_list@[0 as int]).next =~= DynIndex{ptr:free_head_ptr, index:free_head_index});
    //         // assert(self.next_free_node_of(0) =~= DynIndex{ptr:free_head_ptr, index:free_head_index});
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.get_node_by_dyn_index(self.free_list@[i as int]).next == self.next_free_node_of(i));

    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() - 1 ==> self.get_node_by_dyn_index(self.free_list@[i as int]).prev == old(self).get_node_by_dyn_index(self.free_list@[i]).prev);
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() - 1 ==> self.prev_free_node_of(i) == old(self).prev_free_node_of(i));
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() - 1 ==> self.get_node_by_dyn_index(self.free_list@[i as int]).prev == self.prev_free_node_of(i));
    //         assert(forall|i: int, j:int|  #![auto] i != j && 0 <= i < self.free_list@.len() && 0 <= j < self.free_list@.len() ==> (self.free_list@[i as int] =~= self.free_list@[j as int]) == false);
    //         assert(self.wf_free_head());
    //         assert(self.wf_free_tail());
    //         assert(self.size - self.len == self.free_list@.len());
    //         assert(forall|i:int| #![auto] 0 <= i < self.free_list@.len() ==> self.value_list@.contains(self.free_list@[i]) == false);

    //         assert(self.free_list_wf());
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> page_ptr_valid(self.value_list@[i as int].ptr));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.array_ptrs@.contains(self.value_list@[i as int].ptr));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> dyn_index_valid(self.value_list@[i as int].index));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.get_node_by_dyn_index(self.value_list@[i as int]).next == old(self).get_node_by_dyn_index(old(self).value_list@[(i as int) + 1]).next);
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.next_value_node_of(i) == old(self).next_value_node_of(i + 1));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.get_node_by_dyn_index(self.value_list@[i as int]).next == self.next_value_node_of(i));
    //         assert(forall|i: int| #![auto] 1 <= i < self.value_list@.len() ==> self.get_node_by_dyn_index(self.value_list@[i as int]).prev == old(self).get_node_by_dyn_index(old(self).value_list@[(i as int) + 1]).prev);
    //         assert(forall|i: int| #![auto] 1 <= i < self.value_list@.len() ==>  self.prev_value_node_of(i) == old(self).prev_value_node_of(i + 1));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.get_node_by_dyn_index(self.value_list@[i as int]).prev == self.prev_value_node_of(i));
    //         assert(forall|i: int, j:int|  #![auto] i != j && 0 <= i < self.value_list@.len() && 0 <= j < self.value_list@.len() ==> (self.value_list@[i as int] =~= self.value_list@[j as int]) == false);
    //         assert(self.wf_value_head());
    //         assert(self.wf_value_tail());
    //         assert(self.len == self.value_list@.len());
    //         assert(forall|i:int| #![auto] 0 <= i < self.value_list@.len() ==> self.free_list@.contains(self.value_list@[i]) == false );
    //         assert(self.value_list_wf());

    //         return ret;
    //     }

    // }

    // pub fn push(&mut self, new_value:usize) -> (ret:usize)
    //     requires
    //         old(self).wf(),
    //         old(self)@.contains(new_value) == false,
    //         old(self).size() > old(self).len(),
    //         old(self).size() >= DYN_ARRAY_LEN,
    //     ensures
    //         self.wf(),
    //         self@ =~= old(self)@.push(new_value),
    //         self.size() == old(self).size(),
    //         self.len() == old(self).len() + 1,
    //         self.node_ref_valid(ret),
    //         self.node_ref_resolve(ret) == new_value,
    //         forall|rf:usize| old(self).node_ref_valid(rf) ==> self.node_ref_valid(rf),
    //         forall|rf:usize| old(self).node_ref_valid(rf) ==> rf != ret,
    //         forall|rf:usize| old(self).node_ref_valid(rf) ==> self.node_ref_resolve(rf) == old(self).node_ref_resolve(rf),
    // {
    //     proof{
    //         lemma_seq_properties::<DynIndex>();
    //         lemma_set_properties::<DynIndex>();
    //         usize_dyn_index_lemma();
    //     }
    //     assert(self.free_list@.len() != 0);
    //     if self.size == self.len + 1 {
    //         assert(self.value_list@.len() > 1);
    //         assert(self.free_list@.len() == 1);
    //         assert(self.free_head =~= self.free_tail);
    //         assert(self.free_list@[0] == self.free_tail);
    //         assert(self.next_free_node_of(0).ptr == 0 && self.next_free_node_of(0).index == 0);
    //         assert(self.get_node_by_dyn_index(self.free_tail).next.ptr == 0 && self.get_node_by_dyn_index(self.free_tail).next.index == 0);
    //         let free_head_ptr = self.free_head.ptr;
    //         let free_head_index = self.free_head.index;
    //         let value_tail_ptr = self.value_tail.ptr;
    //         let value_tail_index = self.value_tail.index;
    //         assert(self.array_perms@[free_head_ptr]@.value.get_Some_0().free_set@.contains(free_head_index));
            
    //         self.free_head.ptr = 0;
    //         self.free_head.index = 0;            
    //         self.free_tail.ptr = 0;
    //         self.free_tail.index = 0;
    //         proof{self.free_list@ = self.free_list@.subrange(1,1)}
    //         let mut free_head_array_perm =
    //             Tracked((self.array_perms.borrow_mut()).tracked_remove(free_head_ptr));
    //         assert(free_head_array_perm@@.value.is_Some());
    //         dyn_array_set_prev(&PPtr::<DynArray>::from_usize(free_head_ptr), &mut free_head_array_perm, value_tail_ptr,value_tail_index,free_head_index);
    //         dyn_array_pop_free_to_value(&PPtr::<DynArray>::from_usize(free_head_ptr), &mut free_head_array_perm,free_head_index);
    //         dyn_array_set_value(&PPtr::<DynArray>::from_usize(free_head_ptr), &mut free_head_array_perm,new_value,free_head_index);
    //         proof{
    //             (self.array_perms.borrow_mut())
    //                 .tracked_insert(free_head_ptr, free_head_array_perm.get());
    //         }

    //         let mut value_tail_array_perm =
    //             Tracked((self.array_perms.borrow_mut()).tracked_remove(value_tail_ptr));
    //         assert(value_tail_array_perm@@.value.is_Some());
    //         dyn_array_set_next(&PPtr::<DynArray>::from_usize(value_tail_ptr), &mut value_tail_array_perm, free_head_ptr,free_head_index,value_tail_index);
    //         proof{
    //             (self.array_perms.borrow_mut())
    //                 .tracked_insert(value_tail_ptr, value_tail_array_perm.get());
    //         }

    //         self.value_tail.ptr = free_head_ptr;
    //         self.value_tail.index = free_head_index;
    //         proof{
    //             self.value_list@ = self.value_list@.push(DynIndex{ptr:free_head_ptr,index:free_head_index});
    //             self.spec_seq@ = self.spec_seq@.push(new_value);
    //         }
    //         self.len = self.len + 1;

    //         assert(self.array_perms_wf());
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.array_perms@[self.free_list@[i].ptr]@.value.get_Some_0().free_set@.contains(self.free_list@[i].index));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.array_perms@[self.value_list@[i].ptr]@.value.get_Some_0().value_set@.contains(self.value_list@[i].index));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index) && array_ptr != free_head_ptr ==> (old(self).array_perms@.dom().contains(array_ptr) && old(self).array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index)));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old(self).free_list@.contains(DynIndex{ptr:array_ptr,index:index}) && (DynIndex{ptr:array_ptr,index:index} =~= old(self).free_head == false) ==> self.free_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index) ==> self.free_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old(self).array_perms@.dom().contains(array_ptr) && old(self).array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index) ==> (self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index)));
    //         assert(old(self).value_list@ =~= self.value_list@.subrange(0, self.value_list@.len() - 1));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old(self).value_list@.contains(DynIndex{ptr:array_ptr,index:index}) ==> self.value_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index) ==> self.value_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //         assert(self.array_sets_wf());
    //         assert(self.spec_seq_wf());
    //         assert(self.free_list_wf());
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> page_ptr_valid(self.value_list@[i as int].ptr));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.array_ptrs@.contains(self.value_list@[i as int].ptr));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> dyn_index_valid(self.value_list@[i as int].index));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() - 2 ==> self.get_node_by_dyn_index(self.value_list@[i as int]).next == old(self).get_node_by_dyn_index(self.value_list@[i as int]).next);
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() - 2 ==> self.next_value_node_of(i) == old(self).next_value_node_of(i));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.get_node_by_dyn_index(self.value_list@[i as int]).next == self.next_value_node_of(i));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() - 1 ==> self.get_node_by_dyn_index(self.value_list@[i as int]).prev == old(self).get_node_by_dyn_index(self.value_list@[i as int]).prev);
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() - 1 ==> self.prev_value_node_of(i) == old(self).prev_value_node_of(i));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.get_node_by_dyn_index(self.value_list@[i as int]).prev == self.prev_value_node_of(i));
    //         assert(forall|i: int, j:int|  #![auto] i != j && 0 <= i < self.value_list@.len() && 0 <= j < self.value_list@.len() ==> (self.value_list@[i as int] =~= self.value_list@[j as int]) == false);
    //         assert(self.value_list_wf());

    //         return dyn_ptr_index_to_usize(free_head_ptr, free_head_index);
    //     }else if self.len() != 0 {
    //         assert(self.free_list@.len() > 1);

    //         assert(self.next_free_node_of(self.free_list@.len() - 1).ptr == 0 && self.next_free_node_of(self.free_list@.len() - 1).index == 0);
    //         assert(self.get_node_by_dyn_index(self.free_tail).next.ptr == 0 && self.get_node_by_dyn_index(self.free_tail).next.index == 0);
    //         let free_tail_ptr = self.free_tail.ptr;
    //         let free_tail_index = self.free_tail.index;
    //         let value_tail_ptr = self.value_tail.ptr;
    //         let value_tail_index = self.value_tail.index;
    //         assert(self.array_perms@[free_tail_ptr]@.value.get_Some_0().free_set@.contains(free_tail_index));

    //         let tracked free_tail_array_perm = self.array_perms.borrow().tracked_borrow(free_tail_ptr);
    //         let free_tail_array : &DynArray = PPtr::<DynArray>::from_usize(free_tail_ptr).borrow(Tracked(free_tail_array_perm));
    //         let (prev_free_ptr,prev_free_index) = free_tail_array.get_prev_ptr_index(free_tail_index);

    //         assert(self.free_list@[self.free_list@.len() - 1] =~= self.free_tail);
    //         assert(self.get_node_by_dyn_index(self.free_tail).prev.ptr == prev_free_ptr && self.get_node_by_dyn_index(self.free_tail).prev.index == prev_free_index);
    //         assert(self.get_node_by_dyn_index(self.free_tail).prev.ptr == self.prev_free_node_of(self.free_list@.len() - 1).ptr && self.get_node_by_dyn_index(self.free_tail).prev.index == self.prev_free_node_of(self.free_list@.len() - 1).index);
    //         assert(self.get_node_by_dyn_index(self.free_tail).prev.ptr == self.free_list@[self.free_list@.len() - 2].ptr && self.get_node_by_dyn_index(self.free_tail).prev.index == self.free_list@[self.free_list@.len() - 2].index);
    //         assert(self.free_list@[self.free_list@.len() - 2].ptr == prev_free_ptr && self.free_list@[self.free_list@.len() - 2].index == prev_free_index);

    //         let mut prev_free_array_perm =
    //             Tracked((self.array_perms.borrow_mut()).tracked_remove(prev_free_ptr));
    //         assert(prev_free_array_perm@@.value.is_Some());
    //         dyn_array_set_next(&PPtr::<DynArray>::from_usize(prev_free_ptr), &mut prev_free_array_perm, 0,0,prev_free_index);
    //         proof{
    //             (self.array_perms.borrow_mut())
    //                 .tracked_insert(prev_free_ptr, prev_free_array_perm.get());
    //         }

    //         let mut free_tail_array_perm =
    //             Tracked((self.array_perms.borrow_mut()).tracked_remove(free_tail_ptr));
    //         assert(free_tail_array_perm@@.value.is_Some());
    //         dyn_array_set_prev(&PPtr::<DynArray>::from_usize(free_tail_ptr), &mut free_tail_array_perm, value_tail_ptr,value_tail_index,free_tail_index);
    //         dyn_array_pop_free_to_value(&PPtr::<DynArray>::from_usize(free_tail_ptr), &mut free_tail_array_perm,free_tail_index);
    //         dyn_array_set_value(&PPtr::<DynArray>::from_usize(free_tail_ptr), &mut free_tail_array_perm,new_value,free_tail_index);
    //         proof{
    //             (self.array_perms.borrow_mut())
    //                 .tracked_insert(free_tail_ptr, free_tail_array_perm.get());
    //         }

    //         self.free_tail.ptr = prev_free_ptr;
    //         self.free_tail.index = prev_free_index;
    //         proof{self.free_list@ = self.free_list@.subrange(0,self.free_list@.len() - 1);}

    //         let mut value_tail_array_perm =
    //             Tracked((self.array_perms.borrow_mut()).tracked_remove(value_tail_ptr));
    //         assert(value_tail_array_perm@@.value.is_Some());
    //         dyn_array_set_next(&PPtr::<DynArray>::from_usize(value_tail_ptr), &mut value_tail_array_perm, free_tail_ptr,free_tail_index,value_tail_index);
    //         proof{
    //             (self.array_perms.borrow_mut())
    //                 .tracked_insert(value_tail_ptr, value_tail_array_perm.get());
    //         }

    //         self.value_tail.ptr = free_tail_ptr;
    //         self.value_tail.index = free_tail_index;
    //         proof{
    //             self.value_list@ = self.value_list@.push(DynIndex{ptr:free_tail_ptr,index:free_tail_index});
    //             self.spec_seq@ = self.spec_seq@.push(new_value);
    //         }
    //         self.len = self.len + 1;

    //         assert(self.array_perms_wf());
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.array_perms@[self.free_list@[i].ptr]@.value.get_Some_0().free_set@.contains(self.free_list@[i].index));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.array_perms@[self.value_list@[i].ptr]@.value.get_Some_0().value_set@.contains(self.value_list@[i].index));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index) && array_ptr != free_tail_ptr ==> (old(self).array_perms@.dom().contains(array_ptr) && old(self).array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index)));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old(self).free_list@.contains(DynIndex{ptr:array_ptr,index:index}) && (DynIndex{ptr:array_ptr,index:index} =~= old(self).free_tail == false) ==> self.free_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index) ==> self.free_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old(self).array_perms@.dom().contains(array_ptr) && old(self).array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index) ==> (self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index)));
    //         assert(old(self).value_list@ =~= self.value_list@.subrange(0, self.value_list@.len() - 1));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old(self).value_list@.contains(DynIndex{ptr:array_ptr,index:index}) ==> self.value_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index) ==> self.value_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //         assert(self.array_sets_wf());
    //         assert(self.spec_seq_wf());
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> page_ptr_valid(self.free_list@[i as int].ptr));
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.array_ptrs@.contains(self.free_list@[i as int].ptr));
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> dyn_index_valid(self.free_list@[i as int].index));
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() - 1 ==> self.get_node_by_dyn_index(self.free_list@[i as int]).next == old(self).get_node_by_dyn_index(self.free_list@[i as int]).next);
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() - 1 ==> self.next_free_node_of(i) == old(self).next_free_node_of(i));
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.get_node_by_dyn_index(self.free_list@[i as int]).next == self.next_free_node_of(i));
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.get_node_by_dyn_index(self.free_list@[i as int]).prev == old(self).get_node_by_dyn_index(self.free_list@[i as int]).prev);
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.prev_free_node_of(i) == old(self).prev_free_node_of(i));
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.get_node_by_dyn_index(self.free_list@[i as int]).prev == self.prev_free_node_of(i));
    //         assert(forall|i: int, j:int|  #![auto] i != j && 0 <= i < self.free_list@.len() && 0 <= j < self.free_list@.len() ==> (self.free_list@[i as int] =~= self.free_list@[j as int]) == false);
    //         assert(self.wf_free_head());
    //         assert(self.wf_free_tail());
    //         assert(self.size - self.len == self.free_list@.len());
    //         assert(forall|i:int| #![auto] 0 <= i < self.free_list@.len() ==> self.value_list@.contains(self.free_list@[i]) == false);
    //         assert(self.free_list_wf());
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> page_ptr_valid(self.value_list@[i as int].ptr));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.array_ptrs@.contains(self.value_list@[i as int].ptr));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> dyn_index_valid(self.value_list@[i as int].index));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() - 2 ==> self.get_node_by_dyn_index(self.value_list@[i as int]).next == old(self).get_node_by_dyn_index(self.value_list@[i as int]).next);
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() - 2 ==> self.next_value_node_of(i) == old(self).next_value_node_of(i));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.get_node_by_dyn_index(self.value_list@[i as int]).next == self.next_value_node_of(i));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() - 1 ==> self.get_node_by_dyn_index(self.value_list@[i as int]).prev == old(self).get_node_by_dyn_index(self.value_list@[i as int]).prev);
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() - 1 ==> self.prev_value_node_of(i) == old(self).prev_value_node_of(i));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.get_node_by_dyn_index(self.value_list@[i as int]).prev == self.prev_value_node_of(i));
    //         assert(forall|i: int, j:int|  #![auto] i != j && 0 <= i < self.value_list@.len() && 0 <= j < self.value_list@.len() ==> (self.value_list@[i as int] =~= self.value_list@[j as int]) == false);
    //         assert(self.value_list_wf());

    //         return dyn_ptr_index_to_usize(free_tail_ptr, free_tail_index);
    //     }else{
    //         assert(self.free_list@.len() > 1);
    //         assert(self.value_list@.len() == 0);

    //         assert(self.next_free_node_of(self.free_list@.len() - 1).ptr == 0 && self.next_free_node_of(self.free_list@.len() - 1).index == 0);
    //         assert(self.get_node_by_dyn_index(self.free_tail).next.ptr == 0 && self.get_node_by_dyn_index(self.free_tail).next.index == 0);
    //         let free_tail_ptr = self.free_tail.ptr;
    //         let free_tail_index = self.free_tail.index;
    //         assert(self.array_perms@[free_tail_ptr]@.value.get_Some_0().free_set@.contains(free_tail_index));

    //         let tracked free_tail_array_perm = self.array_perms.borrow().tracked_borrow(free_tail_ptr);
    //         let free_tail_array : &DynArray = PPtr::<DynArray>::from_usize(free_tail_ptr).borrow(Tracked(free_tail_array_perm));
    //         let (prev_free_ptr,prev_free_index) = free_tail_array.get_prev_ptr_index(free_tail_index);

    //         assert(self.free_list@[self.free_list@.len() - 1] =~= self.free_tail);
    //         assert(self.get_node_by_dyn_index(self.free_tail).prev.ptr == prev_free_ptr && self.get_node_by_dyn_index(self.free_tail).prev.index == prev_free_index);
    //         assert(self.get_node_by_dyn_index(self.free_tail).prev.ptr == self.prev_free_node_of(self.free_list@.len() - 1).ptr && self.get_node_by_dyn_index(self.free_tail).prev.index == self.prev_free_node_of(self.free_list@.len() - 1).index);
    //         assert(self.get_node_by_dyn_index(self.free_tail).prev.ptr == self.free_list@[self.free_list@.len() - 2].ptr && self.get_node_by_dyn_index(self.free_tail).prev.index == self.free_list@[self.free_list@.len() - 2].index);
    //         assert(self.free_list@[self.free_list@.len() - 2].ptr == prev_free_ptr && self.free_list@[self.free_list@.len() - 2].index == prev_free_index);

    //         let mut prev_free_array_perm =
    //             Tracked((self.array_perms.borrow_mut()).tracked_remove(prev_free_ptr));
    //         assert(prev_free_array_perm@@.value.is_Some());
    //         dyn_array_set_next(&PPtr::<DynArray>::from_usize(prev_free_ptr), &mut prev_free_array_perm, 0,0,prev_free_index);
    //         proof{
    //             (self.array_perms.borrow_mut())
    //                 .tracked_insert(prev_free_ptr, prev_free_array_perm.get());
    //         }

    //         let mut free_tail_array_perm =
    //             Tracked((self.array_perms.borrow_mut()).tracked_remove(free_tail_ptr));
    //         assert(free_tail_array_perm@@.value.is_Some());
    //         dyn_array_set_prev(&PPtr::<DynArray>::from_usize(free_tail_ptr), &mut free_tail_array_perm, 0,0,free_tail_index);
    //         dyn_array_pop_free_to_value(&PPtr::<DynArray>::from_usize(free_tail_ptr), &mut free_tail_array_perm,free_tail_index);
    //         dyn_array_set_value(&PPtr::<DynArray>::from_usize(free_tail_ptr), &mut free_tail_array_perm,new_value,free_tail_index);
    //         proof{
    //             (self.array_perms.borrow_mut())
    //                 .tracked_insert(free_tail_ptr, free_tail_array_perm.get());
    //         }

    //         self.free_tail.ptr = prev_free_ptr;
    //         self.free_tail.index = prev_free_index;
    //         proof{self.free_list@ = self.free_list@.subrange(0,self.free_list@.len() - 1);}

    //         self.value_tail.ptr = free_tail_ptr;
    //         self.value_tail.index = free_tail_index;
    //         self.value_head.ptr = free_tail_ptr;
    //         self.value_head.index = free_tail_index;
    //         proof{
    //             self.value_list@ = self.value_list@.push(DynIndex{ptr:free_tail_ptr,index:free_tail_index});
    //             self.spec_seq@ = self.spec_seq@.push(new_value);
    //         }
    //         self.len = self.len + 1;

    //         assert(self.array_perms_wf());
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.array_perms@[self.free_list@[i].ptr]@.value.get_Some_0().free_set@.contains(self.free_list@[i].index));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.array_perms@[self.value_list@[i].ptr]@.value.get_Some_0().value_set@.contains(self.value_list@[i].index));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index) && array_ptr != free_tail_ptr ==> (old(self).array_perms@.dom().contains(array_ptr) && old(self).array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index)));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old(self).free_list@.contains(DynIndex{ptr:array_ptr,index:index}) && (DynIndex{ptr:array_ptr,index:index} =~= old(self).free_tail == false) ==> self.free_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index) ==> self.free_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old(self).array_perms@.dom().contains(array_ptr) && old(self).array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index) ==> (self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index)));
    //         assert(old(self).value_list@ =~= self.value_list@.subrange(0, self.value_list@.len() - 1));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old(self).value_list@.contains(DynIndex{ptr:array_ptr,index:index}) ==> self.value_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //         assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index) ==> self.value_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //         assert(self.array_sets_wf());
    //         assert(self.spec_seq_wf());
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> page_ptr_valid(self.free_list@[i as int].ptr));
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.array_ptrs@.contains(self.free_list@[i as int].ptr));
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> dyn_index_valid(self.free_list@[i as int].index));
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() - 1 ==> self.get_node_by_dyn_index(self.free_list@[i as int]).next == old(self).get_node_by_dyn_index(self.free_list@[i as int]).next);
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() - 1 ==> self.next_free_node_of(i) == old(self).next_free_node_of(i));
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.get_node_by_dyn_index(self.free_list@[i as int]).next == self.next_free_node_of(i));
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.get_node_by_dyn_index(self.free_list@[i as int]).prev == old(self).get_node_by_dyn_index(self.free_list@[i as int]).prev);
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.prev_free_node_of(i) == old(self).prev_free_node_of(i));
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.get_node_by_dyn_index(self.free_list@[i as int]).prev == self.prev_free_node_of(i));
    //         assert(forall|i: int, j:int|  #![auto] i != j && 0 <= i < self.free_list@.len() && 0 <= j < self.free_list@.len() ==> (self.free_list@[i as int] =~= self.free_list@[j as int]) == false);
    //         assert(self.wf_free_head());
    //         assert(self.wf_free_tail());
    //         assert(self.size - self.len == self.free_list@.len());
    //         assert(forall|i:int| #![auto] 0 <= i < self.free_list@.len() ==> self.value_list@.contains(self.free_list@[i]) == false);
    //         assert(self.free_list_wf());
    //         assert(self.value_list_wf());

    //         return dyn_ptr_index_to_usize(free_tail_ptr, free_tail_index);
    //     }

    // }

    // pub fn grow(&mut self, new_array_ptr:usize, new_array_perm: Tracked<PointsTo<DynArray>>)
    //     requires
    //         new_array_ptr != 0,
    //         page_ptr_valid(new_array_ptr),
    //         old(self).size < usize::MAX - DYN_ARRAY_LEN,
    //         old(self).wf(),
    //         old(self).array_ptrs@.contains(new_array_ptr) == false,
    //         new_array_perm@@.pptr == new_array_ptr,
    //         new_array_perm@@.value.is_Some(),
    //         new_array_perm@@.value.get_Some_0().seq@.len() == DYN_ARRAY_LEN,
    //         new_array_perm@@.value.get_Some_0().free_set@.finite(),
    //         new_array_perm@@.value.get_Some_0().value_set@.finite(),
    //         new_array_perm@@.value.get_Some_0().free_set@.is_empty(),
    //         new_array_perm@@.value.get_Some_0().value_set@.is_empty(),
    //         new_array_perm@@.value.get_Some_0().free_count == 0,
    //     ensures
    //         self.wf(),
    //         self.spec_seq =~= old(self).spec_seq,
    //         self.size == old(self).size + DYN_ARRAY_LEN,
    //         self.len == old(self).len,
    //         forall|rf:usize| old(self).node_ref_valid(rf) ==> self.node_ref_valid(rf),
    //         forall|rf:usize| old(self).node_ref_valid(rf) ==> self.node_ref_resolve(rf) == old(self).node_ref_resolve(rf),
    // {
    //     proof{
    //         self.array_ptrs@ = self.array_ptrs@.insert(new_array_ptr);
    //         self.array_perms.borrow_mut().tracked_insert(new_array_ptr, new_array_perm.get());
    //     }

    //     proof{
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> old(self).next_free_node_of(i) == self.next_free_node_of(i));
    //         assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> old(self).prev_free_node_of(i) == self.prev_free_node_of(i));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> old(self).next_value_node_of(i) == self.next_value_node_of(i));
    //         assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> old(self).prev_value_node_of(i) == self.prev_value_node_of(i));
    //     }

    //     assert(forall|i:usize|#![auto] 0 <= i < DYN_ARRAY_LEN ==> self.value_list@.contains(DynIndex{ptr:new_array_ptr, index: i}) == false);
    //     assert(forall|i:usize|#![auto] 0 <= i < DYN_ARRAY_LEN ==> self.free_list@.contains(DynIndex{ptr:new_array_ptr, index: i}) == false);

    //     let mut i = 0;
    //     while i != DYN_ARRAY_LEN
    //         invariant
    //             0 <= i <= DYN_ARRAY_LEN,
    //             self.len == old(self).len,
    //             self.array_ptrs@.len() == old(self).array_ptrs@.len() + 1,
    //             self.array_ptrs@ == old(self).array_ptrs@.insert(new_array_ptr),
    //             self.array_ptrs@.contains(new_array_ptr),
    //             self.array_perms@[new_array_ptr]@.value.get_Some_0().seq@.len() == DYN_ARRAY_LEN,
    //             self.array_perms@[new_array_ptr]@.value.get_Some_0().free_set@.finite(),
    //             self.array_perms@[new_array_ptr]@.value.get_Some_0().value_set@.finite(),
    //             self.array_perms@[new_array_ptr]@.value.get_Some_0().value_set@.is_empty(),
    //             self.array_perms@[new_array_ptr]@.value.get_Some_0().value_set@.disjoint(self.array_perms@[new_array_ptr]@.value.get_Some_0().free_set@),
    //             self.array_perms@[new_array_ptr]@.value.get_Some_0().free_set@.len() == i,
    //             self.array_perms@[new_array_ptr]@.value.get_Some_0().free_set@ =~= Set::new(|index: usize| { 0<=index<i}),
    //             self.array_perms@[new_array_ptr]@.value.get_Some_0().free_count == self.array_perms@[new_array_ptr]@.value.get_Some_0().free_set@.len(),
    //             self.value_list_wf(),
    //             self.free_list_wf(),
    //             self.array_sets_wf(),
    //             self.spec_seq_wf(),
    //             self.value_list =~= old(self).value_list,
    //             self.spec_seq =~= old(self).spec_seq,
    //             self.array_ptrs@.finite(),
    //             self.array_ptrs@.contains(0) == false,
    //             self.array_ptrs@ =~= self.array_perms@.dom(),
    //             old(self).size < usize::MAX - DYN_ARRAY_LEN,
    //             self.size == old(self).size + i,
    //             self.size == (self.array_ptrs@.len() - 1) * DYN_ARRAY_LEN + i,
    //             self.array_ptrs@.finite(),
    //             self.array_ptrs@.contains(0) == false,
    //             self.array_ptrs@ =~= self.array_perms@.dom(),
    //             (forall|array_ptr:DynArrayPtr| #![auto] self.array_ptrs@.contains(array_ptr) ==> page_ptr_valid(array_ptr)),
    //             (forall|array_ptr:DynArrayPtr| #![auto] self.array_perms@.dom().contains(array_ptr) ==> self.array_perms@[array_ptr]@.pptr == array_ptr),
    //             (forall|array_ptr:DynArrayPtr| #![auto] self.array_perms@.dom().contains(array_ptr) ==> self.array_perms@[array_ptr]@.value.is_Some()),
    //             (forall|array_ptr:DynArrayPtr| #![auto] self.array_perms@.dom().contains(array_ptr) && array_ptr != new_array_ptr ==> self.array_perms@[array_ptr]@.value.get_Some_0().wf()),
    //             (forall|j:usize|#![auto] 0 <= j < DYN_ARRAY_LEN ==> self.value_list@.contains(DynIndex{ptr:new_array_ptr, index: j}) == false),
    //             (forall|j:usize|#![auto] i <= j < DYN_ARRAY_LEN ==> self.free_list@.contains(DynIndex{ptr:new_array_ptr, index: j}) == false),
    //             forall|rf:usize| old(self).node_ref_valid(rf) ==> self.node_ref_valid(rf),
    //             forall|rf:usize| old(self).node_ref_valid(rf) ==> self.node_ref_resolve(rf) == old(self).node_ref_resolve(rf),
    //         ensures
    //             i == DYN_ARRAY_LEN,
    //             self.array_sets_wf(),
    //             self.free_list_wf(),
    //             self.value_list_wf(),
    //             self.spec_seq_wf(),
    //             self.array_perms@[new_array_ptr]@.value.get_Some_0().value_set@.is_empty(),
    //             self.array_perms@[new_array_ptr]@.value.get_Some_0().free_set@.len() == DYN_ARRAY_LEN,
    //             self.array_perms@[new_array_ptr]@.value.get_Some_0().free_set@ =~= Set::new(|index: usize| { 0<=index<DYN_ARRAY_LEN}),
    //             self.array_perms@[new_array_ptr]@.value.get_Some_0().seq@.len() == DYN_ARRAY_LEN,
    //             self.array_perms@[new_array_ptr]@.value.get_Some_0().free_set@.finite(),
    //             self.array_perms@[new_array_ptr]@.value.get_Some_0().value_set@.finite(),
    //             self.array_perms@[new_array_ptr]@.value.get_Some_0().free_set@.disjoint(self.array_perms@[new_array_ptr]@.value.get_Some_0().value_set@),
    //             self.array_perms@[new_array_ptr]@.value.get_Some_0().free_set@ + self.array_perms@[new_array_ptr]@.value.get_Some_0().value_set@ =~= Set::new(|index: usize| {0<=index<DYN_ARRAY_LEN}),
    //             self.array_perms@[new_array_ptr]@.value.get_Some_0().free_count == self.array_perms@[new_array_ptr]@.value.get_Some_0().free_set@.len(),
    //             self.array_perms@[new_array_ptr]@.value.get_Some_0().wf(),
    //             (forall|array_ptr:DynArrayPtr| #![auto] self.array_perms@.dom().contains(array_ptr) ==> self.array_perms@[array_ptr]@.value.get_Some_0().wf()),
    //             self.array_perms_wf(),
    //             self.wf(),
    //             self.spec_seq =~= old(self).spec_seq,
    //             self.size == old(self).size + DYN_ARRAY_LEN,
    //             self.len == old(self).len,
    //             forall|rf:usize| old(self).node_ref_valid(rf) ==> self.node_ref_valid(rf),
    //             forall|rf:usize| old(self).node_ref_valid(rf) ==> self.node_ref_resolve(rf) == old(self).node_ref_resolve(rf),
    //     {
    //         // let old_free_list = Ghost(self.free_list@);
    //         let old_self = Ghost(*self);
    //         proof{
    //             lemma_seq_properties::<DynIndex>();
    //             lemma_set_properties::<DynIndex>();
    //             usize_dyn_index_lemma();
    //         }
    //         if self.size == self.len(){
    //             assert(self.free_list@.len() == 0);
    //             self.free_tail.ptr = new_array_ptr;
    //             self.free_tail.index = i;
    //             self.free_head.ptr = new_array_ptr;
    //             self.free_head.index = i;

    //             let mut new_array_perm =
    //                 Tracked((self.array_perms.borrow_mut()).tracked_remove(new_array_ptr));
    //             dyn_array_set_next(&PPtr::<DynArray>::from_usize(new_array_ptr), &mut new_array_perm, 0, 0,i);
    //             dyn_array_set_prev(&PPtr::<DynArray>::from_usize(new_array_ptr), &mut new_array_perm, 0,0,i);
    //             dyn_array_push_free(&PPtr::<DynArray>::from_usize(new_array_ptr), &mut new_array_perm, i);
    //             proof{
    //                 (self.array_perms.borrow_mut())
    //                     .tracked_insert(new_array_ptr, new_array_perm.get());
    //             }
    //             proof{
    //                 self.free_list@ = self.free_list@.push(DynIndex{ptr:new_array_ptr, index: i});
    //             }
    
    //             self.size = self.size + 1;
    
    //             i = i + 1;

    //             assert(forall|array_ptr:DynArrayPtr| #![auto] old_self@.array_perms@.dom().contains(array_ptr) && array_ptr != new_array_ptr ==> old_self@.array_perms@[array_ptr]@.value.get_Some_0().free_set =~= self.array_perms@[array_ptr]@.value.get_Some_0().free_set);
    //             assert(forall|index:usize| #![auto] old_self@.array_perms@[new_array_ptr]@.value.get_Some_0().free_set@.contains(index) ==> self.array_perms@[new_array_ptr]@.value.get_Some_0().free_set@.contains(index));
    //             assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index) && array_ptr != new_array_ptr ==> (old_self@.array_perms@.dom().contains(array_ptr) && old_self@.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index)));
    //             assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old_self@.free_list@.contains(DynIndex{ptr:array_ptr,index:index}) ==> self.free_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //             assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index) && array_ptr != new_array_ptr ==> self.free_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //             assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index) ==> self.free_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //             assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index) ==> self.value_list@.contains(DynIndex{ptr:array_ptr,index:index}));

    //             assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> page_ptr_valid(self.value_list@[i as int].ptr));
    //             assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.array_ptrs@.contains(self.value_list@[i as int].ptr));
    //             assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> dyn_index_valid(self.value_list@[i as int].index));
    //             assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.get_node_by_dyn_index(self.value_list@[i as int]) =~= old_self@.get_node_by_dyn_index(self.value_list@[i as int]));
    //             assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.next_value_node_of(i) =~= old_self@.next_value_node_of(i));
    //             assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.prev_value_node_of(i) =~= old_self@.prev_value_node_of(i));
    //             assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.get_node_by_dyn_index(self.value_list@[i as int]).next == self.next_value_node_of(i));
    //             assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.get_node_by_dyn_index(self.value_list@[i as int]).prev == self.prev_value_node_of(i));
    //             assert(forall|i: int, j:int| #![auto] i != j && 0 <= i < self.value_list@.len() && 0 <= j < self.value_list@.len() ==> (self.value_list@[i as int] =~= self.value_list@[j as int]) == false);
    //             assert(self.wf_value_head());
    //             assert(self.wf_value_tail());
    //             assert(self.len == self.value_list@.len());
    //             assert(forall|i:int| #![auto] 0 <= i < self.value_list@.len() ==> self.free_list@.contains(self.value_list@[i]) == false);

    //             assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> page_ptr_valid(self.free_list@[i as int].ptr));
    //             assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.array_ptrs@.contains(self.free_list@[i as int].ptr));
    //             assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> dyn_index_valid(self.free_list@[i as int].index));
    //             assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.get_node_by_dyn_index(self.free_list@[i as int]).next == self.next_free_node_of(i));
    //             assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.get_node_by_dyn_index(self.free_list@[i as int]).prev == self.prev_free_node_of(i));
    //             assert(forall|i: int, j:int|  #![auto] i != j && 0 <= i < self.free_list@.len() && 0 <= j < self.free_list@.len() ==> (self.free_list@[i as int] =~= self.free_list@[j as int]) == false);
    //             assert(self.wf_free_head());
    //             assert(self.wf_free_tail());
    //             assert(self.size - self.len == self.free_list@.len());
    //             assert(forall|i:int| #![auto] 0 <= i < self.free_list@.len() ==> self.value_list@.contains(self.free_list@[i]) == false);
    //             assert(self.free_list@.len() != 0 ==> ((self.array_ptrs@.contains(self.free_head.ptr))&&(dyn_index_valid(self.free_head.index))&&(self.array_ptrs@.contains(self.free_tail.ptr))&&(dyn_index_valid(self.free_tail.index))));
    //         }else{
    //             let free_tail_ptr = self.free_tail.ptr;
    //             let free_tail_index = self.free_tail.index;

    //             assert(self.value_list@.contains(self.free_tail) == false);
    //             assert(self.value_list@.contains(DynIndex{ptr:new_array_ptr,index:i}) == false);
    //             assert(self.free_list@[self.free_list@.len() - 1] =~= DynIndex{ptr:free_tail_ptr,index:free_tail_index});
    
    //             assert(self.array_ptrs@.contains(free_tail_ptr));
    //             assert(self.array_perms@.dom().contains(free_tail_ptr));
    //             let mut free_tail_array_perm =
    //                 Tracked((self.array_perms.borrow_mut()).tracked_remove(free_tail_ptr));
    //             assert(free_tail_array_perm@@.value.is_Some());
    //             dyn_array_set_next(&PPtr::<DynArray>::from_usize(free_tail_ptr), &mut free_tail_array_perm, new_array_ptr,i,free_tail_index );
    //             proof{
    //                 (self.array_perms.borrow_mut())
    //                     .tracked_insert(free_tail_ptr, free_tail_array_perm.get());
    //             }
    
    //             let mut new_array_perm =
    //                 Tracked((self.array_perms.borrow_mut()).tracked_remove(new_array_ptr));
    //             dyn_array_set_next(&PPtr::<DynArray>::from_usize(new_array_ptr), &mut new_array_perm, 0, 0,i);
    //             dyn_array_set_prev(&PPtr::<DynArray>::from_usize(new_array_ptr), &mut new_array_perm, free_tail_ptr,free_tail_index,i);
    //             dyn_array_push_free(&PPtr::<DynArray>::from_usize(new_array_ptr), &mut new_array_perm, i);
    //             proof{
    //                 (self.array_perms.borrow_mut())
    //                     .tracked_insert(new_array_ptr, new_array_perm.get());
    //             }
    
    //             self.free_tail.ptr = new_array_ptr;
    //             self.free_tail.index = i;

    //             proof{
    //                 self.free_list@ = self.free_list@.push(DynIndex{ptr:new_array_ptr, index: i});
    //             }
    
    //             self.size = self.size + 1;
    
    //             i = i + 1;

    //             assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.array_perms@[self.free_list@[i].ptr]@.value.get_Some_0().free_set@.contains(self.free_list@[i].index));
    //             assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.array_perms@[self.value_list@[i].ptr]@.value.get_Some_0().value_set@.contains(self.value_list@[i].index));
    //             assert(old_self@.free_list@ =~= self.free_list@.subrange(0, self.free_list@.len() - 1));
    //             // assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old_self@.array_perms@.dom().contains(array_ptr) && old_self@.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index) ==> 
    //             //     old_self@.free_list@.contains(DynIndex{ptr:array_ptr,index:index})
    //             // );
    //             assert(old_self@.array_perms@.dom() =~= self.array_perms@.dom());

    //             assert(forall|array_ptr:DynArrayPtr| #![auto] old_self@.array_perms@.dom().contains(array_ptr) && array_ptr != new_array_ptr ==> old_self@.array_perms@[array_ptr]@.value.get_Some_0().free_set =~= self.array_perms@[array_ptr]@.value.get_Some_0().free_set);
    //             assert(forall|index:usize| #![auto] old_self@.array_perms@[new_array_ptr]@.value.get_Some_0().free_set@.contains(index) ==> self.array_perms@[new_array_ptr]@.value.get_Some_0().free_set@.contains(index));
    //             assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index) && array_ptr != new_array_ptr ==> (old_self@.array_perms@.dom().contains(array_ptr) && old_self@.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index)));
    //             assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] old_self@.free_list@.contains(DynIndex{ptr:array_ptr,index:index}) ==> self.free_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //             assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index) && array_ptr != new_array_ptr ==> self.free_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //             assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().free_set@.contains(index) ==> self.free_list@.contains(DynIndex{ptr:array_ptr,index:index}));
    //             assert(forall|array_ptr:DynArrayPtr, index:usize| #![auto] self.array_perms@.dom().contains(array_ptr) && self.array_perms@[array_ptr]@.value.get_Some_0().value_set@.contains(index) ==> self.value_list@.contains(DynIndex{ptr:array_ptr,index:index}));

    //             assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> page_ptr_valid(self.value_list@[i as int].ptr));
    //             assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.array_ptrs@.contains(self.value_list@[i as int].ptr));
    //             assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> dyn_index_valid(self.value_list@[i as int].index));
    //             assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.get_node_by_dyn_index(self.value_list@[i as int]) =~= old_self@.get_node_by_dyn_index(self.value_list@[i as int]));
    //             assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.next_value_node_of(i) =~= old_self@.next_value_node_of(i));
    //             assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.prev_value_node_of(i) =~= old_self@.prev_value_node_of(i));
    //             assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.get_node_by_dyn_index(self.value_list@[i as int]).next == self.next_value_node_of(i));
    //             assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> self.get_node_by_dyn_index(self.value_list@[i as int]).prev == self.prev_value_node_of(i));
    //             assert(forall|i: int, j:int| #![auto] i != j && 0 <= i < self.value_list@.len() && 0 <= j < self.value_list@.len() ==> (self.value_list@[i as int] =~= self.value_list@[j as int]) == false);
    //             assert(self.wf_value_head());
    //             assert(self.wf_value_tail());
    //             assert(self.len == self.value_list@.len());
    //             assert(forall|i:int| #![auto] 0 <= i < self.value_list@.len() ==> self.free_list@.contains(self.value_list@[i]) == false);

    //             assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> page_ptr_valid(self.free_list@[i as int].ptr));
    //             assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.array_ptrs@.contains(self.free_list@[i as int].ptr));
    //             assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> dyn_index_valid(self.free_list@[i as int].index));
    //             assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() - 2 ==> self.get_node_by_dyn_index(self.free_list@[i as int]).next == old_self@.get_node_by_dyn_index(self.free_list@[i as int]).next);
    //             assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() - 2 ==> self.next_free_node_of(i) == old_self@.next_free_node_of(i));
    //             assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() - 2 ==> self.get_node_by_dyn_index(self.free_list@[i as int]).next == self.next_free_node_of(i));
    //             assert(self.get_node_by_dyn_index(self.free_list@[self.free_list@.len() - 2 as int]).next == DynIndex{ptr:new_array_ptr, index: (i - 1usize) as usize});
    //             assert(self.next_free_node_of(self.free_list@.len() - 2) == DynIndex{ptr:new_array_ptr, index: (i - 1usize) as usize});
    //             assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.get_node_by_dyn_index(self.free_list@[i as int]).next == self.next_free_node_of(i));

    //             assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() - 1 ==> self.get_node_by_dyn_index(self.free_list@[i as int]).prev == old_self@.get_node_by_dyn_index(self.free_list@[i as int]).prev);
    //             assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() - 1 ==> self.prev_free_node_of(i) == old_self@.prev_free_node_of(i));
    //             assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> self.get_node_by_dyn_index(self.free_list@[i as int]).prev == self.prev_free_node_of(i));
    //             assert(forall|i: int, j:int|  #![auto] i != j && 0 <= i < self.free_list@.len() && 0 <= j < self.free_list@.len() ==> (self.free_list@[i as int] =~= self.free_list@[j as int]) == false);
    //             assert(self.wf_free_head());
    //             assert(self.wf_free_tail());
    //             assert(self.size - self.len == self.free_list@.len());
    //             assert(forall|i:int| #![auto] 0 <= i < self.free_list@.len() ==> self.value_list@.contains(self.free_list@[i]) == false);
    //             assert(self.free_list@.len() != 0 ==> ((self.array_ptrs@.contains(self.free_head.ptr))&&(dyn_index_valid(self.free_head.index))&&(self.array_ptrs@.contains(self.free_tail.ptr))&&(dyn_index_valid(self.free_tail.index))));
    //         }
    //     }
    // }

    pub open spec fn view(&self) -> Seq<usize>{
        self.spec_seq@
    }

    pub open spec fn wf(&self) -> bool {
        self.array_perms_wf()
        &&
        self.array_sets_wf()
        &&
        self.free_list_wf()
        &&
        self.value_list_wf()
        &&
        self.spec_seq_wf()
    }

    pub fn new() -> (ret: Self)
        ensures
            ret.wf(),
            ret.len() == 0,
            ret.size() == 0,
    {
        let ret = Self{
            free_head: DynIndex{
                ptr:0,
                index:0
            },
            free_tail:  DynIndex{
                ptr:0,
                index:0
            },
        
            value_head:  DynIndex{
                ptr:0,
                index:0
            },
            value_tail:  DynIndex{
                ptr:0,
                index:0
            },
        
            array_ptrs : Ghost(Set::empty()),
            array_perms : Tracked(Map::tracked_empty()),
        
            size: 0,
            len: 0,
        
            value_list: Ghost(Seq::empty()),
            free_list: Ghost(Seq::empty()),
            spec_seq: Ghost(Seq::empty()),
        
        };
        assert(ret.array_perms_wf());
        assert(ret.array_sets_wf());
        assert(ret.free_list_wf());
        assert(ret.value_list_wf());
        ret
    }

}
}
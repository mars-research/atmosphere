use vstd::prelude::*;
verus! {
use core::mem::MaybeUninit;

use vstd::seq_lib::*;
use crate::page_alloc::*;
use vstd::ptr::*;
use crate::define::*;

pub mod dyn_array_util;
pub use dyn_array_util::*;

pub const DYN_ARRAY_LEN:usize = 128;

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
        (self.free_set@ + self.value_set@).len() == DYN_ARRAY_LEN
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
        self.wf_free_head()
        &&
        self.wf_free_tail()
        &&
        self.size - self.len == self.free_list@.len()
        &&
        forall|i:int| #![auto] 0 <= i < self.free_list@.len() ==> self.value_list@.contains(self.free_list@[i]) == false
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

    pub fn grow(&mut self, new_array_ptr:usize, new_array_perm: Tracked<PointsTo<DynArray>>)
        requires
            new_array_ptr != 0,
            page_ptr_valid(new_array_ptr),
            old(self).size < usize::MAX - DYN_ARRAY_LEN,
            old(self).wf(),
            old(self).array_ptrs@.contains(new_array_ptr) == false,
            new_array_perm@@.pptr == new_array_ptr,
            new_array_perm@@.value.is_Some(),
            new_array_perm@@.value.get_Some_0().seq@.len() == DYN_ARRAY_LEN,
            new_array_perm@@.value.get_Some_0().free_set@.finite(),
            new_array_perm@@.value.get_Some_0().value_set@.finite(),
            new_array_perm@@.value.get_Some_0().free_set@.is_empty(),
            new_array_perm@@.value.get_Some_0().value_set@.is_empty(),
            new_array_perm@@.value.get_Some_0().free_count == 0,
    {
        proof{
            self.array_ptrs@ = self.array_ptrs@.insert(new_array_ptr);
            self.array_perms.borrow_mut().tracked_insert(new_array_ptr, new_array_perm.get());
        }

        proof{
            assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> old(self).next_free_node_of(i) == self.next_free_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.free_list@.len() ==> old(self).prev_free_node_of(i) == self.prev_free_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> old(self).next_value_node_of(i) == self.next_value_node_of(i));
            assert(forall|i: int| #![auto] 0 <= i < self.value_list@.len() ==> old(self).prev_value_node_of(i) == self.prev_value_node_of(i));
        }

        let mut i = 0;
        while i != DYN_ARRAY_LEN
            invariant
                self.array_ptrs@.len() == old(self).array_ptrs@.len() + 1,
                self.array_ptrs@ == old(self).array_ptrs@.insert(new_array_ptr),
                self.array_ptrs@.contains(new_array_ptr),
                self.array_perms@[new_array_ptr]@.value.get_Some_0().seq@.len() == DYN_ARRAY_LEN,
                self.array_perms@[new_array_ptr]@.value.get_Some_0().free_set@.finite(),
                self.array_perms@[new_array_ptr]@.value.get_Some_0().value_set@.finite(),
                self.array_perms@[new_array_ptr]@.value.get_Some_0().value_set@.is_empty(),
                self.array_perms@[new_array_ptr]@.value.get_Some_0().free_set@ =~= Set::new(|index: usize| { 0<=index<i}),
                self.array_perms@[new_array_ptr]@.value.get_Some_0().free_count == self.array_perms@[new_array_ptr]@.value.get_Some_0().free_set@.len(),
                self.value_list_wf(),
                self.free_list_wf(),
                self.array_sets_wf(),
                self.array_ptrs@.finite(),
                self.array_ptrs@.contains(0) == false,
                self.array_ptrs@ =~= self.array_perms@.dom(),
                self.size == old(self).array_ptrs@.len() * DYN_ARRAY_LEN + i,
                (forall|array_ptr:DynArrayPtr| #![auto] self.array_ptrs@.contains(array_ptr) ==> page_ptr_valid(array_ptr)),
                (forall|array_ptr:DynArrayPtr| #![auto] self.array_perms@.dom().contains(array_ptr) ==> self.array_perms@[array_ptr]@.pptr == array_ptr),
                (forall|array_ptr:DynArrayPtr| #![auto] self.array_perms@.dom().contains(array_ptr) ==> self.array_perms@[array_ptr]@.value.is_Some()),
                (forall|array_ptr:DynArrayPtr| #![auto] self.array_perms@.dom().contains(array_ptr) && array_ptr != new_array_ptr ==> self.array_perms@[array_ptr]@.value.get_Some_0().wf()),
        {
        }
    }

    pub open spec fn wf(&self) -> bool {
        self.array_perms_wf()
        &&
        self.array_sets_wf()
        &&
        self.free_list_wf()
        &&
        self.value_list_wf()
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
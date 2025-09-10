use vstd::prelude::*;
verus! {

use crate::slinkedlist::node::*;
use crate::define::SLLIndex;
use crate::lemma::lemma_u::*;

#[verifier::reject_recursive_types(T)]
pub struct StaticLinkedList<T, const N: usize> {
    pub ar: [Node<T>; N],
    pub spec_seq: Ghost<Seq<T>>,
    pub value_list: Ghost<Seq<SLLIndex>>,
    pub value_list_head: SLLIndex,
    pub value_list_tail: SLLIndex,
    pub value_list_len: usize,
    pub free_list: Ghost<Seq<SLLIndex>>,
    pub free_list_head: SLLIndex,
    pub free_list_tail: SLLIndex,
    pub free_list_len: usize,
    pub size: usize,
    pub arr_seq: Ghost<Seq<Node<T>>>,
}

// specs
impl<T, const N: usize> StaticLinkedList<T, N> {
    pub open spec fn spec_len(&self) -> usize {
        self@.len() as usize
    }

    #[verifier(when_used_as_spec(spec_len))]
    pub fn len(&self) -> (l: usize)
        ensures
            l == self.value_list_len,
            self.wf() ==> l == self.len(),
    {
        self.value_list_len
    }

    pub closed spec fn spec_get(&self, index: SLLIndex) -> Option<T>
        recommends
            0 <= index < N,
    {
        self.arr_seq@[index as int].value
    }

    pub closed spec fn get_raw_element(&self, i: int) -> Node<T>
        recommends
            0 <= i < N,
    {
        self.arr_seq@[i]
    }

    pub proof fn unique_implys_no_duplicates(&self)
        requires
            self.unique(),
            self.wf(),
        ensures
            self@.no_duplicates(),
    {
        assert(forall|i, j|
            (0 <= i < self.len() && 0 <= j < self.len() && i != j) ==> self@[i] != self@[j]);
    }

    pub open spec fn unique(&self) -> bool {
        forall|i: int, j: int|
            #![trigger self.spec_seq@[i], self.spec_seq@[j]]
            0 <= i < self.len() && 0 <= j < self.len() && i != j ==> self.spec_seq@[i]
                != self.spec_seq@[j]
    }

    // #[verifier(inline)]
    pub open spec fn view(&self) -> Seq<T> {
        self.spec_seq@
    }

    pub closed spec fn get_node_ref(&self, v: T) -> SLLIndex
        recommends
            self.wf(),
            self@.contains(v),
    {   
        self.value_list@[self@.index_of(v)]
    }

    pub closed spec fn node_ref_valid(&self, index: SLLIndex) -> bool {
        self.value_list@.contains(index)
    }

    pub closed spec fn node_ref_resolve(&self, index: SLLIndex) -> T
        recommends
            self.node_ref_valid(index),
    {
        self.arr_seq@[index as int].value.get_Some_0()
    }

    pub closed spec fn prev_free_node_of(&self, i: nat) -> int
        recommends
            i < self.free_list@.len(),
    {
        if i == 0 {
            -1
        } else {
            self.free_list@[i - 1int] as int
        }
    }

    pub closed spec fn next_free_node_of(&self, i: nat) -> int
        recommends
            i < self.free_list@.len(),
    {
        if i + 1 == self.free_list@.len() {
            -1
        } else {
            self.free_list@[i + 1int] as int
        }
    }

    pub closed spec fn wf_free_node_head(&self) -> bool {
        if self.free_list@.len() == 0 {
            self.free_list_head == -1
        } else {
            self.free_list_head == self.free_list@[0]
        }
    }

    pub closed spec fn wf_free_node_tail(&self) -> bool {
        if self.free_list@.len() == 0 {
            self.free_list_tail == -1
        } else {
            self.free_list_tail == self.free_list@[self.free_list@.len() - 1]
        }
    }

    pub closed spec fn free_list_wf(&self) -> bool {
        &&& forall|i: nat|
         // #![trigger self.arr_seq@[self.free_list@[i as int] as int].next, self.next_free_node_of(i)]

            #![trigger self.arr_seq@[self.free_list@[i as int] as int].next]
            #![trigger self.next_free_node_of(i)]
            0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].next
                == self.next_free_node_of(i)
        &&& forall|i: nat|
         // #![trigger self.arr_seq@[self.free_list@[i as int] as int].prev, self.prev_free_node_of(i)]

            #![trigger self.arr_seq@[self.free_list@[i as int] as int].prev]
            #![trigger self.prev_free_node_of(i)]
            0 <= i < self.free_list@.len() ==> self.arr_seq@[self.free_list@[i as int] as int].prev
                == self.prev_free_node_of(i)
        &&& forall|i: nat|
            #![trigger self.free_list@[i as int]]
            0 <= i < self.free_list@.len() ==> 0 <= self.free_list@[i as int] < N
        &&& forall|i: int, j: int|
            #![trigger self.free_list@[i], self.free_list@[j]]
            0 <= i < self.free_list_len && 0 <= j < self.free_list_len && i != j
                ==> self.free_list@[i] != self.free_list@[j]
        &&& self.wf_free_node_head()
        &&& self.wf_free_node_tail()
        &&& self.free_list_len == self.free_list@.len()
    }

    pub closed spec fn prev_value_node_of(&self, i: int) -> int
        recommends
            0 <= i < self.value_list@.len(),
    {
        if i == 0 {
            -1
        } else {
            self.value_list@[i - 1int] as int
        }
    }

    pub closed spec fn next_value_node_of(&self, i: int) -> int
        recommends
            0 <= i < self.value_list@.len(),
    {
        if i + 1 == self.value_list@.len() {
            -1
        } else {
            self.value_list@[i + 1int] as int
        }
    }

    pub closed spec fn wf_value_node_head(&self) -> bool {
        if self.value_list@.len() == 0 {
            self.value_list_head == -1
        } else {
            self.value_list_head == self.value_list@[0]
        }
    }

    pub closed spec fn wf_value_node_tail(&self) -> bool {
        if self.value_list@.len() == 0 {
            self.value_list_tail == -1
        } else {
            self.value_list_tail == self.value_list@[self.value_list@.len() - 1]
        }
    }

    pub closed spec fn value_list_wf(&self) -> bool {
        &&& forall|i: int|
            #![trigger self.arr_seq@[self.value_list@[i as int] as int].next]
            #![trigger self.next_value_node_of(i)]
            0 <= i < self.value_list@.len()
                ==> self.arr_seq@[self.value_list@[i as int] as int].next
                == self.next_value_node_of(i)
        &&& forall|i: int|
            #![trigger self.arr_seq@[self.value_list@[i as int] as int].prev]
            #![trigger self.prev_value_node_of(i)]
            0 <= i < self.value_list@.len()
                ==> self.arr_seq@[self.value_list@[i as int] as int].prev
                == self.prev_value_node_of(i)
        &&& forall|i: int|
            #![trigger self.value_list@[i as int]]
            0 <= i < self.value_list@.len() ==> 0 <= self.value_list@[i as int] < N
        &&& self.unique()
        &&& self.wf_value_node_head()
        &&& self.wf_value_node_tail()
        &&& self.value_list_len == self.value_list@.len()
    }

    pub closed spec fn free_list_ptr_all_null(&self) -> bool {
        forall|i: SLLIndex|
            #![trigger self.arr_seq@[i as int].value.is_Some(), self.value_list@.contains(i)]
            0 <= i < N && self.arr_seq@[i as int].value.is_Some() ==> self.value_list@.contains(i)
    }

    pub closed spec fn array_wf(&self) -> bool {
        &&& self.arr_seq@.len() == N
        &&& self.size == N
    }

    pub closed spec fn spec_seq_wf(&self) -> bool {
        &&& self.spec_seq@.len() == self.value_list_len
        &&& forall|i: int|
            #![trigger self.spec_seq@[i as int]]
            #![trigger self.value_list@[i as int]]
            0 <= i < self.value_list_len
                ==> self.arr_seq@[self.value_list@[i as int] as int].value.is_Some()
                && self.arr_seq@[self.value_list@[i as int] as int].value.get_Some_0()
                =~= self.spec_seq@[i as int]
    }

    pub closed spec fn wf(&self) -> bool {
        &&& N <= i32::MAX
        &&& N > 2
        &&& self.array_wf()
        &&& self.free_list_len + self.value_list_len == N
        &&& self.value_list_wf()
        &&& self.free_list_wf()
        &&& self.spec_seq_wf()
        &&& forall|i: int, j: int|
            #![trigger self.value_list@[i], self.free_list@[j]]
            0 <= i < self.value_list@.len() && 0 <= j < self.free_list@.len()
                ==> self.value_list@[i] != self.free_list@[j]
    }
}

//proof
impl<T: Copy, const N: usize> StaticLinkedList<T, N> {
    pub proof fn wf_to_no_duplicates(&self)
        requires
            self.wf(),
        ensures
            self.spec_seq@.no_duplicates(),
    {
    }
}

impl<T: Copy, const N: usize> StaticLinkedList<T, N> {
    pub fn init(&mut self)
        requires
            N > 2,
            N < SLLIndex::MAX,
            old(self).array_wf(),
        ensures
            self.wf(),
            self@ =~= Seq::empty(),
            self.len() == 0,
            forall|i: SLLIndex| #![trigger self.node_ref_valid(i)] self.node_ref_valid(i) == false,
    {
        self.spec_seq = Ghost(Seq::empty());

        self.value_list = Ghost(Seq::empty());
        self.value_list_head = -1;
        self.value_list_tail = -1;
        self.value_list_len = 0;

        self.free_list = Ghost(Seq::empty());
        self.free_list_head = -1;
        self.free_list_tail = -1;
        self.free_list_len = 0;

        assert(self.value_list_wf());
        assert(self.free_list_wf());
        assert(self.spec_seq_wf());
        assert(forall|i: int, j: int|
            #![trigger self.value_list@[i], self.free_list@[j]]
            0 <= i < self.value_list@.len() && 0 <= j < self.free_list@.len()
                ==> self.value_list@[i] != self.free_list@[j]);

        for i in 0..N
            invariant
                0 <= i <= N,
                N > 2,
                N < SLLIndex::MAX,
                self.array_wf(),
                self.free_list_len == i,
                self.free_list_len + self.value_list_len == i,
                self.value_list_wf(),
                self.free_list_wf(),
                self.spec_seq_wf(),
                forall|i: int, j: int|
                    #![trigger self.value_list@[i], self.free_list@[j]]
                    0 <= i < self.value_list@.len() && 0 <= j < self.free_list@.len()
                        ==> self.value_list@[i] != self.free_list@[j],
                forall|j: int|
                    #![trigger self.free_list@[j]]
                    0 <= j < self.free_list_len ==> self.free_list@[j] == j as SLLIndex,
                forall|i: SLLIndex|
                    #![trigger self.node_ref_valid(i)]
                    self.node_ref_valid(i) == false,
        {
            self.free_list_len = self.free_list_len + 1;
            if i == 0 {
                self.free_list_head = 0;
                self.free_list_tail = 0;
                self.free_list = Ghost(Seq::empty().push(0));
                self.set_prev(0 as SLLIndex, -1);
                self.set_next(0 as SLLIndex, -1);
                self.set_value(0 as SLLIndex, None);
                assert(self.free_list_wf());
            } else {
                self.free_list = Ghost(self.free_list@.push(i as SLLIndex));
                self.set_next(self.free_list_tail, i as SLLIndex);
                self.set_prev(i as SLLIndex, self.free_list_tail);
                self.set_next(i as SLLIndex, -1);
                self.set_value(i as SLLIndex, None);
                self.free_list_tail = i as SLLIndex;
                assert(self.free_list_wf());
            }
        }
        assert(self.wf());
    }

    pub fn get_head(&self) -> (ret: T)
        requires
            self.wf(),
            self.len() > 0,
        ensures
            ret == self@[0],
    {
        self.get_value(self.value_list_head).unwrap()
    }

    pub fn push(&mut self, new_value: &T) -> (free_node_index: SLLIndex)
        requires
            old(self).wf(),
            old(self).len() < N,
            old(self).unique(),
            old(self)@.contains(*new_value) == false,
            N > 2,
        ensures
            self.wf(),
            self@ == old(self)@.push(*new_value),
            self.len() == old(self).len() + 1,
            forall|v:T|
                #![auto]
                old(self)@.contains(v) ==> 
                    old(self).get_node_ref(v) == 
                        self.get_node_ref(v),
            self.get_node_ref(*new_value) == free_node_index,
    {
        proof {
            seq_push_lemma::<SLLIndex>();
            seq_push_lemma::<T>();
            seq_push_index_of_lemma::<T>();
        }
        if self.value_list_len == 0 {
            // value list empty
            // assert(self.value_list_head == -1);
            // assert(self.value_list_tail == -1);
            let ret = self.free_list_head;
            // assert(ret != -1);
            // assert(ret != self.free_list_tail);
            let next_free_list_head = self.get_next(self.free_list_head);
            // assert(next_free_list_head == self.free_list@[1]);
            self.free_list_head = next_free_list_head;
            self.set_prev(self.free_list_head, -1);

            self.free_list_len = self.free_list_len - 1;
            proof {
                self.free_list@ = self.free_list@.skip(1);
            }
            self.value_list_head = ret;
            self.value_list_tail = ret;
            self.set_prev(ret, -1);

            assert(forall|i: nat|
                #![trigger old(self).arr_seq@[i as int]]
                #![trigger self.arr_seq@[i as int], old(self).arr_seq@[i as int]]
                0 <= i < N && i != ret ==> old(self).arr_seq@[i as int].next
                    == self.arr_seq@[i as int].next);

            self.set_next(ret, -1);
            proof {
                self.value_list@ = self.value_list@.push(ret);
                self.spec_seq@ = self.spec_seq@.push(*new_value);
            }
            self.value_list_len = self.value_list_len + 1;
            self.set_value(ret, Some(*new_value));
            
            assert(self.wf());
            assert(self@ == old(self)@.push(*new_value));
            return ret;
        } else if self.free_list_len == 1 {
            let ret = self.free_list_tail;
            self.free_list_len = 0;
            self.free_list_head = -1;
            self.free_list_tail = -1;
            proof {
                self.free_list@ = self.free_list@.skip(1);
            }

            let old_value_list_tail = self.value_list_tail;
            self.set_prev(ret, old_value_list_tail);
            self.set_next(old_value_list_tail, ret);
            self.value_list_tail = ret;
            proof {
                self.value_list@ = self.value_list@.push(ret);
                self.spec_seq@ = self.spec_seq@.push(*new_value);
            }
            self.value_list_len = self.value_list_len + 1;

            self.set_value(ret, Some(*new_value));

            assert(self.wf());
            assert(self@ == old(self)@.push(*new_value));
            return ret;

        } else {
            assert(self.free_list_len > 1 && self.value_list_len > 0);
            let ret = self.free_list_head;
            let old_value_list_tail = self.value_list_tail;

            let new_free_list_head = self.get_next(ret);
            self.set_prev(new_free_list_head, -1);
            self.free_list_head = new_free_list_head;
            self.free_list_len = self.free_list_len - 1;
            proof {
                self.free_list@ = self.free_list@.skip(1);
            }
            self.set_next(old_value_list_tail, ret);
            self.set_prev(ret, old_value_list_tail);
            self.set_next(ret, -1);
            self.value_list_tail = ret;
            self.value_list_len = self.value_list_len + 1;
            proof {
                self.value_list@ = self.value_list@.push(ret);
                self.spec_seq@ = self.spec_seq@.push(*new_value);
            }
            self.set_value(ret, Some(*new_value));
            assert(self.wf());
            return ret;
        }
    }

    pub fn pop(&mut self) -> (ret: (T, SLLIndex))
        requires
            old(self).wf(),
            old(self).len() > 0,
            old(self).unique(),
            N > 2,
        ensures
            self.wf(),
            self.len() == old(self).len() - 1,
            self@ == old(self)@.skip(1),
            ret.0 == old(self)@[0],
            ret.1 == old(self).get_node_ref(ret.0),
            forall|v:T|
                #![auto]
                self@.contains(v) ==> 
                    old(self).get_node_ref(v) == 
                        self.get_node_ref(v),
    {
        proof {
            seq_push_lemma::<SLLIndex>();
            seq_skip_lemma::<SLLIndex>();
            seq_skip_lemma::<T>();
            seq_skip_index_of_lemma::<T>();
        }
        if self.free_list_len == 0 {
            let ret_index = self.value_list_head;
            let ret = self.get_value(ret_index).unwrap();

            let new_value_list_head = self.get_next(ret_index);
            self.value_list_head = new_value_list_head;
            self.set_prev(new_value_list_head, -1);
            proof {
                self.value_list@ = self.value_list@.skip(1);
                self.spec_seq@ = self.spec_seq@.skip(1);
            }
            self.value_list_len = self.value_list_len - 1;

            self.free_list_head = ret_index;
            self.free_list_tail = ret_index;
            self.set_prev(ret_index, -1);
            self.set_next(ret_index, -1);
            proof {
                self.free_list@ = self.free_list@.push(ret_index);
            }
            self.free_list_len = self.free_list_len + 1;

            assert(self.wf());
            return (ret, ret_index);
        } else if self.value_list_len == 1 {
            let ret_index = self.value_list_head;
            let ret = self.get_value(ret_index).unwrap();

            let old_free_list_tail = self.free_list_tail;
            self.set_next(old_free_list_tail, ret_index);
            self.set_prev(ret_index, old_free_list_tail);
            self.free_list_tail = ret_index;
            self.free_list_len = self.free_list_len + 1;
            proof {
                self.free_list@ = self.free_list@.push(ret_index);
            }

            self.value_list_head = -1;
            self.value_list_tail = -1;
            proof {
                self.value_list@ = self.value_list@.skip(1);
                self.spec_seq@ = self.spec_seq@.skip(1);
            }
            self.value_list_len = self.value_list_len - 1;

            assert(self.wf());

            return (ret, ret_index);
        } else {
            let ret_index = self.value_list_head;
            let ret = self.get_value(ret_index).unwrap();

            let new_value_list_head = self.get_next(ret_index);
            self.value_list_head = new_value_list_head;
            self.set_prev(new_value_list_head, -1);
            proof {
                self.value_list@ = self.value_list@.skip(1);
                self.spec_seq@ = self.spec_seq@.skip(1);
            }
            self.value_list_len = self.value_list_len - 1;

            let old_free_list_tail = self.free_list_tail;
            self.set_next(ret_index, -1);
            self.set_next(old_free_list_tail, ret_index);
            self.set_prev(ret_index, old_free_list_tail);
            self.free_list_tail = ret_index;
            self.free_list_len = self.free_list_len + 1;
            proof {
                self.free_list@ = self.free_list@.push(ret_index);
            }
            assert(self.wf());
            return (ret, ret_index);
        }
    }

    pub fn remove_helper1(&mut self, remove_index: SLLIndex, v: Ghost<T>) -> (ret: T)
        requires
            old(self).wf(),
            old(self)@.contains(v@),
            old(self).get_node_ref(v@) == remove_index,
            old(self).value_list_len == 1,
        ensures
            self.wf(),
            self.len() == old(self).len() - 1,
            ret == v@,
            self.unique(),
            self@ =~= old(self)@.remove_value(ret),
            forall|v:T|
                #![auto]
                self@.contains(v) ==> 
                    old(self).get_node_ref(v) == 
                        self.get_node_ref(v),
    {
        proof {
            seq_push_lemma::<SLLIndex>();
            seq_skip_lemma::<SLLIndex>();
            seq_skip_lemma::<T>();
            seq_skip_index_of_lemma::<T>();
        }
        let ret = self.get_value(remove_index).unwrap();
        let old_free_list_tail = self.free_list_tail;
        self.set_next(old_free_list_tail, remove_index);
        self.set_prev(remove_index, old_free_list_tail);
        self.free_list_tail = remove_index;
        self.free_list_len = self.free_list_len + 1;
        proof {
            self.free_list@ = self.free_list@.push(remove_index);
        }

        self.value_list_head = -1;
        self.value_list_tail = -1;
        proof {
            self.value_list@ = self.value_list@.skip(1);
            self.spec_seq@ = self.spec_seq@.skip(1);
        }
        self.value_list_len = self.value_list_len - 1;

        assert(self.wf());
        return ret;
    }

    pub fn remove_helper2(&mut self, remove_index: SLLIndex, v: Ghost<T>) -> (ret: T)
        requires
            old(self).wf(),
            old(self)@.contains(v@),
            old(self).get_node_ref(v@) == remove_index,
            old(self).value_list_len != 1,
            old(self).free_list_len == 0 && old(self).value_list_head == remove_index,
        ensures
            self.wf(),
            self.len() == old(self).len() - 1,
            ret == v@,
            self.unique(),
            self@ =~= old(self)@.remove_value(ret),
            forall|v:T|
                #![auto]
                self@.contains(v) ==> 
                    old(self).get_node_ref(v) == 
                        self.get_node_ref(v),
    {
        proof {
            seq_push_lemma::<SLLIndex>();
            seq_skip_lemma::<SLLIndex>();
            seq_skip_lemma::<T>();
            seq_skip_index_of_lemma::<T>();
        }
        let ret = self.get_value(remove_index).unwrap();
        let new_value_list_head = self.get_next(remove_index);
        self.value_list_head = new_value_list_head;
        self.set_prev(new_value_list_head, -1);
        proof {
            self.value_list@ = self.value_list@.skip(1);
            self.spec_seq@ = self.spec_seq@.skip(1);
        }
        self.value_list_len = self.value_list_len - 1;

        self.free_list_head = remove_index;
        self.free_list_tail = remove_index;
        self.set_prev(remove_index, -1);
        self.set_next(remove_index, -1);
        proof {
            self.free_list@ = self.free_list@.push(remove_index);
        }
        self.free_list_len = self.free_list_len + 1;

        assert(self.wf());
        return ret;
    }

    pub fn remove_helper3(&mut self, remove_index: SLLIndex, v: Ghost<T>) -> (ret: T)
        requires
            old(self).wf(),
            old(self)@.contains(v@),
            old(self).get_node_ref(v@) == remove_index,
            old(self).value_list_len != 1,
            old(self).free_list_len == 0 && old(self).value_list_tail == remove_index,
        ensures
            self.wf(),
            self.len() == old(self).len() - 1,
            self.unique(),
            self@ =~= old(self)@.remove_value(ret),
            ret == v@,
            forall|v:T|
                #![auto]
                self@.contains(v) ==> 
                    old(self).get_node_ref(v) == 
                        self.get_node_ref(v),
    {
        proof {
            seq_push_lemma::<SLLIndex>();
            seq_remove_lemma::<SLLIndex>();
            seq_remove_lemma::<T>();
            // seq_remove_index_of_lemma::<SLLIndex>();
            // seq_remove_index_of_lemma::<T>();
        }
        let ret = self.get_value(remove_index).unwrap();
        let new_value_list_tail = self.get_prev(remove_index);
        self.value_list_tail = new_value_list_tail;
        self.set_next(new_value_list_tail, -1);
        proof {
            self.value_list@ = self.value_list@.subrange(0, self.value_list_len as int - 1).add(
                self.value_list@.subrange(self.value_list_len as int, self.value_list_len as int),
            );
            self.spec_seq@ = self.spec_seq@.subrange(0, self.value_list_len as int - 1).add(
                self.spec_seq@.subrange(self.value_list_len as int, self.value_list_len as int),
            );
        }
        self.value_list_len = self.value_list_len - 1;

        self.free_list_head = remove_index;
        self.free_list_tail = remove_index;
        self.set_prev(remove_index, -1);
        self.set_next(remove_index, -1);
        proof {
            self.free_list@ = self.free_list@.push(remove_index);
        }
        self.free_list_len = self.free_list_len + 1;

        assert(self.wf());
        return ret;
    }

    pub fn remove_helper4(&mut self, remove_index: SLLIndex, v: Ghost<T>) -> (ret: T)
        requires
            old(self).wf(),
            old(self)@.contains(v@),
            old(self).get_node_ref(v@) == remove_index,
            old(self).value_list_len != 1,
            old(self).free_list_len == 0 && old(self).value_list_tail != remove_index && old(
                self,
            ).value_list_head != remove_index,
        ensures
            self.wf(),
            self.len() == old(self).len() - 1,
            ret == v@,
            forall|v:T|
                #![auto]
                self@.contains(v) ==> 
                    old(self).get_node_ref(v) == 
                        self.get_node_ref(v),
            self.unique(),
            self@ =~= old(self)@.remove_value(ret),
    {
        proof {
            seq_push_lemma::<SLLIndex>();
            seq_remove_lemma::<SLLIndex>();
            seq_remove_lemma::<T>();
            // seq_remove_index_of_lemma::<SLLIndex>();
            // seq_remove_index_of_lemma::<T>();
        }
        let ret = self.get_value(remove_index).unwrap();
        let prev = self.get_prev(remove_index);
        let next = self.get_next(remove_index);
        self.set_next(prev, next);
        self.set_prev(next, prev);

        let ghost_index = Ghost(self.spec_seq@.index_of(v@));
        assert(0 <= ghost_index@ < self.spec_seq@.len());
        assert(self.spec_seq@[ghost_index@] == v@);
        assert(self.value_list@[ghost_index@] == remove_index);

        proof {
            self.value_list@ = self.value_list@.subrange(0, ghost_index@).add(
                self.value_list@.subrange(ghost_index@ + 1, self.value_list_len as int),
            );
            self.spec_seq@ = self.spec_seq@.subrange(0, ghost_index@).add(
                self.spec_seq@.subrange(ghost_index@ + 1, self.value_list_len as int),
            );
        }
        self.value_list_len = self.value_list_len - 1;

        self.free_list_head = remove_index;
        self.free_list_tail = remove_index;
        self.set_prev(remove_index, -1);
        self.set_next(remove_index, -1);
        proof {
            self.free_list@ = self.free_list@.push(remove_index);
        }
        self.free_list_len = self.free_list_len + 1;

        assert(self.wf()) by {
            assert(self.array_wf());
            assert( self.free_list_len + self.value_list_len == N);
            assert( self.value_list_wf());
            assert( self.free_list_wf());
            assert( self.spec_seq_wf());
        };
        assert(
            forall|v:T|
                #![auto]
                self@.contains(v) ==> 
                    old(self).get_node_ref(v) == 
                        self.get_node_ref(v)
        );
        return ret;
    }

    pub fn remove_helper5(&mut self, remove_index: SLLIndex, v:Ghost<T>) -> (ret: T)
        requires
            old(self).wf(),
            old(self)@.contains(v@),
            old(self).get_node_ref(v@) == remove_index,
            old(self).value_list_len != 1,
            old(self).free_list_len != 0 && old(self).value_list_head == remove_index && old(
                self,
            ).value_list_len != 1,
        ensures
            self.wf(),
            self.len() == old(self).len() - 1,
            self.unique(),
            self@ =~= old(self)@.remove_value(ret),
            ret == v@,
            forall|v:T|
                #![auto]
                self@.contains(v) ==> 
                    old(self).get_node_ref(v) == 
                        self.get_node_ref(v),
    {
        proof {
            seq_push_lemma::<SLLIndex>();
            seq_skip_lemma::<SLLIndex>();
            seq_skip_lemma::<T>();
            seq_skip_index_of_lemma::<T>();
        }
        let ret = self.get_value(remove_index).unwrap();
        let new_value_list_head = self.get_next(remove_index);
        self.value_list_head = new_value_list_head;
        self.set_prev(new_value_list_head, -1);
        proof {
            self.value_list@ = self.value_list@.skip(1);
            self.spec_seq@ = self.spec_seq@.skip(1);
        }
        self.value_list_len = self.value_list_len - 1;

        let old_free_list_tail = self.free_list_tail;
        self.set_next(old_free_list_tail, remove_index);
        self.set_next(remove_index, -1);
        self.set_prev(remove_index, old_free_list_tail);
        self.free_list_tail = remove_index;
        self.free_list_len = self.free_list_len + 1;
        proof {
            self.free_list@ = self.free_list@.push(remove_index);
        }

        assert(self.wf());
        return ret;
    }

    pub fn remove_helper6(&mut self, remove_index: SLLIndex, v:Ghost<T>) -> (ret: T)
        requires
            old(self).wf(),
            old(self)@.contains(v@),
            old(self).get_node_ref(v@) == remove_index, 
            old(self).value_list_len != 1,
            old(self).free_list_len != 0 && old(self).value_list_tail == remove_index && old(
                self,
            ).value_list_len != 1,
        ensures
            self.wf(),
            self.len() == old(self).len() - 1,
            self.unique(),
            self@ =~= old(self)@.remove_value(ret),
            ret == v@,
            forall|v:T|
                #![auto]
                self@.contains(v) ==> 
                    old(self).get_node_ref(v) == 
                        self.get_node_ref(v),
    {
        proof {
            seq_push_lemma::<SLLIndex>();
            seq_remove_lemma::<SLLIndex>();
            seq_remove_lemma::<T>();
        }
        let ret = self.get_value(remove_index).unwrap();
        let new_value_list_tail = self.get_prev(remove_index);
        self.value_list_tail = new_value_list_tail;
        self.set_next(new_value_list_tail, -1);
        proof {
            self.value_list@ = self.value_list@.subrange(0, self.value_list_len as int - 1).add(
                self.value_list@.subrange(self.value_list_len as int, self.value_list_len as int),
            );
            self.spec_seq@ = self.spec_seq@.subrange(0, self.value_list_len as int - 1).add(
                self.spec_seq@.subrange(self.value_list_len as int, self.value_list_len as int),
            );
        }
        self.value_list_len = self.value_list_len - 1;

        let old_free_list_tail = self.free_list_tail;
        self.set_next(old_free_list_tail, remove_index);
        self.set_next(remove_index, -1);
        self.set_prev(remove_index, old_free_list_tail);
        self.free_list_tail = remove_index;
        self.free_list_len = self.free_list_len + 1;
        proof {
            self.free_list@ = self.free_list@.push(remove_index);
        }

        assert(self.wf());
        return ret;
    }

    pub fn remove_helper7(&mut self, remove_index: SLLIndex, v:Ghost<T>) -> (ret: T)
        requires
            old(self).wf(),
            old(self)@.contains(v@),
            old(self).get_node_ref(v@) == remove_index, 
            old(self).value_list_len != 1,
            old(self).free_list_len != 0 && old(self).value_list_tail != remove_index && old(
                self,
            ).value_list_head != remove_index && old(self).value_list_len != 1,
        ensures
            self.wf(),
            self.len() == old(self).len() - 1,
            self.unique(),
            self@ =~= old(self)@.remove_value(ret),
            ret == v@,
            forall|v:T|
                #![auto]
                self@.contains(v) ==> 
                    old(self).get_node_ref(v) == 
                        self.get_node_ref(v),
    {
        proof {
            seq_push_lemma::<SLLIndex>();
            seq_skip_lemma::<SLLIndex>();
            seq_remove_lemma::<SLLIndex>();
            seq_remove_lemma_2::<SLLIndex>();
            seq_remove_lemma::<T>();
        }
        let ret = self.get_value(remove_index).unwrap();
        let prev = self.get_prev(remove_index);
        let next = self.get_next(remove_index);
        self.set_next(prev, next);
        self.set_prev(next, prev);

        let ghost_index = Ghost(self.value_list@.index_of(remove_index));
        assert(0 <= ghost_index@ < self.value_list@.len());
        assert(self.value_list@[ghost_index@] == remove_index);

        proof {
            self.value_list@ = self.value_list@.subrange(0, ghost_index@).add(
                self.value_list@.subrange(ghost_index@ + 1, self.value_list_len as int),
            );
            self.spec_seq@ = self.spec_seq@.subrange(0, ghost_index@).add(
                self.spec_seq@.subrange(ghost_index@ + 1, self.value_list_len as int),
            );
        }
        self.value_list_len = self.value_list_len - 1;

        let old_free_list_tail = self.free_list_tail;
        self.set_next(old_free_list_tail, remove_index);
        self.set_next(remove_index, -1);
        self.set_prev(remove_index, old_free_list_tail);
        self.free_list_tail = remove_index;
        self.free_list_len = self.free_list_len + 1;
        proof {
            self.free_list@ = self.free_list@.push(remove_index);
        }

        assert(self.wf());
        return ret;
    }

    pub fn remove(&mut self, remove_index: SLLIndex, v: Ghost<T>) -> (ret: T)
        requires
            old(self).wf(),
            old(self).unique(),
            old(self)@.contains(v@),
            old(self).get_node_ref(v@) == remove_index, 
        ensures
            self.wf(),
            self.len() == old(self).len() - 1,
            self.unique(),
            self@ =~= old(self)@.remove_value(ret),
            ret == v@,
            forall|v:T|
                #![auto]
                self@.contains(v) ==> 
                    old(self).get_node_ref(v) == 
                        self.get_node_ref(v),
    {
        assert(self.value_list_len != 0);
        if self.value_list_len == 1 {
            return self.remove_helper1(remove_index, v);
        } else if self.free_list_len == 0 && self.value_list_head == remove_index {
            return self.remove_helper2(remove_index, v);
        } else if self.free_list_len == 0 && self.value_list_tail == remove_index {
            return self.remove_helper3(remove_index,v);
        } else if self.free_list_len == 0 {
            return self.remove_helper4(remove_index, v);
        } else if self.value_list_head == remove_index {
            return self.remove_helper5(remove_index, v);
        } else if self.value_list_tail == remove_index {
            return self.remove_helper6(remove_index, v);
        } else {
            return self.remove_helper7(remove_index, v);
        }
    }
}

} // verus!

use vstd::prelude::*;
verus! {
use crate::mars_dynamiclinkedlist::*;
use vstd::ptr::*;
use core::mem::MaybeUninit;

#[verifier(external_body)]
pub fn dyn_array_set_free_count(pptr: &PPtr::<DynArray>, perm: &mut Tracked<PointsTo<DynArray>>, free_count: usize)
    requires pptr.id() == old(perm)@@.pptr,
                old(perm)@@.value.is_Some(),
    ensures pptr.id() == perm@@.pptr,
            perm@@.value.is_Some(),
            // perm@@.value.get_Some_0().free_count == old(perm)@@.value.get_Some_0().free_count,
            perm@@.value.get_Some_0().ar == old(perm)@@.value.get_Some_0().ar,
            perm@@.value.get_Some_0().seq == old(perm)@@.value.get_Some_0().seq,
            perm@@.value.get_Some_0().free_set == old(perm)@@.value.get_Some_0().free_set,
            perm@@.value.get_Some_0().value_set == old(perm)@@.value.get_Some_0().value_set,
            perm@@.value.get_Some_0().free_count == free_count,
{
    unsafe {
        let uptr = pptr.to_usize() as *mut MaybeUninit<DynArray>;
        (*uptr).assume_init_mut().free_count = free_count;
    }
}

#[verifier(external_body)]
pub fn dyn_array_set_next(pptr: &PPtr::<DynArray>, perm: &mut Tracked<PointsTo<DynArray>>, next_ptr: usize, next_index: usize, index:usize)
    requires pptr.id() == old(perm)@@.pptr,
                old(perm)@@.value.is_Some(),
                dyn_index_valid(index),
    ensures pptr.id() == perm@@.pptr,
            perm@@.value.is_Some(),
            perm@@.value.get_Some_0().free_count == old(perm)@@.value.get_Some_0().free_count,
            perm@@.value.get_Some_0().ar == old(perm)@@.value.get_Some_0().ar,
            // perm@@.value.get_Some_0().seq == old(perm)@@.value.get_Some_0().seq,
            perm@@.value.get_Some_0().free_set == old(perm)@@.value.get_Some_0().free_set,
            perm@@.value.get_Some_0().value_set == old(perm)@@.value.get_Some_0().value_set,
            perm@@.value.get_Some_0().seq@.len() == old(perm)@@.value.get_Some_0().seq@.len(),
            forall|i:usize| #![auto] dyn_index_valid(i) ==> perm@@.value.get_Some_0()@[i as int].value == old(perm)@@.value.get_Some_0()@[i as int].value,
            forall|i:usize| #![auto] dyn_index_valid(i) ==> perm@@.value.get_Some_0()@[i as int].prev == old(perm)@@.value.get_Some_0()@[i as int].prev,
            forall|i:usize| #![auto] dyn_index_valid(i) && i != index ==> perm@@.value.get_Some_0()@[i as int].next == old(perm)@@.value.get_Some_0()@[i as int].next,
            perm@@.value.get_Some_0()@[index as int].next =~= (DynIndex{ptr:next_ptr, index: next_index}),
{
    unsafe {
        let uptr = pptr.to_usize() as *mut MaybeUninit<DynArray>;
        (*uptr).assume_init_mut().ar[index].next = next_ptr | next_index;
    }
}

#[verifier(external_body)]
pub fn dyn_array_set_prev(pptr: &PPtr::<DynArray>, perm: &mut Tracked<PointsTo<DynArray>>, prev_ptr: usize, prev_index: usize, index:usize)
    requires pptr.id() == old(perm)@@.pptr,
                old(perm)@@.value.is_Some(),
                dyn_index_valid(index),
    ensures pptr.id() == perm@@.pptr,
            perm@@.value.is_Some(),
            perm@@.value.get_Some_0().free_count == old(perm)@@.value.get_Some_0().free_count,
            perm@@.value.get_Some_0().ar == old(perm)@@.value.get_Some_0().ar,
            // perm@@.value.get_Some_0().seq == old(perm)@@.value.get_Some_0().seq,
            perm@@.value.get_Some_0().free_set == old(perm)@@.value.get_Some_0().free_set,
            perm@@.value.get_Some_0().value_set == old(perm)@@.value.get_Some_0().value_set,
            perm@@.value.get_Some_0().seq@.len() == old(perm)@@.value.get_Some_0().seq@.len(),
            forall|i:usize| #![auto] dyn_index_valid(i) ==> perm@@.value.get_Some_0()@[i as int].value == old(perm)@@.value.get_Some_0()@[i as int].value,
            forall|i:usize| #![auto] dyn_index_valid(i) ==> perm@@.value.get_Some_0()@[i as int].next == old(perm)@@.value.get_Some_0()@[i as int].next,
            forall|i:usize| #![auto] dyn_index_valid(i) && i != index ==> perm@@.value.get_Some_0()@[i as int].prev == old(perm)@@.value.get_Some_0()@[i as int].prev,
            perm@@.value.get_Some_0()@[index as int].prev =~= (DynIndex{ptr:prev_ptr, index: prev_index}),
{
    unsafe {
        let uptr = pptr.to_usize() as *mut MaybeUninit<DynArray>;
        (*uptr).assume_init_mut().ar[index].prev = prev_ptr | prev_index;
    }
}

#[verifier(external_body)]
pub fn dyn_array_push_free(pptr: &PPtr::<DynArray>, perm: &mut Tracked<PointsTo<DynArray>>, free_index:usize)
    requires pptr.id() == old(perm)@@.pptr,
                old(perm)@@.value.is_Some(),
                old(perm)@@.value.get_Some_0().free_count != DYN_ARRAY_LEN,
                old(perm)@@.value.get_Some_0().free_set@.contains(free_index) == false,
                dyn_index_valid(free_index),
    ensures pptr.id() == perm@@.pptr,
            perm@@.value.is_Some(),
            perm@@.value.get_Some_0().free_count == old(perm)@@.value.get_Some_0().free_count + 1,
            perm@@.value.get_Some_0().ar == old(perm)@@.value.get_Some_0().ar,
            perm@@.value.get_Some_0().seq == old(perm)@@.value.get_Some_0().seq,
            perm@@.value.get_Some_0().free_set@ == old(perm)@@.value.get_Some_0().free_set@.insert(free_index),
            perm@@.value.get_Some_0().value_set == old(perm)@@.value.get_Some_0().value_set,
{
    unsafe {
        let uptr = pptr.to_usize() as *mut MaybeUninit<DynArray>;
        proof{
            (*uptr).assume_init_mut().free_set@ = (*uptr).assume_init_mut().free_set@.insert(free_index);
        }
        (*uptr).assume_init_mut().free_count = (*uptr).assume_init_mut().free_count + 1;
    }
}

}
use vstd::prelude::*;
verus! {
use crate::mars_dynamiclinkedlist::*;
use vstd::ptr::*;

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

}
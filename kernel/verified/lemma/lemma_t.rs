use vstd::prelude::*;
verus! {

use crate::define::*;
use crate::util::page_ptr_util_u::*;

#[verifier(external_body)]
pub proof fn lemma_usize_u64(x: u64)
    ensures
        x as usize as u64 == x,
{
    unimplemented!();
}

#[verifier(external_body)]
pub proof fn lemma_usize_int(x: int)
    ensures
        x as usize as int == x,
{
    unimplemented!();
}

#[verifier(external_body)]
pub proof fn set_lemma<A>()
    ensures
        forall|s1: Set<A>, s2: Set<A>, e: A|
            (s1 + s2).insert(e) == s1 + (s2.insert(e)) && s1 + (s2.insert(e)) == s2 + (s1.insert(e))
                && (s1 + s2).insert(e) == s2 + (s1.insert(e)) && (!(s1 + s2).contains(e)
                <==> !s1.contains(e) && !s2.contains(
                e,
            )),
// forall|s1:Set<A>, s2:Set<A>, s3:Set<A>, s4:Set<A>, e:A|
//     (!(s1 + s2 + s3 + s4).contains(e)) <==> (!s1.contains(e) && !s2.contains(e) && !s3.contains(e) && !s4.contains(e))

{
}

#[verifier(external_body)]
pub proof fn set_insert_lemma<A>()
    ensures
        forall|s1: Set<A>, x: A, y: A| x != y ==> (s1.insert(x).contains(y) == s1.contains(y)),
        forall|s1: Set<A>, x: A, y: A| s1.contains(y) ==> s1.insert(x).contains(y),
        forall|s1: Set<A>, x: A| s1.contains(x) ==> (s1.insert(x) == s1),
{
}

#[verifier(external_body)]
pub proof fn set_add_lemma<A>()
    ensures
        forall|s1: Set<A>|  s1 + Set::<A>::empty() == s1,
        forall|s1: Set<A>, s2: Set<A>, diff: Set<A>| 
            diff.subset_of(s1) ==> (s1 - diff) + (s2 + diff) == s1 + s2
{
}

//TODO: @Xiangdong prove this
#[verifier(external_body)]
pub proof fn page_ptr_lemma()
    ensures
        forall|ptr: PagePtr|
            #![auto]
            page_ptr_valid(ptr) ==> page_index_valid(page_ptr2page_index(ptr)),
        forall|index: usize|
            #![auto]
            page_index_valid(index) ==> page_ptr_valid(page_index2page_ptr(index)),
        forall|ptr: PagePtr|
            #![auto]
            page_ptr_valid(ptr) ==> page_index2page_ptr(page_ptr2page_index(ptr)) == ptr,
        forall|index: usize|
            #![auto]
            page_index_valid(index) ==> page_ptr2page_index(page_index2page_ptr(index)) == index,
        forall|ptr1: PagePtr, ptr2: PagePtr|
            #![auto]
            page_index_valid(ptr1) && page_index_valid(ptr2) && ptr1 == ptr2
                ==> page_ptr2page_index(ptr1) == page_ptr2page_index(ptr2),
        forall|ptr1: PagePtr, ptr2: PagePtr|
            #![auto]
            page_index_valid(ptr1) && page_index_valid(ptr2) && ptr1 != ptr2
                ==> page_ptr2page_index(ptr1) != page_ptr2page_index(ptr2),
        forall|index1: usize, index2: usize|
            #![auto]
            page_index_valid(index1) && page_index_valid(index2) && index1 == index2
                ==> page_index2page_ptr(index1) == page_index2page_ptr(index2),
        forall|index1: usize, index2: usize|
            #![auto]
            page_index_valid(index1) && page_index_valid(index2) && index1 != index2
                ==> page_index2page_ptr(index1) != page_index2page_ptr(index2),
{
    // assert(forall|index:usize| #![auto] page_index_valid(index) ==> (index * 4096) % 4096 == 0);
    // assert(forall|index:usize| #![auto] page_index_valid(index) ==> (index * 4096) == page_index2page_ptr(index));
    // assert(forall|index:usize| #![auto] page_index_valid(index) ==> page_index2page_ptr(index) % 4096 == 0);
}

} // verus!

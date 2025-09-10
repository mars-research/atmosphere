use vstd::prelude::*;
verus! {

use core::mem::MaybeUninit;
use crate::define::*;
use vstd::simple_pptr::PointsTo;
use crate::process_manager::endpoint::*;

#[verifier(external_body)]
pub fn endpoint_add_ref(
    endpoint_ptr: EndpointPtr,
    endpoint_perm: &mut Tracked<PointsTo<Endpoint>>,
    thread_ptr: ThreadPtr,
    endpoint_idx: EndpointIdx,
)
    requires
        old(endpoint_perm)@.is_init(),
        old(endpoint_perm)@.addr() == endpoint_ptr,
        old(endpoint_perm)@.value().rf_counter != usize::MAX,
        old(endpoint_perm)@.value().get_owning_threads().contains((thread_ptr, endpoint_idx))
            == false,
    ensures
        endpoint_perm@.is_init(),
        endpoint_perm@.addr() == endpoint_ptr,
        endpoint_perm@.value().queue == old(endpoint_perm)@.value().queue,
        endpoint_perm@.value().queue_state == old(endpoint_perm)@.value().queue_state,
        // endpoint_perm@.value().rf_counter == old(endpoint_perm)@.value().rf_counter,
        // endpoint_perm@.value().owning_threads == old(endpoint_perm)@.value().owning_threads,
        endpoint_perm@.value().owning_container == old(endpoint_perm)@.value().owning_container,
        endpoint_perm@.value().rf_counter == old(endpoint_perm)@.value().rf_counter + 1,
        endpoint_perm@.value().get_owning_threads() == old(
            endpoint_perm,
        )@.value().get_owning_threads().insert((thread_ptr, endpoint_idx)),
{
    unsafe {
        let uptr = endpoint_ptr as *mut MaybeUninit<Endpoint>;
        let ret = (*uptr).assume_init_mut().rf_counter += 1;
    }
}

#[verifier(external_body)]
pub fn endpoint_remove_ref(
    endpoint_ptr: EndpointPtr,
    endpoint_perm: &mut Tracked<PointsTo<Endpoint>>,
    thread_ptr: ThreadPtr,
    endpoint_idx: EndpointIdx,
)
    requires
        old(endpoint_perm)@.is_init(),
        old(endpoint_perm)@.addr() == endpoint_ptr,
        old(endpoint_perm)@.value().rf_counter != 0,
        old(endpoint_perm)@.value().get_owning_threads().contains((thread_ptr, endpoint_idx)),
    ensures
        endpoint_perm@.is_init(),
        endpoint_perm@.addr() == endpoint_ptr,
        endpoint_perm@.value().queue == old(endpoint_perm)@.value().queue,
        endpoint_perm@.value().queue_state == old(endpoint_perm)@.value().queue_state,
        // endpoint_perm@.value().rf_counter == old(endpoint_perm)@.value().rf_counter,
        // endpoint_perm@.value().owning_threads == old(endpoint_perm)@.value().owning_threads,
        endpoint_perm@.value().owning_container == old(endpoint_perm)@.value().owning_container,
        endpoint_perm@.value().rf_counter == old(endpoint_perm)@.value().rf_counter - 1,
        endpoint_perm@.value().get_owning_threads() == old(
            endpoint_perm,
        )@.value().get_owning_threads().remove((thread_ptr, endpoint_idx)),
{
    unsafe {
        let uptr = endpoint_ptr as *mut MaybeUninit<Endpoint>;
        let ret = (*uptr).assume_init_mut().rf_counter -= 1;
    }
}

#[verifier(external_body)]
pub fn endpoint_set_owning_container(
    endpoint_ptr: EndpointPtr,
    endpoint_perm: &mut Tracked<PointsTo<Endpoint>>,
    owning_container: ContainerPtr,
)
    requires
        old(endpoint_perm)@.is_init(),
        old(endpoint_perm)@.addr() == endpoint_ptr,
    ensures
        endpoint_perm@.is_init(),
        endpoint_perm@.addr() == endpoint_ptr,
        endpoint_perm@.value().queue == old(endpoint_perm)@.value().queue,
        endpoint_perm@.value().queue_state == old(endpoint_perm)@.value().queue_state,
        endpoint_perm@.value().rf_counter == old(endpoint_perm)@.value().rf_counter,
        endpoint_perm@.value().owning_threads == old(endpoint_perm)@.value().owning_threads,
        endpoint_perm@.value().owning_container == owning_container,
        endpoint_perm@.value().rf_counter == old(endpoint_perm)@.value().rf_counter,
{
    unsafe {
        let uptr = endpoint_ptr as *mut MaybeUninit<Endpoint>;
        let ret = (*uptr).assume_init_mut().owning_container = owning_container;
    }
}

#[verifier(external_body)]
pub fn endpoint_pop_head(
    endpoint_ptr: EndpointPtr,
    endpoint_perm: &mut Tracked<PointsTo<Endpoint>>,
) -> (ret: (ThreadPtr, SLLIndex))
    requires
        old(endpoint_perm)@.is_init(),
        old(endpoint_perm)@.addr() == endpoint_ptr,
        old(endpoint_perm)@.value().queue.len() > 0,
    ensures
        endpoint_perm@.is_init(),
        endpoint_perm@.addr() == endpoint_ptr,
        // endpoint_perm@.value().queue == old(endpoint_perm)@.value().queue,
        endpoint_perm@.value().queue_state == old(endpoint_perm)@.value().queue_state,
        endpoint_perm@.value().rf_counter == old(endpoint_perm)@.value().rf_counter,
        endpoint_perm@.value().owning_threads == old(endpoint_perm)@.value().owning_threads,
        endpoint_perm@.value().owning_container == old(endpoint_perm)@.value().owning_container,
        endpoint_perm@.value().rf_counter == old(endpoint_perm)@.value().rf_counter,
        endpoint_perm@.value().queue.wf(),
        endpoint_perm@.value().queue.len() == old(endpoint_perm)@.value().queue.len() - 1,
        endpoint_perm@.value().queue@ == old(endpoint_perm)@.value().queue@.skip(1),
        ret.0 == old(endpoint_perm)@.value().queue@[0],
        old(endpoint_perm)@.value().queue.value_list@[0] == ret.1,
        old(endpoint_perm)@.value().queue.node_ref_valid(ret.1),
        old(endpoint_perm)@.value().queue.node_ref_resolve(ret.1) == ret.0,
        forall|index: SLLIndex|
            #![trigger old(endpoint_perm)@.value().queue.node_ref_valid(index)]
            #![trigger endpoint_perm@.value().queue.node_ref_valid(index)]
            old(endpoint_perm)@.value().queue.node_ref_valid(index) && index != ret.1
                ==> endpoint_perm@.value().queue.node_ref_valid(index),
        forall|index: SLLIndex|
            #![trigger old(endpoint_perm)@.value().queue.node_ref_valid(index)]
            #![trigger endpoint_perm@.value().queue.node_ref_resolve(index)]
            #![trigger old(endpoint_perm)@.value().queue.node_ref_resolve(index)]
            old(endpoint_perm)@.value().queue.node_ref_valid(index) && index != ret.1
                ==> endpoint_perm@.value().queue.node_ref_resolve(index) == old(
                endpoint_perm,
            )@.value().queue.node_ref_resolve(index),
        forall|index: SLLIndex|
            #![trigger old(endpoint_perm)@.value().queue.node_ref_valid(index)]
            #![trigger endpoint_perm@.value().queue.node_ref_valid(index)]
            #![trigger old(endpoint_perm)@.value().queue.node_ref_resolve(index)]
            #![trigger endpoint_perm@.value().queue.node_ref_resolve(index)]
            old(endpoint_perm)@.value().queue.node_ref_valid(index) && old(
                endpoint_perm,
            )@.value().queue.node_ref_resolve(index) != ret.0
                ==> endpoint_perm@.value().queue.node_ref_valid(index)
                && endpoint_perm@.value().queue.node_ref_resolve(index) == old(
                endpoint_perm,
            )@.value().queue.node_ref_resolve(index),
        endpoint_perm@.value().queue.unique(),
        endpoint_perm@.value().queue@.no_duplicates(),
{
    unsafe {
        let uptr = endpoint_ptr as *mut MaybeUninit<Endpoint>;
        let ret = (*uptr).assume_init_mut().queue.pop();
        ret
    }
}

#[verifier(external_body)]
pub fn endpoint_push(
    endpoint_ptr: EndpointPtr,
    endpoint_perm: &mut Tracked<PointsTo<Endpoint>>,
    t_ptr: ThreadPtr,
) -> (ret: SLLIndex)
    requires
        old(endpoint_perm)@.is_init(),
        old(endpoint_perm)@.addr() == endpoint_ptr,
        old(endpoint_perm)@.value().queue.len() < MAX_NUM_THREADS_PER_ENDPOINT,
    ensures
        endpoint_perm@.is_init(),
        endpoint_perm@.addr() == endpoint_ptr,
        // endpoint_perm@.value().queue == old(endpoint_perm)@.value().queue,
        endpoint_perm@.value().queue_state == old(endpoint_perm)@.value().queue_state,
        endpoint_perm@.value().rf_counter == old(endpoint_perm)@.value().rf_counter,
        endpoint_perm@.value().owning_threads == old(endpoint_perm)@.value().owning_threads,
        endpoint_perm@.value().owning_container == old(endpoint_perm)@.value().owning_container,
        endpoint_perm@.value().rf_counter == old(endpoint_perm)@.value().rf_counter,
        endpoint_perm@.value().queue.wf(),
        endpoint_perm@.value().queue@ == old(endpoint_perm)@.value().queue@.push(t_ptr),
        endpoint_perm@.value().queue.len() == old(endpoint_perm)@.value().queue.len() + 1,
        forall|index: SLLIndex|
            #![trigger old(endpoint_perm)@.value().queue.node_ref_valid(index)]
            #![trigger endpoint_perm@.value().queue.node_ref_valid(index)]
            old(endpoint_perm)@.value().queue.node_ref_valid(index)
                ==> endpoint_perm@.value().queue.node_ref_valid(index),
        forall|index: SLLIndex|
            #![trigger old(endpoint_perm)@.value().queue.node_ref_valid(index)]
            old(endpoint_perm)@.value().queue.node_ref_valid(index) ==> index != ret,
        forall|index: SLLIndex|
            #![trigger old(endpoint_perm)@.value().queue.node_ref_valid(index)]
            #![trigger endpoint_perm@.value().queue.node_ref_resolve(index)]
            #![trigger old(endpoint_perm)@.value().queue.node_ref_resolve(index)]
            old(endpoint_perm)@.value().queue.node_ref_valid(index)
                ==> endpoint_perm@.value().queue.node_ref_resolve(index) == old(
                endpoint_perm,
            )@.value().queue.node_ref_resolve(index),
        endpoint_perm@.value().queue.node_ref_valid(ret),
        endpoint_perm@.value().queue.node_ref_resolve(ret) == t_ptr,
        endpoint_perm@.value().queue.unique(),
{
    unsafe {
        let uptr = endpoint_ptr as *mut MaybeUninit<Endpoint>;
        let ret = (*uptr).assume_init_mut().queue.push(&t_ptr);
        ret
    }
}

#[verifier(external_body)]
pub fn endpoint_push_and_set_state(
    endpoint_ptr: EndpointPtr,
    endpoint_perm: &mut Tracked<PointsTo<Endpoint>>,
    t_ptr: ThreadPtr,
    queue_state: EndpointState,
) -> (ret: SLLIndex)
    requires
        old(endpoint_perm)@.is_init(),
        old(endpoint_perm)@.addr() == endpoint_ptr,
        old(endpoint_perm)@.value().queue.len() < MAX_NUM_THREADS_PER_ENDPOINT,
    ensures
        endpoint_perm@.is_init(),
        endpoint_perm@.addr() == endpoint_ptr,
        // endpoint_perm@.value().queue == old(endpoint_perm)@.value().queue,
        endpoint_perm@.value().queue_state == queue_state,
        endpoint_perm@.value().rf_counter == old(endpoint_perm)@.value().rf_counter,
        endpoint_perm@.value().owning_threads == old(endpoint_perm)@.value().owning_threads,
        endpoint_perm@.value().owning_container == old(endpoint_perm)@.value().owning_container,
        endpoint_perm@.value().rf_counter == old(endpoint_perm)@.value().rf_counter,
        endpoint_perm@.value().queue.wf(),
        endpoint_perm@.value().queue@ == old(endpoint_perm)@.value().queue@.push(t_ptr),
        endpoint_perm@.value().queue.len() == old(endpoint_perm)@.value().queue.len() + 1,
        forall|index: SLLIndex|
            #![trigger old(endpoint_perm)@.value().queue.node_ref_valid(index)]
            #![trigger endpoint_perm@.value().queue.node_ref_valid(index)]
            old(endpoint_perm)@.value().queue.node_ref_valid(index)
                ==> endpoint_perm@.value().queue.node_ref_valid(index),
        forall|index: SLLIndex|
            #![trigger old(endpoint_perm)@.value().queue.node_ref_valid(index)]
            old(endpoint_perm)@.value().queue.node_ref_valid(index) ==> index != ret,
        forall|index: SLLIndex|
            #![trigger old(endpoint_perm)@.value().queue.node_ref_valid(index)]
            #![trigger endpoint_perm@.value().queue.node_ref_resolve(index)]
            #![trigger old(endpoint_perm)@.value().queue.node_ref_resolve(index)]
            old(endpoint_perm)@.value().queue.node_ref_valid(index)
                ==> endpoint_perm@.value().queue.node_ref_resolve(index) == old(
                endpoint_perm,
            )@.value().queue.node_ref_resolve(index),
        endpoint_perm@.value().queue.node_ref_valid(ret),
        endpoint_perm@.value().queue.node_ref_resolve(ret) == t_ptr,
        endpoint_perm@.value().queue.unique(),
{
    unsafe {
        let uptr = endpoint_ptr as *mut MaybeUninit<Endpoint>;
        let ret = (*uptr).assume_init_mut().queue.push(&t_ptr);
        (*uptr).assume_init_mut().queue_state = queue_state;
        ret
    }
}

#[verifier(external_body)]
pub fn page_to_endpoint(page_ptr: PagePtr, page_perm: Tracked<PagePerm4k>) -> (ret: (
    EndpointPtr,
    Tracked<PointsTo<Endpoint>>,
))
    requires
        page_perm@.is_init(),
        page_perm@.addr() == page_ptr,
    ensures
        ret.0 == page_ptr,
        ret.1@.is_init(),
        ret.1@.addr() == ret.0,
        ret.1@.value().queue.wf(),
        ret.1@.value().queue.unique(),
        ret.1@.value().queue@ =~= Seq::<ThreadPtr>::empty(),
        ret.1@.value().queue_state =~= EndpointState::SEND,
        ret.1@.value().rf_counter =~= 0,
        ret.1@.value().owning_threads@ =~= Set::<(ThreadPtr, EndpointIdx)>::empty(),
        ret.1@.value().owning_container == 0,
{
    unsafe {
        let uptr = page_ptr as *mut MaybeUninit<Endpoint>;
        (*uptr).assume_init_mut().queue.init();
        (*uptr).assume_init_mut().queue_state = EndpointState::SEND;
        (*uptr).assume_init_mut().rf_counter = 0;
        (*uptr).assume_init_mut().owning_container = 0;
        (page_ptr, Tracked::assume_new())
    }
}

#[verifier(external_body)]
pub fn endpoint_to_page(endpoint_ptr: EndpointPtr, endpoint_perm: Tracked<PointsTo<Endpoint>>) -> (ret: (
    PagePtr,
    Tracked<PagePerm4k>,
))
    requires
        endpoint_perm@.is_init(),
        endpoint_perm@.addr() == endpoint_ptr, 
    ensures
        ret.0 == endpoint_ptr,
        ret.1@.is_init(),
        ret.1@.addr() == endpoint_ptr,
{
    (endpoint_ptr, Tracked::assume_new())
}

pub fn page_to_endpoint_with_thread_and_container(
    owning_container: ContainerPtr,
    owning_thread: ThreadPtr,
    endpoint_idx: EndpointIdx,
    page_ptr: PagePtr,
    page_perm: Tracked<PagePerm4k>,
) -> (ret: (EndpointPtr, Tracked<PointsTo<Endpoint>>))
    requires
        page_perm@.is_init(),
        page_perm@.addr() == page_ptr,
    ensures
        ret.0 == page_ptr,
        ret.1@.is_init(),
        ret.1@.addr() == ret.0,
        ret.1@.value().queue.wf(),
        ret.1@.value().queue.unique(),
        ret.1@.value().queue@ =~= Seq::<ThreadPtr>::empty(),
        ret.1@.value().queue_state =~= EndpointState::SEND,
        ret.1@.value().rf_counter =~= 1,
        ret.1@.value().owning_threads@ =~= Set::<(ThreadPtr, EndpointIdx)>::empty().insert(
            (owning_thread, endpoint_idx),
        ),
        ret.1@.value().owning_container == owning_container,
{
    let (mut endpoint_ptr, mut endpoint_perm) = page_to_endpoint(page_ptr, page_perm);
    endpoint_add_ref(endpoint_ptr, &mut endpoint_perm, owning_thread, endpoint_idx);
    endpoint_set_owning_container(endpoint_ptr, &mut endpoint_perm, owning_container);
    (endpoint_ptr, endpoint_perm)
}

} // verus!

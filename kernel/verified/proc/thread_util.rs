use crate::trap::Registers;
use core::mem::MaybeUninit;
use vstd::prelude::*;
verus! {
use vstd::ptr::{
    PPtr, PointsTo,
    // PAGE_SZ,
};
use crate::proc::*;

use crate::define::*;

use crate::mars_staticlinkedlist::*;

#[verifier(external_body)]
pub fn page_to_thread(page: (PagePPtr,Tracked<PagePerm>)) -> (ret :(PPtr::<Thread>, Tracked<PointsTo<Thread>>))
    requires page.0.id() == page.1@@.pptr,
            page.1@@.value.is_Some(),
    ensures ret.0.id() == ret.1@@.pptr,
            ret.0.id() == page.0.id(),
            ret.1@@.value.is_Some(),
            ret.1@@.value.get_Some_0().endpoint_descriptors.wf(),
            ret.1@@.value.get_Some_0().endpoint_descriptors@ =~= Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat,|i: int| {0}),
            ret.1@@.value.get_Some_0().ipc_payload.message =~= None,
            ret.1@@.value.get_Some_0().ipc_payload.page_payload =~= None,
            ret.1@@.value.get_Some_0().ipc_payload.endpoint_payload =~= None,
            ret.1@@.value.get_Some_0().callee =~= None,
            ret.1@@.value.get_Some_0().caller =~= None,
            ret.1@@.value.get_Some_0().trap_frame.is_None(),
{
    unsafe{let uptr = page.0.to_usize() as *mut MaybeUninit<Thread>;
    (*uptr).assume_init_mut().endpoint_descriptors.init2zero();
    (*uptr).assume_init_mut().ipc_payload.message = None;
    (*uptr).assume_init_mut().ipc_payload.page_payload = None;
    (*uptr).assume_init_mut().callee = None;
    (*uptr).assume_init_mut().caller = None;
    (PPtr::<Thread>::from_usize(page.0.to_usize()), Tracked::assume_new())}
}


#[verifier(external_body)]
pub fn thread_set_scheduler_rf(pptr: &PPtr::<Thread>, perm: &mut Tracked< PointsTo<Thread>>, scheduler_rf: Option<Index>)
requires pptr.id() == old(perm)@@.pptr,
            old(perm)@@.value.is_Some(),
ensures pptr.id() == perm@@.pptr,
        perm@@.value.is_Some(),
        perm@@.value.get_Some_0().parent == old(perm)@@.value.get_Some_0().parent,
        perm@@.value.get_Some_0().state == old(perm)@@.value.get_Some_0().state,
        perm@@.value.get_Some_0().parent_rf == old(perm)@@.value.get_Some_0().parent_rf,
        //perm@@.value.get_Some_0().scheduler_rf == old(perm)@@.value.get_Some_0().scheduler_rf,
        perm@@.value.get_Some_0().endpoint_ptr == old(perm)@@.value.get_Some_0().endpoint_ptr,
        perm@@.value.get_Some_0().endpoint_rf == old(perm)@@.value.get_Some_0().endpoint_rf,
        perm@@.value.get_Some_0().endpoint_descriptors == old(perm)@@.value.get_Some_0().endpoint_descriptors,
        perm@@.value.get_Some_0().ipc_payload == old(perm)@@.value.get_Some_0().ipc_payload,
        perm@@.value.get_Some_0().error_code == old(perm)@@.value.get_Some_0().error_code,
        perm@@.value.get_Some_0().callee == old(perm)@@.value.get_Some_0().callee,
        perm@@.value.get_Some_0().caller == old(perm)@@.value.get_Some_0().caller,
        perm@@.value.get_Some_0().trap_frame == old(perm)@@.value.get_Some_0().trap_frame,
        perm@@.value.get_Some_0().scheduler_rf == scheduler_rf,
{
unsafe {
    let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
    (*uptr).assume_init_mut().scheduler_rf = scheduler_rf;
}
}

#[verifier(external_body)]
pub fn thread_set_state(pptr: &PPtr::<Thread>,perm: &mut Tracked<PointsTo<Thread>>, state: ThreadState)
requires pptr.id() == old(perm)@@.pptr,
            old(perm)@@.value.is_Some(),
ensures pptr.id() == perm@@.pptr,
        perm@@.value.is_Some(),
        perm@@.value.get_Some_0().parent == old(perm)@@.value.get_Some_0().parent,
        //perm@@.value.get_Some_0().state == old(perm)@@.value.get_Some_0().state,
        perm@@.value.get_Some_0().parent_rf == old(perm)@@.value.get_Some_0().parent_rf,
        perm@@.value.get_Some_0().scheduler_rf == old(perm)@@.value.get_Some_0().scheduler_rf,
        perm@@.value.get_Some_0().endpoint_ptr == old(perm)@@.value.get_Some_0().endpoint_ptr,
        perm@@.value.get_Some_0().endpoint_rf == old(perm)@@.value.get_Some_0().endpoint_rf,
        perm@@.value.get_Some_0().endpoint_descriptors =~= old(perm)@@.value.get_Some_0().endpoint_descriptors,
        perm@@.value.get_Some_0().ipc_payload == old(perm)@@.value.get_Some_0().ipc_payload,
        perm@@.value.get_Some_0().error_code == old(perm)@@.value.get_Some_0().error_code,
        perm@@.value.get_Some_0().callee == old(perm)@@.value.get_Some_0().callee,
        perm@@.value.get_Some_0().caller == old(perm)@@.value.get_Some_0().caller,
        perm@@.value.get_Some_0().trap_frame == old(perm)@@.value.get_Some_0().trap_frame,
        perm@@.value.get_Some_0().state == state,
{
unsafe {
    let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
    (*uptr).assume_init_mut().state = state;
}
}

#[verifier(external_body)]
pub fn thread_set_parent(pptr: &PPtr::<Thread>,perm: &mut Tracked<PointsTo<Thread>>, parent: ProcPtr)
requires pptr.id() == old(perm)@@.pptr,
            old(perm)@@.value.is_Some(),
ensures pptr.id() == perm@@.pptr,
        perm@@.value.is_Some(),
        //perm@@.value.get_Some_0().parent == old(perm)@@.value.get_Some_0().parent,
        perm@@.value.get_Some_0().state == old(perm)@@.value.get_Some_0().state,
        perm@@.value.get_Some_0().parent_rf == old(perm)@@.value.get_Some_0().parent_rf,
        perm@@.value.get_Some_0().scheduler_rf == old(perm)@@.value.get_Some_0().scheduler_rf,
        perm@@.value.get_Some_0().endpoint_ptr == old(perm)@@.value.get_Some_0().endpoint_ptr,
        perm@@.value.get_Some_0().endpoint_rf == old(perm)@@.value.get_Some_0().endpoint_rf,
        perm@@.value.get_Some_0().endpoint_descriptors == old(perm)@@.value.get_Some_0().endpoint_descriptors,
        perm@@.value.get_Some_0().ipc_payload == old(perm)@@.value.get_Some_0().ipc_payload,
        perm@@.value.get_Some_0().error_code == old(perm)@@.value.get_Some_0().error_code,
        perm@@.value.get_Some_0().callee == old(perm)@@.value.get_Some_0().callee,
        perm@@.value.get_Some_0().caller == old(perm)@@.value.get_Some_0().caller,
        perm@@.value.get_Some_0().trap_frame == old(perm)@@.value.get_Some_0().trap_frame,
        perm@@.value.get_Some_0().parent == parent,
{
unsafe {
    let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
    (*uptr).assume_init_mut().parent = parent;
}
}

#[verifier(external_body)]
pub fn thread_set_endpoint_descriptors(pptr: &PPtr::<Thread>,perm: &mut Tracked<PointsTo<Thread>>, index: usize, endpoint_pointer: EndpointPtr) -> (ret: EndpointPtr)
requires pptr.id() == old(perm)@@.pptr,
            old(perm)@@.value.is_Some(),
            0<=index<MAX_NUM_ENDPOINT_DESCRIPTORS,
            endpoint_descriptors_unique(old(perm)@@.value.get_Some_0().endpoint_descriptors)
ensures pptr.id() == perm@@.pptr,
        perm@@.value.is_Some(),
        perm@@.value.get_Some_0().parent == old(perm)@@.value.get_Some_0().parent,
        perm@@.value.get_Some_0().state == old(perm)@@.value.get_Some_0().state,
        perm@@.value.get_Some_0().parent_rf == old(perm)@@.value.get_Some_0().parent_rf,
        perm@@.value.get_Some_0().scheduler_rf == old(perm)@@.value.get_Some_0().scheduler_rf,
        perm@@.value.get_Some_0().endpoint_ptr == old(perm)@@.value.get_Some_0().endpoint_ptr,
        perm@@.value.get_Some_0().endpoint_rf == old(perm)@@.value.get_Some_0().endpoint_rf,
        //perm@@.value.get_Some_0().endpoint_descriptors == old(perm)@@.value.get_Some_0().endpoint_descriptors,
        perm@@.value.get_Some_0().ipc_payload == old(perm)@@.value.get_Some_0().ipc_payload,
        perm@@.value.get_Some_0().error_code == old(perm)@@.value.get_Some_0().error_code,
        perm@@.value.get_Some_0().callee == old(perm)@@.value.get_Some_0().callee,
        perm@@.value.get_Some_0().caller == old(perm)@@.value.get_Some_0().caller,
        perm@@.value.get_Some_0().trap_frame == old(perm)@@.value.get_Some_0().trap_frame,
        perm@@.value.get_Some_0().endpoint_descriptors.wf(),
        perm@@.value.get_Some_0().endpoint_descriptors@ =~= old(perm)@@.value.get_Some_0().endpoint_descriptors@.update(index as int, endpoint_pointer),
        perm@@.value.get_Some_0().endpoint_descriptors@.contains(endpoint_pointer),
        ret == old(perm)@@.value.get_Some_0().endpoint_descriptors@[index as int],
        forall|_endpoint_ptr: EndpointPtr| #![auto]  _endpoint_ptr != ret && _endpoint_ptr != 0 && _endpoint_ptr != endpoint_pointer
            ==> perm@@.value.get_Some_0().endpoint_descriptors@.contains(_endpoint_ptr) == old(perm)@@.value.get_Some_0().endpoint_descriptors@.contains(_endpoint_ptr),
{
unsafe {
    let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
    let ret = (*uptr).assume_init_mut().endpoint_descriptors.ar[index];
    (*uptr).assume_init_mut().endpoint_descriptors.ar[index] = endpoint_pointer;
    return ret;
}
}

#[verifier(external_body)]
pub fn thread_set_parent_rf(pptr: &PPtr::<Thread>,perm: &mut Tracked<PointsTo<Thread>>, parent_rf: Index)
requires pptr.id() == old(perm)@@.pptr,
            old(perm)@@.value.is_Some(),
ensures pptr.id() == perm@@.pptr,
        perm@@.value.is_Some(),
        perm@@.value.get_Some_0().parent == old(perm)@@.value.get_Some_0().parent,
        perm@@.value.get_Some_0().state == old(perm)@@.value.get_Some_0().state,
        //perm@@.value.get_Some_0().parent_rf == old(perm)@@.value.get_Some_0().parent_rf,
        perm@@.value.get_Some_0().scheduler_rf == old(perm)@@.value.get_Some_0().scheduler_rf,
        perm@@.value.get_Some_0().endpoint_ptr == old(perm)@@.value.get_Some_0().endpoint_ptr,
        perm@@.value.get_Some_0().endpoint_rf == old(perm)@@.value.get_Some_0().endpoint_rf,
        perm@@.value.get_Some_0().endpoint_descriptors == old(perm)@@.value.get_Some_0().endpoint_descriptors,
        perm@@.value.get_Some_0().ipc_payload == old(perm)@@.value.get_Some_0().ipc_payload,
        perm@@.value.get_Some_0().error_code == old(perm)@@.value.get_Some_0().error_code,
        perm@@.value.get_Some_0().callee == old(perm)@@.value.get_Some_0().callee,
        perm@@.value.get_Some_0().caller == old(perm)@@.value.get_Some_0().caller,
        perm@@.value.get_Some_0().trap_frame == old(perm)@@.value.get_Some_0().trap_frame,
        perm@@.value.get_Some_0().parent_rf == parent_rf,
{
unsafe {
    let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
    (*uptr).assume_init_mut().parent_rf =parent_rf;
}
}


#[verifier(external_body)]
pub fn thread_set_endpoint_ptr(pptr: &PPtr::<Thread>,perm: &mut Tracked<PointsTo<Thread>>, endpoint_ptr: Option<EndpointPtr>)
requires pptr.id() == old(perm)@@.pptr,
            old(perm)@@.value.is_Some(),
ensures pptr.id() == perm@@.pptr,
        perm@@.value.is_Some(),
        perm@@.value.get_Some_0().parent == old(perm)@@.value.get_Some_0().parent,
        perm@@.value.get_Some_0().state == old(perm)@@.value.get_Some_0().state,
        perm@@.value.get_Some_0().parent_rf == old(perm)@@.value.get_Some_0().parent_rf,
        perm@@.value.get_Some_0().scheduler_rf == old(perm)@@.value.get_Some_0().scheduler_rf,
        //perm@@.value.get_Some_0().endpoint_ptr == old(perm)@@.value.get_Some_0().endpoint_ptr,
        perm@@.value.get_Some_0().endpoint_rf == old(perm)@@.value.get_Some_0().endpoint_rf,
        perm@@.value.get_Some_0().endpoint_descriptors == old(perm)@@.value.get_Some_0().endpoint_descriptors,
        perm@@.value.get_Some_0().ipc_payload == old(perm)@@.value.get_Some_0().ipc_payload,
        perm@@.value.get_Some_0().error_code == old(perm)@@.value.get_Some_0().error_code,
        perm@@.value.get_Some_0().callee == old(perm)@@.value.get_Some_0().callee,
        perm@@.value.get_Some_0().caller == old(perm)@@.value.get_Some_0().caller,
        perm@@.value.get_Some_0().trap_frame == old(perm)@@.value.get_Some_0().trap_frame,
        perm@@.value.get_Some_0().endpoint_ptr == endpoint_ptr,
{
    unsafe {
        let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
        (*uptr).assume_init_mut().endpoint_ptr =endpoint_ptr;
    }
}


#[verifier(external_body)]
pub fn thread_set_endpoint_rf(pptr: &PPtr::<Thread>,perm: &mut Tracked<PointsTo<Thread>>, endpoint_rf: Option<Index>)
requires pptr.id() == old(perm)@@.pptr,
            old(perm)@@.value.is_Some(),
ensures pptr.id() == perm@@.pptr,
        perm@@.value.is_Some(),
        perm@@.value.get_Some_0().parent == old(perm)@@.value.get_Some_0().parent,
        perm@@.value.get_Some_0().state == old(perm)@@.value.get_Some_0().state,
        perm@@.value.get_Some_0().parent_rf == old(perm)@@.value.get_Some_0().parent_rf,
        perm@@.value.get_Some_0().scheduler_rf == old(perm)@@.value.get_Some_0().scheduler_rf,
        perm@@.value.get_Some_0().endpoint_ptr == old(perm)@@.value.get_Some_0().endpoint_ptr,
        //perm@@.value.get_Some_0().endpoint_rf == old(perm)@@.value.get_Some_0().endpoint_rf,
        perm@@.value.get_Some_0().endpoint_descriptors == old(perm)@@.value.get_Some_0().endpoint_descriptors,
        perm@@.value.get_Some_0().ipc_payload == old(perm)@@.value.get_Some_0().ipc_payload,
        perm@@.value.get_Some_0().error_code == old(perm)@@.value.get_Some_0().error_code,
        perm@@.value.get_Some_0().callee == old(perm)@@.value.get_Some_0().callee,
        perm@@.value.get_Some_0().caller == old(perm)@@.value.get_Some_0().caller,
        perm@@.value.get_Some_0().trap_frame == old(perm)@@.value.get_Some_0().trap_frame,
        perm@@.value.get_Some_0().endpoint_rf == endpoint_rf,
{
    unsafe {
        let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
        (*uptr).assume_init_mut().endpoint_rf =endpoint_rf;
    }
}

#[verifier(external_body)]
pub fn thread_set_error_code(pptr: &PPtr::<Thread>,perm: &mut Tracked<PointsTo<Thread>>, error_code: Option<ErrorCodeType>)
requires pptr.id() == old(perm)@@.pptr,
            old(perm)@@.value.is_Some(),
ensures pptr.id() == perm@@.pptr,
        perm@@.value.is_Some(),
        perm@@.value.get_Some_0().parent == old(perm)@@.value.get_Some_0().parent,
        perm@@.value.get_Some_0().state == old(perm)@@.value.get_Some_0().state,
        perm@@.value.get_Some_0().parent_rf == old(perm)@@.value.get_Some_0().parent_rf,
        perm@@.value.get_Some_0().scheduler_rf == old(perm)@@.value.get_Some_0().scheduler_rf,
        perm@@.value.get_Some_0().endpoint_ptr == old(perm)@@.value.get_Some_0().endpoint_ptr,
        perm@@.value.get_Some_0().endpoint_rf == old(perm)@@.value.get_Some_0().endpoint_rf,
        perm@@.value.get_Some_0().endpoint_descriptors == old(perm)@@.value.get_Some_0().endpoint_descriptors,
        perm@@.value.get_Some_0().ipc_payload == old(perm)@@.value.get_Some_0().ipc_payload,
        //perm@@.value.get_Some_0().error_code == old(perm)@@.value.get_Some_0().error_code,
        perm@@.value.get_Some_0().callee == old(perm)@@.value.get_Some_0().callee,
        perm@@.value.get_Some_0().caller == old(perm)@@.value.get_Some_0().caller,
        perm@@.value.get_Some_0().trap_frame == old(perm)@@.value.get_Some_0().trap_frame,
        perm@@.value.get_Some_0().error_code == error_code,
{
    unsafe {
        let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
        (*uptr).assume_init_mut().error_code =error_code;
    }
}

#[verifier(external_body)]
pub fn thread_set_ipc_payload(pptr: &PPtr::<Thread>,perm: &mut Tracked<PointsTo<Thread>>, ipc_payload:IPCPayLoad)
requires pptr.id() == old(perm)@@.pptr,
            old(perm)@@.value.is_Some(),
ensures pptr.id() == perm@@.pptr,
        perm@@.value.is_Some(),
        perm@@.value.get_Some_0().parent == old(perm)@@.value.get_Some_0().parent,
        perm@@.value.get_Some_0().state == old(perm)@@.value.get_Some_0().state,
        perm@@.value.get_Some_0().parent_rf == old(perm)@@.value.get_Some_0().parent_rf,
        perm@@.value.get_Some_0().scheduler_rf == old(perm)@@.value.get_Some_0().scheduler_rf,
        perm@@.value.get_Some_0().endpoint_ptr == old(perm)@@.value.get_Some_0().endpoint_ptr,
        perm@@.value.get_Some_0().endpoint_rf == old(perm)@@.value.get_Some_0().endpoint_rf,
        perm@@.value.get_Some_0().endpoint_descriptors == old(perm)@@.value.get_Some_0().endpoint_descriptors,
        // perm@@.value.get_Some_0().ipc_payload == old(perm)@@.value.get_Some_0().ipc_payload,
        perm@@.value.get_Some_0().error_code == old(perm)@@.value.get_Some_0().error_code,
        perm@@.value.get_Some_0().callee == old(perm)@@.value.get_Some_0().callee,
        perm@@.value.get_Some_0().caller == old(perm)@@.value.get_Some_0().caller,
        perm@@.value.get_Some_0().trap_frame == old(perm)@@.value.get_Some_0().trap_frame,
        perm@@.value.get_Some_0().ipc_payload == ipc_payload,
{
    unsafe {
        let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
        (*uptr).assume_init_mut().ipc_payload = ipc_payload;
    }
}

#[verifier(external_body)]
pub fn thread_set_callee(pptr: &PPtr::<Thread>,perm: &mut Tracked<PointsTo<Thread>>, callee: Option<ThreadPtr>)
requires pptr.id() == old(perm)@@.pptr,
            old(perm)@@.value.is_Some(),
ensures pptr.id() == perm@@.pptr,
        perm@@.value.is_Some(),
        perm@@.value.get_Some_0().parent == old(perm)@@.value.get_Some_0().parent,
        perm@@.value.get_Some_0().state == old(perm)@@.value.get_Some_0().state,
        perm@@.value.get_Some_0().parent_rf == old(perm)@@.value.get_Some_0().parent_rf,
        perm@@.value.get_Some_0().scheduler_rf == old(perm)@@.value.get_Some_0().scheduler_rf,
        perm@@.value.get_Some_0().endpoint_ptr == old(perm)@@.value.get_Some_0().endpoint_ptr,
        perm@@.value.get_Some_0().endpoint_rf == old(perm)@@.value.get_Some_0().endpoint_rf,
        perm@@.value.get_Some_0().endpoint_descriptors == old(perm)@@.value.get_Some_0().endpoint_descriptors,
        perm@@.value.get_Some_0().ipc_payload == old(perm)@@.value.get_Some_0().ipc_payload,
        perm@@.value.get_Some_0().error_code == old(perm)@@.value.get_Some_0().error_code,
        // perm@@.value.get_Some_0().callee == old(perm)@@.value.get_Some_0().callee,
        perm@@.value.get_Some_0().caller == old(perm)@@.value.get_Some_0().caller,
        perm@@.value.get_Some_0().trap_frame == old(perm)@@.value.get_Some_0().trap_frame,
        perm@@.value.get_Some_0().callee == callee,
{
    unsafe {
        let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
        (*uptr).assume_init_mut().callee = callee;
    }
}

#[verifier(external_body)]
pub fn thread_set_caller(pptr: &PPtr::<Thread>,perm: &mut Tracked<PointsTo<Thread>>, caller: Option<ThreadPtr>)
requires pptr.id() == old(perm)@@.pptr,
            old(perm)@@.value.is_Some(),
ensures pptr.id() == perm@@.pptr,
        perm@@.value.is_Some(),
        perm@@.value.get_Some_0().parent == old(perm)@@.value.get_Some_0().parent,
        perm@@.value.get_Some_0().state == old(perm)@@.value.get_Some_0().state,
        perm@@.value.get_Some_0().parent_rf == old(perm)@@.value.get_Some_0().parent_rf,
        perm@@.value.get_Some_0().scheduler_rf == old(perm)@@.value.get_Some_0().scheduler_rf,
        perm@@.value.get_Some_0().endpoint_ptr == old(perm)@@.value.get_Some_0().endpoint_ptr,
        perm@@.value.get_Some_0().endpoint_rf == old(perm)@@.value.get_Some_0().endpoint_rf,
        perm@@.value.get_Some_0().endpoint_descriptors == old(perm)@@.value.get_Some_0().endpoint_descriptors,
        perm@@.value.get_Some_0().ipc_payload == old(perm)@@.value.get_Some_0().ipc_payload,
        perm@@.value.get_Some_0().error_code == old(perm)@@.value.get_Some_0().error_code,
        perm@@.value.get_Some_0().callee == old(perm)@@.value.get_Some_0().callee,
        // perm@@.value.get_Some_0().caller == old(perm)@@.value.get_Some_0().caller,
        perm@@.value.get_Some_0().trap_frame == old(perm)@@.value.get_Some_0().trap_frame,
        perm@@.value.get_Some_0().caller == caller,
{
    unsafe {
        let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
        (*uptr).assume_init_mut().caller = caller;
    }
}

#[verifier(external_body)]
pub fn thread_set_trap_frame(pptr: &PPtr::<Thread>,perm: &mut Tracked<PointsTo<Thread>>, trap_frame: &Registers)
requires pptr.id() == old(perm)@@.pptr,
            old(perm)@@.value.is_Some(),
ensures pptr.id() == perm@@.pptr,
        perm@@.value.is_Some(),
        perm@@.value.get_Some_0().parent == old(perm)@@.value.get_Some_0().parent,
        perm@@.value.get_Some_0().state == old(perm)@@.value.get_Some_0().state,
        perm@@.value.get_Some_0().parent_rf == old(perm)@@.value.get_Some_0().parent_rf,
        perm@@.value.get_Some_0().scheduler_rf == old(perm)@@.value.get_Some_0().scheduler_rf,
        perm@@.value.get_Some_0().endpoint_ptr == old(perm)@@.value.get_Some_0().endpoint_ptr,
        perm@@.value.get_Some_0().endpoint_rf == old(perm)@@.value.get_Some_0().endpoint_rf,
        perm@@.value.get_Some_0().endpoint_descriptors == old(perm)@@.value.get_Some_0().endpoint_descriptors,
        perm@@.value.get_Some_0().ipc_payload == old(perm)@@.value.get_Some_0().ipc_payload,
        perm@@.value.get_Some_0().error_code == old(perm)@@.value.get_Some_0().error_code,
        perm@@.value.get_Some_0().callee == old(perm)@@.value.get_Some_0().callee,
        perm@@.value.get_Some_0().caller == old(perm)@@.value.get_Some_0().caller,
        perm@@.value.get_Some_0().trap_frame.is_Some(),
        perm@@.value.get_Some_0().trap_frame.get_Some_0() =~= trap_frame,
{
    unsafe {
        let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
        (*uptr).assume_init_mut().trap_frame.set_self(trap_frame);
    }
}

#[verifier(external_body)]
pub fn thread_set_trap_frame_fast(pptr: &PPtr::<Thread>,perm: &mut Tracked<PointsTo<Thread>>, trap_frame: &Registers)
requires pptr.id() == old(perm)@@.pptr,
            old(perm)@@.value.is_Some(),
ensures pptr.id() == perm@@.pptr,
        perm@@.value.is_Some(),
        perm@@.value.get_Some_0().parent == old(perm)@@.value.get_Some_0().parent,
        perm@@.value.get_Some_0().state == old(perm)@@.value.get_Some_0().state,
        perm@@.value.get_Some_0().parent_rf == old(perm)@@.value.get_Some_0().parent_rf,
        perm@@.value.get_Some_0().scheduler_rf == old(perm)@@.value.get_Some_0().scheduler_rf,
        perm@@.value.get_Some_0().endpoint_ptr == old(perm)@@.value.get_Some_0().endpoint_ptr,
        perm@@.value.get_Some_0().endpoint_rf == old(perm)@@.value.get_Some_0().endpoint_rf,
        perm@@.value.get_Some_0().endpoint_descriptors == old(perm)@@.value.get_Some_0().endpoint_descriptors,
        perm@@.value.get_Some_0().ipc_payload == old(perm)@@.value.get_Some_0().ipc_payload,
        perm@@.value.get_Some_0().error_code == old(perm)@@.value.get_Some_0().error_code,
        perm@@.value.get_Some_0().callee == old(perm)@@.value.get_Some_0().callee,
        perm@@.value.get_Some_0().caller == old(perm)@@.value.get_Some_0().caller,
        perm@@.value.get_Some_0().trap_frame.is_Some(),
        perm@@.value.get_Some_0().trap_frame.get_Some_0() =~= trap_frame,
{
    unsafe {
        let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
        (*uptr).assume_init_mut().trap_frame.set_self_fast(trap_frame);
    }
}

#[verifier(external_body)]
pub fn thread_empty_trap_frame(pptr: &PPtr::<Thread>,perm: &mut Tracked<PointsTo<Thread>>)
requires pptr.id() == old(perm)@@.pptr,
            old(perm)@@.value.is_Some(),
ensures pptr.id() == perm@@.pptr,
        perm@@.value.is_Some(),
        perm@@.value.get_Some_0().parent == old(perm)@@.value.get_Some_0().parent,
        perm@@.value.get_Some_0().state == old(perm)@@.value.get_Some_0().state,
        perm@@.value.get_Some_0().parent_rf == old(perm)@@.value.get_Some_0().parent_rf,
        perm@@.value.get_Some_0().scheduler_rf == old(perm)@@.value.get_Some_0().scheduler_rf,
        perm@@.value.get_Some_0().endpoint_ptr == old(perm)@@.value.get_Some_0().endpoint_ptr,
        perm@@.value.get_Some_0().endpoint_rf == old(perm)@@.value.get_Some_0().endpoint_rf,
        perm@@.value.get_Some_0().endpoint_descriptors == old(perm)@@.value.get_Some_0().endpoint_descriptors,
        perm@@.value.get_Some_0().ipc_payload == old(perm)@@.value.get_Some_0().ipc_payload,
        perm@@.value.get_Some_0().error_code == old(perm)@@.value.get_Some_0().error_code,
        perm@@.value.get_Some_0().callee == old(perm)@@.value.get_Some_0().callee,
        perm@@.value.get_Some_0().caller == old(perm)@@.value.get_Some_0().caller,
        perm@@.value.get_Some_0().trap_frame.is_None(),
{
    unsafe {
        let uptr = pptr.to_usize() as *mut MaybeUninit<Thread>;
        (*uptr).assume_init_mut().trap_frame.set_to_none();
    }
}

#[verifier(external_body)]
pub fn endpoint_remove_thread(endpoint_pptr: PPtr::<Endpoint>,endpoint_perm: &mut Tracked<PointsTo<Endpoint>>, rf: Index) -> (ret: ThreadPtr)
    requires
        endpoint_pptr.id() == old(endpoint_perm)@@.pptr,
        old(endpoint_perm)@@.value.is_Some(),
        old(endpoint_perm)@@.value.get_Some_0().queue.wf(),
        old(endpoint_perm)@@.value.get_Some_0().queue.node_ref_valid(rf),
        old(endpoint_perm)@@.value.get_Some_0().queue.unique(),
    ensures
        endpoint_pptr.id() == endpoint_perm@@.pptr,
        endpoint_perm@@.value.is_Some(),
        endpoint_perm@@.value.get_Some_0().queue.wf(),
        endpoint_perm@@.value.get_Some_0().owning_threads@ =~= old(endpoint_perm)@@.value.get_Some_0().owning_threads@,
        endpoint_perm@@.value.get_Some_0().rf_counter =~= old(endpoint_perm)@@.value.get_Some_0().rf_counter,
        endpoint_perm@@.value.get_Some_0().queue_state =~= old(endpoint_perm)@@.value.get_Some_0().queue_state,
        endpoint_perm@@.value.get_Some_0().queue.value_list_len == old(endpoint_perm)@@.value.get_Some_0().queue.value_list_len - 1,
        ret == old(endpoint_perm)@@.value.get_Some_0().queue.node_ref_resolve(rf),
        endpoint_perm@@.value.get_Some_0().queue.spec_seq@ == old(endpoint_perm)@@.value.get_Some_0().queue.spec_seq@.remove(old(endpoint_perm)@@.value.get_Some_0().queue.spec_seq@.index_of(old(endpoint_perm)@@.value.get_Some_0().queue.node_ref_resolve(rf))),
        forall| value:usize|  #![auto]  ret != value ==> old(endpoint_perm)@@.value.get_Some_0().queue.spec_seq@.contains(value) == endpoint_perm@@.value.get_Some_0().queue.spec_seq@.contains(value),
        endpoint_perm@@.value.get_Some_0().queue.spec_seq@.contains(ret) == false,
        forall|_index:Index| old(endpoint_perm)@@.value.get_Some_0().queue.node_ref_valid(_index) && _index != rf ==> endpoint_perm@@.value.get_Some_0().queue.node_ref_valid(_index),
        forall|_index:Index| old(endpoint_perm)@@.value.get_Some_0().queue.node_ref_valid(_index) && _index != rf ==> endpoint_perm@@.value.get_Some_0().queue.node_ref_resolve(_index) == old(endpoint_perm)@@.value.get_Some_0().queue.node_ref_resolve(_index),
        endpoint_perm@@.value.get_Some_0().queue.unique(),
        // endpoint_perm@@.value.get_Some_0().queue.len() == 0 ==> endpoint_perm@@.value.get_Some_0().state == EMPTY,
        // endpoint_perm@@.value.get_Some_0().queue.len() != 0 ==> endpoint_perm@@.value.get_Some_0().state == old(endpoint_perm)@@.value.get_Some_0().state,

{
    let uptr = endpoint_pptr.to_usize() as *mut MaybeUninit<Endpoint>;
    unsafe{let ret = (*uptr).assume_init_mut().queue.remove(rf);

    return ret;}
}

}

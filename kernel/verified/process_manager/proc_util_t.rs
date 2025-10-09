use vstd::prelude::*;
verus! {

use core::mem::MaybeUninit;
use crate::define::*;
use vstd::simple_pptr::PointsTo;
use crate::process_manager::process::*;

#[verifier(external_body)]
pub fn proc_push_thread(
    proc_ptr: ProcPtr,
    proc_perm: &mut Tracked<PointsTo<Process>>,
    thread_ptr: &ThreadPtr,
) -> (ret: SLLIndex)
    requires
        old(proc_perm)@.is_init(),
        old(proc_perm)@.addr() == proc_ptr,
        old(proc_perm)@.value().owned_threads.wf(),
        old(proc_perm)@.value().owned_threads.unique(),
        old(proc_perm)@.value().owned_threads.len() < MAX_NUM_THREADS_PER_PROC,
        old(proc_perm)@.value().owned_threads@.contains(*thread_ptr) == false,
    ensures
        proc_perm@.is_init(),
        proc_perm@.addr() == proc_ptr,
        proc_perm@.value().owning_container =~= old(proc_perm)@.value().owning_container,
        proc_perm@.value().rev_ptr =~= old(proc_perm)@.value().rev_ptr,
        proc_perm@.value().pcid =~= old(proc_perm)@.value().pcid,
        proc_perm@.value().ioid =~= old(proc_perm)@.value().ioid,
        // proc_perm@.value().owned_threads =~= old(proc_perm)@.value().owned_threads,
        proc_perm@.value().parent =~= old(proc_perm)@.value().parent,
        proc_perm@.value().parent_rev_ptr =~= old(proc_perm)@.value().parent_rev_ptr,
        proc_perm@.value().children =~= old(proc_perm)@.value().children,
        proc_perm@.value().uppertree_seq =~= old(proc_perm)@.value().uppertree_seq,
        proc_perm@.value().subtree_set =~= old(proc_perm)@.value().subtree_set,
        proc_perm@.value().depth =~= old(proc_perm)@.value().depth,
        proc_perm@.value().dmd_paging_mode =~= old(proc_perm)@.value().dmd_paging_mode,
        proc_perm@.value().owned_threads.wf(),
        proc_perm@.value().owned_threads@ =~= old(proc_perm)@.value().owned_threads@.push(
            *thread_ptr,
        ),
        proc_perm@.value().owned_threads.len() == old(proc_perm)@.value().owned_threads.len() + 1,
        forall|v:ThreadPtr|
            #![auto]
            old(proc_perm)@.value().owned_threads@.contains(v) ==> 
                old(proc_perm)@.value().owned_threads.get_node_ref(v) == 
                    proc_perm@.value().owned_threads.get_node_ref(v),
        proc_perm@.value().owned_threads.get_node_ref(*thread_ptr) == ret,
        proc_perm@.value().owned_threads.unique(),
{
    unsafe {
        let uptr = proc_ptr as *mut MaybeUninit<Process>;
        let ret = (*uptr).assume_init_mut().owned_threads.push(thread_ptr);
        return ret;
    }
}

#[verifier(external_body)]
pub fn proc_remove_thread(
    proc_ptr: ProcPtr,
    proc_perm: &mut Tracked<PointsTo<Process>>,
    rev_ptr: SLLIndex,
    thread_ptr: Ghost<ThreadPtr>,
) -> (ret: ThreadPtr)
    requires
        old(proc_perm)@.is_init(),
        old(proc_perm)@.addr() == proc_ptr,
        old(proc_perm)@.value().owned_threads.wf(),
        old(proc_perm)@.value().owned_threads@.contains(thread_ptr@),
        old(proc_perm)@.value().owned_threads.get_node_ref(thread_ptr@) == rev_ptr,
    ensures
        proc_perm@.is_init(),
        proc_perm@.addr() == proc_ptr,
        proc_perm@.value().owning_container =~= old(proc_perm)@.value().owning_container,
        proc_perm@.value().rev_ptr =~= old(proc_perm)@.value().rev_ptr,
        proc_perm@.value().pcid =~= old(proc_perm)@.value().pcid,
        proc_perm@.value().ioid =~= old(proc_perm)@.value().ioid,
        // proc_perm@.value().owned_threads =~= old(proc_perm)@.value().owned_threads,
        proc_perm@.value().parent =~= old(proc_perm)@.value().parent,
        proc_perm@.value().parent_rev_ptr =~= old(proc_perm)@.value().parent_rev_ptr,
        proc_perm@.value().children =~= old(proc_perm)@.value().children,
        proc_perm@.value().uppertree_seq =~= old(proc_perm)@.value().uppertree_seq,
        proc_perm@.value().subtree_set =~= old(proc_perm)@.value().subtree_set,
        proc_perm@.value().depth =~= old(proc_perm)@.value().depth,
        proc_perm@.value().dmd_paging_mode =~= old(proc_perm)@.value().dmd_paging_mode,
        proc_perm@.value().owned_threads.wf(),
        proc_perm@.value().owned_threads.len() == old(proc_perm)@.value().owned_threads.len() - 1,
        ret == thread_ptr@,
        forall|v:ThreadPtr|
            #![auto]
            proc_perm@.value().owned_threads@.contains(v) ==> 
                old(proc_perm)@.value().owned_threads.get_node_ref(v) == 
                    proc_perm@.value().owned_threads.get_node_ref(v),
        proc_perm@.value().owned_threads.unique(),
        proc_perm@.value().owned_threads@ =~= old(proc_perm)@.value().owned_threads@.remove_value(ret),
{
    unsafe {
        let uptr = proc_ptr as *mut MaybeUninit<Process>;
        let ret = (*uptr).assume_init_mut().owned_threads.remove(rev_ptr, Ghost(0));
        return ret;
    }
}

#[verifier(external_body)]
pub fn proc_push_child(
    proc_ptr: ProcPtr,
    proc_perm: &mut Tracked<PointsTo<Process>>,
    new_proc_ptr: &ProcPtr,
) -> (ret: SLLIndex)
    requires
        old(proc_perm)@.is_init(),
        old(proc_perm)@.addr() == proc_ptr,
        old(proc_perm)@.value().children.wf(),
        old(proc_perm)@.value().children.unique(),
        old(proc_perm)@.value().children.len() < MAX_NUM_THREADS_PER_PROC,
        old(proc_perm)@.value().children@.contains(*new_proc_ptr) == false,
    ensures
        proc_perm@.is_init(),
        proc_perm@.addr() == proc_ptr,
        proc_perm@.value().owning_container =~= old(proc_perm)@.value().owning_container,
        proc_perm@.value().rev_ptr =~= old(proc_perm)@.value().rev_ptr,
        proc_perm@.value().pcid =~= old(proc_perm)@.value().pcid,
        proc_perm@.value().ioid =~= old(proc_perm)@.value().ioid,
        proc_perm@.value().owned_threads =~= old(proc_perm)@.value().owned_threads,
        proc_perm@.value().parent =~= old(proc_perm)@.value().parent,
        proc_perm@.value().parent_rev_ptr =~= old(proc_perm)@.value().parent_rev_ptr,
        // proc_perm@.value().children =~= old(proc_perm)@.value().children,
        proc_perm@.value().uppertree_seq =~= old(proc_perm)@.value().uppertree_seq,
        proc_perm@.value().subtree_set =~= old(proc_perm)@.value().subtree_set,
        proc_perm@.value().depth =~= old(proc_perm)@.value().depth,
        proc_perm@.value().dmd_paging_mode =~= old(proc_perm)@.value().dmd_paging_mode,
        proc_perm@.value().children.wf(),
        proc_perm@.value().children@ =~= old(proc_perm)@.value().children@.push(*new_proc_ptr),
        proc_perm@.value().children.len() == old(proc_perm)@.value().children.len() + 1,
         forall|v:ProcPtr|
            #![auto]
            old(proc_perm)@.value().children@.contains(v) ==> 
                old(proc_perm)@.value().children.get_node_ref(v) == 
                    proc_perm@.value().children.get_node_ref(v),
        proc_perm@.value().children.get_node_ref(*new_proc_ptr) == ret,
        proc_perm@.value().children.unique(),
{
    unsafe {
        let uptr = proc_ptr as *mut MaybeUninit<Process>;
        let ret = (*uptr).assume_init_mut().children.push(new_proc_ptr);
        return ret;
    }
}

#[verifier(external_body)]
pub fn proc_remove_child(
    proc_ptr: ProcPtr,
    proc_perm: &mut Tracked<PointsTo<Process>>,
    rev_ptr: SLLIndex,
    child_proc_ptr: Ghost<ProcPtr>,
) -> (ret: ProcPtr)
    requires
        old(proc_perm)@.is_init(),
        old(proc_perm)@.addr() == proc_ptr,
        old(proc_perm)@.value().children.wf(),
        old(proc_perm)@.value().children.unique(),
        old(proc_perm)@.value().children@.contains(child_proc_ptr@),
    ensures
        proc_perm@.is_init(),
        proc_perm@.addr() == proc_ptr,
        proc_perm@.value().owning_container =~= old(proc_perm)@.value().owning_container,
        proc_perm@.value().rev_ptr =~= old(proc_perm)@.value().rev_ptr,
        proc_perm@.value().pcid =~= old(proc_perm)@.value().pcid,
        proc_perm@.value().ioid =~= old(proc_perm)@.value().ioid,
        proc_perm@.value().owned_threads =~= old(proc_perm)@.value().owned_threads,
        proc_perm@.value().parent =~= old(proc_perm)@.value().parent,
        proc_perm@.value().parent_rev_ptr =~= old(proc_perm)@.value().parent_rev_ptr,
        // proc_perm@.value().children =~= old(proc_perm)@.value().children,
        proc_perm@.value().uppertree_seq =~= old(proc_perm)@.value().uppertree_seq,
        proc_perm@.value().subtree_set =~= old(proc_perm)@.value().subtree_set,
        proc_perm@.value().depth =~= old(proc_perm)@.value().depth,
        proc_perm@.value().dmd_paging_mode =~= old(proc_perm)@.value().dmd_paging_mode,
        proc_perm@.value().children.wf(),
        proc_perm@.value().children@ =~= old(proc_perm)@.value().children@.remove_value(child_proc_ptr@),
        proc_perm@.value().children.len() == old(proc_perm)@.value().children.len() - 1,
         forall|v:ProcPtr|
            #![auto]
            proc_perm@.value().children@.contains(v) ==> 
                old(proc_perm)@.value().children.get_node_ref(v) == 
                    proc_perm@.value().children.get_node_ref(v),
        proc_perm@.value().children.unique(),
{
    unsafe {
        let uptr = proc_ptr as *mut MaybeUninit<Process>;
        let ret = (*uptr).assume_init_mut().children.remove(rev_ptr, child_proc_ptr);
        return ret;
    }
}


#[verifier(external_body)]
pub fn page_to_proc(
    page_ptr: PagePtr,
    page_perm: Tracked<PagePerm4k>,
    owning_container: ContainerPtr,
    rev_ptr: SLLIndex,
    pcid: Pcid,
    ioid: Option<IOid>,
    parent: Option<ProcPtr>,
    parent_rev_ptr: Option<SLLIndex>,
    uppertree_seq: Ghost<Seq<ProcPtr>>,
    subtree_set: Ghost<Set<ProcPtr>>,
    depth: usize,
) -> (ret: (ProcPtr, Tracked<PointsTo<Process>>))
    requires
        page_perm@.is_init(),
        page_perm@.addr() == page_ptr,
    ensures
        ret.0 == page_ptr,
        ret.1@.is_init(),
        ret.1@.addr() == ret.0,
        ret.1@.value().owning_container == owning_container,
        ret.1@.value().rev_ptr == rev_ptr,
        ret.1@.value().pcid == pcid,
        ret.1@.value().ioid == ioid,
        ret.1@.value().owned_threads.wf(),
        ret.1@.value().owned_threads@ == Seq::<ThreadPtr>::empty(),
        ret.1@.value().owned_threads.len() == 0,
        ret.1@.value().parent == parent,
        ret.1@.value().children.wf(),
        ret.1@.value().children@ =~= Seq::empty(),
        ret.1@.value().parent_rev_ptr == parent_rev_ptr,
        ret.1@.value().uppertree_seq == uppertree_seq,
        ret.1@.value().subtree_set == subtree_set,
        ret.1@.value().depth == depth,
        ret.1@.value().dmd_paging_mode == DemandPagingMode::NoDMDPG,
{
    unsafe {
        let uptr = page_ptr as *mut MaybeUninit<Process>;
        (*uptr).assume_init_mut().owning_container = owning_container;
        (*uptr).assume_init_mut().rev_ptr = rev_ptr;
        (*uptr).assume_init_mut().pcid = pcid;
        (*uptr).assume_init_mut().ioid = ioid;
        (*uptr).assume_init_mut().owned_threads.init();
        (*uptr).assume_init_mut().children.init();
        (*uptr).assume_init_mut().parent = parent;
        (*uptr).assume_init_mut().parent_rev_ptr = parent_rev_ptr;
        (*uptr).assume_init_mut().depth = depth;
        (*uptr).assume_init_mut().dmd_paging_mode = DemandPagingMode::NoDMDPG;
        (page_ptr, Tracked::assume_new())
    }
}

#[verifier(external_body)]
pub fn proc_to_page(
    proc_ptr: ProcPtr,
    proc_perm: Tracked<PointsTo<Process>>,
) -> (ret: (PagePtr, Tracked<PagePerm4k>))
    requires
        proc_perm@.is_init(),
        proc_perm@.addr() == proc_ptr,
    ensures
        ret.0 == proc_ptr,
        ret.1@.is_init(),
        ret.1@.addr() == ret.0,
{
    (proc_ptr, Tracked::assume_new())
}

pub fn page_to_proc_with_first_thread(
    page_ptr: PagePtr,
    page_perm: Tracked<PagePerm4k>,
    owning_container: ContainerPtr,
    rev_ptr: SLLIndex,
    pcid: Pcid,
    ioid: Option<IOid>,
    first_thread: ThreadPtr,
    parent: Option<ProcPtr>,
    parent_rev_ptr: Option<SLLIndex>,
    uppertree_seq: Ghost<Seq<ProcPtr>>,
    subtree_set: Ghost<Set<ProcPtr>>,
    depth: usize,
) -> (ret: (ProcPtr, Tracked<PointsTo<Process>>, SLLIndex))
    requires
        page_perm@.is_init(),
        page_perm@.addr() == page_ptr,
    ensures
        ret.0 == page_ptr,
        ret.1@.is_init(),
        ret.1@.addr() == ret.0,
        ret.1@.value().owning_container == owning_container,
        ret.1@.value().rev_ptr == rev_ptr,
        ret.1@.value().pcid == pcid,
        ret.1@.value().ioid == ioid,
        ret.1@.value().owned_threads.wf(),
        ret.1@.value().owned_threads@ == Seq::<ThreadPtr>::empty().push(first_thread),
        ret.1@.value().owned_threads.len() == 1,
        ret.1@.value().owned_threads.get_node_ref(first_thread) == ret.2,
        ret.1@.value().parent == parent,
        ret.1@.value().children.wf(),
        ret.1@.value().children@ =~= Seq::empty(),
        ret.1@.value().parent_rev_ptr == parent_rev_ptr,
        ret.1@.value().uppertree_seq == uppertree_seq,
        ret.1@.value().subtree_set == subtree_set,
        ret.1@.value().depth == depth,
        ret.1@.value().dmd_paging_mode == DemandPagingMode::NoDMDPG,
{
    let (p_ptr, mut p_perm) = page_to_proc(
        page_ptr,
        page_perm,
        owning_container,
        rev_ptr,
        pcid,
        ioid,
        parent,
        parent_rev_ptr,
        uppertree_seq,
        subtree_set,
        depth,
    );
    let sll = proc_push_thread(p_ptr, &mut p_perm, &first_thread);

    (p_ptr, p_perm, sll)
}

#[verifier(external_body)]
pub fn proc_perms_update_subtree_set(
    perms: &mut Tracked<Map<ProcPtr, PointsTo<Process>>>,
    uppertree_seq: Ghost<Seq<ProcPtr>>,
    new_proc_ptr: ProcPtr,
)
    ensures
        old(perms)@.dom() =~= perms@.dom(),
        forall|p_ptr: ProcPtr|
            #![trigger uppertree_seq@.contains(p_ptr)]
            #![trigger perms@.dom().contains(p_ptr)]
            #![trigger perms@[p_ptr]]
            perms@.dom().contains(p_ptr) && uppertree_seq@.contains(p_ptr) == false
                ==> perms@[p_ptr] =~= old(perms)@[p_ptr],
        forall|p_ptr: ProcPtr|
         // #![trigger perms@[p_ptr].value().owning_container]

            #![trigger perms@.dom().contains(p_ptr)]
            #![trigger perms@[p_ptr]]
            perms@.dom().contains(p_ptr) ==> perms@[p_ptr].is_init() =~= old(
                perms,
            )@[p_ptr].is_init() && perms@[p_ptr].addr() =~= old(perms)@[p_ptr].addr()
                && perms@[p_ptr].value().owning_container =~= old(
                perms,
            )@[p_ptr].value().owning_container && perms@[p_ptr].value().rev_ptr =~= old(
                perms,
            )@[p_ptr].value().rev_ptr && perms@[p_ptr].value().pcid =~= old(
                perms,
            )@[p_ptr].value().pcid && perms@[p_ptr].value().ioid =~= old(perms)@[p_ptr].value().ioid
                && perms@[p_ptr].value().owned_threads =~= old(perms)@[p_ptr].value().owned_threads
                && perms@[p_ptr].value().parent =~= old(perms)@[p_ptr].value().parent
                && perms@[p_ptr].value().parent_rev_ptr =~= old(
                perms,
            )@[p_ptr].value().parent_rev_ptr && perms@[p_ptr].value().children =~= old(
                perms,
            )@[p_ptr].value().children && perms@[p_ptr].value().uppertree_seq =~= old(
                perms,
            )@[p_ptr].value().uppertree_seq && perms@[p_ptr].value().depth =~= old(
                perms,
            )@[p_ptr].value().depth && perms@[p_ptr].value().dmd_paging_mode =~= old(
                perms,
            )@[p_ptr].value().dmd_paging_mode,
        forall|p_ptr: ProcPtr|
            #![trigger uppertree_seq@.contains(p_ptr)]
            #![trigger perms@[p_ptr].value().subtree_set]
            #![trigger old(perms)@[p_ptr].value().subtree_set]
            uppertree_seq@.contains(p_ptr) ==> perms@[p_ptr].value().subtree_set@ =~= old(
                perms,
            )@[p_ptr].value().subtree_set@.insert(new_proc_ptr),
        perms@[new_proc_ptr].value().subtree_set =~= old(perms)@[new_proc_ptr].value().subtree_set,
{
}

#[verifier(external_body)]
pub fn proc_perms_remove_subtree_set(
    perms: &mut Tracked<Map<ProcPtr, PointsTo<Process>>>,
    uppertree_seq: Ghost<Seq<ProcPtr>>,
    proc_ptr: ProcPtr,
)
    ensures
        old(perms)@.dom() =~= perms@.dom(),
        forall|p_ptr: ProcPtr|
            #![trigger uppertree_seq@.contains(p_ptr)]
            #![trigger perms@.dom().contains(p_ptr)]
            #![trigger perms@[p_ptr]]
            perms@.dom().contains(p_ptr) && uppertree_seq@.contains(p_ptr) == false
                ==> perms@[p_ptr] =~= old(perms)@[p_ptr],
        forall|p_ptr: ProcPtr|
            #![trigger perms@.dom().contains(p_ptr)]
            #![trigger perms@[p_ptr]]
            perms@.dom().contains(p_ptr) 
            ==> perms@[p_ptr].is_init() =~= old(
                perms,
            )@[p_ptr].is_init() && perms@[p_ptr].addr() =~= old(perms)@[p_ptr].addr()
                && perms@[p_ptr].value().owning_container =~= old(
                perms,
            )@[p_ptr].value().owning_container && perms@[p_ptr].value().rev_ptr =~= old(
                perms,
            )@[p_ptr].value().rev_ptr && perms@[p_ptr].value().pcid =~= old(
                perms,
            )@[p_ptr].value().pcid && perms@[p_ptr].value().ioid =~= old(perms)@[p_ptr].value().ioid
                && perms@[p_ptr].value().owned_threads =~= old(perms)@[p_ptr].value().owned_threads
                && perms@[p_ptr].value().parent =~= old(perms)@[p_ptr].value().parent
                && perms@[p_ptr].value().parent_rev_ptr =~= old(
                perms,
            )@[p_ptr].value().parent_rev_ptr && perms@[p_ptr].value().children =~= old(
                perms,
            )@[p_ptr].value().children && perms@[p_ptr].value().uppertree_seq =~= old(
                perms,
            )@[p_ptr].value().uppertree_seq && perms@[p_ptr].value().depth =~= old(
                perms,
            )@[p_ptr].value().depth && perms@[p_ptr].value().dmd_paging_mode =~= old(
                perms,
            )@[p_ptr].value().dmd_paging_mode,
        forall|p_ptr: ProcPtr|
            #![trigger uppertree_seq@.contains(p_ptr)]
            #![trigger perms@[p_ptr].value()]
            #![trigger perms@[p_ptr].value().subtree_set]
            #![trigger old(perms)@[p_ptr].value().subtree_set]
            uppertree_seq@.contains(p_ptr) ==> perms@[p_ptr].value().subtree_set@ =~= 
            old(perms)@[p_ptr].value().subtree_set@.remove(proc_ptr),
{
}

} // verus!

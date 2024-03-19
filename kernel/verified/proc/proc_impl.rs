use super::*;

// use core::mem::MaybeUninit;

use vstd::prelude::*;
verus! {
use vstd::ptr::*;

// use crate::mars_staticlinkedlist::*;

// use crate::setters::*;
use crate::define::*;
// use vstd::set_lib::lemma_set_properties;
// use vstd::seq_lib::lemma_seq_properties;

// use crate::proc::*;


impl ProcessManager {
    pub fn new_proc(&mut self, page_ptr: PagePtr, page_perm: Tracked<PagePerm>, new_pcid: Pcid, new_ioid: Option<IOid>) -> (ret: ProcPtr)
        requires
            old(self).wf(),
            page_perm@@.pptr == page_ptr,
            page_perm@@.value.is_Some(),
            old(self).get_proc_ptrs().len() < MAX_NUM_PROCS,
            old(self).get_proc_man_page_closure().contains(page_ptr) == false,
            old(self).get_pcid_closure().contains(new_pcid) == false,
            0<=new_pcid<PCID_MAX,
            new_ioid.is_Some() ==> old(self).get_ioid_closure().contains(new_ioid.get_Some_0()) == false,
            new_ioid.is_Some() ==> 0 <= new_ioid.unwrap() < IOID_MAX,
        ensures
            self.wf(),
            self.scheduler =~= old(self).scheduler,
            self.get_pcid_closure() =~= old(self).get_pcid_closure().insert(new_pcid),
            new_ioid.is_Some() ==> self.get_ioid_closure() =~= old(self).get_ioid_closure().insert(new_ioid.get_Some_0()),
            new_ioid.is_None() ==> self.get_ioid_closure() =~= old(self).get_ioid_closure(),
            self.get_proc_man_page_closure() =~= old(self).get_proc_man_page_closure().insert(page_ptr),
            self.get_proc_ptrs() =~= old(self).get_proc_ptrs().push(ret),
            self.get_proc_ptrs().contains(ret),
            self.get_proc(ret).pcid == new_pcid,
            self.get_proc_man_page_closure() =~= old(self).get_proc_man_page_closure().insert(ret),
            self.get_thread_ptrs() =~= old(self).get_thread_ptrs(),
            self.get_endpoint_ptrs() =~= old(self).get_endpoint_ptrs(),
            self.proc_perms@[ret]@.value.get_Some_0().owned_threads.len() == 0,
            forall|proc_ptr:ProcPtr|#![auto] old(self).get_proc_ptrs().contains(proc_ptr) ==> self.get_proc(proc_ptr) =~= old(self).get_proc(proc_ptr),
            forall|thread_ptr:ThreadPtr|#![auto] self.get_thread_ptrs().contains(thread_ptr) ==> self.get_thread(thread_ptr) =~= old(self).get_thread(thread_ptr),
            forall|endpoint_ptr:EndpointPtr|#![auto] self.get_endpoint_ptrs().contains(endpoint_ptr) ==> self.get_endpoint(endpoint_ptr) =~= old(self).get_endpoint(endpoint_ptr),
    {
        assert(forall|_endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(_endpoint_ptr)
    ==>  (forall|_thread_ptr:ThreadPtr| #![auto] self.endpoint_perms@[_endpoint_ptr]@.value.get_Some_0().queue@.contains(_thread_ptr)
        ==> (
            (self.thread_perms@.dom().contains(_thread_ptr))
            &&
            (self.thread_perms@[_thread_ptr]@.value.get_Some_0().state == BLOCKED)
            &&
            (self.thread_perms@[_thread_ptr]@.value.get_Some_0().endpoint_ptr.unwrap() == _endpoint_ptr)
        )
));
        assert(self.proc_ptrs@.contains(page_ptr) == false);
        let ret = page_ptr;
        let (proc_pptr,mut proc_perm) = page_to_proc((PPtr::<[u8; PAGE_SZ]>::from_usize(page_ptr),page_perm));

        let proc_ptr = proc_pptr.to_usize();

        proc_perm_init(PPtr::<Process>::from_usize(proc_ptr),  &mut proc_perm);
        assert(proc_perm@@.value.get_Some_0().owned_threads.wf());

        assert(self.proc_ptrs.wf());
        assert(self.proc_ptrs.size == MAX_NUM_PROCS);

        let pl_rf = self.proc_ptrs.push(ret);

        proc_set_pl_rf(PPtr::<Process>::from_usize(proc_ptr),  &mut proc_perm, pl_rf);
        proc_set_pcid(PPtr::<Process>::from_usize(proc_ptr),  &mut proc_perm, new_pcid);
        if new_ioid.is_none(){
            proc_set_ioid(PPtr::<Process>::from_usize(proc_ptr),  &mut proc_perm, None);
        }else{
            proc_set_ioid(PPtr::<Process>::from_usize(proc_ptr),  &mut proc_perm, new_ioid);
            proof{
                self.ioid_closure@ = self.ioid_closure@.insert(new_ioid.get_Some_0());
            }
        }


        assert(self.proc_perms@.dom().contains(ret) == false);
        proof{
            (self.proc_perms.borrow_mut())
                .tracked_insert(ret, proc_perm.get());
        }

        proof{
            self.pcid_closure@ = self.pcid_closure@.insert(new_pcid);}

        assert(self.wf_threads());
        assert(self.wf_procs());
        assert(self.wf_scheduler());
        assert(self.wf_mem_closure());
        assert(self.wf_pcid_closure());
        assert(self.wf_ipc());
        assert(self.wf_ioid_closure());
        assert(self.endpoint_ptrs@ =~= self.endpoint_perms@.dom());
        assert(self.endpoint_perms@.dom().contains(0) == false);
        assert(self.wf_endpoints());
        assert(self.wf());

        return ret;
    }

    pub fn free_proc(&mut self, proc_ptr: ProcPtr) -> (ret: (PagePPtr,Tracked<PagePerm>))
        requires
            old(self).wf(),
            old(self).get_proc_ptrs().contains(proc_ptr),
            old(self).get_proc(proc_ptr).owned_threads.len() == 0,
    {
        assert(self.proc_perms@.dom().contains(proc_ptr));
        let tracked mut proc_perm =
            (self.proc_perms.borrow_mut()).tracked_remove(proc_ptr);
        let pl_rf = PPtr::<Process>::from_usize(proc_ptr).borrow(Tracked(&proc_perm)).pl_rf;
        let pcid = PPtr::<Process>::from_usize(proc_ptr).borrow(Tracked(&proc_perm)).pcid;
        let ioid = PPtr::<Process>::from_usize(proc_ptr).borrow(Tracked(&proc_perm)).ioid;
        let removed_proc_ptr = self.proc_ptrs.remove(pl_rf);
        assert(removed_proc_ptr == proc_ptr);
        proof{
            self.pcid_closure@ = self.pcid_closure@.remove(pcid);
        }
        if ioid.is_some(){
            proof {self.ioid_closure@ = self.ioid_closure@.remove(ioid.unwrap()); }
        }
        assert(self.wf_threads());
        assert(self.wf_procs());
        assert(self.wf_scheduler());
        assert(self.wf_mem_closure());
        assert(self.wf_pcid_closure());
        assert(self.wf_ioid_closure());
        assert(self.wf());

        return proc_to_page((PPtr::<Process>::from_usize(proc_ptr), Tracked(proc_perm)));
    }
}
}

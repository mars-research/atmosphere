use super::*;

use vstd::prelude::*;
verus! {
use vstd::ptr::*;

use crate::define::*;
use crate::trap::*;



impl ProcessManager {

    // pub fn push_scheduler_with_error_code(&mut self, thread_ptr: ThreadPtr, error_code: Option<ErrorCodeType>, pt_regs: PtRegs)
    //     requires
    //         old(self).wf(),
    //         old(self).scheduler.len() < MAX_NUM_THREADS,
    //         old(self).get_thread_ptrs().contains(thread_ptr),
    //         old(self).get_thread(thread_ptr).state != SCHEDULED,
    //         old(self).get_thread(thread_ptr).state != BLOCKED,
    //         old(self).get_thread(thread_ptr).state != CALLING,
    //     ensures
    //         self.wf(),
    //         forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) == old(self).get_thread_ptrs().contains(_thread_ptr),
    //         forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != thread_ptr ==> self.get_thread(_thread_ptr) =~= old(self).get_thread(_thread_ptr),
    //         forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != thread_ptr ==> self.get_thread(_thread_ptr).state =~= old(self).get_thread(_thread_ptr).state,
    //         self.get_thread(thread_ptr).state == SCHEDULED,
    //         self.scheduler.len() == old(self).scheduler.len() + 1,
    //         self.proc_ptrs =~= old(self).proc_ptrs,
    //         self.proc_perms =~= old(self).proc_perms,
    //         self.thread_ptrs =~= old(self).thread_ptrs,
    //         //self.thread_perms=@ =~= old(self).thread_perms@,
    //         self.endpoint_ptrs =~= old(self).endpoint_ptrs,
    //         self.endpoint_perms =~= old(self).endpoint_perms,
    //         self.pcid_closure =~= old(self).pcid_closure,
    //         self.ioid_closure =~= old(self).ioid_closure,
    //         self.get_thread(thread_ptr).parent =~= old(self).get_thread(thread_ptr).parent,
    //         //self.get_thread(thread_ptr).state =~= old(self).get_thread(thread_ptr).state,
    //         self.get_thread(thread_ptr).parent_rf =~= old(self).get_thread(thread_ptr).parent_rf,
    //         // self.get_thread(thread_ptr).scheduler_rf =~= old(self).get_thread(thread_ptr).scheduler_rf,
    //         self.get_thread(thread_ptr).endpoint_ptr =~= old(self).get_thread(thread_ptr).endpoint_ptr,
    //         self.get_thread(thread_ptr).endpoint_rf =~= old(self).get_thread(thread_ptr).endpoint_rf,
    //         self.get_thread(thread_ptr).endpoint_descriptors =~= old(self).get_thread(thread_ptr).endpoint_descriptors,
    //         self.get_thread(thread_ptr).ipc_payload =~= old(self).get_thread(thread_ptr).ipc_payload,
    //         self.get_thread(thread_ptr).error_code =~= error_code,
    //         // self.get_thread(thread_ptr).trap_frame =~= pt_regs,
    // {

    //     let ret = self.scheduler.push(thread_ptr);
    //     let thread_pptr = PPtr::<Thread>::from_usize(thread_ptr);
    //     let mut thread_perm =
    //         Tracked((self.thread_perms.borrow_mut()).tracked_remove(thread_ptr));
    //     thread_set_scheduler_rf(&thread_pptr, &mut thread_perm, Some(ret));
    //     thread_set_state(&thread_pptr,&mut thread_perm, SCHEDULED);
    //     thread_set_error_code(&thread_pptr,&mut thread_perm, error_code);
    //     thread_set_trap_frame(&thread_pptr,&mut thread_perm, Some(pt_regs));
    //     proof{
    //         assert(self.thread_perms@.dom().contains(thread_ptr) == false);
    //         (self.thread_perms.borrow_mut())
    //             .tracked_insert(thread_ptr, thread_perm.get());
    //     }

    //     assert(self.wf_threads());
    //     assert(self.wf_procs());
    //     assert(self.wf_scheduler());
    //     assert(self.wf_mem_closure());
    //     assert(self.wf_pcid_closure());
    //     assert(self.wf_ipc());
    // }

    // pub fn pop_scheduler_with_error_code(&mut self) -> (ret: (ThreadPtr,Option<ErrorCodeType>))
    //     requires
    //         old(self).wf(),
    //         old(self).scheduler.len() > 0,
    //     ensures
    //         self.wf(),
    //         self.get_thread_ptrs().contains(ret.0),
    //         self.scheduler@.contains(ret.0) == false,
    //         old(self).get_thread(ret.0).state == SCHEDULED,
    //         self.get_pcid_closure() =~= old(self).get_pcid_closure(),
    //         self.get_ioid_closure() =~= old(self).get_ioid_closure(),
    //         forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) == old(self).get_thread_ptrs().contains(_thread_ptr),
    //         forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != ret.0 ==> self.get_thread(_thread_ptr) =~= old(self).get_thread(_thread_ptr),
    //         forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != ret.0 ==> self.get_thread(_thread_ptr).state =~= old(self).get_thread(_thread_ptr).state,
    //         self.get_thread(ret.0).state == RUNNING,
    //         self.get_thread(ret.0).parent == old(self).get_thread(ret.0).parent,
    //         //self.get_thread(ret.0).state == old(self).get_thread(ret.0).state,
    //         self.get_thread(ret.0).parent_rf == old(self).get_thread(ret.0).parent_rf,
    //         self.get_thread(ret.0).scheduler_rf == old(self).get_thread(ret.0).scheduler_rf,
    //         self.get_thread(ret.0).endpoint_rf == old(self).get_thread(ret.0).endpoint_rf,
    //         self.get_thread(ret.0).endpoint_descriptors == old(self).get_thread(ret.0).endpoint_descriptors,
    //         self.get_thread(ret.0).parent_rf == old(self).get_thread(ret.0).parent_rf,
    //         ret.0 == old(self).scheduler@[0],
    //         self.get_proc_man_page_closure() =~= old(self).get_proc_man_page_closure(),
    //         self.scheduler.len() == old(self).scheduler.len() - 1,
    //         self.get_thread_ptrs().contains(ret.0),
    //         ret.1 =~= self.get_thread(ret.0).error_code,
    // {
    //     let ret = self.scheduler.pop();
    //     let thread_pptr = PPtr::<Thread>::from_usize(ret);
    //     let mut thread_perm =
    //         Tracked((self.thread_perms.borrow_mut()).tracked_remove(ret));
    //     thread_set_state(&thread_pptr, &mut thread_perm, RUNNING);
    //     proof{
    //         assert(self.thread_perms@.dom().contains(ret) == false);
    //         (self.thread_perms.borrow_mut())
    //             .tracked_insert(ret, thread_perm.get());
    //     }
    //     assert(old(self).scheduler@[0] == ret);
    //     assert(old(self).scheduler@.contains(ret));
    //     assert(self.thread_perms@.dom().contains(ret));


    //     assert(self.wf_threads());
    //     assert(self.wf_procs());
    //     assert(self.wf_scheduler());
    //     assert(self.wf_mem_closure());
    //     assert(self.wf_pcid_closure());
    //     let error_code = self.get_error_code_by_thread_ptr(ret);
    //     return (ret,error_code);
    // }

    pub fn push_scheduler(&mut self, thread_ptr: ThreadPtr, error_code: Option<ErrorCodeType>, pt_regs: PtRegs)
        requires
            old(self).wf(),
            old(self).scheduler.len() < MAX_NUM_THREADS,
            old(self).get_thread_ptrs().contains(thread_ptr),
            old(self).get_thread(thread_ptr).state != SCHEDULED,
            old(self).get_thread(thread_ptr).state != BLOCKED,
            old(self).get_thread(thread_ptr).state != CALLING,
        ensures
            self.wf(),
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) == old(self).get_thread_ptrs().contains(_thread_ptr),
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != thread_ptr ==> self.get_thread(_thread_ptr) =~= old(self).get_thread(_thread_ptr),
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != thread_ptr ==> self.get_thread(_thread_ptr).state =~= old(self).get_thread(_thread_ptr).state,
            self.get_thread(thread_ptr).state == SCHEDULED,
            self.scheduler.len() == old(self).scheduler.len() + 1,
            self.proc_ptrs =~= old(self).proc_ptrs,
            self.proc_perms =~= old(self).proc_perms,
            self.thread_ptrs =~= old(self).thread_ptrs,
            //self.thread_perms=@ =~= old(self).thread_perms@,
            self.endpoint_ptrs =~= old(self).endpoint_ptrs,
            self.endpoint_perms =~= old(self).endpoint_perms,
            self.pcid_closure =~= old(self).pcid_closure,
            self.ioid_closure =~= old(self).ioid_closure,
            self.get_thread(thread_ptr).parent =~= old(self).get_thread(thread_ptr).parent,
            //self.get_thread(thread_ptr).state =~= old(self).get_thread(thread_ptr).state,
            self.get_thread(thread_ptr).parent_rf =~= old(self).get_thread(thread_ptr).parent_rf,
            // self.get_thread(thread_ptr).scheduler_rf =~= old(self).get_thread(thread_ptr).scheduler_rf,
            self.get_thread(thread_ptr).endpoint_ptr =~= old(self).get_thread(thread_ptr).endpoint_ptr,
            self.get_thread(thread_ptr).endpoint_rf =~= old(self).get_thread(thread_ptr).endpoint_rf,
            self.get_thread(thread_ptr).endpoint_descriptors =~= old(self).get_thread(thread_ptr).endpoint_descriptors,
            self.get_thread(thread_ptr).ipc_payload =~= old(self).get_thread(thread_ptr).ipc_payload,
            self.get_thread(thread_ptr).error_code =~= error_code,
            self.scheduler@ =~= old(self).scheduler@.push(thread_ptr),
    {

        let ret = self.scheduler.push(thread_ptr);
        let thread_pptr = PPtr::<Thread>::from_usize(thread_ptr);
        let mut thread_perm =
            Tracked((self.thread_perms.borrow_mut()).tracked_remove(thread_ptr));
        thread_set_scheduler_rf(&thread_pptr, &mut thread_perm, Some(ret));
        thread_set_state(&thread_pptr,&mut thread_perm, SCHEDULED);
        thread_set_trap_frame(&thread_pptr,&mut thread_perm, Some(pt_regs));
        thread_set_error_code(&thread_pptr,&mut thread_perm, error_code);
        proof{
            assert(self.thread_perms@.dom().contains(thread_ptr) == false);
            (self.thread_perms.borrow_mut())
                .tracked_insert(thread_ptr, thread_perm.get());
        }

        assert(self.wf_threads());
        assert(self.wf_procs());
        assert(self.wf_scheduler());
        assert(self.wf_mem_closure());
        assert(self.wf_pcid_closure());
        assert(self.wf_ipc());
    }

    pub fn pop_scheduler(&mut self) -> (ret: (ThreadPtr, PtRegs, Option<ErrorCodeType>))
        requires
            old(self).wf(),
            old(self).scheduler.len() > 0,
        ensures
            self.wf(),
            self.get_thread_ptrs().contains(ret.0),
            self.scheduler@.contains(ret.0) == false,
            old(self).get_thread(ret.0).state == SCHEDULED,
            self.get_pcid_closure() =~= old(self).get_pcid_closure(),
            self.get_ioid_closure() =~= old(self).get_ioid_closure(),
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) == old(self).get_thread_ptrs().contains(_thread_ptr),
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != ret.0 ==> self.get_thread(_thread_ptr) =~= old(self).get_thread(_thread_ptr),
            forall|_thread_ptr:ThreadPtr| #![auto] self.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != ret.0 ==> self.get_thread(_thread_ptr).state =~= old(self).get_thread(_thread_ptr).state,
            self.get_thread(ret.0).state == RUNNING,
            self.get_thread(ret.0).parent == old(self).get_thread(ret.0).parent,
            //self.get_thread(ret.0).state == old(self).get_thread(ret.0).state,
            self.get_thread(ret.0).parent_rf == old(self).get_thread(ret.0).parent_rf,
            self.get_thread(ret.0).scheduler_rf == old(self).get_thread(ret.0).scheduler_rf,
            self.get_thread(ret.0).endpoint_rf == old(self).get_thread(ret.0).endpoint_rf,
            self.get_thread(ret.0).endpoint_descriptors == old(self).get_thread(ret.0).endpoint_descriptors,
            self.get_thread(ret.0).parent_rf == old(self).get_thread(ret.0).parent_rf,
            ret.0 == old(self).scheduler@[0],
            self.get_proc_man_page_closure() =~= old(self).get_proc_man_page_closure(),
            self.scheduler.len() == old(self).scheduler.len() - 1,
            self.get_thread_ptrs().contains(ret.0),
            self.scheduler@ =~= old(self).scheduler@.subrange(1,old(self).scheduler.len() as int),
    {
        let tmp_thread_ptr = self.scheduler.get_head();
        assert(self.scheduler@.contains(tmp_thread_ptr));
        assert(self.get_thread_ptrs().contains(tmp_thread_ptr));
        let thread_pt_regs = self.get_pt_regs_by_thread_ptr(tmp_thread_ptr).unwrap();
        let thread_error_code = self.get_error_code_by_thread_ptr(tmp_thread_ptr);
        let thread_ptr = self.scheduler.pop();
        let thread_pptr = PPtr::<Thread>::from_usize(thread_ptr);
        let mut thread_perm =
            Tracked((self.thread_perms.borrow_mut()).tracked_remove(thread_ptr));
        thread_set_state(&thread_pptr, &mut thread_perm, RUNNING);
        thread_set_trap_frame(&thread_pptr, &mut thread_perm, None);
        thread_set_error_code(&thread_pptr, &mut thread_perm, None);
        proof{
            assert(self.thread_perms@.dom().contains(thread_ptr) == false);
            (self.thread_perms.borrow_mut())
                .tracked_insert(thread_ptr, thread_perm.get());
        }
        assert(old(self).scheduler@[0] == thread_ptr);
        assert(old(self).scheduler@.contains(thread_ptr));
        assert(self.thread_perms@.dom().contains(thread_ptr));


        assert(self.wf_threads());
        assert(self.wf_procs());
        assert(self.wf_scheduler());
        assert(self.wf_mem_closure());
        assert(self.wf_pcid_closure());
        return (thread_ptr, thread_pt_regs, thread_error_code);
    }
    // pub fn free_thread_from_scheduler(&mut self, thread_ptr:ThreadPtr)
    //     requires
    //         old(self).wf(),
    //         old(self).get_thread_ptrs().contains(thread_ptr),
    //         old(self).get_thread(thread_ptr).state == SCHEDULED,
    // {
    //     assert(self.thread_perms@.dom().contains(thread_ptr));
    //     let tracked thread_perm = self.thread_perms.borrow().tracked_borrow(thread_ptr);
    //     let thread : &Thread = PPtr::<Thread>::from_usize(thread_ptr).borrow(Tracked(thread_perm));
    //     let parent_ptr = thread.parent;
    //     assert(self.get_proc_ptrs().contains(parent_ptr));
    //     assert(self.proc_perms@.dom().contains(parent_ptr));
    //     assert(self.get_proc(parent_ptr).owned_threads.wf());
    //     assert(self.get_proc(parent_ptr).owned_threads@.contains(thread_ptr));
    //     assert(self.scheduler.wf());
    //     assert(self.scheduler@.contains(thread_ptr));
    //     assert(thread.scheduler_rf.is_Some());
    //     self.scheduler.remove(thread.scheduler_rf.unwrap());
    //     assert(self.scheduler@.contains(thread_ptr) == false);

    //     // assert(self.proc_perms@.dom().contains(parent_ptr));
    //     // let mut proc_perm =
    //     //     Tracked((self.proc_perms.borrow_mut()).tracked_remove(parent_ptr));
    //     // proc_remove_thread(PPtr::<Process>::from_usize(parent_ptr), &mut proc_perm, thread.parent_rf);
    //     // assert(self.proc_perms@.dom().contains(parent_ptr) == false);
    //     // proof{
    //     //     (self.proc_perms.borrow_mut())
    //     //         .tracked_insert(parent_ptr, proc_perm.get());
    //     // }
    //     let mut thread_perm =
    //         Tracked((self.thread_perms.borrow_mut()).tracked_remove(thread_ptr));
    //     assert(self.thread_perms@.dom().contains(thread_ptr) == false);
    //     thread_set_state(&PPtr::<Thread>::from_usize(thread_ptr), &mut thread_perm, TRANSIT);
    //     proof{
    //         (self.thread_perms.borrow_mut())
    //             .tracked_insert(thread_ptr, thread_perm.get());
    //     }
    //     // proof{
    //     //     self.thread_ptrs@ = self.thread_ptrs@.remove(thread_ptr);
    //     // }
    //     assert(self.wf_threads());
    //     assert(self.wf_procs());
    //     assert(self.wf_scheduler());
    //     assert(self.wf_mem_closure());
    //     assert(self.wf_pcid_closure());
    //     assert(self.wf());
    // }
}
}

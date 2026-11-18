use vstd::prelude::*;
verus! {

use crate::define::*;
use crate::trap::*;
use crate::process_manager::thread::*;
use crate::process_manager::spec_proof::*;
use crate::process_manager::cpu::*;
use vstd::simple_pptr::PPtr;

// Timer preemption.
//
// The run-queue functions in impl_base.rs save and restore only the registers that a syscall
// preserves. The two functions here handle the saved context of a thread that an interrupt took
// off the CPU. They change nothing but the trap frame of one thread.
impl ProcessManager {
    /// What the functions in this file leave alone: everything except the trap frame of `t_ptr`.
    pub open spec fn same_except_trap_frame(&self, prev: ProcessManager, t_ptr: ThreadPtr) -> bool {
        &&& self.root_container == prev.root_container
        &&& self.container_perms@ == prev.container_perms@
        &&& self.process_perms@ == prev.process_perms@
        &&& self.endpoint_perms@ == prev.endpoint_perms@
        &&& self.cpu_list == prev.cpu_list
        &&& self.thread_perms@.dom() == prev.thread_perms@.dom()
        &&& forall|t: ThreadPtr|
            #![trigger self.thread_perms@[t]]
            prev.thread_perms@.dom().contains(t) && t != t_ptr ==> self.thread_perms@[t]
                == prev.thread_perms@[t]
        &&& self.get_thread(t_ptr).owning_container == prev.get_thread(t_ptr).owning_container
        &&& self.get_thread(t_ptr).owning_proc == prev.get_thread(t_ptr).owning_proc
        &&& self.get_thread(t_ptr).state == prev.get_thread(t_ptr).state
        &&& self.get_thread(t_ptr).proc_rev_ptr == prev.get_thread(t_ptr).proc_rev_ptr
        &&& self.get_thread(t_ptr).scheduler_rev_ptr == prev.get_thread(t_ptr).scheduler_rev_ptr
        &&& self.get_thread(t_ptr).blocking_endpoint_ptr == prev.get_thread(
            t_ptr,
        ).blocking_endpoint_ptr
        &&& self.get_thread(t_ptr).blocking_endpoint_index == prev.get_thread(
            t_ptr,
        ).blocking_endpoint_index
        &&& self.get_thread(t_ptr).endpoint_rev_ptr == prev.get_thread(t_ptr).endpoint_rev_ptr
        &&& self.get_thread(t_ptr).running_cpu == prev.get_thread(t_ptr).running_cpu
        &&& self.get_thread(t_ptr).endpoint_descriptors == prev.get_thread(
            t_ptr,
        ).endpoint_descriptors
        &&& self.get_thread(t_ptr).ipc_payload == prev.get_thread(t_ptr).ipc_payload
        &&& self.get_thread(t_ptr).error_code == prev.get_thread(t_ptr).error_code
    }

    /// Saves the whole context of a thread that an interrupt took off the CPU.
    pub fn save_preempted_trap_frame(&mut self, t_ptr: ThreadPtr, pt_regs: &Registers)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(t_ptr),
        ensures
            self.wf(),
            self.same_except_trap_frame(*old(self), t_ptr),
            self.get_thread(t_ptr).trap_frame.is_Some(),
            self.get_thread(t_ptr).trap_frame.unwrap() == *pt_regs,
            self.get_thread(t_ptr).trap_frame.preempted,
    {
        broadcast use ProcessManager::reveal_process_manager_wf;

        let tracked mut t_perm = self.thread_perms.borrow_mut().tracked_remove(t_ptr);
        let t_pptr = PPtr::<Thread>::from_usize(t_ptr);
        let mut thread = t_pptr.take(Tracked(&mut t_perm));
        thread.trap_frame.set_self_preempted(pt_regs);
        t_pptr.put(Tracked(&mut t_perm), thread);
        proof {
            self.thread_perms.borrow_mut().tracked_insert(t_ptr, t_perm);
        }

        assert(self.same_except_trap_frame(*old(self), t_ptr));
        proof {
            self.same_except_trap_frame_imply_wf(*old(self), t_ptr);
        }
    }

    /// Hands back the whole context of a thread if an interrupt took the thread off the CPU.
    ///
    /// Returns whether it did. If so, `pt_regs` holds every register of the thread, and the saved
    /// context is no longer marked. Otherwise nothing changes: the thread entered the kernel
    /// through a syscall, and the fast restore of the run-queue functions is all it needs.
    pub fn take_preempted_trap_frame(&mut self, t_ptr: ThreadPtr, pt_regs: &mut Registers) -> (ret:
        bool)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(t_ptr),
        ensures
            self.wf(),
            self.same_except_trap_frame(*old(self), t_ptr),
            ret == old(self).get_thread(t_ptr).trap_frame.preempted,
            ret ==> *pt_regs == old(self).get_thread(t_ptr).trap_frame.reg,
            !ret ==> *pt_regs == *old(pt_regs),
            !self.get_thread(t_ptr).trap_frame.preempted,
            self.get_thread(t_ptr).trap_frame.exists == old(self).get_thread(
                t_ptr,
            ).trap_frame.exists,
            self.get_thread(t_ptr).trap_frame.reg == old(self).get_thread(t_ptr).trap_frame.reg,
    {
        broadcast use ProcessManager::reveal_process_manager_wf;

        if !self.get_thread(t_ptr).trap_frame.preempted {
            return false;
        }
        let tracked mut t_perm = self.thread_perms.borrow_mut().tracked_remove(t_ptr);
        let t_pptr = PPtr::<Thread>::from_usize(t_ptr);
        let mut thread = t_pptr.take(Tracked(&mut t_perm));
        *pt_regs = thread.trap_frame.reg;
        thread.trap_frame.clear_preempted();
        t_pptr.put(Tracked(&mut t_perm), thread);
        proof {
            self.thread_perms.borrow_mut().tracked_insert(t_ptr, t_perm);
        }

        assert(self.same_except_trap_frame(*old(self), t_ptr));
        proof {
            self.same_except_trap_frame_imply_wf(*old(self), t_ptr);
        }
        true
    }

    /// What the end of a time slice does when it switches threads: round-robin in the run queue of
    /// the container that owns the CPU. The thread that ran goes to the tail of the queue, and
    /// `next`, the thread that was at the head, runs.
    pub open spec fn preempt_spec(&self, prev: ProcessManager, cpu_id: CpuId, next: ThreadPtr) -> bool {
        let prev_thread = prev.get_cpu(cpu_id).current_thread.unwrap();
        let c_ptr = prev.get_cpu(cpu_id).owning_container;
        &&& prev.get_cpu(cpu_id).current_thread.is_Some()
        &&& prev.get_container(c_ptr).scheduler@.len() > 0
        &&& next == prev.get_container(c_ptr).scheduler@[0]
        &&& next != prev_thread
        &&& self.get_cpu(cpu_id).current_thread == Some(next)
        &&& self.get_cpu(cpu_id).owning_container == c_ptr
        &&& self.get_thread(next).state == ThreadState::RUNNING
        &&& self.get_thread(prev_thread).state == ThreadState::SCHEDULED
        &&& self.get_container(c_ptr).scheduler@ == prev.get_container(c_ptr).scheduler@.push(
            prev_thread,
        ).skip(1)
    }

    /// Ends the time slice of the thread that runs on `cpu_id`.
    ///
    /// Returns `None`, and changes nothing, if the CPU runs no thread, if no other thread of the
    /// container is runnable, or if the run queue has no room for the running thread. Otherwise
    /// switches threads as `preempt_spec` describes and returns the next thread and whether an
    /// interrupt took it off the CPU earlier. `pt_regs` is the interrupted context on entry and
    /// the context of the next thread on return: all of it if the next thread was preempted, and
    /// the registers that a syscall preserves, with the others cleared, if it was not.
    pub fn preempt_running_thread(&mut self, cpu_id: CpuId, pt_regs: &mut Registers) -> (ret: Option<
        (ThreadPtr, bool),
    >)
        requires
            old(self).wf(),
            0 <= cpu_id < NUM_CPUS,
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure(),
            self.proc_dom() =~= old(self).proc_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom(),
            forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
                    p_ptr,
                ),
            forall|e_ptr: EndpointPtr|
                #![trigger self.get_endpoint(e_ptr)]
                self.endpoint_dom().contains(e_ptr) ==> self.get_endpoint(e_ptr) =~= old(
                    self,
                ).get_endpoint(e_ptr),
            ret.is_None() ==> *self == *old(self) && *pt_regs == *old(pt_regs),
            ret.is_Some() ==> self.thread_dom().contains(ret.unwrap().0) && self.preempt_spec(
                *old(self),
                cpu_id,
                ret.unwrap().0,
            ),
    {
        broadcast use ProcessManager::reveal_process_manager_wf;

        let cpu = *self.cpu_list.get(cpu_id);
        if !cpu.active || cpu.current_thread.is_none() {
            return None;
        }
        let prev_thread = cpu.current_thread.unwrap();
        let c_ptr = cpu.owning_container;
        // A running thread is not in the run queue.
        assert(self.get_thread(prev_thread).owning_container == c_ptr);
        assert(self.get_thread(prev_thread).state == ThreadState::RUNNING);
        assert(!self.get_container(c_ptr).scheduler@.contains(prev_thread));

        let runnable = self.get_container(c_ptr).scheduler.len();
        if runnable == 0 || runnable >= MAX_CONTAINER_SCHEDULER_LEN {
            return None;
        }
        let ghost head = self.get_container(c_ptr).scheduler@[0];
        assert(self.get_container(c_ptr).scheduler@.contains(head));
        assert(head != prev_thread);

        // Running -> tail of the run queue, with the whole context saved.
        self.schedule_running_thread(cpu_id, pt_regs);
        self.save_preempted_trap_frame(prev_thread, pt_regs);

        // Head of the run queue -> running.
        let next_thread = self.pop_scheduler_for_idle_cpu(cpu_id, pt_regs);
        assert(next_thread == head);
        let preempted = self.take_preempted_trap_frame(next_thread, pt_regs);
        if !preempted {
            pt_regs.clear_caller_saved();
        }
        Some((next_thread, preempted))
    }

    /// No invariant of the process manager reads a trap frame.
    pub proof fn same_except_trap_frame_imply_wf(&self, prev: ProcessManager, t_ptr: ThreadPtr)
        requires
            prev.wf(),
            prev.thread_dom().contains(t_ptr),
            self.same_except_trap_frame(prev, t_ptr),
            self.thread_perms@[t_ptr].is_init(),
            self.thread_perms@[t_ptr].addr() == t_ptr,
        ensures
            self.wf(),
    {
        broadcast use ProcessManager::reveal_process_manager_wf;

        assert(self.container_perms_wf());
        assert(self.container_tree_wf());
        assert(self.container_fields_wf());
        assert(self.proc_perms_wf());
        assert(self.process_trees_wf());
        assert(self.process_fields_wf());
        assert(self.cpus_wf());
        assert(self.container_cpu_wf());
        assert(self.memory_disjoint());
        assert(self.processes_container_wf());
        assert(self.threads_process_wf());
        assert(self.threads_perms_wf());
        assert(self.endpoint_perms_wf());
        assert(self.threads_endpoint_descriptors_wf());
        assert(self.endpoints_queue_wf());
        assert(self.endpoints_container_wf());
        assert(self.schedulers_wf());
        assert(self.pcid_ioid_wf());
        assert(self.threads_cpu_wf());
        assert(self.threads_container_wf());
    }
}

} // verus!

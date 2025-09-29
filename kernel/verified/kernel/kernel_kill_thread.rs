use vstd::prelude::*;
verus! {
use crate::define::*;
use crate::kernel::Kernel;
use crate::va_range::*;
use crate::process_manager::spec_util::*;
use crate::process_manager::spec_impl::*;
impl Kernel {
    pub fn kernel_kill_thread(&mut self, thread_ptr: ThreadPtr)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
        ensures
            // self.wf(),
    {

        let thread_state = self.proc_man.get_thread(thread_ptr).state;
        let blocking_endpoint_index = self.proc_man.get_thread(thread_ptr).blocking_endpoint_index;

        assert(thread_state == ThreadState::BLOCKED ==> blocking_endpoint_index.is_Some()) by {
            broadcast use ProcessManager::reveal_process_manager_wf;
        }

        for i in 0..MAX_NUM_ENDPOINT_DESCRIPTORS
            invariant
                0 <= i <= MAX_NUM_ENDPOINT_DESCRIPTORS,
                self.wf(),
                self.thread_dom().contains(thread_ptr),
                self.container_dom() == old(self).container_dom(),
                self.proc_dom() == old(self).proc_dom(),
                self.thread_dom() == old(self).thread_dom(),
                containers_tree_unchanged(old(self).proc_man, self.proc_man),
                containers_owned_proc_unchanged(old(self).proc_man, self.proc_man),
                processes_unchanged(old(self).proc_man, self.proc_man),
                threads_unchanged_except(old(self).proc_man, self.proc_man, set![thread_ptr]),
                self.get_thread(thread_ptr).state == old(self).get_thread(thread_ptr).state,
                self.get_thread(thread_ptr).state == thread_state,
                self.get_thread(thread_ptr).blocking_endpoint_index == old(self).get_thread(thread_ptr).blocking_endpoint_index,
                self.get_thread(thread_ptr).blocking_endpoint_index == blocking_endpoint_index,
                thread_state == ThreadState::BLOCKED ==> blocking_endpoint_index.is_Some(),
                forall|j:EndpointIdx| #![auto] 0<=j<i 
                    ==> 
                    (thread_state == ThreadState::BLOCKED && blocking_endpoint_index == Some(j))
                    ||
                    self.get_thread(thread_ptr).endpoint_descriptors@[j as int].is_None(),
        {
            match thread_state {
                ThreadState::BLOCKED => {
                    if blocking_endpoint_index.unwrap() != i {
                        self.kernel_drop_endpoint(thread_ptr, i);
                    }
                },
                _ => {
                    self.kernel_drop_endpoint(thread_ptr, i);
                }
            }
        }

        match self.proc_man.get_thread(thread_ptr).state {
            ThreadState::SCHEDULED => {
                self.proc_man.kill_scheduled_thread(thread_ptr);
            },
            ThreadState::BLOCKED => {
                self.proc_man.kill_blocked_thread(thread_ptr);
            },
            ThreadState::RUNNING => {
                self.proc_man.kill_running_thread(thread_ptr);
            },
        
        }
    }
}

}
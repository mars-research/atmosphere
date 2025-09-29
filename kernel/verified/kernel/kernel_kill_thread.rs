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
            self.wf(),
            self.thread_dom() == old(self).thread_dom().remove(thread_ptr),
            threads_unchanged_except(old(self).proc_man, self.proc_man, set![]),
            self.proc_dom() == old(self).proc_dom(),
            process_tree_unchanged(old(self).proc_man, self.proc_man),
            self.container_dom() == old(self).container_dom(),
            containers_tree_unchanged(old(self).proc_man, self.proc_man),
            self.get_proc(old(self).get_thread(thread_ptr).owning_proc).owned_threads@ == 
              old(self).get_proc(old(self).get_thread(thread_ptr).owning_proc).owned_threads@.remove_value(thread_ptr), 
            self.get_proc(old(self).get_thread(thread_ptr).owning_proc).owned_threads.len() == 
              old(self).get_proc(old(self).get_thread(thread_ptr).owning_proc).owned_threads.len() - 1,  
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
                old(self).get_thread(thread_ptr).owning_proc == self.get_thread(thread_ptr).owning_proc,
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
                let (page_ptr, page_perm) = self.proc_man.kill_scheduled_thread(thread_ptr);
                self.page_alloc.free_page_4k(page_ptr, page_perm);
                assert(self.memory_wf()) by {
                    assert(self.mem_man.page_closure() + self.proc_man.page_closure()
                    == self.page_alloc.allocated_pages_4k());
                assert(self.page_alloc.mapped_pages_2m() =~= Set::empty());
                assert(self.page_alloc.mapped_pages_1g() =~= Set::empty());
                assert(self.page_alloc.allocated_pages_2m() =~= Set::empty());
                assert(self.page_alloc.allocated_pages_1g() =~= Set::empty());
                assert(self.page_alloc.container_map_4k@.dom() =~= self.proc_man.container_dom());
                assert(self.page_alloc.container_map_2m@.dom() =~= self.proc_man.container_dom());
                assert(self.page_alloc.container_map_1g@.dom() =~= self.proc_man.container_dom());
                };
                assert(self.page_mapping_wf());
                assert(self.mapping_wf());
                assert(self.pcid_ioid_wf());
            },
            ThreadState::BLOCKED => {
                let ((page_ptr, page_perm), page_op) = self.proc_man.kill_blocked_thread(thread_ptr);
                self.page_alloc.free_page_4k(page_ptr, page_perm);
                if let Some((page_ptr2, page_perm2)) = page_op{
                    self.page_alloc.free_page_4k(page_ptr2, page_perm2);
                }
                assert(self.memory_wf()) by {
                    assert(self.mem_man.page_closure() + self.proc_man.page_closure()
                    == self.page_alloc.allocated_pages_4k());
                assert(self.page_alloc.mapped_pages_2m() =~= Set::empty());
                assert(self.page_alloc.mapped_pages_1g() =~= Set::empty());
                assert(self.page_alloc.allocated_pages_2m() =~= Set::empty());
                assert(self.page_alloc.allocated_pages_1g() =~= Set::empty());
                assert(self.page_alloc.container_map_4k@.dom() =~= self.proc_man.container_dom());
                assert(self.page_alloc.container_map_2m@.dom() =~= self.proc_man.container_dom());
                assert(self.page_alloc.container_map_1g@.dom() =~= self.proc_man.container_dom());
                };
                assert(self.page_mapping_wf());
                assert(self.mapping_wf());
                assert(self.pcid_ioid_wf());
            },
            ThreadState::RUNNING => {
                let (page_ptr, page_perm) = self.proc_man.kill_running_thread(thread_ptr);
                self.page_alloc.free_page_4k(page_ptr, page_perm);
                assert(self.memory_wf()) by {
                    assert(self.mem_man.page_closure() + self.proc_man.page_closure()
                    == self.page_alloc.allocated_pages_4k());
                assert(self.page_alloc.mapped_pages_2m() =~= Set::empty());
                assert(self.page_alloc.mapped_pages_1g() =~= Set::empty());
                assert(self.page_alloc.allocated_pages_2m() =~= Set::empty());
                assert(self.page_alloc.allocated_pages_1g() =~= Set::empty());
                assert(self.page_alloc.container_map_4k@.dom() =~= self.proc_man.container_dom());
                assert(self.page_alloc.container_map_2m@.dom() =~= self.proc_man.container_dom());
                assert(self.page_alloc.container_map_1g@.dom() =~= self.proc_man.container_dom());
                };
                assert(self.page_mapping_wf());
                assert(self.mapping_wf());
                assert(self.pcid_ioid_wf());
            },
        
        }
    }

    pub fn kernel_proc_kill_all_threads(&mut self, proc_ptr: ProcPtr)
        requires
            old(self).wf(),
            old(self).proc_dom().contains(proc_ptr),
        ensures
            self.wf(),
            self.proc_dom().contains(proc_ptr),
            self.get_proc(proc_ptr).owned_threads.len() == 0,

            self.proc_dom() == old(self).proc_dom(),
            process_tree_unchanged(old(self).proc_man, self.proc_man),
            self.container_dom() == old(self).container_dom(),
            containers_tree_unchanged(old(self).proc_man, self.proc_man),
    {
        let num_threads = self.proc_man.get_proc(proc_ptr).owned_threads.len();
        assert(self.get_proc(proc_ptr).owned_threads.len()  == num_threads) by {
            broadcast use ProcessManager::reveal_process_manager_wf;
            };
        for i in 0..num_threads
            invariant
            self.wf(),
            self.proc_dom().contains(proc_ptr),
            self.get_proc(proc_ptr).owned_threads.len() == num_threads - i,

            self.proc_dom() == old(self).proc_dom(),
            process_tree_unchanged(old(self).proc_man, self.proc_man),
            self.container_dom() == old(self).container_dom(),
            containers_tree_unchanged(old(self).proc_man, self.proc_man),
        {
            let thread_ptr = self.proc_man.get_proc(proc_ptr).owned_threads.get_head();
            assert(self.proc_man.get_proc(proc_ptr).owned_threads@.contains(thread_ptr)); // Why....
            assert(self.thread_dom().contains(thread_ptr)) by {broadcast use ProcessManager::reveal_process_manager_wf;};
            assert(self.get_thread(thread_ptr).owning_proc == proc_ptr) by {broadcast use ProcessManager::reveal_process_manager_wf;};
            self.kernel_kill_thread(thread_ptr);
        }

    }
}

}
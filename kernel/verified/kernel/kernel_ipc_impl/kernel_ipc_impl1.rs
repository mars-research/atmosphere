// use vstd::prelude::*;
// verus!{

// // use crate::array_vec::*;
// use crate::proc::*;
// // use crate::page_alloc::*;
// // use crate::cpu::*;
// // use crate::mars_array::MarsArray;
// // use crate::pagetable::*;
// use crate::cpu::*;
// use crate::define::*;
// use crate::trap::*;
// // use crate::page_alloc::*;

// use crate::kernel::*;

// impl Kernel {

//     pub fn kernel_push_current_thread_to_endpoint(&mut self, cpu_id:CPUID, thread_ptr: ThreadPtr, endpoint_idx: EndpointIdx, ipc_payload: IPCPayLoad, pt_regs: Registers)
//         requires
//             old(self).wf(),
//             0<=cpu_id<NUM_CPUS,
//             old(self).cpu_list@[cpu_id as int].get_is_idle() == false,
//             old(self).cpu_list@[cpu_id as int].get_current_thread().unwrap() == thread_ptr,
//             0<=endpoint_idx<MAX_NUM_ENDPOINT_DESCRIPTORS,
//             old(self).proc_man.get_thread(thread_ptr).endpoint_descriptors@[endpoint_idx as int] != 0,
//             old(self).proc_man.get_endpoint(old(self).proc_man.get_thread(thread_ptr).endpoint_descriptors@[endpoint_idx as int]).len() < MAX_NUM_THREADS_PER_ENDPOINT,
//     {
//         if self.proc_man.scheduler.len() == 0{
//             assert(self.proc_man.get_thread(thread_ptr).endpoint_descriptors@[endpoint_idx as int] != 0);
//             self.proc_man.set_thread_to_transit(thread_ptr);
//             self.proc_man.push_endpoint(thread_ptr, endpoint_idx, ipc_payload);
//             self.cpu_list.set_current_thread(cpu_id, None);
//             assert(self.wf());
//         }else{
//             self.proc_man.set_thread_to_transit(thread_ptr);
//             self.proc_man.push_endpoint(thread_ptr, endpoint_idx, ipc_payload);
//             let new_thread_ptr = self.proc_man.pop_scheduler();
//             self.cpu_list.set_current_thread(cpu_id, Some(new_thread_ptr));
//             assert(self.wf());
//         }

//     }

//     pub fn kernel_pop_receiver_endpoint(&mut self, cpu_id:CPUID, thread_ptr: ThreadPtr, endpoint_idx:EndpointIdx) -> (ret: (ThreadPtr,ErrorCodeType))
//         requires
//             old(self).wf(),
//             0<=cpu_id<NUM_CPUS,
//             old(self).cpu_list@[cpu_id as int].get_is_idle() == false,
//             old(self).cpu_list@[cpu_id as int].get_current_thread().unwrap() == thread_ptr,
//             0<=endpoint_idx<MAX_NUM_ENDPOINT_DESCRIPTORS,
//             old(self).proc_man.get_thread(thread_ptr).endpoint_descriptors@[endpoint_idx as int] != 0,
//             old(self).proc_man.get_endpoint(old(self).proc_man.get_thread(thread_ptr).endpoint_descriptors@[endpoint_idx as int]).len() != 0,
//             old(self).proc_man.scheduler.len() != MAX_NUM_THREADS,
//         ensures
//             self.wf(),
//             self.proc_man.get_proc_ptrs() =~= old(self).proc_man.get_proc_ptrs(),
//             self.proc_man.get_thread_ptrs() =~= old(self).proc_man.get_thread_ptrs(),
//             self.page_alloc =~= old(self).page_alloc,
//             self.mmu_man =~= old(self).mmu_man,
//             self.proc_man.get_thread_ptrs().contains(ret.0),
//     {
//         let new_thread_ptr = self.proc_man.pop_endpoint(thread_ptr, endpoint_idx);

//         let sender_is_calling = self.proc_man.get_thread_if_is_calling(thread_ptr);
//         let receiver_is_calling = self.proc_man.get_thread_if_is_calling(new_thread_ptr);
//         let receiver_caller = self.proc_man.get_thread_caller(new_thread_ptr);
//         if sender_is_calling == true && receiver_is_calling == true && receiver_caller.is_none() {
//             //sender is blocked on a call to the receiver
//             self.proc_man.set_thread_caller(thread_ptr, new_thread_ptr);
//             self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
//             assert(self.wf());
//             return (new_thread_ptr,SUCCESS);
//         }

//         // assert(forall|thread_ptr:ThreadPtr|#![auto] thread_ptr != new_thread_ptr && self.proc_man.get_thread_ptrs().contains(thread_ptr) ==> self.proc_man.get_thread(thread_ptr).state != TRANSIT);
//         // assert(old(self).proc_man.get_thread(new_thread_ptr).state == BLOCKED);
//         // assert(forall|i:int|#![auto]0<=i<NUM_CPUS && old(self).cpu_list@[i].get_current_thread().is_Some()
//         //     ==> old(self).cpu_list@[i].get_current_thread().unwrap() != new_thread_ptr);
//         // self.proc_man.set_thread_to_running(new_thread_ptr);
//         self.proc_man.push_scheduler(thread_ptr);
//         self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));

//         // assert(
//         //     self.proc_man.wf());
//         // assert(
//         //     self.mmu_man.wf()
//         // );
//         // assert(

//         //     self.page_alloc.wf()
//         // );
//         // assert(
//         //     self.cpu_list.wf()
//         // );

//         // assert(
//         //     self.kernel_cpu_list_wf()
//         // );
//         // assert(
//         //     self.kernel_mem_layout_wf()
//         // );
//         // assert(self.page_alloc =~= old(self).page_alloc);
//         // assert(self.mmu_man =~= old(self).mmu_man);
//         // assert(
//         //     self.kernel_mmu_page_alloc_pagetable_wf()
//         // );
//         // assert(
//         //     self.kernel_mmu_page_alloc_iommutable_wf()
//         // );
//         // assert(self.kernel_proc_mmu_wf());
//         // assert(self.kernel_proc_no_thread_in_transit());
//         // assert(forall|i:int|#![auto]0<=i<NUM_CPUS
//         //     ==> old(self).cpu_list@[i].tlb =~= self.cpu_list@[i].tlb);
//         // assert(forall|i:int|#![auto]0<=i<NUM_CPUS
//         //     ==> old(self).cpu_list@[i].iotlb =~= self.cpu_list@[i].iotlb);
//         // assert(self.kernel_tlb_wf());

//         assert(self.wf());

//         if sender_is_calling == true || receiver_is_calling == true {
//             return (new_thread_ptr, CALL_FAILED);
//         }

//         return (new_thread_ptr, SUCCESS);
//     }

//     pub fn kernel_pop_sender_endpoint(&mut self, cpu_id:CPUID, thread_ptr: ThreadPtr, endpoint_idx:EndpointIdx) -> (ret: (ThreadPtr,ErrorCodeType))
//         requires
//             old(self).wf(),
//             0<=cpu_id<NUM_CPUS,
//             old(self).cpu_list@[cpu_id as int].get_is_idle() == false,
//             old(self).cpu_list@[cpu_id as int].get_current_thread().unwrap() == thread_ptr,
//             0<=endpoint_idx<MAX_NUM_ENDPOINT_DESCRIPTORS,
//             old(self).proc_man.get_thread(thread_ptr).endpoint_descriptors@[endpoint_idx as int] != 0,
//             old(self).proc_man.get_endpoint(old(self).proc_man.get_thread(thread_ptr).endpoint_descriptors@[endpoint_idx as int]).len() != 0,
//             old(self).proc_man.scheduler.len() != MAX_NUM_THREADS,
//         ensures
//             self.wf(),
//             self.proc_man.get_proc_ptrs() =~= old(self).proc_man.get_proc_ptrs(),
//             self.proc_man.get_thread_ptrs() =~= old(self).proc_man.get_thread_ptrs(),
//             self.page_alloc =~= old(self).page_alloc,
//             self.mmu_man =~= old(self).mmu_man,
//             self.proc_man.get_thread_ptrs().contains(ret.0),
//     {
//         let new_thread_ptr = self.proc_man.pop_endpoint(thread_ptr, endpoint_idx);

//         let receiver_is_calling = self.proc_man.get_thread_if_is_calling(thread_ptr);
//         let sender_is_calling = self.proc_man.get_thread_if_is_calling(new_thread_ptr);
//         let receiver_caller = self.proc_man.get_thread_caller(thread_ptr);
//         if sender_is_calling == true && receiver_is_calling == true && receiver_caller.is_none() {
//             //sender is blocked on a call to the receiver
//             self.proc_man.set_thread_caller(new_thread_ptr, thread_ptr);
//             self.cpu_list.set_current_thread(cpu_id,Some(thread_ptr));
//             assert(self.wf());
//             return (new_thread_ptr,SUCCESS);
//         }

//         // assert(forall|thread_ptr:ThreadPtr|#![auto] thread_ptr != new_thread_ptr && self.proc_man.get_thread_ptrs().contains(thread_ptr) ==> self.proc_man.get_thread(thread_ptr).state != TRANSIT);
//         // assert(old(self).proc_man.get_thread(new_thread_ptr).state == BLOCKED);
//         // assert(forall|i:int|#![auto]0<=i<NUM_CPUS && old(self).cpu_list@[i].get_current_thread().is_Some()
//         //     ==> old(self).cpu_list@[i].get_current_thread().unwrap() != new_thread_ptr);
//         // self.proc_man.set_thread_to_running(new_thread_ptr);
//         self.proc_man.push_scheduler(thread_ptr);
//         self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));

//         // assert(
//         //     self.proc_man.wf());
//         // assert(
//         //     self.mmu_man.wf()
//         // );
//         // assert(

//         //     self.page_alloc.wf()
//         // );
//         // assert(
//         //     self.cpu_list.wf()
//         // );

//         // assert(
//         //     self.kernel_cpu_list_wf()
//         // );
//         // assert(
//         //     self.kernel_mem_layout_wf()
//         // );
//         // assert(self.page_alloc =~= old(self).page_alloc);
//         // assert(self.mmu_man =~= old(self).mmu_man);
//         // assert(
//         //     self.kernel_mmu_page_alloc_pagetable_wf()
//         // );
//         // assert(
//         //     self.kernel_mmu_page_alloc_iommutable_wf()
//         // );
//         // assert(self.kernel_proc_mmu_wf());
//         // assert(self.kernel_proc_no_thread_in_transit());
//         // assert(forall|i:int|#![auto]0<=i<NUM_CPUS
//         //     ==> old(self).cpu_list@[i].tlb =~= self.cpu_list@[i].tlb);
//         // assert(forall|i:int|#![auto]0<=i<NUM_CPUS
//         //     ==> old(self).cpu_list@[i].iotlb =~= self.cpu_list@[i].iotlb);
//         // assert(self.kernel_tlb_wf());

//         assert(self.wf());

//         if sender_is_calling == true || receiver_is_calling == true {
//             return (new_thread_ptr, CALL_FAILED);
//         }

//         return (new_thread_ptr, SUCCESS);
//     }
// }
// }

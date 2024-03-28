use vstd::prelude::*;
verus! {

// use crate::array_vec::*;
// use crate::proc::*;
// use crate::page_alloc::*;
// use crate::cpu::*;
// use crate::mars_array::MarsArray;
use crate::proc::*;
use crate::pagetable::*;
use crate::cpu::*;
use crate::define::*;
use crate::trap::*;
// use crate::page_alloc::*;
use crate::page_alloc::*;

use crate::kernel::*;


impl Kernel {
    pub fn syscall_send_wait(&mut self, cpu_id:CPUID, pt_regs: Registers, endpoint_index: EndpointIdx, ipc_payload:IPCPayLoad) -> (ret: SyscallReturnStruct)
        requires
            old(self).wf(),
        ensures
            self.wf(),
    {
        let (default_pcid, default_cr3) = self.mmu_man.get_reserved_pcid_and_cr3();
        if cpu_id >= NUM_CPUS{
            return SyscallReturnStruct::new(CPU_ID_INVALID,default_pcid,default_cr3,pt_regs);
        }

        if self.cpu_list.get(cpu_id).get_is_idle() {
            return SyscallReturnStruct::new(CPU_NO_IDLE,default_pcid,default_cr3,pt_regs);
        }

        assert(self.cpu_list[cpu_id as int].get_is_idle() == false);
        let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
        assert(current_thread_ptr_op.is_Some());
        let current_thread_ptr = current_thread_ptr_op.unwrap();

        let pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
        let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);

        if endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS{
            return SyscallReturnStruct::new(ENDPOINT_INDEX_INVALID,pcid,cr3,pt_regs);
        }

        let target_endpoint_ptr = self.proc_man.get_thread_endpoint_ptr_by_endpoint_idx(current_thread_ptr, endpoint_index);
        if target_endpoint_ptr == 0 {
            return SyscallReturnStruct::new(SHARED_ENDPOINT_NOT_EXIST,pcid,cr3,pt_regs);
        }

        if self.proc_man.get_endpoint_state_by_endpoint_ptr(target_endpoint_ptr) == SEND {
            //sender queue
            if self.proc_man.get_endpoint_len_by_endpoint_ptr(target_endpoint_ptr) == MAX_NUM_THREADS_PER_ENDPOINT{
                return SyscallReturnStruct::new(ENDPOINT_FULL,pcid,cr3,pt_regs);
            }

            // self.kernel_push_current_thread_to_endpoint()
            if self.proc_man.scheduler.len() == 0{
                //block current thread on endpoint and spin current cpu
                assert(self.proc_man.get_thread(current_thread_ptr).endpoint_descriptors@[endpoint_index as int] != 0);
                self.proc_man.push_endpoint(current_thread_ptr, endpoint_index, ipc_payload, pt_regs);
                self.cpu_list.set_current_thread(cpu_id, None);
                assert(self.wf());
                return SyscallReturnStruct::new(NO_NEXT_THREAD,0,0,pt_regs);
            }else{
                //block current thread on endpoint and pop scheduler
                self.proc_man.push_endpoint(current_thread_ptr, endpoint_index, ipc_payload, pt_regs);
                let (new_thread_ptr,new_pt_regs,error_code)  = self.proc_man.pop_scheduler();
                self.cpu_list.set_current_thread(cpu_id, Some(new_thread_ptr));
                assert(self.wf());
                let new_pcid = self.proc_man.get_pcid_by_thread_ptr(new_thread_ptr);
                let new_cr3 = self.mmu_man.get_cr3_by_pcid(new_pcid);
                if error_code.is_none(){
                    return SyscallReturnStruct::new(NO_ERROR_CODE,new_pcid,new_cr3,new_pt_regs);
                }else{
                    return SyscallReturnStruct::new(error_code.unwrap(),new_pcid,new_cr3,new_pt_regs);
                }
            }
        }
        else{
            //receiver queue
            if self.proc_man.get_endpoint_len_by_endpoint_ptr(target_endpoint_ptr) == 0{
                //change the endpoint to a sender queue.

                // self.proc_man.proc_man_set_endpoint_queue_state_by_endpoint_ptr(target_endpoint_ptr, SEND);
                // assert(self.wf());
                if self.proc_man.scheduler.len() == 0{
                    //block current thread on endpoint and spin current cpu
                    assert(self.proc_man.get_thread(current_thread_ptr).endpoint_descriptors@[endpoint_index as int] != 0);
                    self.proc_man.push_endpoint_and_set_state(current_thread_ptr, endpoint_index, ipc_payload, pt_regs, SEND);
                    self.cpu_list.set_current_thread(cpu_id, None);
                    assert(self.wf());
                    return SyscallReturnStruct::new(NO_NEXT_THREAD,0,0,pt_regs);
                }else{
                    //block current thread on endpoint and pop scheduler
                    self.proc_man.push_endpoint_and_set_state(current_thread_ptr, endpoint_index, ipc_payload, pt_regs, SEND);
                    let (new_thread_ptr,new_pt_regs,error_code)  = self.proc_man.pop_scheduler();
                    self.cpu_list.set_current_thread(cpu_id, Some(new_thread_ptr));
                    assert(self.wf());
                    let new_pcid = self.proc_man.get_pcid_by_thread_ptr(new_thread_ptr);
                    let new_cr3 = self.mmu_man.get_cr3_by_pcid(new_pcid);
                    let error_code = self.proc_man.get_error_code_by_thread_ptr(new_thread_ptr);
                    if error_code.is_none(){
                        return SyscallReturnStruct::new(NO_ERROR_CODE,new_pcid,new_cr3,new_pt_regs);
                    }else{
                        return SyscallReturnStruct::new(error_code.unwrap(),new_pcid,new_cr3,new_pt_regs);
                    }
                }

            }
                // pop the receiver.
                if self.proc_man.scheduler.len() == MAX_NUM_THREADS {
                    return SyscallReturnStruct::new(SCHEDULER_NO_SPACE,pcid,cr3,pt_regs);
                }

                let (new_thread_ptr,new_pt_regs) = self.proc_man.pop_endpoint_to_running(current_thread_ptr, endpoint_index);

                let receiver_caller = self.proc_man.get_thread_caller(new_thread_ptr);

                let sender_ipc_payload = ipc_payload;
                let receiver_ipc_payload = self.proc_man.get_ipc_payload_by_thread_ptr(new_thread_ptr);

                let sender_pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
                let receiver_pcid = self.proc_man.get_pcid_by_thread_ptr(new_thread_ptr);
                assert(0<=sender_pcid<PCID_MAX);
                assert(self.mmu_man.get_free_pcids_as_set().contains(sender_pcid) == false);
                assert(0<=receiver_pcid<PCID_MAX);
                assert(self.mmu_man.get_free_pcids_as_set().contains(receiver_pcid) == false);

                let new_pcid = self.proc_man.get_pcid_by_thread_ptr(new_thread_ptr);
                let new_cr3 = self.mmu_man.get_cr3_by_pcid(new_pcid);

                if sender_ipc_payload.calling == true || receiver_ipc_payload.calling == true {
                    //one of them is calling
                    if sender_ipc_payload.calling != true || receiver_ipc_payload.calling != true || receiver_caller.is_some()
                        || sender_ipc_payload.message.is_none() || receiver_ipc_payload.message.is_none()
                        || sender_ipc_payload.page_payload.is_some() || receiver_ipc_payload.page_payload.is_some()
                        || sender_ipc_payload.endpoint_payload.is_some() || receiver_ipc_payload.endpoint_payload.is_some()
                        || sender_ipc_payload.pci_payload.is_some() || receiver_ipc_payload.pci_payload.is_some()
                    {
                        self.proc_man.push_scheduler(current_thread_ptr, Some(CALL_FAILED),pt_regs);
                        self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
                        return SyscallReturnStruct::new(CALL_FAILED,new_pcid,new_cr3,new_pt_regs);
                    }else{
                        let sender_va = sender_ipc_payload.message.unwrap().0;
                        let receiver_va = receiver_ipc_payload.message.unwrap().0;

                        let sender_len = sender_ipc_payload.message.unwrap().1;
                        let receiver_len = receiver_ipc_payload.message.unwrap().1;

                        if (va_valid(sender_va) == false) || (va_valid(receiver_va) == false) || (sender_len != receiver_len)
                            || (receiver_len>4096) || (receiver_len<=0)
                        {
                            self.proc_man.push_scheduler(current_thread_ptr, Some(CALL_FAILED),pt_regs);
                            self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
                            return SyscallReturnStruct::new(CALL_FAILED,new_pcid,new_cr3,new_pt_regs);
                        }else{
                            let sender_pa_op = self.mmu_man.mmu_get_va_entry_by_pcid(pcid,sender_va);
                            let receiver_pa_op = self.mmu_man.mmu_get_va_entry_by_pcid(new_pcid,receiver_va);

                            if sender_pa_op.is_none() || receiver_pa_op.is_none() {
                                self.proc_man.push_scheduler(current_thread_ptr, Some(CALL_FAILED),pt_regs);
                                self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
                                return SyscallReturnStruct::new(CALL_FAILED,new_pcid,new_cr3,new_pt_regs);
                            }else{
                                let sender_pa = sender_pa_op.unwrap().addr;
                                let receiver_pa = receiver_pa_op.unwrap().addr;

                                if sender_pa == receiver_pa {
                                    self.proc_man.push_scheduler(current_thread_ptr, Some(CALL_FAILED),pt_regs);
                                    self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
                                    return SyscallReturnStruct::new(CALL_FAILED,new_pcid,new_cr3,new_pt_regs);
                                }else{
                                    self.kernel_pass_message(sender_pa, receiver_pa, receiver_len);

                                    self.proc_man.set_thread_caller(current_thread_ptr, new_thread_ptr, pt_regs);
                                    self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));

                                    return SyscallReturnStruct::new(SUCCESS,new_pcid,new_cr3,new_pt_regs);
                                }
                            }
                        }
                    }
                }
                else if sender_ipc_payload.message.is_some() || receiver_ipc_payload.message.is_some()
                {
                    //sharing message
                    if sender_ipc_payload.message.is_none() || receiver_ipc_payload.message.is_none() {
                        self.proc_man.push_scheduler(current_thread_ptr, Some(MESSAGE_INVALID),pt_regs);
                        self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
                        return SyscallReturnStruct::new(MESSAGE_INVALID,new_pcid,new_cr3,new_pt_regs);
                    }
                    else if sender_ipc_payload.page_payload.is_some() || receiver_ipc_payload.page_payload.is_some()
                        || sender_ipc_payload.endpoint_payload.is_some() || receiver_ipc_payload.endpoint_payload.is_some()
                        || sender_ipc_payload.pci_payload.is_some() || receiver_ipc_payload.pci_payload.is_some()
                    {
                        self.proc_man.push_scheduler(current_thread_ptr, Some(MESSAGE_INVALID),pt_regs);
                        self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
                        return SyscallReturnStruct::new(MESSAGE_INVALID,new_pcid,new_cr3,new_pt_regs);
                    }
                    else{
                        let sender_va = sender_ipc_payload.message.unwrap().0;
                        let receiver_va = receiver_ipc_payload.message.unwrap().0;

                        let sender_len = sender_ipc_payload.message.unwrap().1;
                        let receiver_len = receiver_ipc_payload.message.unwrap().1;

                        if (va_valid(sender_va) == false) || (va_valid(receiver_va) == false) || (sender_len != receiver_len)
                            || (receiver_len>4096) || (receiver_len<=0)
                        {
                            self.proc_man.push_scheduler(current_thread_ptr, Some(MESSAGE_INVALID),pt_regs);
                            self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
                            return SyscallReturnStruct::new(MESSAGE_INVALID,new_pcid,new_cr3,new_pt_regs);
                        }else{
                            let sender_pa_op = self.mmu_man.mmu_get_va_entry_by_pcid(pcid,sender_va);
                            let receiver_pa_op = self.mmu_man.mmu_get_va_entry_by_pcid(new_pcid,receiver_va);

                            if sender_pa_op.is_none() || receiver_pa_op.is_none() {
                                self.proc_man.push_scheduler(current_thread_ptr, Some(MESSAGE_INVALID),pt_regs);
                                self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
                                return SyscallReturnStruct::new(MESSAGE_INVALID,new_pcid,new_cr3,new_pt_regs);
                            }else{
                                let sender_pa = sender_pa_op.unwrap().addr;
                                let receiver_pa = receiver_pa_op.unwrap().addr;

                                if sender_pa == receiver_pa {
                                    self.proc_man.push_scheduler(current_thread_ptr, Some(MESSAGE_INVALID),pt_regs);
                                    self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
                                    return SyscallReturnStruct::new(MESSAGE_INVALID,new_pcid,new_cr3,new_pt_regs);
                                }else{
                                    self.kernel_pass_message(sender_pa, receiver_pa, receiver_len);

                                    self.proc_man.push_scheduler(current_thread_ptr, Some(SUCCESS),pt_regs);
                                    self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
                                    return SyscallReturnStruct::new(SUCCESS,new_pcid,new_cr3,new_pt_regs);
                                }
                            }
                        }
                    }

                }else if sender_ipc_payload.page_payload.is_some() || receiver_ipc_payload.page_payload.is_some()
                {
                    //sharing pages
                    if sender_ipc_payload.page_payload.is_none() || receiver_ipc_payload.page_payload.is_none()
                        || sender_ipc_payload.endpoint_payload.is_some() || receiver_ipc_payload.endpoint_payload.is_some()
                        || sender_ipc_payload.pci_payload.is_some() || receiver_ipc_payload.pci_payload.is_some()
                    {
                        self.proc_man.push_scheduler(current_thread_ptr, Some(PAGE_PAYLOAD_INVALID),pt_regs);
                        self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
                        return SyscallReturnStruct::new(PAGE_PAYLOAD_INVALID,new_pcid,new_cr3,new_pt_regs);
                    }else{
                        let (sender_page_start,sender_page_len) = sender_ipc_payload.page_payload.unwrap();
                        let (receiver_page_start,receiver_page_len) = receiver_ipc_payload.page_payload.unwrap();
                        let perm_bits = READ_WRITE_EXECUTE as usize;

                        if sender_page_len != receiver_page_len || sender_page_len >= usize::MAX/3 || va_perm_bits_valid(perm_bits) == false
                            || self.page_alloc.free_pages.len() < 3 * sender_page_len
                        {   self.proc_man.push_scheduler(current_thread_ptr, Some(PAGE_PAYLOAD_INVALID),pt_regs);
                            self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
                            return SyscallReturnStruct::new(PAGE_PAYLOAD_INVALID,new_pcid,new_cr3,new_pt_regs);
                        }else{
                            if self.kernel_page_sharing_helper(sender_pcid, receiver_pcid, perm_bits, sender_page_start, receiver_page_start, sender_page_len){
                                self.proc_man.push_scheduler(current_thread_ptr, Some(SUCCESS),pt_regs);
                                self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
                                self.kernel_map_pagetable_range_page_to_pagetable(sender_pcid, receiver_pcid, sender_page_start, receiver_page_start, perm_bits,sender_page_len);
                                return SyscallReturnStruct::new(SUCCESS,new_pcid,new_cr3,new_pt_regs);
                            }else{
                                self.proc_man.push_scheduler(current_thread_ptr, Some(PAGE_PAYLOAD_INVALID),pt_regs);
                                self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
                                return SyscallReturnStruct::new(PAGE_PAYLOAD_INVALID,new_pcid,new_cr3,new_pt_regs);
                            }
                        }
                    }

                }else if sender_ipc_payload.endpoint_payload.is_some() || receiver_ipc_payload.endpoint_payload.is_some()
                {
                    //sharing endpoint
                    if sender_ipc_payload.endpoint_payload.is_none() || receiver_ipc_payload.endpoint_payload.is_none() {
                        self.proc_man.push_scheduler(current_thread_ptr, Some(ENDPOINT_PAYLOAD_INVALID),pt_regs);
                        self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
                        return SyscallReturnStruct::new(ENDPOINT_PAYLOAD_INVALID,new_pcid,new_cr3,new_pt_regs);
                    }else{
                        let sender_endpoint_index = sender_ipc_payload.endpoint_payload.unwrap();
                        let receiver_endpoint_index = receiver_ipc_payload.endpoint_payload.unwrap();

                        if sender_endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS || receiver_endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS {
                            self.proc_man.push_scheduler(current_thread_ptr, Some(ENDPOINT_PAYLOAD_INVALID),pt_regs);
                            self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
                            return SyscallReturnStruct::new(ENDPOINT_PAYLOAD_INVALID,new_pcid,new_cr3,new_pt_regs);
                        }else{
                            let sender_endpoint_ptr = self.proc_man.get_thread_endpoint_ptr_by_endpoint_idx(current_thread_ptr, sender_endpoint_index);
                            let receiver_endpoint_ptr = self.proc_man.get_thread_endpoint_ptr_by_endpoint_idx(new_thread_ptr, receiver_endpoint_index);

                            if sender_endpoint_ptr == 0 || receiver_endpoint_ptr != 0
                                ||self.proc_man.get_endpoint_rf_counter_by_endpoint_ptr(sender_endpoint_ptr) == usize::MAX
                                ||self.proc_man.check_receiver_endpoint_descriptors(new_thread_ptr, sender_endpoint_ptr) == false
                            {
                                self.proc_man.push_scheduler(current_thread_ptr, Some(ENDPOINT_PAYLOAD_INVALID),pt_regs);
                                self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
                                return SyscallReturnStruct::new(ENDPOINT_PAYLOAD_INVALID,new_pcid,new_cr3,new_pt_regs);
                            }else{
                            // assert(self == old(self));
                            self.proc_man.pass_endpoint(current_thread_ptr,sender_endpoint_index,new_thread_ptr,receiver_endpoint_index);
                            self.proc_man.push_scheduler(current_thread_ptr, Some(SUCCESS),pt_regs);
                            self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));

                            return SyscallReturnStruct::new(SUCCESS,new_pcid,new_cr3,new_pt_regs);
                            }
                        }
                    }
                }else if sender_ipc_payload.pci_payload.is_some() || receiver_ipc_payload.pci_payload.is_some()
                {
                    //sending
                    let ipc_success = true;
                    if sender_ipc_payload.pci_payload.is_none() || receiver_ipc_payload.pci_payload.is_none() {
                        self.proc_man.push_scheduler(current_thread_ptr, Some(PCI_DEV_PAYLOAD_INVALID),pt_regs);
                        self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
                        return SyscallReturnStruct::new(PCI_DEV_PAYLOAD_INVALID,new_pcid,new_cr3,new_pt_regs);
                    }else{
                        let (sender_bus,sender_dev,sender_fun) = sender_ipc_payload.pci_payload.unwrap();
                        let (receiver_bus,receiver_dev,receiver_fun) = receiver_ipc_payload.pci_payload.unwrap();

                        if sender_dev >= 32u8 || sender_fun >= 8u8
                            || receiver_dev >= 32u8 || receiver_fun >= 8u8
                        {
                            self.proc_man.push_scheduler(current_thread_ptr, Some(PCI_DEV_PAYLOAD_INVALID),pt_regs);
                            self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
                            return SyscallReturnStruct::new(PCI_DEV_PAYLOAD_INVALID,new_pcid,new_cr3,new_pt_regs);
                        }else{
                            let sender_ioid_op = self.proc_man.get_ioid_by_thread_ptr(current_thread_ptr);
                            let receive_ioid_op = self.proc_man.get_ioid_by_thread_ptr(new_thread_ptr);

                            if sender_ioid_op.is_none() || receive_ioid_op.is_none()
                                ||self.mmu_man.mmu_get_pci_dev_by_ioid(sender_ioid_op.unwrap(),sender_bus,sender_dev,sender_fun) == false
                                || self.mmu_man.mmu_get_pci_dev_by_ioid(receive_ioid_op.unwrap(),receiver_bus,receiver_dev,receiver_fun) == true
                            {
                                self.proc_man.push_scheduler(current_thread_ptr, Some(PCI_DEV_PAYLOAD_INVALID),pt_regs);
                                self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
                                return SyscallReturnStruct::new(PCI_DEV_PAYLOAD_INVALID,new_pcid,new_cr3,new_pt_regs);
                            }else{
                                self.mmu_man.mmu_send_pci_dev_by_ioid(receive_ioid_op.unwrap(),receiver_bus,receiver_dev,receiver_fun);
                                self.proc_man.push_scheduler(current_thread_ptr, Some(SUCCESS),pt_regs);
                                self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
                                return SyscallReturnStruct::new(SUCCESS,new_pcid,new_cr3,new_pt_regs);
                            }
                        }
                    }

                }else{
                    self.proc_man.push_scheduler(current_thread_ptr, Some(SUCCESS),pt_regs);
                    self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));

                    return SyscallReturnStruct::new(SUCCESS,new_pcid,new_cr3,new_pt_regs);
                }
        }
    }
}
}
